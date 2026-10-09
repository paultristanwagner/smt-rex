#!/usr/bin/env python3
"""Differential test of smtrex-poly against sympy.

The Rust example `sympy_cases` emits JSON lines (inputs plus SMT-Rex's answers); this script
recomputes each answer with sympy and reports every disagreement. Run from the repository root:

    cargo build --release -p smtrex-poly --example sympy_cases
    nice -n 19 nix shell --impure \
        --expr 'with import <nixpkgs> {}; python3.withPackages (p: [ p.sympy ])' \
        -c python3 poly/tests/sympy/sympy_diff.py --count 2000 --seed 1 --jobs 4

(`nix shell nixpkgs#python3Packages.sympy` alone does not put sympy on python3's path; any
python with sympy >= 1.14 works.) `--kernel K` restricts to one kernel (gcd sqf factor res disc
roots count ran sign mres mdisc meval mgcd msqf psc ranop msign mroots); `--file F` checks a saved case file instead of running
the generator. Exit status 1 if any case mismatches.

What is checked, per kernel:
- gcd, res, disc, mres, mdisc, meval: exact equality with sympy's gcd / resultant /
  discriminant / substitution. (sympy's resultant has a sign bug when deg f < deg g; see
  sym_resultant.)
- sqf, factor: the multiset of (factor, multiplicity) and the content equal sympy's
  sqf_list / factor_list (after normalising every factor to a positive leading coefficient).
- roots: the number of distinct real roots equals sympy's count_roots; every exact root is a
  root of the given multiplicity; every interval has non-root endpoints and contains exactly one
  root by sympy's (Sturm-based) count_roots, of the multiplicity reported; intervals are ordered
  and disjoint.
- count: distinct and with-multiplicity counts on a closed interval equal sympy's count_roots
  on f and on its square-free factors.
- ran: two real roots (sympy's real_roots, indexed among distinct roots); equality must match
  sympy's exact (canonical CRootOf / radical) equality, and the order must match the sign of
  a - b evaluated to 300 digits.
- sign: the sign of q at a root of f; zero must match exact divisibility (the root is a root of
  gcd(q, f)), nonzero signs must match a 300-digit evaluation.
- mgcd: the multivariate gcd equals sympy's gcd up to sign.
- msqf: content and square-free part of the primitive part in a variable equal sympy's
  Poly(f, v).primitive() and sqf_part, up to sign.
- psc: every principal subresultant coefficient, sign included, equals the determinant of the
  subresultant submatrix computed by sympy (an omitted one must be 0).
- ranop: the sum or product of two real roots: the result's polynomial is irreducible and its
  given real root agrees with the sympy value of a + b or a * b to 120 digits.
- msign: the sign of a multivariate polynomial at a point whose coordinates are real roots
  (built like CAD samples, so coordinates are related): zero must match a 300-digit
  evaluation below 1e-250, nonzero signs must match it.
- mroots: the real roots of p(point, y): their number equals the number of real roots that
  mpmath's polyroots finds at 200 digits for the numerically evaluated coefficients, and every
  root agrees with one of them; a nullified fiber must have all coefficients numerically 0.
"""

import argparse
import json
import subprocess
import sys
from collections import Counter
from multiprocessing import Pool

import sympy
from sympy import Poly, Rational, symbols, ZZ

X = symbols("x")
XS = symbols("x0 x1 x2 x3")
DIGITS = 300


def upoly(c):
    """Ascending integer coefficients -> sympy Poly in x."""
    return Poly(list(reversed(c)) if c else [0], X, domain=ZZ)


def rat(s):
    n, d = s.split("/")
    return Rational(int(n), int(d))


def mexpr(terms):
    e = sympy.Integer(0)
    for mono, c in terms:
        t = sympy.Integer(c)
        for i, k in enumerate(mono):
            t *= XS[i] ** k
        e += t
    return sympy.expand(e)


def normalise(content, factors):
    """Make every factor's leading coefficient positive, moving signs into the content."""
    content = int(content)
    out = Counter()
    for f, k in factors:
        if f.LC() < 0:
            f = -f
            if k % 2 == 1:
                content = -content
        out[(tuple(int(c) for c in f.all_coeffs()), k)] += 1
    return content, out


def sym_resultant(f, g):
    """sympy's resultant, with the sign fixed for deg f < deg g.

    sympy 1.14's subresultant resultant swaps the arguments when deg f < deg g without the
    (-1)^(deg f * deg g) correction, so resultant(-3x-2, g) for a degree-7 g has the wrong sign
    (sympy's own sylvester(f, g, x).det() disagrees with it). Calling it with the larger degree
    first and fixing the sign gives the true Sylvester determinant.
    """
    n, m = f.degree(), g.degree()
    if n >= m:
        return f.resultant(g)
    r = g.resultant(f)
    return -r if (n * m) % 2 == 1 else r


def distinct_real_roots(f):
    seen = []
    for r in sympy.real_roots(f):
        if not seen or seen[-1] != r:
            seen.append(r)
    return seen


def check(case):
    k = case["k"]
    if k == "gcd":
        f, g = upoly(case["f"]), upoly(case["g"])
        want = sympy.gcd(f, g)
        if want.LC() < 0:
            want = -want
        got = upoly(case["r"])
        return got == want, f"want {want.as_expr()}"
    if k in ("sqf", "factor"):
        f = upoly(case["f"])
        c, fs = f.sqf_list() if k == "sqf" else f.factor_list()
        want = normalise(c, fs)
        got = normalise(case["c"], [(upoly(g), m) for g, m in case["r"]])
        return got == want, f"want {want}"
    if k == "res":
        f, g = upoly(case["f"]), upoly(case["g"])
        want = int(sym_resultant(f, g)) if not (f.is_zero or g.is_zero) else 0
        return want == int(case["r"]), f"want {want}"
    if k == "disc":
        f = upoly(case["f"])
        want = 0 if f.degree() <= 0 else int(f.discriminant())
        return want == int(case["r"]), f"want {want}"
    if k == "roots":
        f = upoly(case["f"])
        sqf = f.sqf_list()[1]
        roots = case["r"]
        if f.count_roots() != len(roots):
            return False, f"sympy counts {f.count_roots()} distinct real roots"
        prev_hi = None
        for lo_s, hi_s, m in roots:
            lo, hi = rat(lo_s), rat(hi_s)
            if prev_hi is not None and not prev_hi <= lo:
                return False, f"intervals overlap at {lo}"
            prev_hi = hi
            if lo == hi:
                lin = Poly(lo.q * X - lo.p, X, domain=ZZ)
                mult = 0
                g = f
                while g.rem(lin).is_zero:
                    g = g.quo(lin)
                    mult += 1
                if mult != m:
                    return False, f"{lo} has multiplicity {mult}, not {m}"
            else:
                if not lo < hi or f.eval(lo) == 0 or f.eval(hi) == 0:
                    return False, f"bad interval ({lo}, {hi})"
                hits = [(g, e) for g, e in sqf if g.count_roots(lo, hi) > 0]
                if len(hits) != 1 or hits[0][0].count_roots(lo, hi) != 1:
                    return False, f"({lo}, {hi}) does not isolate one root"
                if hits[0][1] != m:
                    return False, f"({lo}, {hi}) multiplicity {hits[0][1]}, not {m}"
        return True, ""
    if k == "count":
        f = upoly(case["f"])
        a = rat(case["a"]) if case["a"] is not None else None
        b = rat(case["b"]) if case["b"] is not None else None
        n = f.count_roots(a, b)
        m = sum(e * g.count_roots(a, b) for g, e in f.sqf_list()[1])
        return (n, m) == (case["n"], case["m"]), f"want n={n} m={m}"
    if k == "ran":
        a = distinct_real_roots(upoly(case["f"]))[case["i"]]
        b = distinct_real_roots(upoly(case["g"]))[case["j"]]
        eq = bool(a == b)
        d = sympy.N(a - b, DIGITS)
        if eq:
            want = 0
        else:
            if abs(d) < sympy.Float(10) ** (-DIGITS + 20):
                return False, "sympy: unequal but numerically equal (raise DIGITS)"
            want = 1 if d > 0 else -1
        ok = (want == case["r"]) and (eq == case["eq"])
        return ok, f"want cmp={want} eq={eq} ({a} vs {b})"
    if k == "sign":
        f, q = upoly(case["f"]), upoly(case["q"])
        a = distinct_real_roots(f)[case["i"]]
        if q.is_zero:
            want = 0
        else:
            g = sympy.gcd(f, q)
            vanishes = g.degree() > 0 and a in distinct_real_roots(g)
            if vanishes:
                want = 0
            else:
                v = sympy.N(q.as_expr().subs(X, a), DIGITS)
                if abs(v) < sympy.Float(10) ** (-DIGITS + 20):
                    return False, "sympy: nonzero but numerically zero (raise DIGITS)"
                want = 1 if v > 0 else -1
        return want == case["r"], f"want {want}"
    if k in ("mres", "mdisc", "meval"):
        f = mexpr(case["f"])
        v = XS[case["v"]]
        got = mexpr(case["r"])
        if k == "mres":
            g = mexpr(case["g"])
            if f == 0 or g == 0:
                want = sympy.Integer(0)
            else:
                want = sym_resultant(Poly(f, v), Poly(g, v))
                want = want.as_expr() if hasattr(want, "as_expr") else want
        elif k == "mdisc":
            if f == 0 or sympy.degree(f, v) <= 0:
                want = sympy.Integer(0)
            else:
                want = Poly(f, v).discriminant().as_expr()
        else:
            r = rat(case["x"])
            if f == 0:
                want = sympy.Integer(0)
            else:
                deg = sympy.degree(f, v)
                want = sympy.Integer(r.q) ** deg * f.subs(v, r)
        return sympy.expand(want - got) == 0, f"want {sympy.expand(want)}"
    if k == "mgcd":
        f, g, got = mexpr(case["f"]), mexpr(case["g"]), mexpr(case["r"])
        want = sympy.gcd(f, g)
        ok = sympy.expand(got - want) == 0 or sympy.expand(got + want) == 0
        return ok, f"want {want}"
    if k == "msqf":
        f = mexpr(case["f"])
        if f == 0:
            return True, ""
        v = XS[case["v"]]
        cont, prim = Poly(f, v).primitive()
        want_c = cont.as_expr() if hasattr(cont, "as_expr") else cont
        want_r = sympy.sqf_part(prim.as_expr()) if Poly(prim, v).degree() > 0 else sympy.Integer(1)
        got_c, got_r = mexpr(case["c"]), mexpr(case["r"])
        same = lambda a, b: sympy.expand(a - b) == 0 or sympy.expand(a + b) == 0  # noqa: E731
        return same(got_c, want_c) and same(got_r, want_r), f"want content {want_c}, sqf {want_r}"
    if k == "psc":
        v = XS[case["v"]]
        f, g = mexpr(case["f"]), mexpr(case["g"])
        if f == 0 or g == 0:
            return case["r"] == [], "zero input"
        F, G = Poly(f, v), Poly(g, v)
        n, m = F.degree(), G.degree()
        got = {j: mexpr(t) for j, t in case["r"]}
        if not all(j < min(n, m) for j in got):
            return False, "index out of range"
        # The determinant is a polynomial in the other variables. Symbolic determinants are
        # slow, so it is compared at random integer points (determinants commute with
        # substitution); a wrong polynomial survives four random points with negligible
        # probability (Schwartz–Zippel). Without other variables the comparison is exact.
        others = sorted((f + g).free_symbols - {v}, key=str)
        import random
        rnd = random.Random(json.dumps(case["f"]))
        points = [{x: rnd.randint(-10**6, 10**6) for x in others} for _ in range(4)] if others else [{}]
        for pt in points:
            Fp, Gp = Poly(f.subs(pt), v), Poly(g.subs(pt), v)
            if Fp.degree() != n or Gp.degree() != m:
                continue  # a leading coefficient vanishes at this point
            for j in range(min(n, m)):
                want = psc_det(Fp, Gp, j)
                have = sympy.expand(got.get(j, sympy.Integer(0)).subs(pt))
                if want != have:
                    return False, f"psc_{j} at {pt}: want {want}, got {have}"
        return True, ""
    if k == "ranop":
        a = distinct_real_roots(upoly(case["f"]))[case["i"]]
        b = distinct_real_roots(upoly(case["g"]))[case["j"]]
        val = a + b if case["op"] == "add" else a * b
        r = upoly(case["r"])
        if r.degree() == 1:
            rr = sympy.Rational(-r.all_coeffs()[1], r.all_coeffs()[0])
        else:
            if not r.is_irreducible:
                return False, f"{r.as_expr()} is reducible"
            rr = distinct_real_roots(r)[case["ri"]]
        d = sympy.N(rr - val, 150)
        return abs(d) < sympy.Float(10) ** -120, f"differs by {d}"
    if k == "msign":
        vals = [distinct_real_roots(upoly(q))[i] for q, i in case["pt"]]
        f = mexpr(case["f"]).subs({XS[i]: vals[i] for i in range(len(vals))})
        v = sympy.N(f, DIGITS)
        if abs(v) < sympy.Float(10) ** -250:
            want = 0
        elif abs(v) < sympy.Float(10) ** -200:
            return False, "sympy: ambiguous magnitude (raise DIGITS)"
        else:
            want = 1 if v > 0 else -1
        return want == case["r"], f"want {want} (value {sympy.N(v, 20)})"
    if k == "mroots":
        import mpmath
        mpmath.mp.dps = 200
        vals = [distinct_real_roots(upoly(q))[i] for q, i in case["pt"]]
        kk = len(vals)
        y = XS[kk]
        P = Poly(mexpr(case["f"]), y)
        sub = {XS[i]: vals[i] for i in range(kk)}
        coeffs = [mpmath.mpf(str(sympy.N(c.subs(sub), 220))) for c in P.all_coeffs()]
        tiny = mpmath.mpf(10) ** -150
        if case["r"] == "null":
            return all(abs(c) < tiny for c in coeffs), "nullified but a coefficient is nonzero"
        while coeffs and abs(coeffs[0]) < tiny:
            coeffs.pop(0)
        if not coeffs:
            return False, "numerically nullified but reported roots"
        real = []
        if len(coeffs) > 1:
            roots = mpmath.polyroots(coeffs, maxsteps=2000, extraprec=2000)
            for z in roots:
                if abs(mpmath.im(z)) < mpmath.mpf(10) ** -50:
                    x = mpmath.re(z)
                    if not any(abs(x - w) < mpmath.mpf(10) ** -40 for w in real):
                        real.append(x)
        real.sort()
        got = []
        for q, i in case["r"]:
            r = upoly(q)
            if r.degree() == 1:
                g = sympy.Rational(-r.all_coeffs()[1], r.all_coeffs()[0])
            else:
                g = distinct_real_roots(r)[i]
            got.append(mpmath.mpf(str(sympy.N(g, 80))))
        if len(got) != len(real):
            return False, f"{len(got)} roots, mpmath finds {len(real)}: {[mpmath.nstr(x, 12) for x in real]}"
        for a, b in zip(got, real):
            if abs(a - b) > mpmath.mpf(10) ** -30:
                return False, f"root {mpmath.nstr(a, 20)} vs {mpmath.nstr(b, 20)}"
        return True, ""
    return False, f"unknown kernel {k}"


def psc_det(F, G, j):
    """psc_j(F, G) as the determinant of the first n + m - 2j columns of the matrix with rows
    x^(m-j-1) F, ..., F, x^(n-j-1) G, ..., G (coefficients of x^(n+m-j-1) down to x^0)."""
    n, m = F.degree(), G.degree()
    width = n + m - j
    fc, gc = F.all_coeffs(), G.all_coeffs()  # descending
    rows = []
    for i in range(m - j):
        row = [sympy.Integer(0)] * width
        for t, c in enumerate(fc):
            row[i + t] = c
        rows.append(row)
    for i in range(n - j):
        row = [sympy.Integer(0)] * width
        for t, c in enumerate(gc):
            row[i + t] = c
        rows.append(row)
    cols = n + m - 2 * j
    return sympy.expand(sympy.Matrix([r[:cols] for r in rows]).det(method="berkowitz"))


def run_one(line):
    case = json.loads(line)
    try:
        ok, why = check(case)
    except Exception as e:  # a sympy exception is reported, not swallowed
        ok, why = False, f"exception: {type(e).__name__}: {e}"
    return case["k"], ok, why, line


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--kernel", default="all")
    ap.add_argument("--count", type=int, default=200)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--file")
    ap.add_argument("--bin", default="target/release/examples/sympy_cases")
    args = ap.parse_args()
    if args.file:
        lines = open(args.file).read().splitlines()
    else:
        out = subprocess.run(
            [args.bin, args.kernel, str(args.seed), str(args.count)],
            check=True, capture_output=True, text=True,
        ).stdout
        lines = out.splitlines()
    totals, fails = Counter(), Counter()
    with Pool(args.jobs) as pool:
        for k, ok, why, line in pool.imap_unordered(run_one, lines, chunksize=4):
            totals[k] += 1
            if not ok:
                fails[k] += 1
                print(f"MISMATCH [{k}] {why}\n  {line}", flush=True)
    for k in sorted(totals):
        print(f"{k:7s} {totals[k]:6d} cases  {fails[k]:4d} mismatches")
    print(f"total   {sum(totals.values()):6d} cases  {sum(fails.values()):4d} mismatches")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
