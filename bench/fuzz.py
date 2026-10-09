#!/usr/bin/env python3
"""Differential fuzzer: random QF_UF, QF_LRA, QF_LIA, QF_NRA or QF_BV scripts, SMT-Rex against z3
(or cvc5).

Each script declares some symbols, then mixes assertions, `let`, `define-fun`, `:named`,
`push`/`pop`, `check-sat` and `check-sat-assuming`. Every verdict must agree with the reference
solver; SMT-Rex must never answer `unknown` (a failed model self-check) or report an error.

    python3 bench/fuzz.py --count 2000            # 2000 QF_UF scripts
    python3 bench/fuzz.py --logic QF_NRA          # any of the five logics
    python3 bench/fuzz.py --logic QF_LIA --opt    # compare maximize/minimize optima
    python3 bench/fuzz.py --count 0 --seed 7      # run forever from seed 7

Seeds are deterministic: `--seed N --count 1` replays one script. Failing scripts are saved to
bench/results/fuzz-fail-<seed>.smt2. A script on which a solver exceeds `--timeout` is counted
as a timeout, not a failure, and saved to bench/results/fuzz-timeout-<seed>.smt2.
"""

import argparse
import random
import re
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bench import RESULTS, solver_command  # noqa: E402

TIMEOUT = 60  # seconds per solver run (--timeout)


class Generator:
    """The parts all generators share. Subclasses set `r` (the random source), `bools`,
    `named`, and `form(depth)`, a random formula."""

    FORM_DEPTH = 3  # assertions have depth 1..FORM_DEPTH
    NAMED = 0.12  # probability that an assertion is :named
    ASSUME_AT = 0.78  # thresholds of the command mix, see `commands`
    PUSH_AT = 0.89

    def pick(self, xs):
        return self.r.choice(xs)

    def assumption(self):
        p = self.pick(self.bools)
        return self.pick([p, f"(not {p})"])

    def commands(self, out):
        """Append 1-6 commands (assert, check-sat, check-sat-assuming, push, pop) and a final
        check-sat. Names made by `:named` are dropped again on the matching pop."""
        depth, named_at = 0, []
        for _ in range(self.r.randint(1, 6)):
            k = self.r.random()
            if k < 0.55:
                f = self.form(self.r.randint(1, self.FORM_DEPTH))
                if self.r.random() < self.NAMED:
                    n = f"n{len(self.named)}"
                    out.append(f"(assert (! {f} :named {n}))")
                    self.named.append(n)
                else:
                    out.append(f"(assert {f})")
            elif k < 0.7:
                out.append("(check-sat)")
            elif k < self.ASSUME_AT:
                out.append(f"(check-sat-assuming ({self.assumption()}))")
            elif k < self.PUSH_AT:
                out.append("(push 1)")
                named_at.append(len(self.named))
                depth += 1
            elif depth:
                out.append("(pop 1)")
                del self.named[named_at.pop():]
                depth -= 1
        out.append("(check-sat)")
        return "\n".join(out) + "\n"


class UfGen(Generator):
    """QF_UF: one or two uninterpreted sorts, constants, functions and predicates."""

    FORM_DEPTH = 4
    NAMED = 0.15
    ASSUME_AT = 0.8
    PUSH_AT = 0.9

    def __init__(self, seed):
        self.r = random.Random(seed)
        self.sorts = ["U"] if self.r.random() < 0.6 else ["U", "V"]
        self.consts = {
            s: [f"{s.lower()}{i}" for i in range(self.r.randint(2, 5))] for s in self.sorts
        }
        self.bools = [f"p{i}" for i in range(self.r.randint(1, 3))]
        self.funcs = {}  # name -> (argument sorts, result sort)
        for i in range(self.r.randint(1, 4)):
            args = [self.r.choice(self.sorts + ["Bool"]) for _ in range(self.r.randint(1, 2))]
            self.funcs[f"f{i}"] = (args, self.r.choice(self.sorts + ["Bool"]))
        self.defs = {}
        self.named = []
        self.vars = []  # (name, sort) of the let-bound names in scope

    def assumption(self):
        return " ".join(self.pick([p, f"(not {p})"]) for p in self.r.sample(self.bools, 1))

    def term(self, sort, d):
        if sort == "Bool":
            return self.form(d)
        r = self.r.random()
        vs = [n for n, s in self.vars if s == sort]
        if d <= 0 or r < 0.3:
            if vs and self.r.random() < 0.5:
                return self.pick(vs)
            return self.pick(self.consts[sort])
        fs = [f for f, (_, ret) in self.funcs.items() if ret == sort]
        ds = [f for f, (_, ret) in self.defs.items() if ret == sort]
        if r < 0.65 and fs:
            f = self.pick(fs)
            return f"({f} {' '.join(self.term(s, d - 1) for s in self.funcs[f][0])})"
        if r < 0.75 and ds:
            f = self.pick(ds)
            return f"({f} {' '.join(self.term(s, d - 1) for s in self.defs[f][0])})"
        if r < 0.9:
            return f"(ite {self.form(d - 1)} {self.term(sort, d - 1)} {self.term(sort, d - 1)})"
        return self.let(sort, d)

    def let(self, sort, d):
        n = self.r.randint(1, 2)
        binds = []
        for i in range(n):
            s = self.pick(self.sorts + ["Bool"])
            binds.append((f"x{len(self.vars)}_{i}", s, self.term(s, d - 1)))
        self.vars.extend((name, s) for name, s, _ in binds)
        body = self.term(sort, d - 1)
        del self.vars[len(self.vars) - n:]
        return f"(let ({' '.join(f'({n} {e})' for n, _, e in binds)}) {body})"

    def form(self, d):
        r = self.r.random()
        vs = [n for n, s in self.vars if s == "Bool"]
        if d <= 0 or r < 0.15:
            return self.pick(self.bools + vs + self.named + ["true", "false"])
        k = self.r.random()
        if k < 0.3:
            s = self.pick(self.sorts + ["Bool"]) if self.r.random() < 0.2 else self.pick(self.sorts)
            op = "=" if self.r.random() < 0.7 else "distinct"
            n = 2 if op == "=" or self.r.random() < 0.6 else 3
            return f"({op} {' '.join(self.term(s, d - 1) for _ in range(n))})"
        if k < 0.42:
            return f"(not {self.form(d - 1)})"
        if k < 0.62:
            op = self.pick(["and", "or", "=>", "xor"])
            n = self.r.randint(2, 3)
            return f"({op} {' '.join(self.form(d - 1) for _ in range(n))})"
        if k < 0.72:
            return f"(ite {self.form(d - 1)} {self.form(d - 1)} {self.form(d - 1)})"
        ps = [f for f, (_, ret) in self.funcs.items() if ret == "Bool"]
        if k < 0.85 and ps:
            f = self.pick(ps)
            return f"({f} {' '.join(self.term(s, d - 1) for s in self.funcs[f][0])})"
        return self.let("Bool", d)

    def script(self):
        out = ["(set-logic QF_UF)"]
        out += [f"(declare-sort {s} 0)" for s in self.sorts]
        for s, cs in self.consts.items():
            out += [f"(declare-fun {c} () {s})" for c in cs]
        out += [f"(declare-const {p} Bool)" for p in self.bools]
        for f, (args, ret) in self.funcs.items():
            out.append(f"(declare-fun {f} ({' '.join(args)}) {ret})")
        for i in range(self.r.randint(0, 2)):
            params = [(f"y{j}", self.pick(self.sorts + ["Bool"]))
                      for j in range(self.r.randint(1, 2))]
            ret = self.pick(self.sorts + ["Bool"])
            self.vars = list(params)
            body = self.term(ret, 2)
            self.vars = []
            name = f"d{i}"
            ps = " ".join(f"({n} {s})" for n, s in params)
            out.append(f"(define-fun {name} ({ps}) {ret} {body})")
            self.defs[name] = ([s for _, s in params], ret)
        return self.commands(out)


class LraGen(Generator):
    """QF_LRA: linear (in)equalities with small and fractional coefficients, ite over reals."""

    INT = False
    LOGIC = "QF_LRA"

    def __init__(self, seed):
        self.r = random.Random(seed)
        self.sort = "Int" if self.INT else "Real"
        self.reals = [f"x{i}" for i in range(self.r.randint(1, 4))]
        self.bools = [f"p{i}" for i in range(self.r.randint(1, 2))]
        self.defs = {}
        self.vars = []
        self.named = []

    def const(self):
        k = self.r.random()
        if k < 0.6 or self.INT:
            n = self.r.randint(-6, 6)
            return str(n) if n >= 0 else f"(- {-n})"
        if k < 0.8:
            return f"(/ {self.r.randint(1, 7)} {self.r.randint(1, 5)})"
        return f"{self.r.randint(0, 9)}.{self.r.randint(0, 99)}"

    def call(self, f, d):
        args = [self.term(d - 1) if s == self.sort else self.form(d - 1) for s in self.defs[f][0]]
        return f"({f} {' '.join(args)})"

    def term(self, d):
        vs = [n for n, s in self.vars if s == self.sort]
        k = self.r.random()
        if d <= 0 or k < 0.25:
            return self.pick(self.reals + vs) if self.r.random() < 0.8 else self.const()
        if k < 0.5:
            n = self.r.randint(2, 3)
            return f"(+ {' '.join(self.term(d - 1) for _ in range(n))})"
        if k < 0.62:
            if self.r.random() < 0.7:
                return f"(- {self.term(d - 1)} {self.term(d - 1)})"
            return f"(- {self.term(d - 1)})"
        if k < 0.78:
            return f"(* {self.const()} {self.term(d - 1)})"
        if k < 0.84:
            if self.INT:
                op = self.pick(["div", "mod", "abs"])
                if op == "abs":
                    return f"(abs {self.term(d - 1)})"
                k2 = self.r.choice([1, 2, 3, 4, -2, -3])
                return f"({op} {self.term(d - 1)} {k2 if k2 > 0 else f'(- {-k2})'})"
            return f"(/ {self.term(d - 1)} {self.r.randint(1, 4)})"
        if k < 0.92:
            return f"(ite {self.form(d - 1)} {self.term(d - 1)} {self.term(d - 1)})"
        ds = [f for f, (_, ret) in self.defs.items() if ret == self.sort]
        if ds:
            return self.call(self.pick(ds), d)
        name = f"v{len(self.vars)}"
        self.vars.append((name, self.sort))
        body = self.term(d - 1)
        self.vars.pop()
        return f"(let (({name} {self.term(d - 1)})) {body})"

    def form(self, d):
        bs = [n for n, s in self.vars if s == "Bool"]
        k = self.r.random()
        if d <= 0 or k < 0.12:
            return self.pick(self.bools + bs + self.named + ["true", "false"])
        if k < 0.5:
            op = self.pick(["<=", "<", ">=", ">", "=", "distinct"])
            n = 3 if self.r.random() < 0.15 else 2
            return f"({op} {' '.join(self.term(d - 1) for _ in range(n))})"
        if k < 0.6:
            return f"(not {self.form(d - 1)})"
        if k < 0.82:
            op = self.pick(["and", "or", "=>", "xor"])
            return f"({op} {self.form(d - 1)} {self.form(d - 1)})"
        if k < 0.9:
            return f"(ite {self.form(d - 1)} {self.form(d - 1)} {self.form(d - 1)})"
        ds = [f for f, (_, ret) in self.defs.items() if ret == "Bool"]
        if ds:
            return self.call(self.pick(ds), d)
        return f"(= {self.form(d - 1)} {self.form(d - 1)})"

    def script(self):
        out = [f"(set-logic {self.LOGIC})"]
        out += [f"(declare-fun {x} () {self.sort})" for x in self.reals]
        out += [f"(declare-const {p} Bool)" for p in self.bools]
        for i in range(self.r.randint(0, 2)):
            params = [(f"y{j}", self.pick([self.sort, self.sort, "Bool"]))
                      for j in range(self.r.randint(1, 2))]
            ret = self.pick([self.sort, "Bool"])
            self.vars = list(params)
            body = self.term(2) if ret == self.sort else self.form(2)
            self.vars = []
            ps = " ".join(f"({n} {s})" for n, s in params)
            out.append(f"(define-fun d{i} ({ps}) {ret} {body})")
            self.defs[f"d{i}"] = ([s for _, s in params], ret)
        return self.commands(out)


class LiaGen(LraGen):
    """QF_LIA: as LraGen over Int, with div/mod/abs by constants."""

    INT = True
    LOGIC = "QF_LIA"


class NraGen(LraGen):
    """QF_NRA: polynomial constraints of degree at most 3 in 2-3 real variables. Half the scripts
    are plain systems of polynomial atoms, the other half have LraGen's boolean structure."""

    LOGIC = "QF_NRA"
    MAX_DEG = 3

    def __init__(self, seed):
        super().__init__(seed)
        self.reals = [f"x{i}" for i in range(self.r.randint(2, 3))]

    def const(self):
        k = self.r.random()
        if k < 0.7:
            n = self.r.randint(-4, 4)
            return str(n) if n >= 0 else f"(- {-n})"
        if k < 0.9:
            return f"(/ {self.r.randint(1, 5)} {self.r.randint(1, 4)})"
        return f"{self.r.randint(0, 3)}.{self.r.choice([0, 5, 25])}"

    def term(self, d, deg=None):
        """A term of degree at most `deg` (default MAX_DEG)."""
        deg = self.MAX_DEG if deg is None else deg
        vs = [n for n, s in self.vars if s == self.sort]
        k = self.r.random()
        if deg == 0:
            return self.const()
        if d <= 0 or k < 0.2:
            return self.pick(self.reals + vs) if self.r.random() < 0.8 else self.const()
        if k < 0.42:
            n = self.r.randint(2, 3)
            return f"(+ {' '.join(self.term(d - 1, deg) for _ in range(n))})"
        if k < 0.5:
            if self.r.random() < 0.7:
                return f"(- {self.term(d - 1, deg)} {self.term(d - 1, deg)})"
            return f"(- {self.term(d - 1, deg)})"
        if k < 0.75 and deg >= 2:
            a = self.r.randint(1, deg - 1)
            return f"(* {self.term(d - 1, a)} {self.term(d - 1, deg - a)})"
        if k < 0.8:
            return f"(* {self.const()} {self.term(d - 1, deg)})"
        if k < 0.85:
            return f"(/ {self.term(d - 1, deg)} {self.r.randint(1, 4)})"
        if k < 0.92:
            return f"(ite {self.form(d - 1)} {self.term(d - 1, deg)} {self.term(d - 1, deg)})"
        ds = [f for f, (_, ret) in self.defs.items() if ret == self.sort]
        if ds and deg == self.MAX_DEG:
            # A body has degree <= MAX_DEG in its parameters: call it on variables only.
            f = self.pick(ds)
            args = [self.pick(self.reals) if s == self.sort else self.form(d - 1)
                    for s in self.defs[f][0]]
            return f"({f} {' '.join(args)})"
        name = f"v{len(self.vars)}"
        self.vars.append((name, self.sort))
        body = self.term(d - 1, deg)
        self.vars.pop()
        # A linear bound term keeps the body within the degree budget.
        return f"(let (({name} {self.term(d - 1, 1)})) {body})"

    def poly(self):
        """A polynomial of degree <= MAX_DEG: a sum of monomials, or a product of two."""
        if self.r.random() < 0.25:
            a = self.r.randint(1, self.MAX_DEG - 1)
            return f"(* {self.sum_of_monomials(a)} {self.sum_of_monomials(self.MAX_DEG - a)})"
        return self.sum_of_monomials(self.MAX_DEG)

    def sum_of_monomials(self, deg):
        terms = []
        for _ in range(self.r.randint(1, 4)):
            k = self.r.randint(0, deg)
            factors = [self.pick(self.reals) for _ in range(k)]
            c = self.r.choice([1, 1, 1, -1, -1, 2, -2, 3, -3, 5])
            c = str(c) if c > 0 else f"(- {-c})"
            terms.append(f"(* {c} {' '.join(factors)})" if factors else c)
        return terms[0] if len(terms) == 1 else f"(+ {' '.join(terms)})"

    def atom(self):
        op = self.pick(["<=", "<", ">=", ">", "=", "=", "distinct"])
        return f"({op} {self.poly()} {self.const() if self.r.random() < 0.5 else '0'})"

    def system(self):
        """2-5 polynomial atoms, some in binary disjunctions."""
        out = [f"(set-logic {self.LOGIC})"]
        out += [f"(declare-fun {x} () Real)" for x in self.reals]
        for _ in range(self.r.randint(2, 5)):
            if self.r.random() < 0.25:
                out.append(f"(assert (or {self.atom()} {self.atom()}))")
            else:
                out.append(f"(assert {self.atom()})")
        out.append("(check-sat)")
        return "\n".join(out) + "\n"

    def script(self):
        if self.r.random() < 0.5:
            return self.system()
        return super().script()


BV_UNARY = ["bvnot", "bvneg"]
BV_BINARY = [
    "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor",
    "bvadd", "bvsub", "bvmul", "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod",
    "bvshl", "bvlshr", "bvashr",
]
BV_LEFT_ASSOC = ["bvand", "bvor", "bvxor", "bvadd", "bvmul"]
BV_COMPARE = ["bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge"]


class BvGen(Generator):
    """QF_BV over widths 1-12: every operator of the logic (division by zero and shifts by at
    least the width included) and the indexed operators. A width of None stands for Bool."""

    FORM_DEPTH = 4

    def __init__(self, seed):
        self.r = random.Random(seed)
        widths = self.r.sample(range(1, 13), self.r.randint(1, 3))
        if self.r.random() < 0.3:
            widths.append(1)
        self.consts = {}
        for i in range(self.r.randint(2, 5)):
            self.consts[f"v{i}"] = self.pick(widths)
        self.widths = sorted(set(self.consts.values()))
        self.bools = [f"p{i}" for i in range(self.r.randint(1, 2))]
        self.defs = {}  # name -> (parameter widths, result width)
        self.vars = []  # (name, width)
        self.named = []

    def literal(self, w):
        v = self.r.choice([0, 1, (1 << w) - 1, 1 << (w - 1), self.r.randrange(1 << w)])
        k = self.r.random()
        if k < 0.4:
            return "#b" + format(v, f"0{w}b")
        if k < 0.6 and w % 4 == 0:
            return "#x" + format(v, f"0{w // 4}x")
        return f"(_ bv{v} {w})"

    def leaf(self, w):
        vs = [n for n, s in self.vars if s == w]
        cs = [c for c, cw in self.consts.items() if cw == w]
        k = self.r.random()
        if vs and k < 0.3:
            return self.pick(vs)
        if cs and k < 0.85:
            return self.pick(cs)
        big = [c for c, cw in self.consts.items() if cw > w]
        if big and k < 0.92:
            c = self.pick(big)
            j = self.r.randint(0, self.consts[c] - w)
            return f"((_ extract {j + w - 1} {j}) {c})"
        return self.literal(w)

    def term(self, w, d):
        k = self.r.random()
        if d <= 0 or k < 0.2:
            return self.leaf(w)
        if k < 0.3:
            return f"({self.pick(BV_UNARY)} {self.term(w, d - 1)})"
        if k < 0.6:
            op = self.pick(BV_BINARY)
            if op in ("bvshl", "bvlshr", "bvashr") and self.r.random() < 0.5:
                # A literal shift amount, often at or beyond the width.
                amount = self.r.randint(0, min((1 << w) - 1, w + 2))
                return f"({op} {self.term(w, d - 1)} (_ bv{amount} {w}))"
            if op in ("bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod") and self.r.random() < 0.2:
                return f"({op} {self.term(w, d - 1)} (_ bv0 {w}))"
            n = 3 if op in BV_LEFT_ASSOC and self.r.random() < 0.15 else 2
            return f"({op} {' '.join(self.term(w, d - 1) for _ in range(n))})"
        if k < 0.66 and w >= 2:
            a = self.r.randint(1, w - 1)
            return f"(concat {self.term(a, d - 1)} {self.term(w - a, d - 1)})"
        if k < 0.72:
            src = self.r.randint(w, min(w + 6, 16))
            j = self.r.randint(0, src - w)
            return f"((_ extract {j + w - 1} {j}) {self.term(src, d - 1)})"
        if k < 0.78:
            a = self.r.randint(1, w)
            op = self.pick(["zero_extend", "sign_extend"])
            return f"((_ {op} {w - a}) {self.term(a, d - 1)})"
        if k < 0.82:
            n = self.pick([n for n in range(1, w + 1) if w % n == 0])
            return f"((_ repeat {n}) {self.term(w // n, d - 1)})"
        if k < 0.86:
            op = self.pick(["rotate_left", "rotate_right"])
            return f"((_ {op} {self.r.randint(0, 2 * w + 1)}) {self.term(w, d - 1)})"
        if (k < 0.9 or self.r.random() < 0.3) and w == 1:
            a = self.pick(self.widths)
            return f"(bvcomp {self.term(a, d - 1)} {self.term(a, d - 1)})"
        if k < 0.94:
            return f"(ite {self.form(d - 1)} {self.term(w, d - 1)} {self.term(w, d - 1)})"
        ds = [f for f, (_, ret) in self.defs.items() if ret == w]
        if ds:
            return self.call(self.pick(ds), d)
        return self.let(w, d)

    def call(self, f, d):
        params, _ = self.defs[f]
        args = [self.form(d - 1) if p is None else self.term(p, d - 1) for p in params]
        return f"({f} {' '.join(args)})"

    def let(self, w, d):
        binds = []
        for i in range(self.r.randint(1, 2)):
            s = self.pick(self.widths + [None])
            e = self.form(d - 1) if s is None else self.term(s, d - 1)
            binds.append((f"x{len(self.vars)}_{i}", s, e))
        self.vars.extend((n, s) for n, s, _ in binds)
        body = self.form(d - 1) if w is None else self.term(w, d - 1)
        del self.vars[len(self.vars) - len(binds):]
        return f"(let ({' '.join(f'({n} {e})' for n, _, e in binds)}) {body})"

    def form(self, d):
        bs = [n for n, s in self.vars if s is None]
        k = self.r.random()
        if d <= 0 or k < 0.1:
            return self.pick(self.bools + bs + self.named + ["true", "false"])
        w = self.pick(self.widths)
        if k < 0.4:
            return f"({self.pick(BV_COMPARE)} {self.term(w, d - 1)} {self.term(w, d - 1)})"
        if k < 0.55:
            op = "=" if self.r.random() < 0.7 else "distinct"
            n = 3 if self.r.random() < 0.15 else 2
            return f"({op} {' '.join(self.term(w, d - 1) for _ in range(n))})"
        if k < 0.63:
            return f"(not {self.form(d - 1)})"
        if k < 0.8:
            op = self.pick(["and", "or", "=>", "xor"])
            return f"({op} {self.form(d - 1)} {self.form(d - 1)})"
        if k < 0.86:
            return f"(ite {self.form(d - 1)} {self.form(d - 1)} {self.form(d - 1)})"
        ds = [f for f, (_, ret) in self.defs.items() if ret is None]
        if ds and k < 0.93:
            return self.call(self.pick(ds), d)
        return self.let(None, d)

    def script(self):
        def sort(w):
            return "Bool" if w is None else f"(_ BitVec {w})"

        out = ["(set-logic QF_BV)"]
        out += [f"(declare-fun {c} () {sort(w)})" for c, w in self.consts.items()]
        out += [f"(declare-const {p} Bool)" for p in self.bools]
        for i in range(self.r.randint(0, 2)):
            params = [(f"y{j}", self.pick(self.widths + [None]))
                      for j in range(self.r.randint(1, 2))]
            ret = self.pick(self.widths + [None])
            self.vars = list(params)
            body = self.form(2) if ret is None else self.term(ret, 2)
            self.vars = []
            ps = " ".join(f"({n} {sort(w)})" for n, w in params)
            out.append(f"(define-fun d{i} ({ps}) {sort(ret)} {body})")
            self.defs[f"d{i}"] = ([w for _, w in params], ret)
        return self.commands(out)


GENERATORS = {"QF_UF": UfGen, "QF_LRA": LraGen, "QF_LIA": LiaGen, "QF_BV": BvGen,
              "QF_NRA": NraGen}


def parse_objective(text):
    """The value of the single objective in a `get-objectives` answer, as (kind, number) with
    kind 'exact', 'oo', '-oo', 'sup' (approached from below) or 'inf' (from above). Reads both
    z3's and SMT-Rex's spellings of epsilon terms."""
    body = text[text.index("(objectives") + len("(objectives"):]
    toks = re.findall(r"\(|\)|[^\s()]+", body)

    def read(i):
        if toks[i] == "(":
            items, i = [], i + 1
            while toks[i] != ")":
                x, i = read(i)
                items.append(x)
            return items, i + 1
        return toks[i], i + 1

    entry, _ = read(0)  # ((term) value)
    value = entry[-1]
    INF = "inf"

    def ev(x):
        """(number, epsilon coefficient), or (INF, sign)."""
        if x == "oo":
            return (INF, 1)
        if x == "epsilon":
            return (Fraction(0), Fraction(1))
        if isinstance(x, str):
            return (Fraction(x), Fraction(0))
        op, *args = x
        vals = [ev(a) for a in args]
        infs = [v for v in vals if v[0] == INF]
        if op == "-" and len(vals) == 1:
            v = vals[0]
            return (INF, -v[1]) if v[0] == INF else (-v[0], -v[1])
        if op in ("+", "-") and infs:
            first = vals[0]
            if op == "-" and first[0] != INF:
                return (INF, -infs[0][1])
            return infs[0]
        if op == "+":
            return (sum(v[0] for v in vals), sum(v[1] for v in vals))
        if op == "-":
            a, b = vals
            return (a[0] - b[0], a[1] - b[1])
        if op == "*":
            a, b = vals
            if infs:
                fin = a if b[0] == INF else b
                inf = b if b[0] == INF else a
                return (INF, inf[1] * (1 if fin[0] > 0 else -1))
            return (a[0] * b[0], a[0] * b[1] + a[1] * b[0])
        if op == "/":
            a, b = vals
            return (a[0] / b[0], a[1] / b[0])
        raise ValueError(f"unexpected {x}")

    n, e = ev(value)
    if n == INF:
        return ("oo" if e > 0 else "-oo", None)
    return ("exact" if e == 0 else ("sup" if e < 0 else "inf"), n)


def objectives(cmd, path):
    """(last verdict, parsed objective or None, all output)."""
    p = subprocess.run(cmd + [str(path)], capture_output=True, text=True, timeout=TIMEOUT)
    out = p.stdout
    lines = [line.strip() for line in out.splitlines()]
    verdict = next((v for v in reversed(lines) if v in ("sat", "unsat", "unknown")), None)
    if verdict != "sat" or "(objectives" not in out:
        return verdict, None, out + p.stderr
    return verdict, parse_objective(out[out.index("(objectives"):]), out + p.stderr


def check_opt(seed, rex, ref, tmp, logic):
    """A random script plus one maximize/minimize; verdicts and optima must agree."""
    gen = {"QF_LRA": LraGen, "QF_LIA": LiaGen}[logic](seed)
    src = gen.script()
    r = random.Random(seed * 7919)
    term = gen.term(2)
    goal = r.choice(["maximize", "minimize"])
    src += f"(push 1)\n({goal} {term})\n(check-sat)\n(get-objectives)\n(pop 1)\n"
    path = tmp / f"opt-{seed}.smt2"
    path.write_text(src)
    try:
        mv, mo, mout = objectives(rex, path)
        tv, to, _ = objectives(ref, path)
    except subprocess.TimeoutExpired as e:
        who = "SMT-Rex" if e.cmd[0] == rex[0] else "the reference"
        return seed, src, f"timeout: {who} took over {e.timeout:.0f} s"
    finally:
        path.unlink()
    if "(error" in mout:
        return seed, src, f"SMT-Rex error: {mout.strip().splitlines()[-1]}"
    if mv != tv:
        return seed, src, f"verdicts differ: SMT-Rex {mv}, reference {tv}"
    if mo != to:
        return seed, src, f"optimum differs: SMT-Rex {mo}, reference {to}"
    return seed, src, None


def verdicts(cmd, path):
    p = subprocess.run(cmd + [str(path)], capture_output=True, text=True, timeout=TIMEOUT)
    lines = [line.strip() for line in p.stdout.splitlines()]
    return [v for v in lines if v in ("sat", "unsat", "unknown")], p.stdout + p.stderr


def check(seed, rex, ref, tmp, logic="QF_UF"):
    """Run one random script on both solvers: (seed, script, problem or None). A problem that
    starts with "timeout:" is a timeout, not a failure."""
    src = GENERATORS[logic](seed).script()
    path = tmp / f"fuzz-{seed}.smt2"
    path.write_text(src)
    try:
        mine, out = verdicts(rex, path)
        theirs, _ = verdicts(ref, path)
    except subprocess.TimeoutExpired as e:
        who = "SMT-Rex" if e.cmd[0] == rex[0] else "the reference"
        return seed, src, f"timeout: {who} took over {e.timeout:.0f} s"
    finally:
        path.unlink()
    problem = None
    if "(error" in out:
        problem = f"SMT-Rex error: {out.strip().splitlines()[-1]}"
    elif "unknown" in mine:
        problem = f"SMT-Rex said unknown: {out.strip()}"
    elif len(mine) != len(theirs):
        problem = f"{len(mine)} verdicts vs {len(theirs)} from the reference"
    elif mine != theirs:
        problem = f"verdicts differ: SMT-Rex {mine}, reference {theirs}"
    return seed, src, problem


def main():
    global TIMEOUT
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--count", type=int, default=1000, help="scripts to run (0 = forever)")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--reference", default="z3", choices=["z3", "cvc5"])
    ap.add_argument("--logic", default="QF_UF", choices=sorted(GENERATORS))
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--timeout", type=float, default=TIMEOUT, help="seconds per solver run")
    ap.add_argument("--opt", action="store_true",
                    help="append a random maximize/minimize and compare optima (QF_LRA, QF_LIA)")
    args = ap.parse_args()
    TIMEOUT = args.timeout
    rex = solver_command("smt-rex")
    ref = solver_command(args.reference)
    if not ref or not ref[0]:
        sys.exit(f"{args.reference} not found")
    RESULTS.mkdir(parents=True, exist_ok=True)
    tmp = RESULTS / "fuzz-tmp"
    tmp.mkdir(exist_ok=True)

    def seeds():
        s = args.seed
        while args.count == 0 or s < args.seed + args.count:
            yield s
            s += 1

    failures = timeouts = done = 0
    run = check_opt if args.opt else check
    with ThreadPoolExecutor(args.jobs) as ex:
        for seed, src, problem in ex.map(lambda s: run(s, rex, ref, tmp, args.logic), seeds()):
            done += 1
            if problem:
                kind = "timeout" if problem.startswith("timeout") else "fail"
                if kind == "timeout":
                    timeouts += 1
                else:
                    failures += 1
                out = RESULTS / f"fuzz-{kind}-{seed}.smt2"
                out.write_text(src)
                print(f"seed {seed}: {problem}\n  saved {out}")
            if done % 500 == 0:
                print(f"{done} scripts, {failures} failures, {timeouts} timeouts", flush=True)
    tmp.rmdir()
    print(f"{done} scripts, {failures} failures, {timeouts} timeouts")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
