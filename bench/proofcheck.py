#!/usr/bin/env python3
"""Check SMT-Rex's Alethe proofs with Carcara.

    python3 bench/proofcheck.py random --count 500            random QF_UF scripts
    python3 bench/proofcheck.py random --logic QF_LRA         random QF_LRA scripts
    python3 bench/proofcheck.py files a.smt2 b.smt2 ...       given scripts

Every `unsat` answer must come with a proof that Carcara checks as valid; an invalid proof or a
solver error fails the run (exit status 1). Scripts outside the supported fragment are counted,
not failed. Environment: CARCARA (default `carcara` on PATH), SMTREX, BENCH_MEM_GB.
"""

import argparse
import json
import os
import random
import resource
import subprocess
import sys
import tempfile
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from bench import MEM_GB, RESULTS, solver_command  # noqa: E402

CARCARA = os.environ.get("CARCARA", "carcara")
CARCARA_FLAGS = ["--expand-let-bindings", "--apply-function-defs", "--allow-int-real-subtyping"]


def limit_memory():
    if MEM_GB > 0:
        cap = int(MEM_GB * (1 << 30))
        resource.setrlimit(resource.RLIMIT_AS, (cap, cap))


def random_uf(seed):
    """QF_UF over one sort: equalities, distinct, predicates, boolean structure, some `let`."""
    r = random.Random(seed)
    consts = [f"c{i}" for i in range(r.randint(2, 6))]
    funs = [(f"f{i}", r.randint(1, 2)) for i in range(r.randint(0, 3))]
    preds = [(f"p{i}", r.randint(0, 2)) for i in range(r.randint(0, 3))]

    def term(d):
        if d == 0 or not funs or r.random() < 0.4:
            return r.choice(consts)
        f, k = r.choice(funs)
        return f"({f} {' '.join(term(d - 1) for _ in range(k))})"

    def atom(d):
        x = r.random()
        if preds and x < 0.3:
            p, k = r.choice(preds)
            return p if k == 0 else f"({p} {' '.join(term(d) for _ in range(k))})"
        if x < 0.4:
            return f"(distinct {' '.join(term(d) for _ in range(r.randint(2, 3)))})"
        a, b = term(d), term(d)
        return f"(= {a} {b})"

    def formula(d):
        if d == 0 or r.random() < 0.35:
            a = atom(2)
            return f"(not {a})" if r.random() < 0.3 else a
        op = r.choice(["and", "or", "=>", "xor", "ite", "=", "not", "and", "or"])
        if op == "not":
            return f"(not {atom(2)})"
        if op in ("and", "or"):
            return f"({op} {' '.join(formula(d - 1) for _ in range(r.randint(2, 3)))})"
        if op == "ite":
            return f"(ite {formula(d - 1)} {formula(d - 1)} {formula(d - 1)})"
        return f"({op} {formula(d - 1)} {formula(d - 1)})"

    out = ["(set-logic QF_UF)", "(declare-sort U 0)"]
    out += [f"(declare-fun {c} () U)" for c in consts]
    out += [f"(declare-fun {f} ({' '.join(['U'] * k)}) U)" for f, k in funs]
    out += [f"(declare-fun {p} ({' '.join(['U'] * k)}) Bool)" for p, k in preds]
    for _ in range(r.randint(2, 8)):
        f = formula(r.randint(1, 3))
        if r.random() < 0.2:
            f = f"(let ((z {term(1)})) (or (= z {r.choice(consts)}) {f}))"
        out.append(f"(assert {f})")
    out.append("(check-sat)")
    return "\n".join(out) + "\n"


def random_lra(seed):
    """QF_LRA: linear atoms over 2-5 reals with real numerals, ite terms, boolean structure."""
    r = random.Random(seed)
    xs = [f"x{i}" for i in range(r.randint(2, 5))]
    bools = [f"b{i}" for i in range(r.randint(0, 2))]

    def num():
        n = r.randint(-6, 6)
        if r.random() < 0.3:
            if n >= 0:
                return f"(/ {abs(n)}.0 {r.randint(1, 4)}.0)"
            return f"(- (/ {-n}.0 {r.randint(1, 4)}.0))"
        return f"{n}.0" if n >= 0 else f"(- {-n}.0)"

    def term(d):
        x = r.random()
        if d == 0 or x < 0.35:
            return r.choice(xs) if r.random() < 0.8 else num()
        if x < 0.6:
            return f"(+ {' '.join(term(d - 1) for _ in range(r.randint(2, 3)))})"
        if x < 0.75:
            return f"(- {term(d - 1)} {term(d - 1)})"
        if x < 0.82:
            return f"(* {num()} {term(d - 1)})"
        if x < 0.9:
            return f"(ite {atom()} {term(d - 1)} {term(d - 1)})"
        return f"(* (/ 1.0 {r.randint(1, 3)}.0) {term(d - 1)})"

    def atom():
        op = r.choice(["<=", "<", ">=", ">", "=", "<=", "distinct"])
        if bools and r.random() < 0.15:
            return r.choice(bools)
        return f"({op} {term(2)} {term(2)})"

    def formula(d):
        if d == 0 or r.random() < 0.4:
            a = atom()
            return f"(not {a})" if r.random() < 0.25 else a
        op = r.choice(["and", "or", "=>", "ite", "or", "and"])
        if op in ("and", "or"):
            return f"({op} {' '.join(formula(d - 1) for _ in range(r.randint(2, 3)))})"
        if op == "ite":
            return f"(ite {formula(d - 1)} {formula(d - 1)} {formula(d - 1)})"
        return f"({op} {formula(d - 1)} {formula(d - 1)})"

    out = ["(set-logic QF_LRA)"]
    out += [f"(declare-fun {x} () Real)" for x in xs]
    out += [f"(declare-fun {b} () Bool)" for b in bools]
    for _ in range(r.randint(2, 7)):
        out.append(f"(assert {formula(r.randint(0, 2))})")
    out.append("(check-sat)")
    return "\n".join(out) + "\n"


GENERATORS = {"QF_UF": random_uf, "QF_LRA": random_lra}


def check(rex, name, src, tmp):
    """(outcome, message): valid, sat, unsupported, timeout, error, carcara-timeout, or
    proof-<carcara's verdict>."""
    path = Path(tmp) / f"{name}.smt2"
    proof = Path(tmp) / f"{name}.smt2.alethe"
    path.write_text(src)
    try:
        p = subprocess.run(rex + [str(path), "--proof", str(proof)], capture_output=True,
                           text=True, timeout=60, preexec_fn=limit_memory)
    except subprocess.TimeoutExpired:
        return "timeout", ""
    if p.returncode != 0:
        msg = (p.stderr or p.stdout).strip()
        return ("unsupported" if "support" in msg else "error"), msg
    if p.stdout.strip() == "sat":
        return "sat", ""
    try:
        c = subprocess.run([CARCARA, "check", *CARCARA_FLAGS, str(proof), str(path)],
                           capture_output=True, text=True, timeout=300,
                           preexec_fn=limit_memory)
    except subprocess.TimeoutExpired:
        return "carcara-timeout", ""
    verdict = (c.stdout.strip().splitlines() or ["?"])[-1]
    if verdict == "valid":
        return "valid", ""
    return f"proof-{verdict}", (c.stderr + c.stdout)[-600:]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    rnd = sub.add_parser("random", help="random scripts")
    rnd.add_argument("--count", type=int, default=200)
    rnd.add_argument("--seed", type=int, default=1)
    rnd.add_argument("--logic", default="QF_UF", choices=sorted(GENERATORS))
    fl = sub.add_parser("files", help="given scripts")
    fl.add_argument("paths", nargs="+")
    for s in (rnd, fl):
        s.add_argument("--jobs", type=int, default=4)
        s.add_argument("--out", help="write every script's outcome to this JSON file")
    args = ap.parse_args()

    if args.cmd == "random":
        gen = GENERATORS[args.logic]
        jobs = [(f"r{args.seed + i}", gen(args.seed + i)) for i in range(args.count)]
    else:
        jobs = [(Path(p).name.replace(".smt2", ""), Path(p).read_text()) for p in args.paths]
    rex = solver_command("smt-rex")
    counts = Counter()
    bad = 0
    rows = []
    with tempfile.TemporaryDirectory() as tmp, ThreadPoolExecutor(args.jobs) as ex:
        results = ex.map(lambda j: check(rex, j[0], j[1], tmp), jobs)
        for (name, src), (res, msg) in zip(jobs, results):
            counts[res] += 1
            msg = msg.strip()
            rows.append({"name": name, "result": res,
                         "message": msg.splitlines()[0] if msg else ""})
            if res.startswith("proof-") or res == "error":
                bad += 1
                if bad <= 5:
                    print(f"{name}: {res}: {msg}", file=sys.stderr)
                    if args.cmd == "random":
                        RESULTS.mkdir(parents=True, exist_ok=True)
                        (RESULTS / f"proof-fail-{name}.smt2").write_text(src)
    print(" ".join(f"{k} {v}" for k, v in sorted(counts.items())))
    if args.out:
        Path(args.out).write_text(json.dumps(rows, indent=1))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
