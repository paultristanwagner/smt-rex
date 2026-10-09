#!/usr/bin/env python3
"""SMT-Rex benchmark harness: fixed SMT-LIB benchmark sets, answer checking, PAR-2 scoring.

Subcommands (run `bench.py <cmd> --help` for options):

  fetch     download one logic's SMT-LIB 2025 archive (checksum-verified) into bench/data/
  make-sets draw the tuning and held-out sets for a logic and write bench/sets/<LOGIC>.json
  run       run one solver over a set, check every answer, report solved / wrong / PAR-2
  compare   compare two result files instance by instance
  report    one Markdown table for several solvers' runs of the same set

`run --set full` runs every file of the logic, as SMT-COMP does: the expected verdict is the
file's :status, and a file with status unknown counts as solved by either answer. `report` then
flags any two solvers that disagree on it.

Scoring. Every instance runs under a CPU-time limit T (the SMT-COMP convention; steadier than
wall-clock when runs share the machine). A solved instance scores its CPU time, an unsolved one
(timeout, crash, `unknown`, parse error) scores 2*T, and PAR-2 is the mean over the set. Any
answer that contradicts the expected verdict is WRONG: the run is disqualified and the command
exits with status 1, whatever its PAR-2.

Only the Python standard library is used. Solvers are located through environment variables
(SMTREX, Z3, CVC5) or PATH; see `SOLVERS` below.
"""

import argparse
import collections
import hashlib
import json
import os
import random
import resource
import shlex
import shutil
import signal
import subprocess
import sys
import tarfile
import threading
import time
import urllib.request
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
DATA = HERE / "data"
SETS = HERE / "sets"
RESULTS = HERE / "results"

ZENODO_RECORD = "15493090"  # SMT-LIB 2025 non-incremental release
ARCHIVE_URL = "https://zenodo.org/records/{record}/files/{logic}.tar.zst?download=1"
ZENODO_API = "https://zenodo.org/api/records/{record}"

VERDICTS = ("sat", "unsat")


# ---------------------------------------------------------------------------------------------
# Solvers


def _which(env, name):
    return os.environ.get(env) or shutil.which(name)


def solver_command(name):
    """The argv prefix for a named solver; the benchmark path is appended."""
    if name == "smt-rex":
        exe = os.environ.get("SMTREX") or str(ROOT / "target" / "release" / "smt-rex")
        return [exe]
    if name == "z3":
        exe = _which("Z3", "z3")
        return [exe, "-smt2"] if exe else None
    if name == "cvc5":
        exe = _which("CVC5", "cvc5")
        return [exe, "--lang=smt2"] if exe else None
    return None


SOLVERS = {
    "smt-rex": "this project's Rust solver (env SMTREX, default target/release/smt-rex)",
    "z3": "Z3 (env Z3, else PATH)",
    "cvc5": "cvc5 (env CVC5, else PATH)",
}


def resolve_solver(args):
    if args.cmd:
        return args.name or "custom", shlex.split(args.cmd)
    cmd = solver_command(args.solver)
    if not cmd or not cmd[0] or not shutil.which(cmd[0]) and not Path(cmd[0]).exists():
        sys.exit(f"solver '{args.solver}' not found: {SOLVERS.get(args.solver, 'unknown name')}")
    return args.solver, cmd


# ---------------------------------------------------------------------------------------------
# Running one instance


def parse_verdict(stdout):
    """The verdict of the last `(check-sat)`: the last line that is exactly sat/unsat/unknown."""
    verdict = None
    for line in stdout.splitlines():
        line = line.strip()
        if line in ("sat", "unsat", "unknown"):
            verdict = line
    return verdict


# Address-space limit per solver process in GiB (BENCH_MEM_GB, 0 = none), so that a runaway
# instance fails on its own instead of taking the machine down. Generous because smt-rex
# reserves a 1 GiB stack.
MEM_GB = float(os.environ.get("BENCH_MEM_GB", "6"))


def run_instance(cmd, path, limit):
    """Run `cmd path` under a CPU-time limit of `limit` seconds (wall-clock backstop 2*limit+5)
    and the address-space limit MEM_GB.

    Returns {verdict, cpu, wall, status} with status one of: ok, timeout, error. Running out of
    memory counts as a timeout (unsolved, not an error), marked with "memout": true.
    """

    def preexec():
        os.setsid()  # own process group, so a timeout kills any children too
        soft = max(1, int(limit + 0.999))
        resource.setrlimit(resource.RLIMIT_CPU, (soft, soft + 1))
        if MEM_GB > 0:
            cap = int(MEM_GB * (1 << 30))
            resource.setrlimit(resource.RLIMIT_AS, (cap, cap))

    start = time.perf_counter()
    proc = subprocess.Popen(
        cmd + [str(path)],
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        preexec_fn=preexec,
    )
    killed = threading.Event()

    def kill():
        killed.set()
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass

    timer = threading.Timer(2 * limit + 5, kill)
    timer.start()
    out_chunks, err_chunks = [], []
    readers = [
        threading.Thread(target=lambda: out_chunks.append(proc.stdout.read())),
        threading.Thread(target=lambda: err_chunks.append(proc.stderr.read())),
    ]
    for r in readers:
        r.start()
    _, status, usage = os.wait4(proc.pid, 0)
    # By hand rather than os.waitstatus_to_exitcode, which needs Python 3.9.
    proc.returncode = -os.WTERMSIG(status) if os.WIFSIGNALED(status) else os.WEXITSTATUS(status)
    timer.cancel()
    for r in readers:
        r.join()
    wall = time.perf_counter() - start
    cpu = usage.ru_utime + usage.ru_stime
    stdout = b"".join(out_chunks).decode(errors="replace")
    stderr = b"".join(err_chunks).decode(errors="replace")

    verdict = parse_verdict(stdout)
    if verdict is None and ("memory allocation" in stderr or "std::bad_alloc" in stderr
                            or "out of memory" in stderr.lower()):
        return {"verdict": None, "cpu": cpu, "wall": wall, "status": "timeout", "memout": True}
    if killed.is_set() or cpu > limit or (
        os.WIFSIGNALED(status) and os.WTERMSIG(status) in (signal.SIGXCPU, signal.SIGKILL)
    ):
        return {"verdict": None, "cpu": cpu, "wall": wall, "status": "timeout"}
    if verdict is None:
        msg = (stderr.strip() or stdout.strip()).splitlines()
        return {
            "verdict": None,
            "cpu": cpu,
            "wall": wall,
            "status": "error",
            "message": (msg[-1] if msg else f"exit code {proc.returncode}")[:200],
        }
    return {"verdict": verdict, "cpu": cpu, "wall": wall, "status": "ok"}


# ---------------------------------------------------------------------------------------------
# fetch


def zenodo_checksum(logic):
    with urllib.request.urlopen(ZENODO_API.format(record=ZENODO_RECORD)) as r:
        meta = json.load(r)
    for f in meta["files"]:
        if f["key"] == f"{logic}.tar.zst":
            return f["size"], f["checksum"]
    sys.exit(f"{logic}.tar.zst is not in Zenodo record {ZENODO_RECORD}")


def cmd_fetch(args):
    logic = args.logic
    size, checksum = zenodo_checksum(logic)
    algo, want = checksum.split(":")
    if size > args.max_mb * 1e6:
        sys.exit(
            f"{logic}.tar.zst is {size / 1e6:.0f} MB, over --max-mb {args.max_mb}. "
            "Raise the limit if you really want it."
        )
    if not shutil.which("zstd"):
        sys.exit("zstd is required to unpack SMT-LIB archives")
    DATA.mkdir(parents=True, exist_ok=True)
    archive = DATA / f"{logic}.tar.zst"
    url = ARCHIVE_URL.format(record=ZENODO_RECORD, logic=logic)
    for attempt in range(1, 4):
        print(f"downloading {logic}.tar.zst ({size / 1e6:.0f} MB), attempt {attempt}")
        h = hashlib.new(algo)
        try:
            with urllib.request.urlopen(url, timeout=120) as r, open(archive, "wb") as out:
                while chunk := r.read(1 << 20):
                    h.update(chunk)
                    out.write(chunk)
        except OSError as e:  # Zenodo drops long downloads now and then
            print(f"  {e}")
        got = archive.stat().st_size if archive.exists() else 0
        if got == size and h.hexdigest() == want:
            break
        print(f"  got {got} of {size} bytes, checksum {h.hexdigest()}")
    else:
        archive.unlink(missing_ok=True)
        sys.exit(f"could not download {archive.name} intact (want checksum {want})")
    print("checksum ok, unpacking")
    with subprocess.Popen(["zstd", "-dc", str(archive)], stdout=subprocess.PIPE) as z:
        with tarfile.open(fileobj=z.stdout, mode="r|") as tar:
            # The "data" filter (Python 3.12, backported to some 3.8+) refuses unsafe members.
            safe = {"filter": "data"} if hasattr(tarfile, "data_filter") else {}
            tar.extractall(DATA, **safe)
    archive.unlink()
    n = sum(1 for _ in logic_root(logic).rglob("*.smt2"))
    print(f"{n} benchmarks in {logic_root(logic).relative_to(ROOT)}")


def logic_root(logic):
    return DATA / "non-incremental" / logic


# ---------------------------------------------------------------------------------------------
# make-sets


def declared_status(path):
    with open(path, errors="replace") as f:
        for line in f:
            if ":status" in line:
                rest = line.split(":status", 1)[1].split()
                if rest:
                    return rest[0].strip(")")
    return None


def family_of(rel):
    """The benchmark family: the top directory, plus a non-numeric second level if present
    (QG-classification/qg5 and /qg7 are different populations; CLEARSY/0001 is not)."""
    parts = Path(rel).parts
    if len(parts) > 2 and not parts[1].isdigit():
        return f"{parts[0]}/{parts[1]}"
    return parts[0]


def cmd_make_sets(args):
    root = logic_root(args.logic)
    if not root.is_dir():
        sys.exit(f"no benchmarks at {root}; run `bench.py fetch {args.logic}` first")
    z3 = solver_command("z3")
    cvc5 = solver_command("cvc5")
    if not z3 or not z3[0] or not cvc5 or not cvc5[0]:
        sys.exit("make-sets needs z3 and cvc5 to confirm the expected verdicts")

    families = collections.defaultdict(list)
    unlabelled = collections.Counter()
    for p in sorted(root.rglob("*.smt2")):
        rel = p.relative_to(root).as_posix()
        if args.labelled_only and declared_status(p) not in VERDICTS:
            unlabelled[family_of(rel)] += 1
            continue
        families[family_of(rel)].append(rel)
    if unlabelled:
        print(f"skipped {sum(unlabelled.values())} files without a sat/unsat :status")

    rng = random.Random(args.seed)
    tuning, heldout = [], []
    per = args.per_family
    for fam in sorted(families):
        files = families[fam]
        picked = rng.sample(files, min(2 * per, len(files)))
        half = (len(picked) + 1) // 2
        tuning += [(fam, f) for f in picked[:half]]
        heldout += [(fam, f) for f in picked[half:]]

    # Confirm every expected verdict with z3 (and cvc5 where z3 cannot decide).
    candidates = tuning + heldout
    print(f"confirming {len(candidates)} verdicts with z3/cvc5 (limit {args.oracle_timeout}s)")

    def confirm(item):
        fam, rel = item
        path = root / rel
        status = declared_status(path)
        z = run_instance(z3, path, args.oracle_timeout)["verdict"]
        c = None
        if args.both_oracles or z not in VERDICTS or status not in VERDICTS:
            c = run_instance(cvc5, path, args.oracle_timeout)["verdict"]
        votes = {v for v in (status, z, c) if v in VERDICTS}
        if len(votes) > 1:
            return item, None, f"oracles disagree: status={status} z3={z} cvc5={c}"
        if not votes:
            return item, None, "no oracle decided it"
        if status not in VERDICTS and not (z in VERDICTS and c in VERDICTS):
            return item, None, f"unlabelled and only one oracle decided (z3={z} cvc5={c})"
        return item, votes.pop(), None

    expected, dropped = {}, []
    with ThreadPoolExecutor(args.jobs) as ex:
        for (fam, rel), verdict, why in ex.map(confirm, candidates):
            if verdict:
                expected[rel] = verdict
            else:
                dropped.append({"path": rel, "reason": why})
                print(f"  dropped {rel}: {why}")

    def entries(items):
        return [
            {"path": rel, "family": fam, "expected": expected[rel]}
            for fam, rel in items
            if rel in expected
        ]

    manifest = {
        "logic": args.logic,
        "source": f"SMT-LIB 2025 non-incremental, Zenodo record {ZENODO_RECORD}",
        "seed": args.seed,
        "per_family": per,
        "timeout": args.timeout,
        "tuning": entries(tuning),
        "heldout": entries(heldout),
        "dropped": dropped,
    }
    if args.labelled_only:
        manifest["labelled_only"] = True
        manifest["unlabelled_skipped"] = dict(sorted(unlabelled.items()))
    if args.both_oracles:
        manifest["both_oracles"] = True
    SETS.mkdir(parents=True, exist_ok=True)
    out = SETS / f"{args.logic}.json"
    out.write_text(json.dumps(manifest, indent=1) + "\n")
    print(
        f"wrote {out.relative_to(ROOT)}: {len(manifest['tuning'])} tuning, "
        f"{len(manifest['heldout'])} held-out, {len(dropped)} dropped"
    )


# ---------------------------------------------------------------------------------------------
# run


def full_set(logic):
    """Every benchmark of the logic; the expected verdict is its :status (may be unknown)."""
    root = logic_root(logic)
    if not root.is_dir():
        sys.exit(f"no benchmarks at {root}; run `bench.py fetch {logic}` first")
    items = []
    for p in sorted(root.rglob("*.smt2")):
        rel = p.relative_to(root).as_posix()
        status = declared_status(p)
        items.append({"path": rel, "family": family_of(rel),
                      "expected": status if status in VERDICTS else "unknown"})
    return {"logic": logic, "timeout": 10}, items


def load_set(logic, which):
    if which == "full":
        return full_set(logic)
    path = SETS / f"{logic}.json"
    if not path.exists():
        sys.exit(f"no set file {path}; run `bench.py make-sets {logic}`")
    manifest = json.loads(path.read_text())
    if which == "all":
        return manifest, manifest["tuning"] + manifest["heldout"]
    return manifest, manifest[which]


def cmd_run(args):
    name, cmd = resolve_solver(args)
    manifest, items = load_set(args.logic, args.set)
    if args.set == "heldout" and not args.i_mean_heldout:
        sys.exit(
            "the held-out set is for final reporting only; pass --i-mean-heldout to run it"
        )
    root = logic_root(args.logic)
    missing = [i["path"] for i in items if not (root / i["path"]).exists()]
    if missing:
        sys.exit(f"{len(missing)} benchmark files missing (first: {missing[0]}); run fetch")
    limit = args.timeout or manifest["timeout"]

    print(f"{name}: {len(items)} instances from {args.logic}/{args.set}, "
          f"CPU limit {limit:g}s, {args.jobs} jobs")
    rows = []
    done = 0

    def one(item):
        return item, run_instance(cmd, root / item["path"], limit)

    with ThreadPoolExecutor(args.jobs) as ex:
        for item, r in ex.map(one, items):
            done += 1
            r = {**item, **r}
            if r["status"] == "ok" and r["verdict"] in VERDICTS:
                wrong = item["expected"] in VERDICTS and r["verdict"] != item["expected"]
                r["outcome"] = "WRONG" if wrong else "solved"
            else:
                r["outcome"] = "unsolved"
            if r["outcome"] == "WRONG":
                print(f"  WRONG {item['path']}: said {r['verdict']}, expected {item['expected']}")
            rows.append(r)
            if not args.quiet and sys.stderr.isatty():
                print(f"\r  {done}/{len(items)}", end="", file=sys.stderr, flush=True)
    if not args.quiet and sys.stderr.isatty():
        print("\r" + " " * 20 + "\r", end="", file=sys.stderr)

    summary = summarize(rows, limit)
    result = {
        "solver": name,
        "command": cmd,
        "logic": args.logic,
        "set": args.set,
        "timeout": limit,
        "jobs": args.jobs,
        "created": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "summary": summary,
        "instances": rows,
    }
    out = Path(args.out) if args.out else RESULTS / (
        f"{args.logic}-{args.set}-{name}-{time.strftime('%Y%m%d-%H%M%S')}.json"
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=1) + "\n")

    print_summary(result)
    print(f"results: {out}")
    return 1 if summary["wrong"] else 0


def par2(rows, limit):
    total = sum(r["cpu"] if r["outcome"] == "solved" else 2 * limit for r in rows)
    return total / len(rows) if rows else 0.0


def summarize(rows, limit):
    by_family = collections.defaultdict(list)
    for r in rows:
        by_family[r["family"]].append(r)
    errors = collections.Counter(r.get("message", "") for r in rows if r["status"] == "error")
    return {
        "instances": len(rows),
        "solved": sum(r["outcome"] == "solved" for r in rows),
        "wrong": sum(r["outcome"] == "WRONG" for r in rows),
        "timeouts": sum(r["status"] == "timeout" for r in rows),
        "errors": sum(r["status"] == "error" for r in rows),
        "unknown": sum(r["status"] == "ok" and r["verdict"] == "unknown" for r in rows),
        "par2": par2(rows, limit),
        "top_errors": errors.most_common(5),
        "families": {
            fam: {
                "instances": len(rs),
                "solved": sum(r["outcome"] == "solved" for r in rs),
                "wrong": sum(r["outcome"] == "WRONG" for r in rs),
                "par2": par2(rs, limit),
            }
            for fam, rs in sorted(by_family.items())
        },
    }


def print_summary(result):
    s = result["summary"]
    verdict = "DISQUALIFIED (wrong answers)" if s["wrong"] else "ok"
    print(f"\n{result['solver']} on {result['logic']}/{result['set']}: {verdict}")
    print(f"  solved {s['solved']}/{s['instances']}  wrong {s['wrong']}  "
          f"timeouts {s['timeouts']}  errors {s['errors']}  unknown {s['unknown']}")
    print(f"  PAR-2 {s['par2']:.3f}s  (CPU limit {result['timeout']:g}s)")
    width = max(len(f) for f in s["families"]) if s["families"] else 6
    print(f"\n  {'family':<{width}}  solved      PAR-2")
    for fam, f in s["families"].items():
        flag = f"  WRONG {f['wrong']}" if f["wrong"] else ""
        print(f"  {fam:<{width}}  {f['solved']:>3}/{f['instances']:<3}  {f['par2']:8.3f}s{flag}")
    if s["top_errors"]:
        print("\n  most common errors:")
        for msg, n in s["top_errors"]:
            print(f"    {n:>4}  {msg}")


# ---------------------------------------------------------------------------------------------
# compare


def cmd_compare(args):
    a = json.loads(Path(args.a).read_text())
    b = json.loads(Path(args.b).read_text())
    if (a["logic"], a["set"], a["timeout"]) != (b["logic"], b["set"], b["timeout"]):
        print("warning: the two runs differ in logic, set or timeout; the comparison is unfair")
    ra = {r["path"]: r for r in a["instances"]}
    rb = {r["path"]: r for r in b["instances"]}
    common = sorted(ra.keys() & rb.keys())
    sa, sb = a["summary"], b["summary"]
    print(f"A = {a['solver']} ({args.a})\nB = {b['solver']} ({args.b})\n")
    print(f"          {'A':>10} {'B':>10}")
    print(f"  solved  {sa['solved']:>10} {sb['solved']:>10}")
    print(f"  wrong   {sa['wrong']:>10} {sb['wrong']:>10}")
    print(f"  PAR-2   {sa['par2']:>9.3f}s {sb['par2']:>9.3f}s")
    gained = [p for p in common if ra[p]["outcome"] != "solved" and rb[p]["outcome"] == "solved"]
    lost = [p for p in common if ra[p]["outcome"] == "solved" and rb[p]["outcome"] != "solved"]
    both = [p for p in common if ra[p]["outcome"] == rb[p]["outcome"] == "solved"]
    print(f"\n  solved by B only: {len(gained)}   solved by A only: {len(lost)}")
    for p in gained[: args.show]:
        print(f"    + {p}")
    for p in lost[: args.show]:
        print(f"    - {p}")
    if both:
        ta = sum(ra[p]["cpu"] for p in both)
        tb = sum(rb[p]["cpu"] for p in both)
        print(f"\n  on the {len(both)} instances both solved: A {ta:.2f}s, B {tb:.2f}s CPU"
              + (f"  (B is {ta / tb:.2f}x A's speed)" if tb > 0 else ""))


# ---------------------------------------------------------------------------------------------
# report


def cmd_report(args):
    """One Markdown table for runs of several solvers on the same logic, set and limit."""
    runs = [json.loads(Path(f).read_text()) for f in args.results]
    runs.sort(key=lambda r: (r["solver"] != "smt-rex", r["solver"]))
    keys = {(r["logic"], r["set"], r["timeout"]) for r in runs}
    if len(keys) > 1:
        sys.exit(f"the runs differ in logic, set or timeout: {sorted(keys)}")
    logic, which, limit = keys.pop()
    by_path = [{i["path"]: i for i in r["instances"]} for r in runs]
    paths = sorted(set().union(*by_path))
    solved = [{p for p, i in b.items() if i["outcome"] == "solved"} for b in by_path]

    lines = [f"### {logic} ({which}, {len(paths)} benchmarks, {limit:g} s CPU)", "",
             "| solver | solved | sat | unsat | wrong | PAR-2 (s) | only this solver |",
             "|---|---:|---:|---:|---:|---:|---:|"]
    for k, r in enumerate(runs):
        mine = by_path[k]
        sat = sum(i["outcome"] == "solved" and i["verdict"] == "sat" for i in mine.values())
        others = set().union(*(solved[j] for j in range(len(runs)) if j != k))
        s = r["summary"]
        lines.append(f"| {r['solver']} | {s['solved']} | {sat} | {s['solved'] - sat} | "
                     f"{s['wrong']} | {s['par2']:.3f} | {len(solved[k] - others)} |")

    # Benchmarks without a :status can still expose a wrong answer: two solvers disagreeing.
    disagree = []
    for p in paths:
        said = {r["solver"]: b[p]["verdict"] for r, b in zip(runs, by_path)
                if p in b and b[p]["outcome"] == "solved"}
        if len(set(said.values())) > 1:
            disagree.append((p, said))
    lines += ["", f"Disagreements between solvers: {len(disagree)}"]
    for p, said in disagree[: args.show]:
        lines.append(f"- `{p}`: " + ", ".join(f"{n} {v}" for n, v in sorted(said.items())))
    for r in runs:
        for i in r["instances"]:
            if i["outcome"] == "WRONG":
                lines.append(f"- WRONG {r['solver']} `{i['path']}`: said {i['verdict']}, "
                             f":status {i['expected']}")
    text = "\n".join(lines) + "\n"
    print(text, end="")
    if args.out:
        Path(args.out).write_text(text)
    return 1 if disagree or any(r["summary"]["wrong"] for r in runs) else 0


# ---------------------------------------------------------------------------------------------


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    sub = ap.add_subparsers(dest="command", required=True)
    jobs = max(1, (os.cpu_count() or 2) // 2)

    p = sub.add_parser("fetch", help="download and unpack one logic's benchmarks")
    p.add_argument("logic", nargs="?", default="QF_UF")
    p.add_argument("--max-mb", type=float, default=1000, help="refuse archives above this size")
    p.set_defaults(func=cmd_fetch)

    p = sub.add_parser("make-sets", help="draw tuning/held-out sets and confirm their verdicts")
    p.add_argument("logic", nargs="?", default="QF_UF")
    p.add_argument("--per-family", type=int, default=20, help="instances per family per set")
    p.add_argument("--seed", type=int, default=2026)
    p.add_argument("--timeout", type=float, default=10, help="CPU limit recorded in the set")
    p.add_argument("--oracle-timeout", type=float, default=60)
    p.add_argument("--labelled-only", action="store_true",
                   help="sample only files whose :status is sat or unsat")
    p.add_argument("--both-oracles", action="store_true",
                   help="always run cvc5 too, so a z3/cvc5 disagreement drops the file")
    p.add_argument("--jobs", type=int, default=jobs)
    p.set_defaults(func=cmd_make_sets)

    p = sub.add_parser("run", help="run a solver over a set")
    p.add_argument("solver", nargs="?", default="smt-rex", help=", ".join(SOLVERS))
    p.add_argument("--logic", default="QF_UF")
    p.add_argument("--set", default="tuning", choices=["tuning", "heldout", "all", "full"],
                   help="full: every file of the logic, expected verdict from :status")
    p.add_argument("--i-mean-heldout", action="store_true",
                   help="confirm a held-out run (keep it for final reports)")
    p.add_argument("--timeout", type=float, help="override the set's CPU limit")
    p.add_argument("--jobs", type=int, default=jobs)
    p.add_argument("--cmd", help="custom solver command line (file path appended)")
    p.add_argument("--name", help="label for a --cmd solver")
    p.add_argument("--out", help="result file (default bench/results/<...>.json)")
    p.add_argument("--quiet", action="store_true")
    p.set_defaults(func=cmd_run)

    p = sub.add_parser("compare", help="compare two result files")
    p.add_argument("a")
    p.add_argument("b")
    p.add_argument("--show", type=int, default=10, help="instances to list per direction")
    p.set_defaults(func=cmd_compare)

    p = sub.add_parser("report", help="Markdown table for several solvers' runs of one set")
    p.add_argument("results", nargs="+")
    p.add_argument("--show", type=int, default=20, help="disagreements to list")
    p.add_argument("--out", help="also write the table here")
    p.set_defaults(func=cmd_report)

    args = ap.parse_args()
    sys.exit(args.func(args) or 0)


if __name__ == "__main__":
    main()
