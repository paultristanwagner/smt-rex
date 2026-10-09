#!/usr/bin/env python3
"""Accept or reject one SMT-Rex change: build it, fuzz it, time it on the tuning sets.

Subcommands (run `evaluate.py <cmd> --help` for options):

  measure   build a solver, fuzz it, run the tuning sets; write a result file (e.g. a baseline)
  run       `measure`, then judge the result against a baseline result file
  verdict   judge an existing result file against a baseline (nothing is rerun)
  check     only the guards: protected files and benchmark names in the candidate's diff

The solver comes from `--ref REF` (a git ref, exported with `git archive`), `--src DIR` (a
directory holding a copy of the repository), or by default the current working tree. It is
built into bench/eval/target/<solver>, never into target/. The harness itself (this script, bench.py,
fuzz.py and the sets) always comes from the checkout this script lives in, never from the
candidate, so a candidate cannot change how it is scored.

A candidate is ACCEPTED only if all of these hold:

  * no protected file changed: nothing under bench/ (the sets, the scripts, the docs)
    and no benchmark file name appears in the solver diff (no special-casing instances);
  * the fuzzer (fuzz.py's generators, against z3) found nothing in any logic;
  * no instance of any tuning set got a wrong answer in any repetition;
  * the overall PAR-2 improved by more than the noise margin, max(--margin-rel * baseline,
    --margin-abs), and no single logic got worse by more than its own margin.

Only the tuning sets are ever run. There is no option to run the held-out sets: final
reports on those go through `bench.py run --set heldout --i-mean-heldout`, by a human.

Python 3.8+ standard library only (RunPod's CPU image ships 3.8).
"""

import argparse
import collections
import hashlib
import json
import os
import platform
import random
import shutil
import statistics
import subprocess
import sys
import tarfile
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import bench  # noqa: E402
import fuzz  # noqa: E402

ROOT = HERE.parent
REPO = ROOT
EVAL = HERE / "eval"  # build cache and scratch space (gitignored)
FUZZ_LOGICS = sorted(fuzz.GENERATORS)
SET_LOGICS = sorted(p.stem for p in bench.SETS.glob("*.json"))
FORMAT = "smtrex-evaluation/1"

# Paths a candidate may not touch (relative to the repo root), and the exceptions.
PROTECTED = ("bench/",)
UNPROTECTED = ("bench/results/", "bench/eval/", "bench/data")

# Noise margin defaults; see bench/loop.md ("The noise margin") for the measurement.
MARGIN_REL = 0.03
MARGIN_ABS = 0.05  # seconds of PAR-2


def log(msg):
    print(msg, flush=True)


# ---------------------------------------------------------------------------------------------
# git


def git(*args, check=True):
    """stdout of `git args` in the repo, or None outside a git checkout."""
    try:
        p = subprocess.run(["git", "-C", str(REPO)] + list(args), stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, universal_newlines=True)
    except FileNotFoundError:
        return None
    if p.returncode != 0:
        if check and (REPO / ".git").exists():
            sys.exit(f"git {' '.join(args)} failed: {p.stderr.strip()}")
        return None
    return p.stdout


def head_commit():
    out = git("rev-parse", "HEAD", check=False)
    return out.strip() if out else None


# ---------------------------------------------------------------------------------------------
# Building


def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def worktree_fingerprint():
    """A hash of the uncommitted state of the checkout (tracked diff plus untracked files)."""
    h = hashlib.sha256()
    h.update((git("diff", "HEAD", "--binary", check=False) or "").encode())
    untracked = git("ls-files", "--others", "--exclude-standard", check=False) or ""
    for rel in sorted(untracked.split()):
        p = REPO / rel
        if p.is_file():
            h.update(rel.encode() + b"\0" + p.read_bytes())
    return h.hexdigest()[:12]


def resolve_source(args):
    """(label, source dir or None for a git ref, commit, ref) for the candidate."""
    if args.ref:
        sha = git("rev-parse", "--verify", args.ref + "^{commit}")
        if not sha:
            sys.exit(f"{args.ref} is not a commit (and this is not a git checkout)")
        sha = sha.strip()
        return {"label": args.label or sha[:12], "kind": "ref", "ref": args.ref, "commit": sha}
    if args.src:
        src = Path(args.src).resolve()
        if not (src / "Cargo.toml").exists():
            sys.exit(f"--src {args.src}: no Cargo.toml (expected a copy of the repository)")
        label = args.label or "src-" + src.parent.name
        return {"label": label, "kind": "src", "src": str(src), "commit": args.commit}
    commit = head_commit()
    fp = worktree_fingerprint() if commit else "nogit"
    label = args.label or "wt-{}-{}".format((commit or "nogit")[:12], fp)
    return {"label": label, "kind": "worktree", "src": str(ROOT), "commit": commit,
            "dirty_fingerprint": fp}


def export_ref(sha):
    """`git archive` the commit into bench/eval/src/<sha>/tree (cached)."""
    dest = EVAL / "src" / sha
    if (dest / "tree" / "Cargo.toml").exists():
        return dest / "tree"
    tmp = Path(tempfile.mkdtemp(prefix="src-", dir=str(EVAL)))
    archive = subprocess.Popen(["git", "-C", str(REPO), "archive", "--format=tar", "--prefix=tree/", sha],
                               stdout=subprocess.PIPE)
    with tarfile.open(fileobj=archive.stdout, mode="r|") as tar:
        if hasattr(tarfile, "data_filter"):  # Python 3.12+ (and patched 3.8.17+)
            tar.extractall(str(tmp), filter="data")
        else:
            tar.extractall(str(tmp))
    if archive.wait() != 0:
        sys.exit(f"git archive {sha} failed")
    dest.parent.mkdir(parents=True, exist_ok=True)
    if dest.exists():
        shutil.rmtree(str(dest))
    tmp.rename(dest)
    return dest / "tree"


def build(source):
    """Build the candidate's smt-rex into bench/eval and return the binary's path."""
    EVAL.mkdir(parents=True, exist_ok=True)
    name = source["commit"][:12] if source["kind"] == "ref" else source["label"]
    out = EVAL / "bin" / f"smt-rex-{name}"
    if source["kind"] == "ref":
        if out.exists():
            log(f"build: reusing {out.relative_to(ROOT)}")
            return out
        src = export_ref(source["commit"])
    else:
        src = Path(source["src"])
    # One target dir per solver: exported sources carry the commit time as their mtime, so with
    # a shared target dir cargo can take the candidate for up to date and reuse another binary.
    target = EVAL / "target" / name
    env = dict(os.environ, CARGO_TARGET_DIR=str(target))
    env.setdefault("CARGO_BUILD_JOBS", "4")
    log(f"build: {source['label']} from {src} (CARGO_BUILD_JOBS={env['CARGO_BUILD_JOBS']})")
    t = time.time()
    p = subprocess.run(["nice", "-n", "19", "cargo", "build", "--release", "--quiet",
                        "--bin", "smt-rex"], cwd=str(src), env=env)
    if p.returncode != 0:
        return None
    out.parent.mkdir(parents=True, exist_ok=True)
    tmp = out.with_name(out.name + ".tmp")
    shutil.copy2(str(target / "release" / "smt-rex"), str(tmp))
    tmp.rename(out)
    log(f"build: done in {time.time() - t:.0f}s -> {out.relative_to(ROOT)}")
    return out


# ---------------------------------------------------------------------------------------------
# Guards


def candidate_diff(source, base_commit):
    """The candidate's change to the solver (not bench/, not docs) relative to the baseline
    commit: (files, added lines).

    None when it cannot be determined (no git, or an --src source)."""
    if source["kind"] == "src" or not source.get("commit") or not base_commit:
        return None
    if git("cat-file", "-e", base_commit + "^{commit}", check=False) is None:
        return None
    if source["kind"] == "ref":
        rng = [base_commit, source["commit"]]
    else:
        rng = [base_commit]  # commit vs working tree
    names = (git("diff", "--name-only", *rng) or "").split()
    patch = git("diff", "--unified=0", *rng, "--", ".", ":!bench", ":!*.md") or ""
    added = [l[1:] for l in patch.splitlines() if l.startswith("+") and not l.startswith("+++")]
    if source["kind"] == "worktree":
        untracked = (git("ls-files", "--others", "--exclude-standard", check=False) or "").split()
        names += untracked
        for rel in untracked:
            p = REPO / rel
            if not rel.startswith("bench/") and not rel.endswith(".md") and p.is_file():
                added += p.read_text(errors="replace").splitlines()
    return sorted(set(names)), added


def benchmark_names():
    """Distinctive names of every set instance (tuning and held-out alike)."""
    names = set()
    for logic in SET_LOGICS:
        m = json.loads((bench.SETS / f"{logic}.json").read_text())
        for item in m["tuning"] + m["heldout"]:
            base = Path(item["path"]).name
            names.add(base)
            stem = Path(base).stem
            if len(stem) >= 12:
                names.add(stem)
    return names


def check_guards(source, base_commit):
    """Problems that disqualify the candidate before anything is measured."""
    diff = candidate_diff(source, base_commit)
    if diff is None:
        return [], "not checked (no git history for this source)"
    files, added = diff
    problems = []
    for f in files:
        if f.startswith(PROTECTED) and not f.startswith(UNPROTECTED):
            problems.append(f"protected file changed: {f}")
    names = benchmark_names()
    text = "\n".join(added)
    hits = sorted(n for n in names if n in text)
    for n in hits[:10]:
        problems.append(f"benchmark name in the solver diff: {n}")
    return problems, f"{len(files)} files changed vs {base_commit[:12]}"


# ---------------------------------------------------------------------------------------------
# Fuzzing


def run_fuzz(binary, count, seed, jobs):
    """Run `count` scripts per logic through fuzz.check; return the summary."""
    summary = {"count": count, "seed": seed, "reference": "z3", "logics": {}, "failures": 0}
    if count <= 0:
        summary["skipped"] = True
        return summary
    z3 = bench.solver_command("z3")
    if not z3 or not z3[0] or not shutil.which(z3[0]):
        sys.exit("fuzzing needs z3: set Z3=/path/to/z3 (or pass --fuzz-count 0, which "
                 "makes `run` reject)")
    tmp = Path(tempfile.mkdtemp(prefix="fuzz-", dir=str(EVAL)))
    try:
        for logic in FUZZ_LOGICS:
            t = time.time()
            seeds = range(seed, seed + count)
            fails = []
            timeouts = 0
            with ThreadPoolExecutor(jobs) as ex:
                for s, src, problem in ex.map(
                        lambda s: fuzz.check(s, [str(binary)], z3, tmp, logic), seeds):
                    # A timeout is counted, not a failure (some random QF_NRA scripts are hard).
                    if problem and problem.startswith("timeout:"):
                        timeouts += 1
                    elif problem:
                        bench.RESULTS.mkdir(parents=True, exist_ok=True)
                        saved = bench.RESULTS / f"eval-fuzz-fail-{logic}-{s}.smt2"
                        saved.write_text(src)
                        fails.append({"seed": s, "problem": problem[:300],
                                      "script": str(saved.relative_to(ROOT))})
            summary["logics"][logic] = {"scripts": count, "failures": len(fails),
                                        "timeouts": timeouts,
                                        "seconds": round(time.time() - t, 1),
                                        "first": fails[:5]}
            summary["failures"] += len(fails)
            log(f"fuzz: {logic} {count} scripts, {len(fails)} failures, {timeouts} timeouts "
                f"({time.time() - t:.0f}s)")
            for f in fails[:3]:
                log(f"  seed {f['seed']}: {f['problem'][:160]}")
    finally:
        shutil.rmtree(str(tmp), ignore_errors=True)
    return summary


# ---------------------------------------------------------------------------------------------
# Benchmarks


def set_digest(manifest):
    """Hash of what is measured: the tuning entries and the CPU limit."""
    blob = json.dumps({"tuning": manifest["tuning"], "timeout": manifest["timeout"]},
                      sort_keys=True)
    return sha256_bytes(blob.encode())[:16]


def run_tuning(binary, logic, repeats, jobs, timeout):
    """Run the logic's tuning set `repeats` times; merge per instance by the median."""
    manifest, items = bench.load_set(logic, "tuning")  # only ever the tuning set
    root = bench.logic_root(logic)
    missing = [i["path"] for i in items if not (root / i["path"]).exists()]
    if missing:
        sys.exit(f"{logic}: {len(missing)} benchmark files missing under {root} "
                 f"(first: {missing[0]})")
    limit = timeout or manifest["timeout"]
    cmd = [str(binary)]
    runs = collections.defaultdict(list)  # path -> [row per repeat]
    for rep in range(repeats):
        t = time.time()
        order = list(items)
        random.Random(rep).shuffle(order)  # spread slow instances differently each time
        with ThreadPoolExecutor(jobs) as ex:
            for item, r in ex.map(lambda i: (i, bench.run_instance(cmd, root / i["path"], limit)),
                                  order):
                if r["status"] == "ok" and r["verdict"] in bench.VERDICTS:
                    r["outcome"] = "solved" if r["verdict"] == item["expected"] else "WRONG"
                else:
                    r["outcome"] = "unsolved"
                if r["outcome"] == "WRONG":
                    log(f"  WRONG {logic}/{item['path']}: said {r['verdict']}, "
                        f"expected {item['expected']}")
                runs[item["path"]].append(r)
        rows = [dict(i, **runs[i["path"]][-1]) for i in items]
        s = bench.summarize(rows, limit)
        log(f"bench: {logic} repeat {rep + 1}/{repeats}: solved {s['solved']}/{s['instances']}"
            f" wrong {s['wrong']} PAR-2 {s['par2']:.3f}s ({time.time() - t:.0f}s wall)")

    merged = []
    for item in items:
        rs = runs[item["path"]]
        scores = [r["cpu"] if r["outcome"] == "solved" else 2 * limit for r in rs]
        n_solved = sum(r["outcome"] == "solved" for r in rs)
        wrong = [r for r in rs if r["outcome"] == "WRONG"]
        row = dict(item)
        row["cpus"] = [round(r["cpu"], 4) for r in rs]
        row["statuses"] = [r["status"] for r in rs]
        row["score"] = statistics.median(scores)
        if wrong:
            row["outcome"], row["verdict"] = "WRONG", wrong[0]["verdict"]
        elif 2 * n_solved >= len(rs):
            row["outcome"] = "solved"
        else:
            row["outcome"] = "unsolved"
        # bench.summarize/par2 read `cpu` and `status`; give them the merged view.
        row["cpu"] = row["score"]
        row["status"] = "ok" if row["outcome"] != "unsolved" else collections.Counter(
            row["statuses"]).most_common(1)[0][0]
        row["verdict"] = row.get("verdict") or next(
            (r["verdict"] for r in rs if r["outcome"] == "solved"), None)
        merged.append(row)
    summary = bench.summarize(merged, limit)
    # PAR-2 from the median scores (summarize counts only "solved" rows' cpu).
    summary["par2"] = sum(r["score"] for r in merged) / len(merged) if merged else 0.0
    for fam, f in summary["families"].items():
        rs = [r for r in merged if r["family"] == fam]
        f["par2"] = sum(r["score"] for r in rs) / len(rs)
    summary["wrong_any_repeat"] = sum(
        any(r["outcome"] == "WRONG" for r in runs[i["path"]]) for i in items)
    return {"timeout": limit, "set_digest": set_digest(manifest), "summary": summary,
            "instances": merged}


def measure(args):
    """Build, guard-check, fuzz and time a candidate; return the result dict (or exit)."""
    source = resolve_source(args)
    base = load_result(args.baseline) if getattr(args, "baseline", None) else None
    logics = args.logics.split(",") if args.logics else SET_LOGICS
    for logic in logics:
        if logic not in SET_LOGICS:
            sys.exit(f"no tuning set for {logic} (have: {', '.join(SET_LOGICS)})")
    result = {
        "format": FORMAT,
        "label": source["label"],
        "source": source,
        "created": time.strftime("%Y-%m-%dT%H:%M:%S"),
        "host": {"node": platform.node(), "cpus": os.cpu_count(),
                 "python": platform.python_version(), "machine": platform.machine()},
        "harness_commit": head_commit(),
        "jobs": args.jobs,
        "repeats": args.repeats,
        "logics": {},
        "build": "ok",
    }
    base_commit = (base or {}).get("source", {}).get("commit")
    problems, note = check_guards(source, base_commit) if base else ([], "no baseline")
    result["guards"] = {"problems": problems, "note": note}
    if problems:
        log("guards: " + "; ".join(problems))
        if not args.keep_going:
            return result

    binary = build(source)
    if binary is None:
        result["build"] = "failed"
        return result
    result["binary"] = str(binary)

    seed = args.fuzz_seed if args.fuzz_seed is not None else random.randrange(1, 10 ** 9)
    result["fuzz"] = run_fuzz(binary, args.fuzz_count, seed, args.jobs)
    if result["fuzz"]["failures"] and not args.keep_going:
        log("fuzz failures: skipping the benchmarks")
        return result

    for logic in logics:
        r = run_tuning(binary, logic, args.repeats, args.jobs, args.timeout)
        result["logics"][logic] = r
        if r["summary"]["wrong_any_repeat"] and not args.keep_going:
            log(f"{logic}: wrong answers, skipping the rest")
            break
    result["overall"] = overall(result)
    return result


def overall(result):
    n = sum(len(r["instances"]) for r in result["logics"].values())
    total = sum(r["summary"]["par2"] * len(r["instances"]) for r in result["logics"].values())
    return {
        "instances": n,
        "par2": total / n if n else 0.0,
        "solved": sum(r["summary"]["solved"] for r in result["logics"].values()),
        "wrong": sum(r["summary"]["wrong_any_repeat"] for r in result["logics"].values()),
    }


# ---------------------------------------------------------------------------------------------
# Verdict


def load_result(path):
    data = json.loads(Path(path).read_text())
    if data.get("format") == FORMAT:
        return data
    if "instances" in data and "logic" in data:  # a bench.py result file
        sys.exit(f"{path} is a bench.py result; make baselines with `evaluate.py measure` so "
                 "that both sides use the same repeats and jobs")
    sys.exit(f"{path} is not an evaluate.py result file")


def judge(cand, base, margin_rel, margin_abs):
    reasons = []
    if cand.get("guards", {}).get("problems"):
        reasons += cand["guards"]["problems"]
    if cand.get("build") != "ok":
        reasons.append("build failed")
    fz = cand.get("fuzz") or {}
    if not fz or fz.get("skipped"):
        reasons.append("fuzzing was skipped")
    elif fz.get("failures"):
        reasons.append(f"{fz['failures']} fuzz failures")
    wrong = sum(r["summary"]["wrong_any_repeat"] for r in cand["logics"].values())
    if wrong:
        reasons.append(f"{wrong} wrong answers")

    logics = {}
    common = sorted(set(cand["logics"]) & set(base["logics"]))
    for logic in common:
        c, b = cand["logics"][logic], base["logics"][logic]
        if (c["set_digest"], c["timeout"]) != (b["set_digest"], b["timeout"]):
            reasons.append(f"{logic}: baseline measured a different set or CPU limit")
            continue
        cr = {r["path"]: r for r in c["instances"]}
        br = {r["path"]: r for r in b["instances"]}
        gained = sorted(p for p in cr if cr[p]["outcome"] == "solved"
                        and br[p]["outcome"] != "solved")
        lost = sorted(p for p in cr if cr[p]["outcome"] != "solved"
                      and br[p]["outcome"] == "solved")
        fams = {}
        for fam, fb in b["summary"]["families"].items():
            fc = c["summary"]["families"].get(fam)
            if fc:
                fams[fam] = {"base": round(fb["par2"], 4), "cand": round(fc["par2"], 4),
                             "delta": round(fc["par2"] - fb["par2"], 4),
                             "solved": [fb["solved"], fc["solved"]]}
        bp, cp = b["summary"]["par2"], c["summary"]["par2"]
        margin = max(margin_rel * bp, margin_abs)
        logics[logic] = {"base_par2": round(bp, 4), "cand_par2": round(cp, 4),
                         "delta": round(cp - bp, 4), "margin": round(margin, 4),
                         "newly_solved": gained, "lost": lost, "families": fams}
        if cp - bp > margin:
            reasons.append(f"{logic} got slower: PAR-2 {bp:.3f}s -> {cp:.3f}s "
                           f"(+{cp - bp:.3f}s > margin {margin:.3f}s)")

    def pooled(res):
        n = sum(len(res["logics"][l]["instances"]) for l in common)
        s = sum(res["logics"][l]["summary"]["par2"] * len(res["logics"][l]["instances"])
                for l in common)
        return s / n if n else 0.0

    bp, cp = pooled(base), pooled(cand)
    margin = max(margin_rel * bp, margin_abs)
    improvement = bp - cp
    if common and improvement <= margin and not reasons:
        reasons.append(f"no significant improvement: PAR-2 {bp:.3f}s -> {cp:.3f}s "
                       f"(gain {improvement:+.3f}s, needs > {margin:.3f}s)")
    if not common and not reasons:
        reasons.append("nothing measured")
    return {
        "verdict": "REJECT" if reasons else "ACCEPT",
        "reasons": reasons,
        "baseline": base.get("label"),
        "candidate": cand.get("label"),
        "par2": {"base": round(bp, 4), "cand": round(cp, 4), "improvement": round(improvement, 4),
                 "improvement_pct": round(100 * improvement / bp, 2) if bp else None,
                 "margin": round(margin, 4), "margin_rel": margin_rel, "margin_abs": margin_abs},
        "logics": logics,
        "fuzz": {k: fz.get(k) for k in ("count", "seed", "failures")} if fz else None,
        "fuzz_logics": {l: v["failures"] for l, v in fz.get("logics", {}).items()},
        "wrong": wrong,
    }


def print_verdict(v):
    log(f"\n{v['verdict']}: {v['candidate']} vs baseline {v['baseline']}")
    for r in v["reasons"]:
        log(f"  - {r}")
    p = v["par2"]
    if p["base"]:
        log(f"  PAR-2 {p['base']:.3f}s -> {p['cand']:.3f}s  ({p['improvement_pct']:+.2f}% gain,"
            f" margin {p['margin']:.3f}s)")
    if v["fuzz"]:
        log(f"  fuzz: {v['fuzz']['failures']} failures in {v['fuzz']['count']} scripts x "
            f"{len(v['fuzz_logics'])} logics (seed {v['fuzz']['seed']})")
    for logic, l in v["logics"].items():
        log(f"  {logic}: PAR-2 {l['base_par2']:.3f}s -> {l['cand_par2']:.3f}s "
            f"(delta {l['delta']:+.3f}s, margin {l['margin']:.3f}s), "
            f"+{len(l['newly_solved'])} solved, -{len(l['lost'])} lost")
        moved = sorted(l["families"].items(), key=lambda kv: -abs(kv[1]["delta"]))[:4]
        for fam, f in moved:
            if abs(f["delta"]) >= 0.005:
                log(f"      {fam:<40} {f['base']:8.3f}s -> {f['cand']:8.3f}s ({f['delta']:+.3f}s)")
        for path in l["newly_solved"][:5]:
            log(f"      + {path}")
        for path in l["lost"][:5]:
            log(f"      - {path}")


# ---------------------------------------------------------------------------------------------
# Commands


def write(result, out, default_name):
    path = Path(out) if out else bench.RESULTS / default_name
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(result, indent=1) + "\n")
    log(f"wrote {path}")
    return path


def cmd_measure(args):
    args.baseline = None
    result = measure(args)
    write(result, args.out, f"eval-{result['label']}.json")
    o = result.get("overall")
    if o:
        log(f"\n{result['label']}: PAR-2 {o['par2']:.3f}s over {o['instances']} instances, "
            f"solved {o['solved']}, wrong {o['wrong']}")
    fz = result.get("fuzz") or {}
    bad = result.get("build") != "ok" or fz.get("failures") or (o or {}).get("wrong")
    if bad:
        log("this result is not a usable baseline (build failure, fuzz failure or wrong answers)")
    return 1 if bad else 0


def cmd_run(args):
    base = load_result(args.baseline)
    result = measure(args)
    result["verdict"] = judge(result, base, args.margin_rel, args.margin_abs)
    write(result, args.out, f"eval-{result['label']}.json")
    print_verdict(result["verdict"])
    return 0 if result["verdict"]["verdict"] == "ACCEPT" else 2


def cmd_check(args):
    source = resolve_source(args)
    problems, note = check_guards(source, args.base_commit)
    log(f"guards: {note}")
    for pr in problems:
        log(f"  - {pr}")
    log("guards: " + ("FAIL" if problems else "ok"))
    return 1 if problems else 0


def cmd_verdict(args):
    cand, base = load_result(args.candidate), load_result(args.baseline)
    v = judge(cand, base, args.margin_rel, args.margin_abs)
    if args.out:
        Path(args.out).write_text(json.dumps(v, indent=1) + "\n")
    print_verdict(v)
    return 0 if v["verdict"] == "ACCEPT" else 2


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    sub = ap.add_subparsers(dest="command")
    sub.required = True
    jobs = max(1, min(6, (os.cpu_count() or 2) // 2))

    def source_opts(p):
        g = p.add_mutually_exclusive_group()
        g.add_argument("--ref", help="git ref to build (default: the working tree)")
        g.add_argument("--src", help="directory with a copy of the repository to build")
        p.add_argument("--label", help="name for the binary and result file")
        p.add_argument("--commit", help="with --src: the commit it was exported from")
        p.add_argument("--logics", help="comma-separated tuning sets to run "
                       f"(default: all, i.e. {','.join(SET_LOGICS)})")
        p.add_argument("--jobs", type=int, default=jobs, help=f"parallel jobs (default {jobs})")
        p.add_argument("--repeats", type=int, default=2,
                       help="runs per tuning set; per-instance median CPU time (default 2)")
        p.add_argument("--timeout", type=float, help="override the sets' CPU limit (seconds)")
        p.add_argument("--fuzz-count", type=int, default=300,
                       help="fuzz scripts per logic, every logic (default 300)")
        p.add_argument("--fuzz-seed", type=int, help="first fuzz seed (default: random, recorded)")
        p.add_argument("--keep-going", action="store_true",
                       help="measure everything even after a disqualifying failure")
        p.add_argument("--out", help="result file (default bench/results/eval-<label>.json)")

    def margin_opts(p):
        p.add_argument("--margin-rel", type=float, default=MARGIN_REL,
                       help=f"noise margin relative to baseline PAR-2 (default {MARGIN_REL})")
        p.add_argument("--margin-abs", type=float, default=MARGIN_ABS,
                       help=f"minimum noise margin in seconds (default {MARGIN_ABS})")

    p = sub.add_parser("measure", help="build, fuzz and time one solver (e.g. a baseline)")
    source_opts(p)
    p.set_defaults(func=cmd_measure)

    p = sub.add_parser("run", help="measure a candidate and judge it against a baseline")
    source_opts(p)
    p.add_argument("--baseline", required=True, help="result file from `measure`")
    margin_opts(p)
    p.set_defaults(func=cmd_run)

    p = sub.add_parser("check", help="only check the guards (protected files, benchmark names)")
    g = p.add_mutually_exclusive_group()
    g.add_argument("--ref", help="git ref to check (default: the working tree)")
    g.add_argument("--src", help=argparse.SUPPRESS)
    p.add_argument("--label", help=argparse.SUPPRESS)
    p.add_argument("--commit", help=argparse.SUPPRESS)
    p.add_argument("--base-commit", required=True, help="the baseline's commit")
    p.set_defaults(func=cmd_check)

    p = sub.add_parser("verdict", help="judge an existing result file against a baseline")
    p.add_argument("candidate")
    p.add_argument("baseline")
    p.add_argument("--out", help="write the verdict JSON here")
    margin_opts(p)
    p.set_defaults(func=cmd_verdict)

    args = ap.parse_args()
    sys.exit(args.func(args) or 0)


if __name__ == "__main__":
    main()
