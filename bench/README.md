# SMT-Rex benchmarks

Fixed benchmark sets with checked answers and PAR-2 scores, a differential fuzzer, a proof
checker driver, and the evaluator that accepts or rejects a solver change. Python 3 standard
library only; `zstd` unpacks the archives. Run from the repository root after `cargo build --release`.

```sh
python3 bench/bench.py fetch QF_UF                    # SMT-LIB 2025 archive, checksum-verified
python3 bench/bench.py run smt-rex --logic QF_UF      # the tuning set
python3 bench/bench.py run z3 --logic QF_UF
python3 bench/bench.py compare bench/results/A.json bench/results/B.json
python3 bench/fuzz.py --logic QF_LRA --count 2000     # random scripts vs z3
python3 bench/proofcheck.py random --logic QF_LRA     # Alethe proofs vs Carcara
```

## Sets

`sets/<LOGIC>.json` lists a tuning and a held-out set drawn from the SMT-LIB 2025
non-incremental release (Zenodo record 15493090, CC BY 4.0) with seed 2026: up to N instances
per family per set, from every family. Every expected verdict is the file's `:status`,
confirmed by z3 4.16 (and cvc5 1.3 where z3 cannot decide); instances where they disagree or
neither decides are dropped.

| set | tuning | held-out | per family | notes |
|---|---|---|---|---|
| QF_UF | 219 | 218 | 20 | `QG-classification` split into its sub-populations |
| QF_LRA | 298 | 298 | 10 | |
| QF_LIA | 2287 | 2274 | 10 | |
| QF_NRA | 309 | 302 | 10 | labelled files only; z3 and cvc5 both confirm every verdict |

`bench.py make-sets LOGIC` redraws a set (`--per-family`, `--labelled-only`,
`--both-oracles`). The benchmark files live in `bench/data/` and are not committed.

**Tuning** is for development. **Held-out** is for final reports only, so that improvements
are not tuned to the instances they are measured on; `run` refuses it without
`--i-mean-heldout`.

## Scoring

Each instance runs under a CPU-time limit T (default 10 s) and an address-space limit
(`BENCH_MEM_GB`, default 6, 0 for none). A solved instance scores its CPU time; a timeout,
memory-out, crash, error or `unknown` scores 2T. PAR-2 is the mean; lower is better. A wrong
answer disqualifies the run: `run` prints the instance and exits with status 1.

At 8 parallel jobs on 16 cores, single instances vary by 10-20% between runs and a set's total
CPU time by about 5%. For small differences, use `--jobs 1` or repeat the runs.

## Solvers

`run` knows `smt-rex` (env `SMTREX`, default `target/release/smt-rex`), `z3` (env `Z3`)
and `cvc5` (env `CVC5`); anything else with `--cmd "solver --flags" --name label`.

## Fuzzing

`fuzz.py` generates random scripts in QF_UF, QF_LRA, QF_LIA, QF_BV or QF_NRA (`--logic`) with
`let`, `define-fun`, `:named`, push/pop and `check-sat-assuming`, and compares every verdict
with z3 (`--reference cvc5` also works). `--opt` adds a `maximize`/`minimize` and compares the
optima (QF_LRA, QF_LIA). Any disagreement, `unknown` or error is a failure and is saved to
`results/fuzz-fail-<seed>.smt2`; `--seed N --count 1` replays it.

## Proofs

`proofcheck.py` runs `smt-rex --proof` on random QF_UF or QF_LRA scripts (`random`) or on given
files (`files`) and checks every unsat proof with
`carcara check --expand-let-bindings --apply-function-defs --allow-int-real-subtyping`
(env `CARCARA`). An invalid proof or a solver error exits with status 1; scripts outside the
supported fragment are counted.

## Accepting a change: `evaluate.py`

```sh
cd bench
export Z3=/path/to/z3
python3 evaluate.py measure --ref main --out results/baseline.json
python3 evaluate.py run --ref my-branch --baseline results/baseline.json   # or the working tree
python3 evaluate.py verdict results/eval-X.json results/baseline.json      # re-judge only
```

It builds each solver into its own `bench/eval/target/<name>`, fuzzes every logic
(`--fuzz-count`, default 300), runs the tuning sets `--repeats` times (default 2, median per
instance), and ACCEPTs (exit 0) only with no change under `bench/`, no benchmark name in
the diff, zero fuzz failures, zero wrong answers, and a PAR-2 gain above `max(3%, 0.05 s)`
with no logic slower than its own margin; otherwise it REJECTs (exit 2). It never runs the
held-out sets. [`loop.md`](loop.md) is the protocol for running it in a loop.

## RunPod

`runpod/pod.py` runs the same evaluation on a RunPod CPU pod, baseline and candidate on the
same machine: `pod.py create`, `pod.py evaluate POD --base REF --cand REF`, then always
`pod.py delete POD`, since pods bill until deleted. `runpod/setup.sh` installs the pinned
toolchain and oracles (`runpod/store-paths.txt`) from the Nix binary cache. Every subcommand
takes `--dry-run`.
