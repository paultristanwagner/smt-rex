# The auto-research loop

The protocol for an agent that tries to make SMT-Rex faster, one small change at a time. A
change counts only if `bench/evaluate.py` ACCEPTs it: zero wrong answers, zero fuzz failures,
and a PAR-2 gain on the tuning sets larger than the noise margin.

**The loop produces ideas, not code to merge.** Every attempt lives on a throwaway branch. An
ACCEPT means the idea is worth building properly; the output of a run is the journal, with the
hypotheses ranked by measured gain. Winning ideas are re-implemented by hand, with their own
tests, and measured again.

**Unattended runs need the project owner's explicit approval.** Without it, run at most the
attempts you were asked for, then stop and report.

## Setup (once per session)

```sh
cd bench
export Z3=/path/to/z3 CARGO_BUILD_JOBS=4    # z3 is the fuzz oracle
nice -n 19 python3 evaluate.py measure --ref main --out results/baseline.json
```

If the baseline itself has fuzz failures or wrong answers, stop: that is a solver bug for the
owner. Measure the baseline on the same machine and with the same `--jobs` as the candidates,
again after every accepted change, and at least every ten attempts (machine load drifts).

## One attempt

1. **Pick one hypothesis** from where the time goes (per-family PAR-2, the instances that time
   out, a `perf record` of one slow instance), written as one sentence that predicts an effect:
   "A Luby unit of 256 instead of 100 cuts PAR-2 on the QG-classification families." Read the
   journal first; never retry a rejected hypothesis unchanged.
2. **Make one small change** on a fresh branch off the baseline commit
   (`git switch -c ar/<n>-<slug> <baseline-commit>`), ideally under ~100 lines. Run
   `cargo test` for the crates you touched. Commit.
3. **Evaluate it:**
   ```sh
   nice -n 19 python3 evaluate.py run --ref ar/<n>-<slug> --baseline results/baseline.json
   ```
   Exit status 0 is ACCEPT, 2 is REJECT, anything else is a harness error (fix the
   environment, not the score). The verdict is under `"verdict"` in `results/eval-<sha>.json`.
   `--logics QF_UF` is fine while iterating; a final decision uses all sets.
4. **Record it** in the journal, whatever the verdict.
5. **On ACCEPT**, merge the branch into the loop's integration branch and re-measure the
   baseline there. **On REJECT**, leave the branch as the record and return to the baseline.

A fuzz failure or a wrong answer is a bug, not a slow change: read the saved script
(`results/eval-fuzz-fail-*.smt2`); if the baseline binary fails it too (`fuzz.py` with
`SMTREX=bench/eval/bin/smt-rex-<base>` and the same seed), stop and report it.

## The journal

One JSON object per attempt, on one line, appended to `bench/results/journal.jsonl`
(gitignored):

```json
{"n": 7, "time": "2026-10-07T21:14:00", "branch": "ar/7-luby-256", "commit": "3f1c...",
 "baseline": "1a28ea42be86", "hypothesis": "Luby unit 256 cuts restarts on QG families",
 "diff": "sat/src/restart.rs: LUBY_UNIT 100 -> 256 (1 line)",
 "verdict": "REJECT", "reasons": ["no significant improvement: ..."],
 "par2_base": 3.412, "par2_cand": 3.371, "improvement_pct": 1.2, "margin": 0.102,
 "fuzz_failures": 0, "wrong": 0, "newly_solved": 1, "lost": 0,
 "result": "results/eval-3f1c....json", "note": "QF_UF -0.08s, QF_LRA +0.01s"}
```

The numbers come straight from the `"verdict"` object, unrounded.

## When to stop

- the attempts you were asked for are done (none given: 5);
- five rejections in a row;
- the baseline has a fuzz failure or a wrong answer, or a candidate fails the same way;
- a harness error you cannot attribute to your environment;
- progress would need breaking a rule below.

Report the session's journal lines, the accepted branches, and the final baseline's PAR-2
against the session's first.

## The held-out report (only on request)

The held-out sets show whether accepted changes generalise. They are run once, at the end, when
the owner asks, never to choose between candidates:

```sh
python3 bench.py run smt-rex --logic QF_UF --set heldout --i-mean-heldout --jobs 6 \
  --out results/heldout-<label>.json        # with SMTREX=bench/eval/bin/smt-rex-<sha>
```

for the first and the final baseline, then `bench.py compare` the two and report both numbers
as they are.

## Not allowed

- **Weakening a check**: the model self-check (an unchecked `sat` must stay `unknown`), the
  fuzzer, the wrong-answer disqualification, the guards in `evaluate.py`.
- **Special-casing benchmarks**: file names, family names, hashes, sizes or `set-info` fields
  used to pick behaviour. `evaluate.py` rejects a diff that mentions a benchmark file name; the
  rule is wider than the check.
- **Touching the harness**: anything under `bench/`. `evaluate.py` rejects such
  candidates; harness changes are separate, owner-reviewed work.
- **Running the held-out sets** inside the loop.
- **Running unattended** without approval. Keep the machine usable: `nice -n 19`,
  `CARGO_BUILD_JOBS=4`, at most 6 jobs locally.
- Force-pushing, rewriting the baseline branch, deleting rejected branches.

## The noise margin

A candidate must beat the baseline's pooled PAR-2 by more than `max(3%, 0.05 s)`
(`--margin-rel`, `--margin-abs`), and no logic may get worse by more than its own margin.

On the 16-core desktop at 6 jobs, three runs of the same solver (QF_UF and QF_LRA tuning, 517
instances, PAR-2 about 5.5 s) differed pairwise by 0.6-1.5% pooled. QF_LRA moved by under
0.6%, QF_UF by up to 3%, almost all of it from families near the time limit, where one instance
crossing the limit moves PAR-2 by 0.1 s. A 3% margin is about twice the pooled noise; it
rejected a no-op change and a change adding 0.25 s of CPU to every run. Re-measure the baseline
before close decisions, and use `--repeats 3` when a gain is under about 5%. A dedicated
RunPod pod is quieter than the shared desktop.
