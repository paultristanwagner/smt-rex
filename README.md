# SMT-Rex

An SMT solver written in Rust. It decides equality with uninterpreted functions (QF_UF), linear
real and integer arithmetic (QF_LRA, QF_LIA, with `maximize`/`minimize`), non-linear real
arithmetic (QF_NRA) and bit-vectors (QF_BV), reads SMT-LIB 2.6 and DIMACS, and writes proofs of
unsatisfiability.

It started as the Java solver for the RWTH lecture
[Satisfiability Checking](https://ths.rwth-aachen.de/teaching/winter-term-2021-2022/lecture-satisfiability-checking/) by Erika Ábrahám and was
rewritten from scratch.

## Results

Every non-incremental benchmark of the SMT-LIB 2025 release, 10 s CPU per benchmark, number
solved. No solver gave a wrong answer and no two solvers disagreed.

| logic | benchmarks | SMT-Rex | z3 4.16 | cvc5 1.3.4 |
|---|---:|---:|---:|---:|
| QF_UF | 7503 | 7376 | 7488 | 7474 |
| QF_LRA | 1753 | 1132 | 1305 | 1221 |
| QF_LIA | 13306 | 8284 | 11579 | 9045 |
| QF_NRA | 12154 | 9953 | 10525 | 10710 |

Reproduce one logic on a RunPod CPU pod with `python3 bench/runpod/pod.py full QF_UF`.

## Use

```sh
nix run . -- problem.smt2                  # or: cargo build --release
smt-rex problem.smt2                       # SMT-LIB script, SMT-LIB responses
smt-rex problem.cnf                        # DIMACS; exit code 10 sat, 20 unsat
smt-rex --timeout 10 problem.smt2
smt-rex --proof proof.alethe problem.smt2
smt-rex                                    # interactive prompt
```

```text
$ smt-rex circle.smt2
sat
(
(define-fun x () Real (root-obj (+ (* 4 (^ x 6)) (* (- 8) (^ x 4)) (* 8 (^ x 2)) (- 3)) 1))
(define-fun y () Real (root-obj (+ (* 2 (^ x 3)) (* (- 2) (^ x 2)) 1) 1))
)
```

The prompt takes SMT-LIB commands and a short formula syntax:

```text
smt-rex> sat (a | b) & (~a | c) & ~c
sat  (20 µs)
  a=0  b=1  c=0
smt-rex> smt QF_LRA (x < 3) & (max(x))
sat  (24 µs)
  max x: no maximum (supremum 3, never reached)
  x=2
smt-rex> smt QF_NRA (x^2 = 2) & (x > 0)
sat  (382 µs)
  x≈1.414214 (root 2 of x^2 - 2)
```

## Why trust an answer

- **sat**: the input is evaluated under the model by an evaluator that shares no code with the
  encoder. If that fails, the answer is `unknown`.
- **unsat**: `--proof` writes LRAT for DIMACS (check with `lrat-check` from drat-trim) and Alethe
  for QF_UF and QF_LRA (check with [Carcara](https://github.com/ufmg-smite/carcara)
  `--expand-let-bindings --apply-function-defs --allow-int-real-subtyping`). Theory lemmas are
  re-derived for the proof, not copied from the solver.
- **Testing**: CI fuzzes all five logics and optimisation against z3 and checks proofs of random
  scripts with Carcara.

## Inside

DPLL(T) with a CDCL SAT core (watched literals, VSIDS, LBD clause deletion, LRAT logging),
congruence closure for EUF, an incremental Simplex with branch and bound for integers,
bit-blasting for bit-vectors, and cylindrical algebraic coverings over exact real algebraic
numbers for QF_NRA.

| crate | |
|---|---|
| `core` | literals, the `Theory` trait, rationals |
| `sat` | CDCL and LRAT proofs |
| `term` | hash-consed terms |
| `theory` | EUF and LRA/LIA |
| `poly` | polynomials, factorisation, real roots, real algebraic numbers |
| `nra` | coverings for QF_NRA |
| `smt` | SMT-LIB, encoding, models, Alethe proofs |
| `cli` | the `smt-rex` binary |
| `bench` | benchmark harness, fuzzer, proof checking, RunPod runner |

Development: `cargo test --release --all`, `python3 bench/fuzz.py --logic QF_NRA`,
[bench/README.md](bench/README.md).

## Design

1. **Every optimisation has one place.** Preprocessing is a sequence of separate passes;
   heuristics sit behind small interfaces; data-layout work stays inside its module.
2. **Every optimisation is measured and can be switched off.** It goes in only if it improves
   the tuning sets beyond the noise margin with no wrong answers.
3. **Correctness never depends on cleverness.** Every `sat` is self-checked; every `unsat` can
   carry a proof.

## License

Licensed under either of [Apache License, Version 2.0](LICENSE-APACHE) or
[MIT license](LICENSE-MIT) at your option. Unless you explicitly state otherwise, any
contribution intentionally submitted for inclusion in SMT-Rex, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or conditions.
