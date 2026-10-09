//! Every `unsat` answer comes with an LRAT proof; check those proofs with a small independent
//! checker (reverse unit propagation along the hints, nothing else).

use smtrex_core::Lit;
use smtrex_sat::proof::{ClauseId, Step};
use smtrex_sat::{SolveResult, Solver};
use std::collections::HashMap;

fn xorshift(s: &mut u64) -> u64 {
    *s ^= *s << 13;
    *s ^= *s >> 7;
    *s ^= *s << 17;
    *s
}

/// Check every derived step of `steps` against the clauses before it. Returns whether the
/// empty clause was derived.
fn check_lrat(steps: &[Step]) -> Result<bool, String> {
    let mut db: HashMap<ClauseId, Vec<Lit>> = HashMap::new();
    let mut refuted = false;
    for s in steps {
        match s {
            Step::Input { id, lits } => {
                db.insert(*id, lits.clone());
            }
            Step::Derived { id, lits, hints } => {
                // Assume every literal of the clause false.
                let mut val: HashMap<u32, bool> = HashMap::new();
                let assign = |val: &mut HashMap<u32, bool>, l: Lit| {
                    val.insert(l.var().index() as u32, !l.is_negated());
                };
                let value = |val: &HashMap<u32, bool>, l: Lit| {
                    val.get(&(l.var().index() as u32))
                        .map(|&b| b != l.is_negated())
                };
                for &l in lits {
                    assign(&mut val, !l);
                }
                let mut conflict = false;
                for h in hints {
                    let c = db.get(h).ok_or(format!("step {id}: unknown hint {h}"))?;
                    if c.iter().any(|&l| value(&val, l) == Some(true)) {
                        return Err(format!("step {id}: hint {h} is satisfied"));
                    }
                    let open: Vec<Lit> = c
                        .iter()
                        .copied()
                        .filter(|&l| value(&val, l).is_none())
                        .collect();
                    match open.len() {
                        0 => {
                            conflict = true;
                            break;
                        }
                        1 => assign(&mut val, open[0]),
                        _ => return Err(format!("step {id}: hint {h} is not unit")),
                    }
                }
                if !conflict {
                    return Err(format!("step {id}: hints end without a conflict"));
                }
                if lits.is_empty() {
                    refuted = true;
                }
                db.insert(*id, lits.clone());
            }
            Step::Theory { id, .. } => return Err(format!("step {id}: theory lemma in pure SAT")),
            Step::Delete { id } => {
                db.remove(id)
                    .ok_or(format!("deleting unknown clause {id}"))?;
            }
        }
    }
    Ok(refuted)
}

#[test]
fn unsat_answers_carry_valid_lrat_proofs() {
    let mut seed = 0x5eed_1234_u64;
    let (mut unsat, mut sat) = (0, 0);
    for case in 0..3000 {
        let n = 4 + (xorshift(&mut seed) % 40) as usize;
        let m = (n as f64 * (3.0 + (xorshift(&mut seed) % 250) as f64 / 100.0)) as usize;
        let mut s = Solver::new();
        s.enable_proof();
        s.ensure_vars(n);
        for _ in 0..m {
            // mostly 3-clauses, some 2-clauses and units
            let k = match xorshift(&mut seed) % 20 {
                0 => 1,
                1..=4 => 2,
                _ => 3,
            };
            let c: Vec<Lit> = (0..k)
                .map(|_| {
                    let v = 1 + (xorshift(&mut seed) % n as u64) as i32;
                    Lit::from_dimacs(if xorshift(&mut seed).is_multiple_of(2) {
                        v
                    } else {
                        -v
                    })
                })
                .collect();
            s.add_clause(&c);
        }
        match s.solve() {
            SolveResult::Unsat => {
                let proof = s.take_proof().unwrap();
                match check_lrat(&proof.steps) {
                    Ok(true) => unsat += 1,
                    Ok(false) => panic!("case {case}: unsat without the empty clause"),
                    Err(e) => panic!("case {case}: {e}"),
                }
            }
            SolveResult::Sat(_) => sat += 1,
            SolveResult::Interrupted => unreachable!(),
        }
    }
    assert!(unsat > 500 && sat > 300, "{unsat} unsat, {sat} sat");
}
