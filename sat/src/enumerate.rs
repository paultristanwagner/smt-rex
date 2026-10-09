//! Brute-force SAT oracle for differential tests: tries every assignment (`num_vars` ≤ 24).

use crate::dimacs::Cnf;

/// Returns `Some(model)` (indexed by variable) if satisfiable, else `None`. Panics if the
/// instance is too large to enumerate.
pub fn solve(cnf: &Cnf) -> Option<Vec<bool>> {
    let n = cnf.num_vars;
    assert!(
        n <= 24,
        "enumerate::solve is only for small instances (n={n})"
    );
    for bits in 0u64..(1u64 << n) {
        let model: Vec<bool> = (0..n).map(|v| (bits >> v) & 1 == 1).collect();
        if model_satisfies(cnf, &model) {
            return Some(model);
        }
    }
    None
}

/// Check whether `model` (indexed by variable) satisfies every clause.
pub fn model_satisfies(cnf: &Cnf, model: &[bool]) -> bool {
    cnf.clauses.iter().all(|clause| {
        clause
            .iter()
            .any(|l| model[l.var().index()] != l.is_negated())
    })
}
