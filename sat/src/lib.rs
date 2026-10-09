//! CDCL SAT solver.
//!
//! - [`cdcl::Solver`]: the CDCL solver, optionally driving a theory (DPLL(T)).
//! - [`dimacs`]: DIMACS CNF reader.
//! - [`enumerate`]: brute-force oracle for differential testing.
//! - [`proof`]: LRAT-style proof log.

pub mod cdcl;
pub mod dimacs;
pub mod enumerate;
mod heap;
pub mod proof;

pub use cdcl::{SolveResult, Solver};
pub use dimacs::Cnf;

/// Solve a parsed CNF with a fresh solver.
pub fn solve_cnf(cnf: &Cnf) -> SolveResult {
    let mut s = Solver::new();
    s.ensure_vars(cnf.num_vars);
    for clause in &cnf.clauses {
        s.add_clause(clause);
    }
    s.solve()
}

#[cfg(test)]
mod tests {
    use super::*;
    use smtrex_core::Lit;

    fn lits(ds: &[i32]) -> Vec<Lit> {
        ds.iter().map(|&d| Lit::from_dimacs(d)).collect()
    }

    #[test]
    fn trivial_sat() {
        let mut s = Solver::new();
        s.ensure_vars(2);
        assert!(s.add_clause(&lits(&[1, 2])));
        assert!(s.add_clause(&lits(&[-1, 2])));
        match s.solve() {
            SolveResult::Sat(m) => assert!(m[1]),
            other => panic!("should be SAT, got {other:?}"),
        }
    }

    #[test]
    fn trivial_unsat() {
        let mut s = Solver::new();
        s.ensure_vars(1);
        s.add_clause(&lits(&[1]));
        s.add_clause(&lits(&[-1]));
        assert_eq!(s.solve(), SolveResult::Unsat);
    }

    #[test]
    fn implication_chain_sat() {
        // (a) & (~a|b) & (~b|c) & (~c|d) -> SAT with all true
        let cnf = dimacs::parse("p cnf 4 4\n1 0\n-1 2 0\n-2 3 0\n-3 4 0\n").unwrap();
        match solve_cnf(&cnf) {
            SolveResult::Sat(m) => assert_eq!(m, vec![true, true, true, true]),
            other => panic!("should be SAT, got {other:?}"),
        }
    }

    #[test]
    fn stop_flag_interrupts() {
        let cnf = dimacs::parse("p cnf 2 1\n1 2 0\n").unwrap();
        let mut s = Solver::new();
        s.ensure_vars(cnf.num_vars);
        for c in &cnf.clauses {
            s.add_clause(c);
        }
        let flag = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(true));
        s.set_stop_flag(flag.clone());
        assert_eq!(s.solve(), SolveResult::Interrupted);
        // Lowering the flag lets the same solver finish.
        flag.store(false, std::sync::atomic::Ordering::Relaxed);
        assert!(matches!(s.solve(), SolveResult::Sat(_)));
    }

    #[test]
    fn pigeonhole_2_into_1_unsat() {
        // x1, x2: pigeon 1, 2 sits in the hole; (x1) & (x2) & (~x1 | ~x2)
        let cnf = dimacs::parse("p cnf 2 3\n1 0\n2 0\n-1 -2 0\n").unwrap();
        assert_eq!(solve_cnf(&cnf), SolveResult::Unsat);
    }
}
