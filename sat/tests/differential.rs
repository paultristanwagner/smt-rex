//! The CDCL solver agrees with the brute-force enumerator on random small CNFs, and every model
//! it returns satisfies the formula.

use smtrex_core::{Lit, Var};
use smtrex_sat::{dimacs::Cnf, enumerate, SolveResult, Solver};

fn xorshift(s: &mut u64) -> u64 {
    let mut x = *s;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    *s = x;
    x
}

#[test]
fn cdcl_agrees_with_enumeration_oracle() {
    let mut seed = 0x9e3779b97f4a7c15u64;
    let trials = 20_000;
    let (mut sat, mut unsat) = (0u32, 0u32);

    for _ in 0..trials {
        let nv = 3 + (xorshift(&mut seed) % 6) as usize; // 3..=8 vars
        let nc = 1 + (xorshift(&mut seed) % 12) as usize; // 1..=12 clauses
        let mut clauses = Vec::with_capacity(nc);
        for _ in 0..nc {
            let w = 1 + (xorshift(&mut seed) % 3) as usize; // width 1..=3
            let mut cl = Vec::with_capacity(w);
            for _ in 0..w {
                let v = (xorshift(&mut seed) % nv as u64) as usize;
                let neg = xorshift(&mut seed) & 1 == 1;
                cl.push(Lit::new(Var::from_index(v), neg));
            }
            clauses.push(cl);
        }
        let cnf = Cnf {
            num_vars: nv,
            clauses,
        };

        let oracle = enumerate::solve(&cnf);
        let mut s = Solver::new();
        s.ensure_vars(nv);
        for c in &cnf.clauses {
            s.add_clause(c);
        }
        let result = s.solve();

        match (&oracle, &result) {
            (Some(_), SolveResult::Sat(model)) => {
                assert!(
                    enumerate::model_satisfies(&cnf, model),
                    "CDCL returned a model that does not satisfy the CNF: {cnf:?} model={model:?}"
                );
                sat += 1;
            }
            (None, SolveResult::Unsat) => unsat += 1,
            (o, r) => panic!(
                "verdict mismatch: oracle_sat={} cdcl={r:?}\ncnf={cnf:?}",
                o.is_some()
            ),
        }
    }
    assert!(sat > 0 && unsat > 0, "expected a mix of SAT and UNSAT");
}
