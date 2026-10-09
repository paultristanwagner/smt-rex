use super::Formula;

/// A literal of a CNF: a variable name and its polarity.
pub type Literal = (String, bool);

/// Tseitin's transformation of a propositional formula: an equisatisfiable CNF whose helper
/// variables `h0, h1, ...` are named so they never collide with the formula's own variables.
/// Literals and negated literals get no helper; `and`/`or` are encoded n-ary.
pub fn tseitin(f: &Formula) -> Vec<Vec<Literal>> {
    struct T {
        clauses: Vec<Vec<Literal>>,
        used: Vec<String>,
        next: usize,
    }
    impl T {
        fn fresh(&mut self) -> String {
            loop {
                let name = format!("h{}", self.next);
                self.next += 1;
                if !self.used.contains(&name) {
                    return name;
                }
            }
        }
        /// A literal equivalent to `f`, adding the defining clauses.
        fn lit(&mut self, f: &Formula) -> Literal {
            match f {
                Formula::Var(v) => (v.clone(), true),
                Formula::Not(a) => {
                    let (v, pol) = self.lit(a);
                    (v, !pol)
                }
                Formula::Const(b) => {
                    // A helper forced to the constant's value.
                    let h = self.fresh();
                    self.clauses.push(vec![(h.clone(), *b)]);
                    (h, true)
                }
                Formula::And(xs) => {
                    let lits: Vec<Literal> = xs.iter().map(|x| self.lit(x)).collect();
                    let h = self.fresh();
                    // h -> each x;  all x -> h
                    for l in &lits {
                        self.clauses.push(vec![(h.clone(), false), l.clone()]);
                    }
                    let mut big: Vec<Literal> = lits.iter().map(|(v, p)| (v.clone(), !p)).collect();
                    big.push((h.clone(), true));
                    self.clauses.push(big);
                    (h, true)
                }
                Formula::Or(xs) => {
                    let lits: Vec<Literal> = xs.iter().map(|x| self.lit(x)).collect();
                    let h = self.fresh();
                    // each x -> h;  h -> some x
                    for (v, p) in &lits {
                        self.clauses.push(vec![(v.clone(), !p), (h.clone(), true)]);
                    }
                    let mut big = lits.clone();
                    big.insert(0, (h.clone(), false));
                    self.clauses.push(big);
                    (h, true)
                }
                Formula::Implies(a, b) => {
                    let (av, ap) = self.lit(a);
                    let bl = self.lit(b);
                    let h = self.fresh();
                    self.clauses
                        .push(vec![(h.clone(), false), (av.clone(), !ap), bl.clone()]);
                    self.clauses.push(vec![(av, ap), (h.clone(), true)]);
                    self.clauses.push(vec![(bl.0, !bl.1), (h.clone(), true)]);
                    (h, true)
                }
                Formula::Iff(a, b) => {
                    let (av, ap) = self.lit(a);
                    let (bv, bp) = self.lit(b);
                    let h = self.fresh();
                    let hn = (h.clone(), false);
                    let hp = (h.clone(), true);
                    self.clauses
                        .push(vec![hn.clone(), (av.clone(), !ap), (bv.clone(), bp)]);
                    self.clauses
                        .push(vec![hn, (bv.clone(), !bp), (av.clone(), ap)]);
                    self.clauses
                        .push(vec![(av.clone(), ap), (bv.clone(), bp), hp.clone()]);
                    self.clauses.push(vec![(av, !ap), (bv, !bp), hp]);
                    (h, true)
                }
                Formula::Eq { .. } | Formula::Cmp { .. } | Formula::Objective { .. } => {
                    unreachable!("tseitin is only for propositional formulas")
                }
            }
        }
    }
    let mut t = T {
        clauses: Vec::new(),
        used: f.vars(),
        next: 0,
    };
    let root = t.lit(f);
    t.clauses.push(vec![root]);
    t.clauses
}

/// A CNF in the short syntax: `(a | ~b) & (c)`.
pub fn show_cnf(clauses: &[Vec<Literal>]) -> String {
    clauses
        .iter()
        .map(|c| {
            let lits: Vec<String> = c
                .iter()
                .map(|(v, p)| if *p { v.clone() } else { format!("~{v}") })
                .collect();
            format!("({})", lits.join(" | "))
        })
        .collect::<Vec<_>>()
        .join(" & ")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::{parse, Atoms};

    fn p(s: &str) -> Formula {
        parse(s, Atoms::Prop).unwrap()
    }

    #[test]
    fn tseitin_helpers_avoid_user_names() {
        let cnf = tseitin(&p("(h0 & h1) | h2"));
        let names: Vec<&str> = cnf.iter().flatten().map(|(v, _)| v.as_str()).collect();
        assert!(names.contains(&"h3"), "{}", show_cnf(&cnf));
        // h0..h2 only ever appear as the user's own variables (never defined as helpers).
        assert!(!cnf.iter().any(|c| c.len() == 1 && c[0].0 == "h0"));
    }

    /// Tseitin is equisatisfiable, and every model of the CNF restricted to the original
    /// variables is a model of the formula (checked by brute force on random formulas).
    #[test]
    fn tseitin_is_equisatisfiable() {
        fn eval(f: &Formula, a: &dyn Fn(&str) -> bool) -> bool {
            match f {
                Formula::Const(b) => *b,
                Formula::Var(v) => a(v),
                Formula::Not(x) => !eval(x, a),
                Formula::And(xs) => xs.iter().all(|x| eval(x, a)),
                Formula::Or(xs) => xs.iter().any(|x| eval(x, a)),
                Formula::Implies(x, y) => !eval(x, a) || eval(y, a),
                Formula::Iff(x, y) => eval(x, a) == eval(y, a),
                Formula::Eq { .. } | Formula::Cmp { .. } | Formula::Objective { .. } => {
                    unreachable!()
                }
            }
        }
        let mut seed = 0x9E3779B97F4A7C15u64;
        let mut rnd = |n: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % n
        };
        fn gen(d: u32, rnd: &mut dyn FnMut(u64) -> u64) -> Formula {
            if d == 0 || rnd(4) == 0 {
                return match rnd(7) {
                    0 => Formula::Const(rnd(2) == 0),
                    k => Formula::Var(["a", "b", "c", "h0"][(k % 4) as usize].into()),
                };
            }
            match rnd(5) {
                0 => Formula::Not(Box::new(gen(d - 1, rnd))),
                1 => Formula::And(vec![gen(d - 1, rnd), gen(d - 1, rnd), gen(d - 1, rnd)]),
                2 => Formula::Or(vec![gen(d - 1, rnd), gen(d - 1, rnd)]),
                3 => Formula::Implies(Box::new(gen(d - 1, rnd)), Box::new(gen(d - 1, rnd))),
                _ => Formula::Iff(Box::new(gen(d - 1, rnd)), Box::new(gen(d - 1, rnd))),
            }
        }
        let mut tested = 0;
        for _ in 0..2000 {
            let f = gen(4, &mut rnd);
            let cnf = tseitin(&f);
            let mut vars: Vec<String> = cnf.iter().flatten().map(|(v, _)| v.clone()).collect();
            vars.sort();
            vars.dedup();
            if vars.len() > 16 {
                continue; // too many to brute-force quickly
            }
            tested += 1;
            let orig = f.vars();
            let mut f_sat = false;
            let mut cnf_sat = false;
            for bits in 0u32..(1 << vars.len()) {
                let val = |v: &str| bits >> vars.iter().position(|x| x == v).unwrap() & 1 == 1;
                if cnf.iter().all(|c| c.iter().any(|(v, p)| val(v) == *p)) {
                    cnf_sat = true;
                    assert!(eval(&f, &val), "CNF model is not a model of {f:?}");
                }
            }
            for bits in 0u32..(1 << orig.len()) {
                let val = |v: &str| bits >> orig.iter().position(|x| x == v).unwrap() & 1 == 1;
                f_sat |= eval(&f, &val);
            }
            assert_eq!(f_sat, cnf_sat, "{f:?}");
        }
        assert!(
            tested >= 500,
            "only {tested} formulas were small enough to check"
        );
    }
}
