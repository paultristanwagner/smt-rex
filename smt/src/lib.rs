//! The SMT layer: wires the CDCL solver to the theories (DPLL(T)) and owns the atom↔variable map.
//!
//! [`SmtBuilder`] lets a front-end build terms, mint theory atoms (each a SAT variable), add
//! clauses over them (the boolean abstraction), and solve. Three theories run side by side behind
//! [`Combined`]: EUF for equalities and uninterpreted functions, LRA for linear arithmetic, NRA
//! for polynomial arithmetic (QF_NRA). Each atom belongs to exactly one of them; they share no
//! terms (no Nelson–Oppen yet), which is complete for the single-theory logics the front-end
//! accepts.

pub mod alethe;
pub mod arith;
pub mod bv;
mod encode;
pub mod model;
pub mod nlarith;
pub mod script;
pub mod sexp;

use rustc_hash::FxHashMap;
use smtrex_core::{Lit, Rational, Theory, Var};
use smtrex_nra::{AtomKind, Nra};
use smtrex_poly::stats as st;
use smtrex_poly::MPoly;
use smtrex_sat::{SolveResult, Solver};
use smtrex_term::TermId;
use smtrex_theory::lra::{AVar, BoundKind};
use smtrex_theory::{Euf, Lra};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

/// EUF, LRA and NRA side by side; every call is routed by which theory owns the atom.
pub struct Combined {
    pub euf: Euf,
    pub lra: Lra,
    pub nra: Nra,
}

impl Default for Combined {
    fn default() -> Self {
        Combined {
            euf: Euf::default(),
            lra: Lra::default(),
            nra: Nra::new(),
        }
    }
}

impl Theory for Combined {
    fn assert(&mut self, lit: Lit) {
        if self.lra.owns(lit.var()) {
            self.lra.assert(lit);
        } else if self.nra.owns(lit.var()) {
            self.nra.assert(lit);
        } else {
            self.euf.assert(lit);
        }
    }

    fn check(&mut self, complete: bool) -> Result<(), Vec<Lit>> {
        self.euf.check(complete)?;
        {
            let _o = st::outer(st::Outer::Lra);
            self.lra.check(complete)?;
        }
        self.nra.check(complete)
    }

    fn propagate(&mut self) -> Vec<Lit> {
        let mut out = self.euf.propagate();
        let _o = st::outer(st::Outer::Lra);
        out.extend(self.lra.propagate());
        out
    }

    fn explain(&mut self, lit: Lit) -> Vec<Lit> {
        if self.lra.owns(lit.var()) {
            self.lra.explain(lit)
        } else {
            self.euf.explain(lit)
        }
    }

    fn push(&mut self) {
        self.euf.push();
        self.lra.push();
        self.nra.push();
    }

    fn pop(&mut self, levels: usize) {
        self.euf.pop(levels);
        self.lra.pop(levels);
        self.nra.pop(levels);
    }

    fn lemmas(&mut self) -> Vec<Vec<Lit>> {
        let mut out = self.lra.lemmas();
        out.extend(self.euf.lemmas());
        out.extend(self.nra.lemmas());
        out
    }
}

pub struct SmtBuilder {
    solver: Solver<Combined>,
    /// Equality atom `(a,b)` (order-normalized) -> its SAT variable.
    eq_vars: FxHashMap<(TermId, TermId), Var>,
    /// Bound atom `(var, kind, constant)` -> its SAT variable.
    bound_vars: FxHashMap<(AVar, BoundKind, Rational), Var>,
    /// Polynomial atom `(poly, kind)` -> its SAT variable.
    poly_vars: FxHashMap<(MPoly, AtomKind), Var>,
    next_var: usize,
    clauses: Vec<Vec<Lit>>,
    /// How many of `clauses` the solver has already received.
    added: usize,
    /// The assignment of the last satisfiable solve, indexed by variable.
    model: Vec<bool>,
}

impl Default for SmtBuilder {
    fn default() -> Self {
        SmtBuilder::new()
    }
}

impl SmtBuilder {
    pub fn new() -> SmtBuilder {
        SmtBuilder {
            solver: Solver::with_theory(Combined::default()),
            eq_vars: FxHashMap::default(),
            bound_vars: FxHashMap::default(),
            poly_vars: FxHashMap::default(),
            next_var: 0,
            clauses: Vec::new(),
            added: 0,
            model: Vec::new(),
        }
    }

    /// Access the EUF theory to build terms (`mk_const` / `mk_app`).
    pub fn euf(&mut self) -> &mut Euf {
        &mut self.solver.theory_mut().euf
    }

    /// Read-only access to the EUF theory, e.g. to read the congruence classes after a SAT solve.
    pub fn euf_ref(&self) -> &Euf {
        &self.solver.theory().euf
    }

    /// Access the arithmetic theory to create variables and terms.
    pub fn lra(&mut self) -> &mut Lra {
        &mut self.solver.theory_mut().lra
    }

    /// Read-only access to the arithmetic theory, e.g. for its model after a SAT solve.
    pub fn lra_ref(&self) -> &Lra {
        &self.solver.theory().lra
    }

    /// Access the nonlinear arithmetic theory to create variables.
    pub fn nra(&mut self) -> &mut Nra {
        &mut self.solver.theory_mut().nra
    }

    /// Read-only access to the nonlinear arithmetic theory, e.g. for its model after a SAT solve.
    pub fn nra_ref(&self) -> &Nra {
        &self.solver.theory().nra
    }

    /// The positive literal of the polynomial atom `p ⋈ 0` (deduplicated; `p` should be
    /// normalised, see [`nlarith::normalize`]).
    pub fn poly_atom(&mut self, p: MPoly, kind: AtomKind) -> Lit {
        let key = (p, kind);
        if let Some(&v) = self.poly_vars.get(&key) {
            return v.pos();
        }
        let v = self.fresh_var();
        self.solver
            .theory_mut()
            .nra
            .register_atom(v, key.0.clone(), kind);
        self.poly_vars.insert(key, v);
        v.pos()
    }

    /// The positive literal of the bound atom `x ⋈ c` (deduplicated).
    pub fn bound_atom(&mut self, x: AVar, kind: BoundKind, c: Rational) -> Lit {
        let key = (x, kind, c);
        if let Some(&v) = self.bound_vars.get(&key) {
            return v.pos();
        }
        let v = self.fresh_var();
        self.solver
            .theory_mut()
            .lra
            .register_atom(v, x, kind, key.2.clone());
        self.bound_vars.insert(key, v);
        v.pos()
    }

    /// A fresh propositional variable (for Tseitin auxiliaries and `Bool`-sorted symbols).
    pub fn fresh_var(&mut self) -> Var {
        // Both theories allocate SAT variables for atoms they create during search (branch and
        // bound, transitivity lemmas), so fresh variables come after all of them.
        let theory = self.solver.theory();
        let i = self
            .next_var
            .max(theory.lra.next_free_sat_var())
            .max(theory.euf.next_free_sat_var());
        self.next_var = i + 1;
        Var::from_index(i)
    }

    /// The positive literal of the equality atom `a = b` (deduplicated, order-insensitive).
    pub fn eq_atom(&mut self, a: TermId, b: TermId) -> Lit {
        let key = if a <= b { (a, b) } else { (b, a) };
        if let Some(&v) = self.eq_vars.get(&key) {
            return v.pos();
        }
        let v = self.fresh_var();
        self.eq_vars.insert(key, v);
        self.solver
            .theory_mut()
            .euf
            .register_eq_atom(v, key.0, key.1);
        v.pos()
    }

    /// Log a proof of `unsat` (see [`smtrex_sat::proof`]). Call before adding clauses.
    pub fn enable_proof(&mut self) {
        self.solver.enable_proof();
    }

    pub fn take_proof(&mut self) -> Option<smtrex_sat::proof::Proof> {
        self.solver.take_proof()
    }

    /// Add a clause to the boolean abstraction.
    pub fn add_clause(&mut self, lits: Vec<Lit>) {
        self.clauses.push(lits);
    }

    /// The value of `lit` in the assignment of the last satisfiable [`Self::solve`].
    pub fn lit_value(&self, lit: Lit) -> bool {
        let v = self.model.get(lit.var().index()).copied().unwrap_or(false);
        v != lit.is_negated()
    }

    /// Stop `solve` early (it returns `None`) once `flag` is raised.
    pub fn set_stop_flag(&mut self, flag: Arc<AtomicBool>) {
        self.solver.set_stop_flag(flag);
    }

    /// Solve. `Some(true)` for SAT, `Some(false)` for UNSAT, `None` if interrupted. Can be
    /// called again after adding clauses (e.g. to look for a better optimum); learnt clauses
    /// are kept.
    pub fn solve(&mut self) -> Option<bool> {
        self.solver.backtrack_to_root();
        self.solver.ensure_vars(self.next_var);
        self.solver.theory_mut().lra.set_sat_var_base(self.next_var);
        // Without arithmetic, EUF owns every variable past the encoding and may mint atoms for
        // transitivity lemmas (LRA mints its own variables, so the two must not both do it).
        let theory = self.solver.theory_mut();
        if theory.lra.num_vars() == 0 {
            theory.euf.enable_transitivity_lemmas(self.next_var);
        }
        for c in &self.clauses[self.added..] {
            self.solver.add_clause(c);
        }
        self.added = self.clauses.len();
        let _o = st::outer(st::Outer::Sat);
        match self.solver.solve() {
            SolveResult::Sat(m) => {
                self.model = m;
                Some(true)
            }
            SolveResult::Unsat => Some(false),
            SolveResult::Interrupted => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn direct_congruence_unsat() {
        // a = b  &  f(a) != f(b)  -> UNSAT
        let mut s = SmtBuilder::new();
        let a = s.euf().mk_const("a");
        let b = s.euf().mk_const("b");
        let fa = s.euf().mk_app("f", vec![a]);
        let fb = s.euf().mk_app("f", vec![b]);
        let e_ab = s.eq_atom(a, b);
        let e_ff = s.eq_atom(fa, fb);
        s.add_clause(vec![e_ab]); // a = b
        s.add_clause(vec![!e_ff]); // f(a) != f(b)
        assert_eq!(s.solve(), Some(false), "a=b & f(a)!=f(b) must be UNSAT");
    }

    #[test]
    fn transitive_congruence_unsat() {
        // a=b, c=d, b=d, f(a)!=f(c) -> UNSAT
        let mut s = SmtBuilder::new();
        let a = s.euf().mk_const("a");
        let b = s.euf().mk_const("b");
        let c = s.euf().mk_const("c");
        let d = s.euf().mk_const("d");
        let fa = s.euf().mk_app("f", vec![a]);
        let fc = s.euf().mk_app("f", vec![c]);
        let e_ab = s.eq_atom(a, b);
        let e_cd = s.eq_atom(c, d);
        let e_bd = s.eq_atom(b, d);
        let e_ff = s.eq_atom(fa, fc);
        s.add_clause(vec![e_ab]);
        s.add_clause(vec![e_cd]);
        s.add_clause(vec![e_bd]);
        s.add_clause(vec![!e_ff]);
        assert_eq!(
            s.solve(),
            Some(false),
            "transitive congruence must be UNSAT"
        );
    }

    #[test]
    fn congruence_sat_without_link() {
        // a=b, c=d, f(a)!=f(c)  (no b=d) -> SAT
        let mut s = SmtBuilder::new();
        let a = s.euf().mk_const("a");
        let b = s.euf().mk_const("b");
        let c = s.euf().mk_const("c");
        let d = s.euf().mk_const("d");
        let fa = s.euf().mk_app("f", vec![a]);
        let fc = s.euf().mk_app("f", vec![c]);
        let e_ab = s.eq_atom(a, b);
        let e_cd = s.eq_atom(c, d);
        let e_ff = s.eq_atom(fa, fc);
        s.add_clause(vec![e_ab]);
        s.add_clause(vec![e_cd]);
        s.add_clause(vec![!e_ff]);
        assert_eq!(s.solve(), Some(true), "a=b & c=d & f(a)!=f(c) must be SAT");
    }

    #[test]
    fn boolean_structure_unsat() {
        // (a=b | a=c) & a!=b & a!=c  -> UNSAT (exercises the SAT/theory loop on a disjunction)
        let mut s = SmtBuilder::new();
        let a = s.euf().mk_const("a");
        let b = s.euf().mk_const("b");
        let c = s.euf().mk_const("c");
        let e_ab = s.eq_atom(a, b);
        let e_ac = s.eq_atom(a, c);
        s.add_clause(vec![e_ab, e_ac]); // a=b OR a=c
        s.add_clause(vec![!e_ab]); // a!=b
        s.add_clause(vec![!e_ac]); // a!=c
        assert_eq!(s.solve(), Some(false));
    }

    #[test]
    fn boolean_structure_sat() {
        // (a=b | a=c) & a!=b  -> SAT (pick a=c)
        let mut s = SmtBuilder::new();
        let a = s.euf().mk_const("a");
        let b = s.euf().mk_const("b");
        let c = s.euf().mk_const("c");
        let e_ab = s.eq_atom(a, b);
        let e_ac = s.eq_atom(a, c);
        s.add_clause(vec![e_ab, e_ac]);
        s.add_clause(vec![!e_ab]);
        assert_eq!(s.solve(), Some(true));
    }

    #[test]
    fn diamond_chain_unsat() {
        // eq_diamond: for each i, (x_i = y_i & y_i = x_{i+1}) | (x_i = z_i & z_i = x_{i+1}),
        // and x_0 != x_n. Exponential for resolution over the input atoms alone; the
        // transitivity lemmas (new atoms x_i = x_{i+1}) make it easy.
        let n = 30;
        let mut s = SmtBuilder::new();
        let x: Vec<TermId> = (0..=n)
            .map(|i| s.euf().mk_const(&format!("x{i}")))
            .collect();
        for i in 0..n {
            let y = s.euf().mk_const(&format!("y{i}"));
            let z = s.euf().mk_const(&format!("z{i}"));
            let (a, b) = (s.eq_atom(x[i], y), s.eq_atom(y, x[i + 1]));
            let (c, d) = (s.eq_atom(x[i], z), s.eq_atom(z, x[i + 1]));
            // (a & b) | (c & d) in CNF
            s.add_clause(vec![a, c]);
            s.add_clause(vec![a, d]);
            s.add_clause(vec![b, c]);
            s.add_clause(vec![b, d]);
        }
        let e = s.eq_atom(x[0], x[n]);
        s.add_clause(vec![!e]);
        assert_eq!(s.solve(), Some(false));
    }
}
