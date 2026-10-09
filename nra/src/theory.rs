//! The NRA theory solver for DPLL(T).
//!
//! Atoms are polynomial sign conditions `p = 0`, `p < 0`, `p > 0` over integer polynomials in the
//! theory's variables (the front-end clears denominators; `≤`, `≥`, `≠` are negated atoms). The
//! theory records the asserted literals; at a complete boolean assignment it decides their
//! conjunction exactly, by default with cylindrical algebraic coverings ([`crate::covering`]),
//! or with the full CAD of [`crate::cad`] ([`Engine`]):
//!
//! - The conjunction is split into components that share no variable; each is decided on its
//!   own. The conflict clause is the negation of the literals of an unsatisfiable core (the
//!   constraints behind the coverings' intervals; the whole component with the full CAD).
//! - Before deciding a component, the previous model is tried on it (exact signs), and the
//!   coverings prefer the previous model's values when sampling.
//!
//! No theory propagation; partial assignments are not checked.

use crate::cad::{satisfies, solve as cad_solve, Constraint, SignSet};
use crate::covering::{self, Outcome};
use rustc_hash::FxHashMap;
use smtrex_core::{Lit, Theory, Var};
use smtrex_poly::stats as st;
use smtrex_poly::{MPoly, RealAlgebraic};

/// The procedure deciding a conjunction.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum Engine {
    /// Cylindrical algebraic coverings ([`crate::covering`]): model-guided, with small
    /// unsatisfiable cores as conflicts. The default.
    #[default]
    Coverings,
    /// The full CAD ([`crate::cad`]); the conflict is the whole component.
    Cad,
    /// Coverings, every answer cross-checked against the full CAD (a panic on disagreement):
    /// the CAD as a test oracle. Selected with the environment variable `SMTREX_NRA_ORACLE`.
    Checked,
}

/// Panic unless the CAD agrees with a coverings answer: a satisfying point must satisfy the
/// constraints, and an unsatisfiable core must be unsatisfiable by the CAD.
fn check_against_cad(cs: &[Constraint], n: usize, r: &Outcome) {
    match r {
        Outcome::Sat(point) => {
            let mut p = point.clone();
            assert!(
                satisfies(cs, &mut p),
                "oracle: coverings model violates {cs:?}"
            );
        }
        Outcome::Unsat(core) => {
            let sub: Vec<Constraint> = core.iter().map(|&i| cs[i].clone()).collect();
            assert!(
                cad_solve(&sub, n).is_none(),
                "oracle: coverings core {core:?} of {cs:?} is satisfiable by the CAD"
            );
        }
    }
}

/// The relation of an atom `p ⋈ 0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AtomKind {
    Eq,
    Lt,
    Gt,
}

#[derive(Clone, Debug)]
struct Atom {
    poly: MPoly,
    kind: AtomKind,
}

#[derive(Default)]
pub struct Nra {
    /// SAT variable index -> atom.
    atoms: Vec<Option<Atom>>,
    num_vars: usize,
    trail: Vec<Lit>,
    levels: Vec<usize>,
    model: Vec<RealAlgebraic>,
    /// Conflict clauses for the solver (see [`Theory::check`] below).
    lemmas: Vec<Vec<Lit>>,
    pub engine: Engine,
}

impl Nra {
    /// A theory with the engine chosen by the environment: `SMTREX_NRA_ENGINE=cad` for the
    /// full CAD, `SMTREX_NRA_ORACLE` for coverings checked against it, coverings otherwise.
    pub fn new() -> Nra {
        let engine = if std::env::var_os("SMTREX_NRA_ORACLE").is_some() {
            Engine::Checked
        } else if std::env::var("SMTREX_NRA_ENGINE").is_ok_and(|e| e == "cad") {
            Engine::Cad
        } else {
            Engine::Coverings
        };
        Nra {
            engine,
            ..Nra::default()
        }
    }

    /// A fresh real variable (its index in [`MPoly`]s).
    pub fn new_var(&mut self) -> usize {
        self.num_vars += 1;
        self.num_vars - 1
    }

    pub fn num_vars(&self) -> usize {
        self.num_vars
    }

    /// Tie SAT variable `sat` to the atom `poly ⋈ 0`.
    pub fn register_atom(&mut self, sat: Var, poly: MPoly, kind: AtomKind) {
        let i = sat.index();
        if i >= self.atoms.len() {
            self.atoms.resize(i + 1, None);
        }
        self.atoms[i] = Some(Atom { poly, kind });
    }

    /// Whether `sat` is one of this theory's atoms.
    pub fn owns(&self, sat: Var) -> bool {
        self.atoms.get(sat.index()).is_some_and(Option::is_some)
    }

    /// The values of the variables after a satisfiable complete check (0 for variables in no
    /// asserted atom).
    pub fn model(&self) -> Vec<RealAlgebraic> {
        let mut m = self.model.clone();
        m.resize(self.num_vars, RealAlgebraic::from_int(0));
        m
    }

    fn constraint(&self, lit: Lit) -> Constraint {
        let a = self.atoms[lit.var().index()].as_ref().expect("an atom");
        let pos = !lit.is_negated();
        let allowed = match (a.kind, pos) {
            (AtomKind::Eq, true) => SignSet::ZERO,
            (AtomKind::Eq, false) => SignSet::NONZERO,
            (AtomKind::Lt, true) => SignSet::NEG,
            (AtomKind::Lt, false) => SignSet::NONNEG,
            (AtomKind::Gt, true) => SignSet::POS,
            (AtomKind::Gt, false) => SignSet::NONPOS,
        };
        Constraint {
            poly: a.poly.clone(),
            allowed,
        }
    }

    /// Decide the asserted literals; `Err` is a conflict clause.
    fn final_check(&mut self) -> Result<(), Vec<Lit>> {
        // Merge literals on the same polynomial into one sign condition.
        let mut conds: FxHashMap<MPoly, (SignSet, Vec<Lit>)> = FxHashMap::default();
        let mut order: Vec<MPoly> = Vec::new();
        for &lit in &self.trail {
            let c = self.constraint(lit);
            let e = conds.entry(c.poly.clone()).or_insert_with(|| {
                order.push(c.poly.clone());
                (SignSet::ANY, Vec::new())
            });
            e.0 = e.0.intersect(c.allowed);
            e.1.push(lit);
        }
        // A polynomial with an empty sign set is a conflict on its own.
        for p in &order {
            let (s, lits) = &conds[p];
            if s.is_empty() {
                st::add(st::Counter::NraTrivialConflicts, 1);
                return Err(lits.iter().map(|&l| !l).collect());
            }
        }
        // Components: union-find over variables.
        let n = self.num_vars;
        let mut parent: Vec<usize> = (0..n).collect();
        fn find(p: &mut [usize], x: usize) -> usize {
            let mut r = x;
            while p[r] != r {
                r = p[r];
            }
            let mut y = x;
            while p[y] != r {
                let next = p[y];
                p[y] = r;
                y = next;
            }
            r
        }
        for p in &order {
            let vs = p.vars();
            for w in vs.windows(2) {
                let (a, b) = (find(&mut parent, w[0]), find(&mut parent, w[1]));
                parent[a] = b;
            }
        }
        let mut comps: FxHashMap<usize, Vec<&MPoly>> = FxHashMap::default();
        let mut comp_order = Vec::new();
        for p in &order {
            let Some(v) = p.vars().first().copied() else {
                continue;
            };
            let r = find(&mut parent, v);
            comps
                .entry(r)
                .or_insert_with(|| {
                    comp_order.push(r);
                    Vec::new()
                })
                .push(p);
        }
        let mut model = std::mem::take(&mut self.model);
        model.resize(n, RealAlgebraic::from_int(0));
        for r in comp_order {
            let polys = &comps[&r];
            let cs: Vec<Constraint> = polys
                .iter()
                .map(|p| Constraint {
                    poly: (*p).clone(),
                    allowed: conds[*p].0,
                })
                .collect();
            st::add(st::Counter::Components, 1);
            let reused = {
                let _o = st::outer(st::Outer::ModelReuse);
                satisfies(&cs, &mut model)
            };
            if reused {
                st::add(st::Counter::ModelReuses, 1);
                continue;
            }
            if st::enabled() {
                record_component(&cs);
            }
            let result = match self.engine {
                Engine::Cad => match cad_solve(&cs, n) {
                    Some(point) => Outcome::Sat(point),
                    None => Outcome::Unsat((0..cs.len()).collect()),
                },
                Engine::Coverings | Engine::Checked => {
                    let (r, _) = covering::solve(&cs, n, Some(&model));
                    if self.engine == Engine::Checked {
                        check_against_cad(&cs, n, &r);
                    }
                    r
                }
            };
            match result {
                Outcome::Sat(point) => {
                    st::add(st::Counter::DecidedSat, 1);
                    for v in component_vars(&cs) {
                        model[v] = point[v].clone();
                    }
                }
                Outcome::Unsat(core) => {
                    self.model = model;
                    st::add(st::Counter::CoreSum, core.len() as u64);
                    st::max(st::Counter::CoreMax, core.len() as u64);
                    st::add(st::Counter::CoreCompSum, cs.len() as u64);
                    let mut clause: Vec<Lit> = Vec::new();
                    for i in core {
                        clause.extend(conds[polys[i]].1.iter().map(|&l| !l));
                    }
                    return Err(clause);
                }
            }
        }
        self.model = model;
        Ok(())
    }
}

/// The variables of `cs`, ascending.
fn component_vars(cs: &[Constraint]) -> Vec<usize> {
    let mut vars: Vec<usize> = cs.iter().flat_map(|c| c.poly.vars()).collect();
    vars.sort_unstable();
    vars.dedup();
    vars
}

/// Diagnostics: the shape of a component about to be decided.
fn record_component(cs: &[Constraint]) {
    let nv = component_vars(cs).len();
    let degrees = cs.iter().filter_map(|c| c.poly.total_degree());
    let nonlinear = degrees.clone().filter(|&d| d > 1).count();
    st::add(st::Counter::CompVarsSum, nv as u64);
    st::max(st::Counter::CompVarsMax, nv as u64);
    st::add(st::Counter::CompConsSum, cs.len() as u64);
    st::max(st::Counter::CompConsMax, cs.len() as u64);
    st::add(st::Counter::CompNonlinSum, nonlinear as u64);
    st::max(st::Counter::CompMaxDeg, degrees.max().unwrap_or(0) as u64);
}

impl Theory for Nra {
    fn assert(&mut self, lit: Lit) {
        if self.owns(lit.var()) {
            self.trail.push(lit);
        }
    }

    /// A conflict is returned as a lemma, not as `Err`: the asserted literals may all have been
    /// assigned below the current decision level (the check only runs on complete assignments),
    /// and the solver's lemma path backjumps to the clause's highest level before analysing it.
    fn check(&mut self, complete: bool) -> Result<(), Vec<Lit>> {
        if !complete || self.trail.is_empty() {
            return Ok(());
        }
        let _o = st::outer(st::Outer::NraPrep);
        st::add(st::Counter::NraChecks, 1);
        if let Err(clause) = self.final_check() {
            st::add(st::Counter::NraConflicts, 1);
            self.lemmas.push(clause);
        }
        Ok(())
    }

    fn lemmas(&mut self) -> Vec<Vec<Lit>> {
        std::mem::take(&mut self.lemmas)
    }

    fn propagate(&mut self) -> Vec<Lit> {
        Vec::new()
    }

    fn explain(&mut self, _lit: Lit) -> Vec<Lit> {
        unreachable!("the NRA theory does not propagate")
    }

    fn push(&mut self) {
        self.levels.push(self.trail.len());
    }

    fn pop(&mut self, levels: usize) {
        for _ in 0..levels {
            if let Some(l) = self.levels.pop() {
                self.trail.truncate(l);
            }
        }
    }
}
