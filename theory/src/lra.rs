//! Linear arithmetic: the incremental general Simplex of Dutertre & de Moura, *A Fast
//! Linear-Arithmetic Solver for DPLL(T)* (CAV 2006).
//!
//! Every linear term gets a variable: an original one, or a slack `s` with the row
//! `s = Σ aᵢ xᵢ`. Atoms are bounds `x ≤ c` / `x ≥ c` on single variables; strict bounds are exact
//! via δ-rationals. Invariants: every row holds under the assignment, and every non-basic
//! variable is within its bounds. `check` repairs violated basic variables by pivoting (Bland's
//! rule); backtracking only restores bounds, never the assignment.
//!
//! A conflict is an infeasible row (Farkas). Propagation derives atoms implied by a single
//! variable's bounds. Integer variables get integral bounds; a fractional value at the final
//! check yields a branch-and-bound split lemma over fresh atoms.

use rustc_hash::FxHashMap;
use smtrex_core::{DeltaRational, Lit, Rational, Theory, Var};

/// An arithmetic variable (column of the tableau).
pub type AVar = u32;

/// A linear combination `Σ coeff·var`.
pub type LinearTerm = Vec<(AVar, Rational)>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BoundKind {
    /// `x ≤ c`
    Le,
    /// `x ≥ c`
    Ge,
}

#[derive(Clone, Debug)]
struct Bound {
    value: DeltaRational,
    /// The (true) literal that asserted this bound.
    lit: Lit,
}

#[derive(Clone, Debug)]
struct Atom {
    var: AVar,
    kind: BoundKind,
    c: Rational,
}

#[derive(Clone, Debug, Default)]
struct VarData {
    value: DeltaRational,
    lower: Option<Bound>,
    upper: Option<Bound>,
    /// Row index if basic.
    row: Option<u32>,
    /// Rows in which this (non-basic) variable occurs.
    occurs: Vec<u32>,
    is_int: bool,
}

#[derive(Clone, Debug)]
struct Row {
    basic: AVar,
    /// `basic = Σ coeff · var`, sorted by var, no zeros, never containing `basic`.
    entries: Vec<(AVar, Rational)>,
}

enum Undo {
    Lower(AVar, Option<Bound>),
    Upper(AVar, Option<Bound>),
}

#[derive(Default)]
pub struct Lra {
    vars: Vec<VarData>,
    rows: Vec<Row>,
    /// SAT variable index -> its bound atom.
    atoms: Vec<Option<Atom>>,
    /// Arithmetic variable -> SAT variables of the atoms on it.
    var_atoms: Vec<Vec<Var>>,
    /// Canonical term -> its slack variable.
    slacks: FxHashMap<LinearTerm, AVar>,
    /// Slack variable -> the term it stands for.
    slack_terms: FxHashMap<AVar, LinearTerm>,
    trail: Vec<Undo>,
    /// Per decision level: (bound trail length, reason trail length) at its start.
    levels: Vec<(usize, usize)>,
    /// A conflict found while asserting, reported by the next `check`.
    conflict: Option<Vec<Lit>>,
    /// Theory-implied literals not yet handed to the SAT solver.
    implied: Vec<Lit>,
    /// SAT variable index -> the bound literal that implied it (recorded at propagation time).
    reasons: FxHashMap<u32, Lit>,
    /// Keys of `reasons` in insertion order, so a pop can drop exactly its levels' entries.
    reason_trail: Vec<u32>,
    /// Variables whose bounds changed since the last `propagate`.
    touched: Vec<AVar>,
    /// Lemmas for the SAT solver (branch-and-bound splits).
    lemmas: Vec<Vec<Lit>>,
    /// The next SAT variable index this theory may allocate for atoms it creates itself.
    next_sat_var: usize,
}

/// The result of [`Lra::maximize`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Optimum {
    /// The maximum over the current bounds, as a δ-rational: `c − kδ` (k > 0) means the
    /// supremum `c` is not attained (a strict bound stops short of it).
    Max(DeltaRational),
    Unbounded,
}

impl Lra {
    pub fn new() -> Lra {
        Lra::default()
    }

    /// A fresh original variable.
    pub fn new_var(&mut self, is_int: bool) -> AVar {
        let v = self.vars.len() as AVar;
        self.vars.push(VarData {
            is_int,
            ..VarData::default()
        });
        self.var_atoms.push(Vec::new());
        v
    }

    pub fn num_vars(&self) -> usize {
        self.vars.len()
    }

    pub fn is_int(&self, v: AVar) -> bool {
        self.vars[v as usize].is_int
    }

    /// The variable standing for `Σ coeff·var` (merging duplicates, dropping zeros). A single
    /// variable with coefficient 1 is itself; otherwise a slack variable with a defining row,
    /// shared by every occurrence of the same term. Callers normalise scaling (see the
    /// front-end); an empty term is not allowed.
    pub fn term_var(&mut self, terms: &[(AVar, Rational)]) -> AVar {
        let mut t: LinearTerm = terms.to_vec();
        t.sort_by_key(|(v, _)| *v);
        let mut merged: LinearTerm = Vec::with_capacity(t.len());
        for (v, c) in t {
            match merged.last_mut() {
                Some((w, d)) if *w == v => *d = &*d + &c,
                _ => merged.push((v, c)),
            }
        }
        merged.retain(|(_, c)| !c.is_zero());
        assert!(!merged.is_empty(), "term_var of an empty term");
        if merged.len() == 1 && merged[0].1 == Rational::one() {
            return merged[0].0;
        }
        if let Some(&s) = self.slacks.get(&merged) {
            return s;
        }
        let is_int = merged
            .iter()
            .all(|(v, c)| self.vars[*v as usize].is_int && c.is_integer());
        let s = self.new_var(is_int);
        // Express the row over the current non-basic variables.
        let mut row: LinearTerm = Vec::new();
        let mut value = DeltaRational::zero();
        for (v, c) in &merged {
            value = value.add_scaled(c, &self.vars[*v as usize].value);
            match self.vars[*v as usize].row {
                None => row = merge_add(&row, &[(*v, Rational::one())], c),
                Some(r) => {
                    let entries = self.rows[r as usize].entries.clone();
                    row = merge_add(&row, &entries, c);
                }
            }
        }
        let r = self.rows.len() as u32;
        for (v, _) in &row {
            self.vars[*v as usize].occurs.push(r);
        }
        self.rows.push(Row {
            basic: s,
            entries: row,
        });
        let sd = &mut self.vars[s as usize];
        sd.row = Some(r);
        sd.value = value;
        self.slack_terms.insert(s, merged.clone());
        self.slacks.insert(merged, s);
        s
    }

    /// Tie SAT variable `sat` to the atom `var ⋈ c`.
    pub fn register_atom(&mut self, sat: Var, var: AVar, kind: BoundKind, c: Rational) {
        let i = sat.index();
        if i >= self.atoms.len() {
            self.atoms.resize(i + 1, None);
        }
        self.atoms[i] = Some(Atom { var, kind, c });
        self.var_atoms[var as usize].push(sat);
    }

    /// The bound atom on SAT variable `sat`: `(Σ coeff·var) ⋈ c`, the sum over original
    /// variables (a single variable with coefficient 1 for an atom on an original variable).
    pub fn atom_of(&self, sat: Var) -> Option<(LinearTerm, BoundKind, Rational)> {
        let a = self.atoms.get(sat.index())?.as_ref()?;
        let term = match self.slack_terms.get(&a.var) {
            Some(t) => t.clone(),
            None => vec![(a.var, Rational::one())],
        };
        Some((term, a.kind, a.c.clone()))
    }

    /// The first SAT variable this theory has not allocated.
    pub fn next_free_sat_var(&self) -> usize {
        self.next_sat_var
    }

    /// SAT variables from `n` up are free for atoms this theory creates during search
    /// (branch-and-bound). Must be called before solving, once the front-end is done.
    pub fn set_sat_var_base(&mut self, n: usize) {
        self.next_sat_var = self.next_sat_var.max(n);
    }

    /// The literal of the atom `x ⋈ c`, reusing an existing atom or creating one.
    fn atom_lit(&mut self, x: AVar, kind: BoundKind, c: Rational) -> Lit {
        for &v in &self.var_atoms[x as usize] {
            let a = self.atoms[v.index()].as_ref().expect("registered");
            if a.kind == kind && a.c == c {
                return v.pos();
            }
        }
        let v = Var::from_index(self.next_sat_var);
        self.next_sat_var += 1;
        self.register_atom(v, x, kind, c);
        v.pos()
    }

    fn is_fractional(&self, x: usize) -> bool {
        let xd = &self.vars[x];
        xd.is_int && !(xd.value.delta.is_zero() && xd.value.value.is_integer())
    }

    /// Patching: move non-basic integer variables by small integer steps to make fractional
    /// basic ones integral. A move is kept only if it stays feasible and reduces the number of
    /// fractional variables. This catches cases where branch-and-bound would chase an unbounded
    /// variable forever.
    fn patch(&mut self) {
        let count = |s: &Self| (0..s.vars.len()).filter(|&x| s.is_fractional(x)).count();
        let mut fractional = count(self);
        for r in 0..self.rows.len() {
            if fractional == 0 {
                return;
            }
            if !self.is_fractional(self.rows[r].basic as usize) {
                continue;
            }
            let candidates: Vec<AVar> = self.rows[r]
                .entries
                .iter()
                .filter(|(x, _)| self.vars[*x as usize].is_int && !self.is_fractional(*x as usize))
                .map(|(x, _)| *x)
                .collect();
            'vars: for x in candidates {
                for step in [1i64, -1, 2, -2, 3, -3, 4, -4] {
                    let old = self.vars[x as usize].value.clone();
                    let new = old.add(&DeltaRational::of(Rational::from_int(step)));
                    let xd = &self.vars[x as usize];
                    if xd.lower.as_ref().is_some_and(|l| new < l.value)
                        || xd.upper.as_ref().is_some_and(|u| new > u.value)
                    {
                        continue;
                    }
                    self.update(x, new);
                    let feasible = self.rows.iter().all(|row| {
                        let bd = &self.vars[row.basic as usize];
                        bd.lower.as_ref().is_none_or(|l| bd.value >= l.value)
                            && bd.upper.as_ref().is_none_or(|u| bd.value <= u.value)
                    });
                    let now = count(self);
                    if feasible && now < fractional {
                        fractional = now;
                        break 'vars;
                    }
                    self.update(x, old);
                }
            }
        }
    }

    /// After a feasible check: if an integer variable has a fractional value `v`, queue the
    /// split `x ≤ ⌊v⌋ ∨ x ≥ ⌊v⌋ + 1`.
    fn branch(&mut self) {
        self.patch();
        let Some(x) = (0..self.vars.len()).find(|&x| self.is_fractional(x)) else {
            return;
        };
        // A δ-part on an integer variable only comes from strict bounds on reals; integers have
        // integral bounds, so their value is a plain rational here.
        let v = &self.vars[x].value.value;
        let lo = v.floor();
        let hi = &lo + &Rational::one();
        let le = self.atom_lit(x as AVar, BoundKind::Le, lo);
        let ge = self.atom_lit(x as AVar, BoundKind::Ge, hi);
        self.lemmas.push(vec![le, ge]);
    }

    /// Whether `sat` is one of this theory's atoms.
    pub fn owns(&self, sat: Var) -> bool {
        self.atoms.get(sat.index()).is_some_and(Option::is_some)
    }

    /// The bound a literal asserts: `(is_upper, value)`. Integer variables get integral bounds
    /// (`x < 5` becomes `x ≤ 4`, `x ≤ 4.5` becomes `x ≤ 4`).
    fn bound_of(&self, atom: &Atom, positive: bool) -> (bool, DeltaRational) {
        let is_int = self.vars[atom.var as usize].is_int;
        let c = &atom.c;
        match (atom.kind, positive) {
            (BoundKind::Le, true) => (
                true,
                if is_int {
                    DeltaRational::of(c.floor())
                } else {
                    DeltaRational::of(c.clone())
                },
            ),
            (BoundKind::Le, false) => (
                false,
                if is_int {
                    DeltaRational::of(&c.floor() + &Rational::one())
                } else {
                    DeltaRational::new(c.clone(), Rational::one())
                },
            ),
            (BoundKind::Ge, true) => (
                false,
                if is_int {
                    DeltaRational::of(c.ceil())
                } else {
                    DeltaRational::of(c.clone())
                },
            ),
            (BoundKind::Ge, false) => (
                true,
                if is_int {
                    DeltaRational::of(&c.ceil() - &Rational::one())
                } else {
                    DeltaRational::new(c.clone(), -Rational::one())
                },
            ),
        }
    }

    fn assert_upper(&mut self, x: AVar, value: DeltaRational, lit: Lit) {
        let xd = &self.vars[x as usize];
        if xd.upper.as_ref().is_some_and(|u| u.value <= value) {
            return; // not tighter
        }
        if let Some(l) = &xd.lower {
            if value < l.value {
                self.conflict = Some(vec![!lit, !l.lit]);
                return;
            }
        }
        let old = self.vars[x as usize].upper.replace(Bound {
            value: value.clone(),
            lit,
        });
        self.trail.push(Undo::Upper(x, old));
        self.touched.push(x);
        if self.vars[x as usize].row.is_none() && self.vars[x as usize].value > value {
            self.update(x, value);
        }
    }

    fn assert_lower(&mut self, x: AVar, value: DeltaRational, lit: Lit) {
        let xd = &self.vars[x as usize];
        if xd.lower.as_ref().is_some_and(|l| l.value >= value) {
            return;
        }
        if let Some(u) = &xd.upper {
            if value > u.value {
                self.conflict = Some(vec![!lit, !u.lit]);
                return;
            }
        }
        let old = self.vars[x as usize].lower.replace(Bound {
            value: value.clone(),
            lit,
        });
        self.trail.push(Undo::Lower(x, old));
        self.touched.push(x);
        if self.vars[x as usize].row.is_none() && self.vars[x as usize].value < value {
            self.update(x, value);
        }
    }

    /// Set non-basic `x` to `v`, keeping every row true.
    fn update(&mut self, x: AVar, v: DeltaRational) {
        let diff = v.sub(&self.vars[x as usize].value);
        for i in 0..self.vars[x as usize].occurs.len() {
            let r = self.vars[x as usize].occurs[i] as usize;
            let a = coeff(&self.rows[r].entries, x).expect("occurs list is exact");
            let b = self.rows[r].basic as usize;
            self.vars[b].value = self.vars[b].value.add_scaled(&a, &diff);
        }
        self.vars[x as usize].value = v;
    }

    /// Pivot basic `b` (row `r`) with non-basic `x`, after moving `b` to `v`.
    fn pivot_and_update(&mut self, r: usize, x: AVar, v: DeltaRational) {
        let b = self.rows[r].basic;
        let a = coeff(&self.rows[r].entries, x).expect("x occurs in the row");
        let theta = v.sub(&self.vars[b as usize].value).scale(&a.recip());
        self.vars[b as usize].value = v;
        self.vars[x as usize].value = self.vars[x as usize].value.add(&theta);
        for i in 0..self.vars[x as usize].occurs.len() {
            let r2 = self.vars[x as usize].occurs[i] as usize;
            if r2 == r {
                continue;
            }
            let a2 = coeff(&self.rows[r2].entries, x).expect("occurs list is exact");
            let b2 = self.rows[r2].basic as usize;
            self.vars[b2].value = self.vars[b2].value.add_scaled(&a2, &theta);
        }
        self.pivot(r, x);
    }

    /// Make `x` basic in row `r` instead of the current basic variable.
    fn pivot(&mut self, r: usize, x: AVar) {
        let b = self.rows[r].basic;
        let entries = std::mem::take(&mut self.rows[r].entries);
        let a = coeff(&entries, x).expect("x occurs in the row");
        let inv = a.recip();
        // x = (1/a)·b − Σ_{j≠x} (a_j/a)·x_j
        let mut new_row: Vec<(AVar, Rational)> = Vec::with_capacity(entries.len());
        for (v, c) in &entries {
            if *v != x {
                new_row.push((*v, -&(c * &inv)));
            }
        }
        insert_sorted(&mut new_row, b, inv);
        // Occurrence lists: x leaves row r, b joins it.
        self.vars[x as usize].occurs.retain(|&q| q != r as u32);
        self.vars[b as usize].occurs.push(r as u32);
        self.vars[b as usize].row = None;
        self.vars[x as usize].row = Some(r as u32);
        self.rows[r].basic = x;
        self.rows[r].entries = new_row;
        // Substitute x in every other row that mentions it.
        let others = std::mem::take(&mut self.vars[x as usize].occurs);
        for &r2 in &others {
            let r2 = r2 as usize;
            let row2 = std::mem::take(&mut self.rows[r2].entries);
            let c = coeff(&row2, x).expect("occurs list is exact");
            let without_x: Vec<(AVar, Rational)> =
                row2.iter().filter(|(v, _)| *v != x).cloned().collect();
            let merged = merge_add(&without_x, &self.rows[r].entries, &c);
            // Fix occurrence lists for variables that entered or left row r2.
            for (v, _) in &merged {
                if coeff(&without_x, *v).is_none() {
                    self.vars[*v as usize].occurs.push(r2 as u32);
                }
            }
            for (v, _) in &without_x {
                if coeff(&merged, *v).is_none() {
                    self.vars[*v as usize].occurs.retain(|&q| q != r2 as u32);
                }
            }
            self.rows[r2].entries = merged;
        }
    }

    /// Restore feasibility, or return a conflict clause (negated bound literals).
    fn simplex(&mut self) -> Result<(), Vec<Lit>> {
        loop {
            // Bland: the violated basic variable with the smallest index.
            let mut pick: Option<(usize, bool)> = None; // (row, needs to increase)
            let mut best = AVar::MAX;
            for (r, row) in self.rows.iter().enumerate() {
                let b = row.basic;
                if b >= best {
                    continue;
                }
                let bd = &self.vars[b as usize];
                if bd.lower.as_ref().is_some_and(|l| bd.value < l.value) {
                    pick = Some((r, true));
                    best = b;
                } else if bd.upper.as_ref().is_some_and(|u| bd.value > u.value) {
                    pick = Some((r, false));
                    best = b;
                }
            }
            let Some((r, increase)) = pick else {
                return Ok(());
            };
            let b = self.rows[r].basic as usize;
            // Bland: the eligible non-basic variable with the smallest index.
            let mut entering: Option<AVar> = None;
            for (x, a) in &self.rows[r].entries {
                let xd = &self.vars[*x as usize];
                let can_up = xd.upper.as_ref().is_none_or(|u| xd.value < u.value);
                let can_down = xd.lower.as_ref().is_none_or(|l| xd.value > l.value);
                let ok = if increase == a.is_positive() {
                    can_up
                } else {
                    can_down
                };
                if ok {
                    entering = Some(*x);
                    break; // entries are sorted by variable
                }
            }
            match entering {
                Some(x) => {
                    let target = if increase {
                        self.vars[b].lower.as_ref().unwrap().value.clone()
                    } else {
                        self.vars[b].upper.as_ref().unwrap().value.clone()
                    };
                    self.pivot_and_update(r, x, target);
                }
                None => {
                    let mut clause = Vec::with_capacity(self.rows[r].entries.len() + 1);
                    let bd = &self.vars[b];
                    let own = if increase { &bd.lower } else { &bd.upper };
                    clause.push(!own.as_ref().unwrap().lit);
                    for (x, a) in &self.rows[r].entries {
                        let xd = &self.vars[*x as usize];
                        // The bound that stops x from moving in the helpful direction.
                        let blocking = if increase == a.is_positive() {
                            &xd.upper
                        } else {
                            &xd.lower
                        };
                        clause.push(!blocking.as_ref().expect("blocked by a bound").lit);
                    }
                    clause.sort_by_key(|l| l.code());
                    clause.dedup();
                    return Err(clause);
                }
            }
        }
    }

    /// Bound propagation: atoms on a touched variable implied by its current bounds.
    fn propagate_bounds(&mut self) {
        let touched = std::mem::take(&mut self.touched);
        for x in touched {
            let (lower, upper) = {
                let xd = &self.vars[x as usize];
                (xd.lower.clone(), xd.upper.clone())
            };
            for i in 0..self.var_atoms[x as usize].len() {
                let sat = self.var_atoms[x as usize][i];
                if self.reasons.contains_key(&(sat.index() as u32)) {
                    continue;
                }
                let atom = self.atoms[sat.index()].clone().expect("registered");
                // Which literal of this atom do the bounds force, and why?
                let forced = match atom.kind {
                    BoundKind::Le => {
                        let (_, up_if_true) = self.bound_of(&atom, true);
                        let (_, low_if_false) = self.bound_of(&atom, false);
                        if let Some(u) = upper.as_ref().filter(|u| u.value <= up_if_true) {
                            Some((sat.pos(), u.lit))
                        } else {
                            lower
                                .as_ref()
                                .filter(|l| l.value >= low_if_false)
                                .map(|l| (sat.neg(), l.lit))
                        }
                    }
                    BoundKind::Ge => {
                        let (_, low_if_true) = self.bound_of(&atom, true);
                        let (_, up_if_false) = self.bound_of(&atom, false);
                        if let Some(l) = lower.as_ref().filter(|l| l.value >= low_if_true) {
                            Some((sat.pos(), l.lit))
                        } else {
                            upper
                                .as_ref()
                                .filter(|u| u.value <= up_if_false)
                                .map(|u| (sat.neg(), u.lit))
                        }
                    }
                };
                if let Some((lit, reason)) = forced {
                    if lit.var() == reason.var() {
                        continue; // the atom asserted itself
                    }
                    self.reasons.insert(sat.index() as u32, reason);
                    self.reason_trail.push(sat.index() as u32);
                    self.implied.push(lit);
                }
            }
        }
    }

    /// Maximise `o` over the current bounds with the primal Simplex (Bland's rule for both the
    /// entering and the leaving variable, so it terminates). Call it only in a feasible state,
    /// e.g. right after a satisfiable solve; it moves the assignment but keeps it feasible.
    pub fn maximize(&mut self, o: AVar) -> Optimum {
        loop {
            // The objective in terms of non-basic variables.
            let objective: Vec<(AVar, Rational)> = match self.vars[o as usize].row {
                Some(r) => self.rows[r as usize].entries.clone(),
                None => vec![(o, Rational::one())],
            };
            // Entering: the smallest non-basic variable that can move in an improving direction.
            let entering = objective.iter().find(|(x, c)| {
                let xd = &self.vars[*x as usize];
                if c.is_positive() {
                    xd.upper.as_ref().is_none_or(|u| xd.value < u.value)
                } else {
                    xd.lower.as_ref().is_none_or(|l| xd.value > l.value)
                }
            });
            let Some((x, c)) = entering.cloned() else {
                return Optimum::Max(self.vars[o as usize].value.clone());
            };
            let up = c.is_positive();
            // Ratio test: how far can x move? Its own bound, and every basic variable it drives.
            let xd = &self.vars[x as usize];
            let mut best: Option<(DeltaRational, Option<usize>)> = if up {
                xd.upper.as_ref().map(|u| (u.value.sub(&xd.value), None))
            } else {
                xd.lower.as_ref().map(|l| (xd.value.sub(&l.value), None))
            };
            let mut best_basic = AVar::MAX;
            for &r in &self.vars[x as usize].occurs {
                let r = r as usize;
                let a = coeff(&self.rows[r].entries, x).expect("occurs list is exact");
                let b = self.rows[r].basic;
                let bd = &self.vars[b as usize];
                // b moves by a·Δ (Δ ≥ 0 in x's direction of travel).
                let b_up = a.is_positive() == up;
                let room = if b_up {
                    bd.upper.as_ref().map(|u| u.value.sub(&bd.value))
                } else {
                    bd.lower.as_ref().map(|l| bd.value.sub(&l.value))
                };
                let Some(room) = room else { continue };
                let step = room.scale(&a.abs().recip());
                let better = match &best {
                    None => true,
                    Some((s, _)) => step < *s || (step == *s && b < best_basic),
                };
                if better {
                    best = Some((step, Some(r)));
                    best_basic = b;
                }
            }
            match best {
                None => return Optimum::Unbounded,
                Some((step, None)) => {
                    // x reaches its own bound.
                    let v = if up {
                        self.vars[x as usize].value.add(&step)
                    } else {
                        self.vars[x as usize].value.sub(&step)
                    };
                    self.update(x, v);
                }
                Some((_, Some(r))) => {
                    // The basic variable of row r hits a bound first: it leaves, x enters.
                    let b = self.rows[r].basic as usize;
                    let a = coeff(&self.rows[r].entries, x).expect("x occurs in the row");
                    let target = if a.is_positive() == up {
                        self.vars[b].upper.as_ref().unwrap().value.clone()
                    } else {
                        self.vars[b].lower.as_ref().unwrap().value.clone()
                    };
                    self.pivot_and_update(r, x, target);
                }
            }
        }
    }

    /// The current value of a variable (a δ-rational).
    pub fn value(&self, x: AVar) -> &DeltaRational {
        &self.vars[x as usize].value
    }

    /// A δ > 0 small enough that replacing δ by it keeps every bound satisfied.
    fn concrete_delta(&self) -> Rational {
        let mut delta = Rational::one();
        for xd in &self.vars {
            let v = &xd.value;
            let mut limit = |lo: &DeltaRational, hi: &DeltaRational| {
                // lo ≤ hi as δ-rationals; keep lo.value + δ·lo.delta ≤ hi.value + δ·hi.delta.
                if lo.value < hi.value && lo.delta > hi.delta {
                    let d = &(&hi.value - &lo.value) / &(&lo.delta - &hi.delta);
                    if d < delta {
                        delta = d;
                    }
                }
            };
            if let Some(l) = &xd.lower {
                limit(&l.value, v);
            }
            if let Some(u) = &xd.upper {
                limit(v, &u.value);
            }
        }
        delta
    }

    /// Concrete values of all variables in the current (feasible) state.
    pub fn model(&self) -> Vec<Rational> {
        let d = self.concrete_delta();
        self.vars.iter().map(|x| x.value.at(&d)).collect()
    }
}

/// `a + f·b` for sparse sorted rows.
fn merge_add(
    a: &[(AVar, Rational)],
    b: &[(AVar, Rational)],
    f: &Rational,
) -> Vec<(AVar, Rational)> {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() || j < b.len() {
        if j == b.len() || (i < a.len() && a[i].0 < b[j].0) {
            out.push(a[i].clone());
            i += 1;
        } else if i == a.len() || b[j].0 < a[i].0 {
            let c = &b[j].1 * f;
            if !c.is_zero() {
                out.push((b[j].0, c));
            }
            j += 1;
        } else {
            let c = b[j].1.mul_add(f, &a[i].1);
            if !c.is_zero() {
                out.push((a[i].0, c));
            }
            i += 1;
            j += 1;
        }
    }
    out
}

fn coeff(row: &[(AVar, Rational)], x: AVar) -> Option<Rational> {
    row.binary_search_by_key(&x, |(v, _)| *v)
        .ok()
        .map(|i| row[i].1.clone())
}

fn insert_sorted(row: &mut Vec<(AVar, Rational)>, x: AVar, c: Rational) {
    let i = row.partition_point(|(v, _)| *v < x);
    row.insert(i, (x, c));
}

impl Theory for Lra {
    fn assert(&mut self, lit: Lit) {
        if self.conflict.is_some() {
            return;
        }
        let Some(atom) = self.atoms.get(lit.var().index()).cloned().flatten() else {
            return;
        };
        let (is_upper, value) = self.bound_of(&atom, !lit.is_negated());
        if is_upper {
            self.assert_upper(atom.var, value, lit);
        } else {
            self.assert_lower(atom.var, value, lit);
        }
    }

    fn check(&mut self, complete: bool) -> Result<(), Vec<Lit>> {
        if let Some(c) = self.conflict.take() {
            return Err(c);
        }
        self.simplex()?;
        if complete {
            self.branch();
        }
        Ok(())
    }

    fn lemmas(&mut self) -> Vec<Vec<Lit>> {
        std::mem::take(&mut self.lemmas)
    }

    fn propagate(&mut self) -> Vec<Lit> {
        if self.conflict.is_none() {
            self.propagate_bounds();
        }
        std::mem::take(&mut self.implied)
    }

    fn explain(&mut self, lit: Lit) -> Vec<Lit> {
        let reason = self.reasons[&(lit.var().index() as u32)];
        vec![lit, !reason]
    }

    fn push(&mut self) {
        self.levels
            .push((self.trail.len(), self.reason_trail.len()));
    }

    fn pop(&mut self, levels: usize) {
        let keep = self.levels.len() - levels;
        let (target, reasons_len) = self.levels[keep];
        self.levels.truncate(keep);
        while self.trail.len() > target {
            match self.trail.pop().unwrap() {
                Undo::Lower(x, b) => self.vars[x as usize].lower = b,
                Undo::Upper(x, b) => self.vars[x as usize].upper = b,
            }
        }
        // A pending conflict always involves the newest assertion, which is now undone.
        self.conflict = None;
        self.implied.clear();
        self.touched.clear();
        // Propagations made in the popped levels are undone in the SAT solver too.
        for k in self.reason_trail.drain(reasons_len..) {
            self.reasons.remove(&k);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64) -> Rational {
        Rational::from_int(n)
    }

    /// Drive the theory like the SAT solver would.
    struct H {
        lra: Lra,
        next: usize,
    }

    impl H {
        fn new() -> H {
            H {
                lra: Lra::new(),
                next: 0,
            }
        }
        fn atom(&mut self, terms: &[(AVar, i64)], kind: BoundKind, c: i64) -> Lit {
            let t: Vec<(AVar, Rational)> = terms.iter().map(|(v, c)| (*v, q(*c))).collect();
            let x = self.lra.term_var(&t);
            let v = Var::from_index(self.next);
            self.next += 1;
            self.lra.register_atom(v, x, kind, q(c));
            v.pos()
        }
        fn check(&mut self, lits: &[Lit]) -> Result<(), Vec<Lit>> {
            for &l in lits {
                self.lra.assert(l);
            }
            self.lra.check(true)
        }
    }

    #[test]
    fn feasible_and_infeasible() {
        let mut h = H::new();
        let x = h.lra.new_var(false);
        let y = h.lra.new_var(false);
        // x + y >= 10, x - y <= 5, x - 2y <= 0: feasible
        let a = h.atom(&[(x, 1), (y, 1)], BoundKind::Ge, 10);
        let b = h.atom(&[(x, 1), (y, -1)], BoundKind::Le, 5);
        let c = h.atom(&[(x, 1), (y, -2)], BoundKind::Le, 0);
        assert!(h.check(&[a, b, c]).is_ok());
        let m = h.lra.model();
        let (xv, yv) = (&m[x as usize], &m[y as usize]);
        assert!(xv + yv >= q(10));
        assert!(xv - yv <= q(5));
        assert!(xv - &(yv * &q(2)) <= q(0));
        // add y <= 3: then x >= 7 and x <= 6, infeasible
        let d = h.atom(&[(y, 1)], BoundKind::Le, 3);
        let e = h.check(&[d]).unwrap_err();
        for l in &e {
            assert!([a, b, c, d].contains(&!*l), "{l:?} in {e:?}");
        }
    }

    #[test]
    fn strict_bounds_are_exact() {
        let mut h = H::new();
        let x = h.lra.new_var(false);
        // x <= 3 and not(x <= 2), i.e. 2 < x <= 3
        let le3 = h.atom(&[(x, 1)], BoundKind::Le, 3);
        let le2 = h.atom(&[(x, 1)], BoundKind::Le, 2);
        assert!(h.check(&[le3, !le2]).is_ok());
        let v = &h.lra.model()[x as usize];
        assert!(v > &q(2) && v <= &q(3), "{v}");
        // y < 3 (not y >= 3) together with 2y >= 6 is infeasible
        let mut h = H::new();
        let y = h.lra.new_var(false);
        let ge3 = h.atom(&[(y, 1)], BoundKind::Ge, 3);
        let c = h.atom(&[(y, 2)], BoundKind::Ge, 6);
        assert!(h.check(&[!ge3]).is_ok());
        assert!(h.check(&[c]).is_err());
    }

    #[test]
    fn integer_bounds_round() {
        let mut h = H::new();
        let x = h.lra.new_var(true);
        // x < 1 and x > 0 has no integer solution: the bounds round to x <= 0 and x >= 1
        let ge1 = h.atom(&[(x, 1)], BoundKind::Ge, 1);
        let le0 = h.atom(&[(x, 1)], BoundKind::Le, 0);
        assert!(h.check(&[!ge1]).is_ok());
        assert!(h.check(&[!le0]).is_err());
    }

    #[test]
    fn backtracking_restores_bounds() {
        let mut h = H::new();
        let x = h.lra.new_var(false);
        let y = h.lra.new_var(false);
        let s = h.atom(&[(x, 1), (y, 1)], BoundKind::Le, 4);
        let a = h.atom(&[(x, 1)], BoundKind::Ge, 3);
        let b = h.atom(&[(y, 1)], BoundKind::Ge, 2);
        assert!(h.check(&[s]).is_ok());
        h.lra.push();
        assert!(h.check(&[a]).is_ok());
        assert!(h.check(&[b]).is_err());
        h.lra.pop(1);
        assert!(h.check(&[b]).is_ok(), "x >= 3 was undone");
    }

    #[test]
    fn bound_propagation() {
        let mut h = H::new();
        let x = h.lra.new_var(false);
        let le3 = h.atom(&[(x, 1)], BoundKind::Le, 3);
        let le5 = h.atom(&[(x, 1)], BoundKind::Le, 5);
        let ge4 = h.atom(&[(x, 1)], BoundKind::Ge, 4);
        h.lra.assert(le3);
        let mut implied = h.lra.propagate();
        implied.sort_by_key(|l| l.code());
        let mut want = vec![le5, !ge4];
        want.sort_by_key(|l| l.code());
        assert_eq!(implied, want);
        assert_eq!(h.lra.explain(le5), vec![le5, !le3]);
    }

    #[test]
    fn propagation_reasons_are_scoped_to_levels() {
        let mut h = H::new();
        let x = h.lra.new_var(false);
        let le3 = h.atom(&[(x, 1)], BoundKind::Le, 3);
        let le5 = h.atom(&[(x, 1)], BoundKind::Le, 5);
        h.lra.push();
        h.lra.assert(le3);
        assert_eq!(h.lra.propagate(), vec![le5]);
        h.lra.pop(1);
        // Asserting x <= 3 again must propagate x <= 5 again.
        h.lra.push();
        h.lra.assert(le3);
        assert_eq!(h.lra.propagate(), vec![le5]);
    }

    #[test]
    fn maximize_bounded_unbounded_and_not_attained() {
        // max x + y  s.t.  x + 2y <= 4,  3x + y <= 6,  x, y >= 0   -> 14/5 at (8/5, 6/5)
        let mut h = H::new();
        let x = h.lra.new_var(false);
        let y = h.lra.new_var(false);
        let c1 = h.atom(&[(x, 1), (y, 2)], BoundKind::Le, 4);
        let c2 = h.atom(&[(x, 3), (y, 1)], BoundKind::Le, 6);
        let x0 = h.atom(&[(x, 1)], BoundKind::Ge, 0);
        let y0 = h.atom(&[(y, 1)], BoundKind::Ge, 0);
        assert!(h.check(&[c1, c2, x0, y0]).is_ok());
        let o = h.lra.term_var(&[(x, q(1)), (y, q(1))]);
        assert_eq!(
            h.lra.maximize(o),
            Optimum::Max(DeltaRational::of(Rational::new(14, 5)))
        );
        // The state is still feasible and every bound still holds.
        assert!(h.lra.check(true).is_ok());
        // Unbounded: max x with only x >= 1.
        let mut h = H::new();
        let x = h.lra.new_var(false);
        let ge1 = h.atom(&[(x, 1)], BoundKind::Ge, 1);
        assert!(h.check(&[ge1]).is_ok());
        assert_eq!(h.lra.maximize(x), Optimum::Unbounded);
        // Not attained: max x with x < 3 gives 3 - δ.
        let mut h = H::new();
        let x = h.lra.new_var(false);
        let ge3 = h.atom(&[(x, 1)], BoundKind::Ge, 3);
        assert!(h.check(&[!ge3]).is_ok());
        assert_eq!(
            h.lra.maximize(x),
            Optimum::Max(DeltaRational::new(q(3), q(-1)))
        );
    }

    /// Random systems: whatever `maximize` returns is checked by the feasibility Simplex. A
    /// reported maximum `m` is reached (the state stays feasible) and nothing above it is
    /// feasible; an unbounded objective can exceed any large value.
    #[test]
    fn maximize_agrees_with_feasibility() {
        let mut s = 0x9E3779B97F4A7C15u64;
        let mut rnd = |n: u64| {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s % n
        };
        let (mut bounded, mut unbounded) = (0, 0);
        for _ in 0..2000 {
            let mut h = H::new();
            let vs: Vec<AVar> = (0..3).map(|_| h.lra.new_var(false)).collect();
            let mut lits = Vec::new();
            for _ in 0..1 + rnd(6) {
                let t: Vec<(AVar, i64)> = vs
                    .iter()
                    .map(|&v| (v, rnd(5) as i64 - 2))
                    .filter(|(_, c)| *c != 0)
                    .collect();
                if t.is_empty() {
                    continue;
                }
                let kind = if rnd(2) == 0 {
                    BoundKind::Le
                } else {
                    BoundKind::Ge
                };
                let l = h.atom(&t, kind, rnd(11) as i64 - 5);
                lits.push(if rnd(4) != 0 { l } else { !l });
            }
            if h.check(&lits).is_err() {
                continue;
            }
            let obj: Vec<(AVar, Rational)> = vs
                .iter()
                .map(|&v| (v, q(rnd(5) as i64 - 2)))
                .filter(|(_, c)| !c.is_zero())
                .collect();
            if obj.is_empty() {
                continue;
            }
            let o = h.lra.term_var(&obj);
            let probe = Var::from_index(h.next);
            h.next += 1;
            match h.lra.maximize(o) {
                Optimum::Max(m) => {
                    bounded += 1;
                    assert!(
                        h.lra.check(true).is_ok(),
                        "maximize left an infeasible state"
                    );
                    assert_eq!(h.lra.value(o), &m);
                    // o > m must be infeasible: with m = c + kδ, that is o > c when k >= 0 and
                    // o >= c when k < 0.
                    h.lra.push();
                    if m.delta.is_negative() {
                        h.lra
                            .register_atom(probe, o, BoundKind::Ge, m.value.clone());
                        h.lra.assert(probe.pos());
                    } else {
                        h.lra
                            .register_atom(probe, o, BoundKind::Le, m.value.clone());
                        h.lra.assert(probe.neg());
                    }
                    assert!(
                        h.lra.check(true).is_err(),
                        "a value above the maximum is feasible"
                    );
                    h.lra.pop(1);
                }
                Optimum::Unbounded => {
                    unbounded += 1;
                    h.lra.register_atom(probe, o, BoundKind::Ge, q(1_000_000));
                    h.lra.assert(probe.pos());
                    assert!(
                        h.lra.check(true).is_ok(),
                        "an unbounded objective cannot reach 10^6"
                    );
                }
            }
        }
        assert!(
            bounded > 200 && unbounded > 200,
            "{bounded} bounded / {unbounded} unbounded"
        );
    }

    /// Random small systems: every reported model satisfies every asserted bound, and every
    /// conflict is made of negated asserted literals.
    #[test]
    fn random_systems() {
        let mut s = 0x2545F4914F6CDD1Du64;
        let mut rnd = |n: u64| {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s % n
        };
        let (mut feasible, mut infeasible) = (0, 0);
        for _ in 0..3000 {
            let mut h = H::new();
            let vs: Vec<AVar> = (0..3).map(|_| h.lra.new_var(false)).collect();
            // (term, kind, constant, polarity) of each asserted atom
            type Asserted = (Vec<(AVar, i64)>, BoundKind, i64, bool);
            let mut asserted: Vec<Asserted> = Vec::new();
            let mut lits = Vec::new();
            for _ in 0..1 + rnd(6) {
                let mut t: Vec<(AVar, i64)> = Vec::new();
                for &v in &vs {
                    let c = rnd(5) as i64 - 2;
                    if c != 0 {
                        t.push((v, c));
                    }
                }
                if t.is_empty() {
                    continue;
                }
                let kind = if rnd(2) == 0 {
                    BoundKind::Le
                } else {
                    BoundKind::Ge
                };
                let c = rnd(11) as i64 - 5;
                let pol = rnd(3) != 0;
                let l = h.atom(&t, kind, c);
                lits.push(if pol { l } else { !l });
                asserted.push((t, kind, c, pol));
            }
            match h.check(&lits) {
                Ok(()) => {
                    feasible += 1;
                    let m = h.lra.model();
                    for (t, kind, c, pol) in &asserted {
                        let val = t.iter().fold(Rational::zero(), |acc, (v, k)| {
                            &acc + &(&m[*v as usize] * &q(*k))
                        });
                        let holds = match kind {
                            BoundKind::Le => val <= q(*c),
                            BoundKind::Ge => val >= q(*c),
                        };
                        assert_eq!(holds, *pol, "model violates an asserted bound");
                    }
                }
                Err(conflict) => {
                    infeasible += 1;
                    for l in &conflict {
                        assert!(lits.contains(&!*l), "{l:?} was not asserted");
                    }
                }
            }
        }
        assert!(
            feasible > 300 && infeasible > 300,
            "{feasible}/{infeasible}"
        );
    }
}
