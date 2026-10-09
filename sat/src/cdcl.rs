//! A CDCL SAT solver: two-watched literals, VSIDS, 1-UIP analysis with non-chronological
//! backjumping, Luby restarts, and LBD-based clause-database reduction.
//!
//! Follows MiniSat/Glucose. Clauses live in a `Vec` addressed by `ClauseRef`, per-variable data
//! is struct-of-arrays, and watch lists are indexed by `Lit::index()`.

use crate::heap::VarHeap;
use crate::proof::{ClauseId, Proof, Step};
use smtrex_core::{Lbool, Lit, NoTheory, Theory, Var};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

/// Index of a clause in the solver's clause vector.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct ClauseRef(u32);

/// A clause false under the current assignment, with its proof id.
type Conflict = (Vec<Lit>, ClauseId);

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Reason {
    Decision,
    Clause(ClauseRef),
    /// Theory-propagated literal; its reason clause is materialized lazily via `Theory::explain`.
    Theory,
}

struct Clause {
    lits: Vec<Lit>,
    /// Proof id (0 when no proof is logged).
    id: ClauseId,
    learnt: bool,
    /// Literal Block Distance (number of distinct decision levels), used for reduction.
    lbd: u32,
    activity: f64,
    deleted: bool,
}

#[derive(Clone, Copy)]
struct Watch {
    clause: ClauseRef,
    /// Some other literal of the clause; if it is true, the clause need not be visited.
    blocker: Lit,
}

/// Outcome of a solve. `Sat` carries a full model indexed by variable. `Interrupted` means the
/// stop flag (see [`Solver::set_stop_flag`]) was raised before an answer was found.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum SolveResult {
    Sat(Vec<bool>),
    Unsat,
    Interrupted,
}

pub struct Solver<T: Theory = NoTheory> {
    theory: T,
    num_vars: usize,
    clauses: Vec<Clause>,
    learnts: Vec<ClauseRef>,
    watches: Vec<Vec<Watch>>, // length 2*num_vars

    // assignment / trail (struct-of-arrays)
    assigns: Vec<Lbool>,
    polarity: Vec<bool>, // saved phase
    level: Vec<u32>,
    reason: Vec<Reason>,
    trail: Vec<Lit>,
    trail_lim: Vec<usize>,
    qhead: usize,

    // VSIDS
    activity: Vec<f64>,
    var_inc: f64,
    var_decay: f64,
    order: VarHeap,

    // clause activity (for learnt reduction)
    cla_inc: f64,
    cla_decay: f64,

    /// False once unsatisfiability is detected at level 0.
    ok: bool,

    // reusable scratch
    seen: Vec<bool>,
    lbd_stamp: Vec<u64>,
    lbd_counter: u64,

    /// Raised from outside (Ctrl-C, a timeout watchdog) to stop `solve` early.
    stop: Option<Arc<AtomicBool>>,

    // proof logging (see `enable_proof`)
    proof: Option<Proof>,
    /// For a variable assigned at level 0: the id of the unit clause asserting it (0 = not yet
    /// derived).
    unit_id: Vec<ClauseId>,
    /// Position of each assigned variable on the trail, to order proof hints.
    trail_pos: Vec<u32>,
}

impl Default for Solver<NoTheory> {
    fn default() -> Self {
        Solver::new()
    }
}

impl Solver<NoTheory> {
    /// A pure-SAT solver (no theory attached).
    pub fn new() -> Solver<NoTheory> {
        Solver::with_theory(NoTheory)
    }
}

impl<T: Theory> Solver<T> {
    /// A solver driving `theory` (DPLL(T)).
    pub fn with_theory(theory: T) -> Solver<T> {
        Solver {
            theory,
            num_vars: 0,
            clauses: Vec::new(),
            learnts: Vec::new(),
            watches: Vec::new(),
            assigns: Vec::new(),
            polarity: Vec::new(),
            level: Vec::new(),
            reason: Vec::new(),
            trail: Vec::new(),
            trail_lim: Vec::new(),
            qhead: 0,
            activity: Vec::new(),
            var_inc: 1.0,
            var_decay: 0.95,
            order: VarHeap::default(),
            cla_inc: 1.0,
            cla_decay: 0.999,
            ok: true,
            seen: Vec::new(),
            lbd_stamp: Vec::new(),
            lbd_counter: 0,
            stop: None,
            proof: None,
            unit_id: Vec::new(),
            trail_pos: Vec::new(),
        }
    }

    /// Log a proof from now on. Must be called before the first clause is added, so input clause
    /// ids are `1, 2, …` in the order of [`Solver::add_clause`] calls.
    pub fn enable_proof(&mut self) {
        debug_assert!(self.clauses.is_empty() && self.trail.is_empty());
        self.proof = Some(Proof::new());
    }

    pub fn proof(&self) -> Option<&Proof> {
        self.proof.as_ref()
    }

    pub fn take_proof(&mut self) -> Option<Proof> {
        self.proof.take()
    }

    fn log(&mut self, step: Step) {
        if let Some(p) = &mut self.proof {
            p.steps.push(step);
        }
    }

    fn fresh_id(&mut self) -> ClauseId {
        self.proof.as_mut().map_or(0, Proof::fresh_id)
    }

    /// Log a theory lemma and return its id.
    fn log_theory(&mut self, lits: &[Lit]) -> ClauseId {
        if self.proof.is_none() {
            return 0;
        }
        let id = self.fresh_id();
        self.log(Step::Theory {
            id,
            lits: lits.to_vec(),
        });
        id
    }

    /// The id of a unit clause asserting the level-0 literal of `v`, derived on first use from
    /// the literal's reason and the units of the reason's other literals.
    fn root_unit_id(&mut self, v: Var) -> ClauseId {
        let id = self.unit_id[v.index()];
        if id != 0 {
            return id;
        }
        debug_assert_eq!(self.level[v.index()], 0);
        let lit = self.trail[self.trail_pos[v.index()] as usize];
        let (reason_lits, reason_id) = match self.reason[v.index()] {
            Reason::Clause(c) => {
                let c = &self.clauses[c.0 as usize];
                (c.lits.clone(), c.id)
            }
            Reason::Theory => {
                let lits = self.theory.explain(lit);
                let id = self.log_theory(&lits);
                (lits, id)
            }
            Reason::Decision => unreachable!("level-0 decisions get their unit id when asserted"),
        };
        let mut units = Vec::new();
        for q in reason_lits {
            if q.var() != v {
                units.push(self.unit_hint(q.var()));
            }
        }
        let hints = rup_hints(units, reason_id);
        let id = self.fresh_id();
        self.log(Step::Derived {
            id,
            lits: vec![lit],
            hints,
        });
        self.unit_id[v.index()] = id;
        id
    }

    /// `(trail position, unit clause id)` of the level-0 variable `v`.
    fn unit_hint(&mut self, v: Var) -> (u32, ClauseId) {
        (self.trail_pos[v.index()], self.root_unit_id(v))
    }

    /// Assert a level-0 literal justified by the unit clause `id`.
    fn enqueue_root(&mut self, l: Lit, id: ClauseId) {
        debug_assert_eq!(self.decision_level(), 0);
        self.enqueue(l, Reason::Decision);
        self.unit_id[l.var().index()] = id;
    }

    /// Log the empty clause, from a clause `id` whose literals are all false at level 0.
    fn log_refutation(&mut self, lits: &[Lit], id: ClauseId) {
        if self.proof.is_none() {
            return;
        }
        let units = lits.iter().map(|l| self.unit_hint(l.var())).collect();
        let hints = rup_hints(units, id);
        let empty = self.fresh_id();
        self.log(Step::Derived {
            id: empty,
            lits: Vec::new(),
            hints,
        });
    }

    /// Mutable access to the attached theory (e.g. to register atoms before solving).
    pub fn theory_mut(&mut self) -> &mut T {
        &mut self.theory
    }

    pub fn theory(&self) -> &T {
        &self.theory
    }

    /// Make `solve` return [`SolveResult::Interrupted`] soon after `flag` becomes true. The flag
    /// is read once per search step, so the cost is one relaxed atomic load.
    pub fn set_stop_flag(&mut self, flag: Arc<AtomicBool>) {
        self.stop = Some(flag);
    }

    fn stop_requested(&self) -> bool {
        self.stop
            .as_ref()
            .is_some_and(|f| f.load(Ordering::Relaxed))
    }

    /// Ensure variables `0..n` exist.
    pub fn ensure_vars(&mut self, n: usize) {
        if n <= self.num_vars {
            return;
        }
        self.assigns.resize(n, Lbool::Undef);
        self.polarity.resize(n, false);
        self.level.resize(n, 0);
        self.reason.resize(n, Reason::Decision);
        self.activity.resize(n, 0.0);
        self.seen.resize(n, false);
        self.lbd_stamp.resize(n, 0);
        self.unit_id.resize(n, 0);
        self.trail_pos.resize(n, 0);
        self.watches.resize(2 * n, Vec::new());
        for v in self.num_vars..n {
            let var = Var::from_index(v);
            self.order.insert(&self.activity, var);
        }
        self.num_vars = n;
    }

    #[inline]
    fn value(&self, l: Lit) -> Lbool {
        match self.assigns[l.var().index()] {
            Lbool::Undef => Lbool::Undef,
            v => {
                // `v` is the variable's value; the literal's value flips if negated.
                if l.is_negated() {
                    if v == Lbool::True {
                        Lbool::False
                    } else {
                        Lbool::True
                    }
                } else {
                    v
                }
            }
        }
    }

    #[inline]
    fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    /// Undo every decision, keeping learnt clauses, so clauses can be added between solves.
    pub fn backtrack_to_root(&mut self) {
        self.backtrack(0);
    }

    /// Add a clause (DIMACS-style literal list). Returns `false` if this makes the formula
    /// trivially unsatisfiable. Must be called at decision level 0.
    pub fn add_clause(&mut self, lits: &[Lit]) -> bool {
        debug_assert_eq!(self.decision_level(), 0);
        let id = self.fresh_id();
        self.log(Step::Input {
            id,
            lits: lits.to_vec(),
        });
        if !self.ok {
            return false;
        }
        // Drop duplicates and level-0-false literals; skip tautologies and satisfied clauses.
        if let Some(mv) = lits.iter().map(|l| l.var().index()).max() {
            self.ensure_vars(mv + 1);
        }
        let mut c: Vec<Lit> = Vec::with_capacity(lits.len());
        let mut dropped: Vec<Lit> = Vec::new();
        for &l in lits {
            match self.value(l) {
                Lbool::True => return true,
                Lbool::False => dropped.push(l),
                Lbool::Undef => {
                    if c.contains(&!l) {
                        return true;
                    }
                    if !c.contains(&l) {
                        c.push(l);
                    }
                }
            }
        }
        // The stored clause differs from the input: derive it from the input and the units of
        // the dropped literals.
        let id = if self.proof.is_some() && c.len() != lits.len() {
            let mut units: Vec<(u32, ClauseId)> =
                dropped.iter().map(|l| self.unit_hint(l.var())).collect();
            units.sort_unstable();
            units.dedup();
            let hints = rup_hints(units, id);
            let derived = self.fresh_id();
            self.log(Step::Derived {
                id: derived,
                lits: c.clone(),
                hints,
            });
            derived
        } else {
            id
        };
        match c.len() {
            0 => {
                self.ok = false;
                false
            }
            1 => {
                self.enqueue_root(c[0], id);
                true
            }
            _ => {
                self.attach_clause(c, false, id);
                true
            }
        }
    }

    fn attach_clause(&mut self, lits: Vec<Lit>, learnt: bool, id: ClauseId) -> ClauseRef {
        let w0 = lits[0];
        let w1 = lits[1];
        let lbd = if learnt { self.compute_lbd(&lits) } else { 0 };
        let cref = ClauseRef(self.clauses.len() as u32);
        self.clauses.push(Clause {
            lits,
            id,
            learnt,
            lbd,
            activity: 0.0,
            deleted: false,
        });
        // Watch the negations of the two watched literals.
        self.watches[(!w0).index()].push(Watch {
            clause: cref,
            blocker: w1,
        });
        self.watches[(!w1).index()].push(Watch {
            clause: cref,
            blocker: w0,
        });
        if learnt {
            self.learnts.push(cref);
        }
        cref
    }

    #[inline]
    fn enqueue(&mut self, l: Lit, reason: Reason) {
        let v = l.var().index();
        self.assigns[v] = Lbool::from_bool(!l.is_negated());
        self.level[v] = self.decision_level();
        self.reason[v] = reason;
        self.trail_pos[v] = self.trail.len() as u32;
        self.trail.push(l);
        self.theory.assert(l);
    }

    /// Boolean constraint propagation. Returns the conflicting clause, if any.
    fn propagate(&mut self) -> Option<ClauseRef> {
        let mut confl = None;
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            // Process clauses watching ¬p (i.e. those whose watched literal ¬p just became false).
            let mut ws = std::mem::take(&mut self.watches[p.index()]);
            let mut i = 0;
            let mut keep = 0;
            'next_watch: while i < ws.len() {
                let w = ws[i];
                i += 1;
                // Shortcut: if the blocker is already satisfied, the clause is fine.
                if self.value(w.blocker) == Lbool::True {
                    ws[keep] = w;
                    keep += 1;
                    continue;
                }
                let cref = w.clause;
                let ci = cref.0 as usize;
                let false_lit = !p;
                // Make sure the false literal is at position 1.
                if self.clauses[ci].lits[0] == false_lit {
                    self.clauses[ci].lits.swap(0, 1);
                }
                let first = self.clauses[ci].lits[0];
                // If the other watched literal is true, the clause is satisfied.
                if first != w.blocker && self.value(first) == Lbool::True {
                    ws[keep] = Watch {
                        clause: cref,
                        blocker: first,
                    };
                    keep += 1;
                    continue;
                }
                // Look for a new literal to watch among positions 2..len.
                let len = self.clauses[ci].lits.len();
                for k in 2..len {
                    let lk = self.clauses[ci].lits[k];
                    if self.value(lk) != Lbool::False {
                        // move lk to the watched position 1, relocate the watch
                        self.clauses[ci].lits.swap(1, k);
                        self.watches[(!lk).index()].push(Watch {
                            clause: cref,
                            blocker: first,
                        });
                        continue 'next_watch; // do not keep in p's list
                    }
                }
                // No new watch: clause is unit or conflicting under `first`.
                match self.value(first) {
                    Lbool::False => {
                        // conflict: keep remaining watches and stop.
                        ws[keep] = w;
                        keep += 1;
                        while i < ws.len() {
                            ws[keep] = ws[i];
                            keep += 1;
                            i += 1;
                        }
                        confl = Some(cref);
                        break;
                    }
                    _ => {
                        ws[keep] = w;
                        keep += 1;
                        self.enqueue(first, Reason::Clause(cref));
                    }
                }
            }
            ws.truncate(keep);
            self.watches[p.index()] = ws;
            if confl.is_some() {
                self.qhead = self.trail.len();
                break;
            }
        }
        confl
    }

    #[inline]
    fn bump_var(&mut self, v: Var) {
        self.activity[v.index()] += self.var_inc;
        if self.activity[v.index()] > 1e100 {
            for a in self.activity.iter_mut() {
                *a *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }
        self.order.increase(&self.activity, v);
    }

    #[inline]
    fn decay_var(&mut self) {
        self.var_inc /= self.var_decay;
    }

    #[inline]
    fn bump_clause(&mut self, ci: usize) {
        self.clauses[ci].activity += self.cla_inc;
        if self.clauses[ci].activity > 1e20 {
            for &cr in &self.learnts {
                self.clauses[cr.0 as usize].activity *= 1e-20;
            }
            self.cla_inc *= 1e-20;
        }
    }

    #[inline]
    fn decay_clause(&mut self) {
        self.cla_inc /= self.cla_decay;
    }

    fn compute_lbd(&mut self, lits: &[Lit]) -> u32 {
        self.lbd_counter += 1;
        let stamp = self.lbd_counter;
        let mut lbd = 0;
        for &l in lits {
            let lev = self.level[l.var().index()] as usize;
            // `lbd_stamp` is indexed by decision level; grow lazily.
            if lev >= self.lbd_stamp.len() {
                self.lbd_stamp.resize(lev + 1, 0);
            }
            if self.lbd_stamp[lev] != stamp {
                self.lbd_stamp[lev] = stamp;
                lbd += 1;
            }
        }
        lbd
    }

    /// 1-UIP analysis of the conflicting clause `reason_lits` (a clause's literals or a theory
    /// conflict clause; proof id `conflict_id`). Resolves backward over the trail; reasons are
    /// clause literals or, for theory-propagated literals, `Theory::explain`. Returns the learnt
    /// clause (asserting literal first), the level to backjump to, and, when a proof is logged,
    /// the clause's hints.
    fn analyze(
        &mut self,
        mut reason_lits: Vec<Lit>,
        conflict_id: ClauseId,
    ) -> (Vec<Lit>, u32, Vec<ClauseId>) {
        let proving = self.proof.is_some();
        // (trail position, id) of every clause the derivation uses, besides the conflict.
        let mut used: Vec<(u32, ClauseId)> = Vec::new();
        let mut learnt: Vec<Lit> = vec![Lit::from_code(0)]; // placeholder for the UIP at [0]
        let mut path_count = 0i32;
        let mut p: Option<Lit> = None;
        let mut index = self.trail.len();

        loop {
            for &q in &reason_lits {
                if Some(q) == p {
                    continue; // skip the resolved-on literal
                }
                let v = q.var();
                if proving && self.level[v.index()] == 0 {
                    used.push(self.unit_hint(v));
                    continue;
                }
                if !self.seen[v.index()] && self.level[v.index()] > 0 {
                    self.bump_var(v);
                    self.seen[v.index()] = true;
                    if self.level[v.index()] >= self.decision_level() {
                        path_count += 1;
                    } else {
                        learnt.push(q);
                    }
                }
            }
            // Select the next literal to resolve: the most recent seen literal on the trail.
            loop {
                index -= 1;
                if self.seen[self.trail[index].var().index()] {
                    break;
                }
            }
            let pl = self.trail[index];
            self.seen[pl.var().index()] = false;
            p = Some(pl);
            path_count -= 1;
            if path_count <= 0 {
                learnt[0] = !pl; // the asserting literal (1-UIP)
                break;
            }
            reason_lits = match self.reason[pl.var().index()] {
                Reason::Clause(c) => {
                    if self.clauses[c.0 as usize].learnt {
                        self.bump_clause(c.0 as usize);
                    }
                    if proving {
                        used.push((
                            self.trail_pos[pl.var().index()],
                            self.clauses[c.0 as usize].id,
                        ));
                    }
                    self.clauses[c.0 as usize].lits.clone()
                }
                Reason::Theory => {
                    let lits = self.theory.explain(pl);
                    if proving {
                        let id = self.log_theory(&lits);
                        used.push((self.trail_pos[pl.var().index()], id));
                    }
                    lits
                }
                Reason::Decision => unreachable!("UIP reached a decision with path_count > 0"),
            };
        }

        // Minimize (MiniSat's recursive scheme): drop a literal whose negation is implied, via
        // clause reasons only, by the clause's other literals. Theory-propagated literals count
        // as non-removable, so no `explain` call is spent on minimization.
        let mut marked: Vec<Var> = learnt.iter().map(|l| l.var()).collect();
        let mut j = 1;
        for i in 1..learnt.len() {
            let q = learnt[i];
            if !self.lit_redundant(q.var(), &mut marked, &mut used) {
                learnt[j] = q;
                j += 1;
            }
        }
        learnt.truncate(j);

        // Backjump to the second-highest level in the clause, whose literal goes to position 1.
        let mut backtrack_level = 0u32;
        if learnt.len() > 1 {
            let mut max_i = 1;
            for i in 2..learnt.len() {
                if self.level[learnt[i].var().index()] > self.level[learnt[max_i].var().index()] {
                    max_i = i;
                }
            }
            learnt.swap(1, max_i);
            backtrack_level = self.level[learnt[1].var().index()];
        }
        for v in marked {
            self.seen[v.index()] = false;
        }
        let mut hints = Vec::new();
        if proving {
            // Reverse unit propagation order: level-0 units and reasons by trail position, then
            // the conflict.
            used.sort_unstable();
            used.dedup_by_key(|u| u.1);
            hints = used.into_iter().map(|(_, id)| id).collect();
            hints.push(conflict_id);
        }
        (learnt, backtrack_level, hints)
    }

    /// Whether variable `v` (false in the learnt clause) is implied by `seen` variables through
    /// clause reasons. Variables proven redundant stay marked `seen` (a cache) and are added to
    /// `marked` for the final cleanup; a failed search unmarks what it marked. On success, the
    /// reasons it used (and the units of their level-0 literals) are added to `used`.
    fn lit_redundant(
        &mut self,
        v: Var,
        marked: &mut Vec<Var>,
        used: &mut Vec<(u32, ClauseId)>,
    ) -> bool {
        if !matches!(self.reason[v.index()], Reason::Clause(_)) {
            return false;
        }
        let proving = self.proof.is_some();
        let top = marked.len();
        let used_top = used.len();
        let mut stack = vec![v];
        while let Some(x) = stack.pop() {
            let Reason::Clause(c) = self.reason[x.index()] else {
                unreachable!("only clause-reason variables are pushed")
            };
            let ci = c.0 as usize;
            if proving {
                used.push((self.trail_pos[x.index()], self.clauses[ci].id));
            }
            for k in 0..self.clauses[ci].lits.len() {
                let u = self.clauses[ci].lits[k].var();
                if proving && u != x && self.level[u.index()] == 0 {
                    used.push(self.unit_hint(u));
                    continue;
                }
                if u == x || self.seen[u.index()] || self.level[u.index()] == 0 {
                    continue;
                }
                if matches!(self.reason[u.index()], Reason::Clause(_)) {
                    self.seen[u.index()] = true;
                    marked.push(u);
                    stack.push(u);
                } else {
                    for w in marked.drain(top..) {
                        self.seen[w.index()] = false;
                    }
                    used.truncate(used_top);
                    return false;
                }
            }
        }
        true
    }

    fn backtrack(&mut self, level: u32) {
        if self.decision_level() <= level {
            return;
        }
        let levels = (self.decision_level() - level) as usize;
        let lim = self.trail_lim[level as usize];
        for i in (lim..self.trail.len()).rev() {
            let l = self.trail[i];
            let v = l.var();
            self.polarity[v.index()] = !l.is_negated(); // save phase
            self.assigns[v.index()] = Lbool::Undef;
            self.order.insert(&self.activity, v);
        }
        self.trail.truncate(lim);
        self.trail_lim.truncate(level as usize);
        self.qhead = self.trail.len();
        self.theory.pop(levels);
    }

    fn pick_branch(&mut self) -> Option<Lit> {
        while let Some(v) = self.order.pop_max(&self.activity) {
            if self.assigns[v.index()] == Lbool::Undef {
                let neg = !self.polarity[v.index()]; // phase saving (default false => positive)
                return Some(Lit::new(v, neg));
            }
        }
        None
    }

    fn new_decision_level(&mut self) {
        self.trail_lim.push(self.trail.len());
        self.theory.push();
    }

    /// Delete the worse half of the learnt clauses (high LBD first, then low activity), keeping
    /// glue clauses (LBD ≤ 2) and current reasons.
    fn reduce_db(&mut self) {
        let mut ls: Vec<ClauseRef> = self
            .learnts
            .iter()
            .copied()
            .filter(|c| !self.clauses[c.0 as usize].deleted)
            .collect();
        ls.sort_by(|&a, &b| {
            let ca = &self.clauses[a.0 as usize];
            let cb = &self.clauses[b.0 as usize];
            cb.lbd
                .cmp(&ca.lbd)
                .then(ca.activity.partial_cmp(&cb.activity).unwrap())
        });
        let half = ls.len() / 2;
        for &cr in ls.iter().take(half) {
            if self.clauses[cr.0 as usize].lbd > 2 && !self.is_reason(cr) {
                self.detach_clause(cr);
            }
        }
        self.learnts.retain(|c| !self.clauses[c.0 as usize].deleted);
    }

    /// Whether `cref` is the reason of its first literal (the only literal a clause can imply).
    fn is_reason(&self, cref: ClauseRef) -> bool {
        let ci = cref.0 as usize;
        let l0 = self.clauses[ci].lits[0];
        self.value(l0) == Lbool::True && self.reason[l0.var().index()] == Reason::Clause(cref)
    }

    fn detach_clause(&mut self, cref: ClauseRef) {
        let ci = cref.0 as usize;
        let w0 = self.clauses[ci].lits[0];
        let w1 = self.clauses[ci].lits[1];
        self.watches[(!w0).index()].retain(|w| w.clause != cref);
        self.watches[(!w1).index()].retain(|w| w.clause != cref);
        self.clauses[ci].deleted = true;
        self.clauses[ci].lits.clear();
        let id = self.clauses[ci].id;
        self.log(Step::Delete { id });
    }

    /// Add a theory lemma during search. It is kept permanently (never reduced). Returns a
    /// conflict clause (and its proof id) if the lemma is false under the current assignment; in
    /// that case and when it is unit, the solver first backtracks to the level where it became so.
    fn add_lemma(&mut self, lits: Vec<Lit>) -> Option<Conflict> {
        if let Some(mv) = lits.iter().map(|l| l.var().index()).max() {
            self.ensure_vars(mv + 1);
        }
        let mut c: Vec<Lit> = Vec::with_capacity(lits.len());
        for l in lits {
            if c.contains(&!l) {
                return None; // tautology
            }
            if !c.contains(&l) {
                c.push(l);
            }
        }
        // Order: true and unassigned literals first, then false ones by decreasing level, so the
        // first two are the right watches.
        let rank = |s: &Self, l: Lit| match s.value(l) {
            Lbool::True => (0, 0),
            Lbool::Undef => (1, 0),
            Lbool::False => (2, u32::MAX - s.level[l.var().index()]),
        };
        c.sort_by_key(|&l| rank(self, l));
        let id = self.log_theory(&c);
        match c.len() {
            0 => {
                self.ok = false;
                return Some((Vec::new(), id));
            }
            1 => {
                // A unit lemma holds at level 0.
                self.backtrack(0);
                match self.value(c[0]) {
                    Lbool::Undef => self.enqueue_root(c[0], id),
                    Lbool::False => return Some((c, id)),
                    Lbool::True => {}
                }
                return None;
            }
            _ => {}
        }
        let v0 = self.value(c[0]);
        let v1 = self.value(c[1]);
        if v0 == Lbool::False {
            // Entirely false: backtrack to its highest level and report it as a conflict there.
            self.backtrack(self.level[c[0].var().index()]);
            self.attach_clause(c.clone(), false, id);
            return Some((c, id));
        }
        if v0 == Lbool::Undef && v1 == Lbool::False {
            // Unit: assert the open literal at the level where the clause became unit.
            self.backtrack(self.level[c[1].var().index()]);
            let cref = self.attach_clause(c.clone(), false, id);
            self.enqueue(c[0], Reason::Clause(cref));
            return None;
        }
        self.attach_clause(c, false, id);
        None
    }

    /// Log the learnt clause, backjump to `bt` and assert its UIP.
    fn learn(&mut self, learnt: Vec<Lit>, bt: u32, hints: Vec<ClauseId>) {
        let id = self.fresh_id();
        if self.proof.is_some() {
            self.log(Step::Derived {
                id,
                lits: learnt.clone(),
                hints,
            });
        }
        self.backtrack(bt);
        if learnt.len() == 1 {
            self.enqueue_root(learnt[0], id);
        } else {
            let asserting = learnt[0];
            let cref = self.attach_clause(learnt, true, id);
            self.bump_clause(cref.0 as usize);
            self.enqueue(asserting, Reason::Clause(cref));
        }
    }

    /// BCP and theory propagation to a joint fixpoint. Returns a conflict, if any.
    fn propagate_all(&mut self) -> Option<Conflict> {
        loop {
            if let Some(confl) = self.propagate() {
                let ci = confl.0 as usize;
                if self.clauses[ci].learnt {
                    self.bump_clause(ci);
                }
                return Some((self.clauses[ci].lits.clone(), self.clauses[ci].id));
            }
            let mut progressed = false;
            for lit in self.theory.propagate() {
                match self.value(lit) {
                    Lbool::True => {}
                    Lbool::Undef => {
                        self.enqueue(lit, Reason::Theory);
                        progressed = true;
                    }
                    Lbool::False => {
                        let lits = self.theory.explain(lit);
                        let id = self.log_theory(&lits);
                        return Some((lits, id));
                    }
                }
            }
            if !progressed {
                return None;
            }
        }
    }

    /// Learn from a conflict and backjump. Returns `false` if the conflict is at level 0.
    fn resolve_conflict(&mut self, (lits, id): Conflict) -> bool {
        if self.decision_level() == 0 {
            self.log_refutation(&lits, id);
            self.ok = false;
            return false;
        }
        let (learnt, bt, hints) = self.analyze(lits, id);
        self.learn(learnt, bt, hints);
        self.decay_var();
        self.decay_clause();
        true
    }

    /// Solve the current formula: the DPLL(T) loop. Propagation runs to a fixpoint, then the
    /// theory is checked and its lemmas are added, then a decision is made. With `NoTheory` this
    /// is plain CDCL.
    pub fn solve(&mut self) -> SolveResult {
        if !self.ok {
            return SolveResult::Unsat;
        }
        let mut restart_no: u64 = 0;
        let mut conflicts_since_restart: u64 = 0;
        let mut max_conflicts = luby(2.0, restart_no) as u64 * 100;
        let mut learnt_limit = (self.clauses.len() as f64 * 1.3).max(1000.0);

        loop {
            if self.stop_requested() {
                self.backtrack(0);
                return SolveResult::Interrupted;
            }
            let mut conflict = self.propagate_all();
            if conflict.is_none() {
                let complete = self.trail.len() == self.num_vars;
                if let Err(lits) = self.theory.check(complete) {
                    let id = self.log_theory(&lits);
                    conflict = Some((lits, id));
                } else {
                    // Lemmas (e.g. branch-and-bound splits) extend the search instead of ending it.
                    let lemmas = self.theory.lemmas();
                    if !lemmas.is_empty() {
                        conflict = lemmas.into_iter().find_map(|lemma| self.add_lemma(lemma));
                        if conflict.is_none() {
                            continue;
                        }
                    }
                }
            }
            if let Some(c) = conflict {
                conflicts_since_restart += 1;
                if !self.resolve_conflict(c) {
                    return SolveResult::Unsat;
                }
                continue;
            }

            if conflicts_since_restart >= max_conflicts {
                self.backtrack(0);
                restart_no += 1;
                conflicts_since_restart = 0;
                max_conflicts = luby(2.0, restart_no) as u64 * 100;
                // Propagate, check and poll lemmas at level 0 before deciding (a theory may add
                // lemmas over new atoms only there).
                continue;
            }
            if self.learnts.len() as f64 >= learnt_limit {
                self.reduce_db();
                learnt_limit *= 1.1;
            }

            match self.pick_branch() {
                None => {
                    let model = (0..self.num_vars)
                        .map(|v| self.assigns[v] == Lbool::True)
                        .collect();
                    return SolveResult::Sat(model);
                }
                Some(dec) => {
                    self.new_decision_level();
                    self.enqueue(dec, Reason::Decision);
                }
            }
        }
    }
}

/// Proof hints for reverse unit propagation: the units in trail order, then `last`.
fn rup_hints(mut units: Vec<(u32, ClauseId)>, last: ClauseId) -> Vec<ClauseId> {
    units.sort_unstable();
    let mut hints: Vec<ClauseId> = units.into_iter().map(|(_, id)| id).collect();
    hints.push(last);
    hints
}

/// Luby sequence (used for restart intervals): 1,1,2,1,1,2,4,...
fn luby(y: f64, mut x: u64) -> f64 {
    let mut size = 1u64;
    let mut seq = 0u32;
    while size < x + 1 {
        seq += 1;
        size = 2 * size + 1;
    }
    while size - 1 != x {
        size = (size - 1) >> 1;
        seq -= 1;
        x %= size;
    }
    y.powi(seq as i32)
}
