//! EUF: equality with uninterpreted functions, by incremental proof-producing congruence closure
//! (Nieuwenhuis & Oliveras, *Proof-Producing Congruence Closure*, RTA 2005).
//!
//! `mk_const`/`mk_app` build terms and register them in the e-graph; `register_eq_atom` ties a
//! SAT variable to an equality atom. The core is a union-find with use-lists and a signature
//! table. Every merge also adds an edge to a proof forest, whose paths explain equalities. Each
//! class keeps a circular member list and the disequalities touching it, so a merge or a new
//! disequality only visits the smaller side, finding conflicts and newly decided atoms at once.
//! All mutations go on one trail, which `pop` undoes in reverse.

use rustc_hash::{FxHashMap, FxHashSet};
use smallvec::SmallVec;
use smtrex_core::{Lbool, Lit, Symbol, Theory, Var};
use smtrex_term::{TermArena, TermId};

/// Why two terms were merged — the justification recorded on a proof-forest edge.
#[derive(Clone, Copy)]
enum Reason {
    /// The asserted (positive) equality literal.
    Input(Lit),
    /// Congruence of two applications with pairwise equal arguments.
    Congruence(TermId, TermId),
}

/// A function symbol with the representatives of its arguments; two applications are congruent
/// iff they share a signature.
type Sig = (Symbol, SmallVec<[TermId; 3]>);

/// An asserted disequality `a != b`, with `lit` the *negated* atom literal that asserted it.
type Diseq = (TermId, TermId, Lit);

/// One reversible mutation recorded on the trail.
enum TrailOp {
    Repr(usize, TermId),
    Size(usize, u32),
    UsePush(usize),
    SigInsert(Sig),
    /// A signature entry was overwritten or removed; restore the old value.
    SigRestore(Sig, TermId),
    Proof(usize, Option<TermId>, Option<Reason>),
    DiseqPush,
    /// `class_diseqs[i]` grew; truncate it back to the saved length.
    ClassDiseqs(usize, usize),
    /// `next[i]` and `next[j]` were swapped (two member circles spliced).
    Splice(usize, usize),
    Assigned(usize, Lbool),
}

pub struct Euf {
    arena: TermArena,

    /// Union-find parent (representative). `repr[i] == i` for a root.
    repr: Vec<TermId>,
    /// Size of the class rooted at each representative (used for union-by-size).
    size: Vec<u32>,
    /// For representative `r`, the applications with an argument in `r`'s class. A merge appends
    /// the smaller root's list to the larger's and leaves the smaller's intact for undo.
    uses: Vec<Vec<TermId>>,
    /// Class member lists: `next` links every class into a circle (spliced on merge).
    next: Vec<TermId>,
    /// For representative `r`, indices into `diseq` of the disequalities with an endpoint in
    /// `r`'s class (maintained like `uses`).
    class_diseqs: Vec<Vec<u32>>,

    /// Proof forest: the edge `i — proof_parent[i]` is justified by `proof_reason[i]`.
    proof_parent: Vec<Option<TermId>>,
    proof_reason: Vec<Option<Reason>>,

    /// Signature table: `(symbol, repr-of-args) -> canonical application term`.
    sig: FxHashMap<Sig, TermId>,

    /// Asserted disequalities.
    diseq: Vec<Diseq>,

    /// SAT variable -> equality atom `(a, b)`.
    atoms: Vec<Option<(TermId, TermId)>>,
    /// Term -> the SAT variables of the equality atoms it is an endpoint of.
    term_atoms: Vec<Vec<u32>>,

    /// SAT variable -> current theory assignment of its atom (`Undef` if not yet asserted).
    /// Atoms already assigned are never propagated.
    assigned: Vec<Lbool>,

    /// For an atom propagated false (`a != b`), the disequality `(p, q, _)` with `a ≡ p`, `b ≡ q`
    /// that witnessed it. Fixed at propagation time: `explain` runs later, after further merges.
    neg_witness: Vec<Option<Diseq>>,

    /// Atom literals the closure decided since the last `propagate` (negative ones with their
    /// witness). Cleared on `pop`: everything in it was found at the current level.
    implied: Vec<(Lit, Option<Diseq>)>,
    /// The first violated disequality found at the current level, if any (cleared on `pop`).
    conflict: Option<Diseq>,

    /// Pending congruence-closure work: pairs of terms to be merged.
    pending: Vec<(TermId, TermId, Reason)>,

    /// Scratch for lowest-common-ancestor queries in the proof forest.
    stamp: Vec<u32>,
    stamp_now: u32,

    /// Mutation trail and the stack of level start offsets (one per `push`).
    trail: Vec<TrailOp>,
    levels: Vec<usize>,

    /// How many arena terms have been registered into the e-graph so far.
    registered: usize,

    /// Unordered term pair -> the SAT variable of its equality atom.
    atom_of: FxHashMap<(TermId, TermId), u32>,
    /// Dynamic transitivity lemmas (see [`Euf::enable_transitivity_lemmas`]).
    dyn_trans: DynTrans,
}

/// Dynamic transitivity lemmas, after dynamic Ackermannization (de Moura & Bjørner; z3's
/// `dyn_ack`). When input equalities `u = v`, `v = w` are adjacent on the explanation of a
/// conflict `THRESHOLD` times, the lemma `u ≠ v ∨ v ≠ w ∨ u = w` is added, creating the atom
/// `u = w` if needed. The new atoms allow short learnt clauses over derived equalities, which
/// resolution over the input atoms alone cannot always give.
#[derive(Default)]
struct DynTrans {
    /// The next free SAT variable, once enabled.
    next_var: Option<usize>,
    /// Hits per triangle `(min(u, w), v, max(u, w))`.
    hits: FxHashMap<(TermId, TermId, TermId), u32>,
    /// Triangles that reached the threshold, with their edge literals, awaiting level 0.
    ready: Vec<(TermId, TermId, Lit, Lit)>,
    /// How many lemmas have been instantiated (capped).
    made: usize,
    cap: usize,
    /// Set while a theory conflict is being explained; only those explanations score hits.
    collecting: bool,
}

impl DynTrans {
    const THRESHOLD: u32 = 32;
}

impl Default for Euf {
    fn default() -> Self {
        Euf::new()
    }
}

impl Euf {
    pub fn new() -> Euf {
        Euf {
            arena: TermArena::new(),
            repr: Vec::new(),
            size: Vec::new(),
            uses: Vec::new(),
            next: Vec::new(),
            class_diseqs: Vec::new(),
            proof_parent: Vec::new(),
            proof_reason: Vec::new(),
            sig: FxHashMap::default(),
            diseq: Vec::new(),
            atoms: Vec::new(),
            term_atoms: Vec::new(),
            assigned: Vec::new(),
            neg_witness: Vec::new(),
            implied: Vec::new(),
            conflict: None,
            pending: Vec::new(),
            stamp: Vec::new(),
            stamp_now: 0,
            trail: Vec::new(),
            levels: Vec::new(),
            registered: 0,
            atom_of: FxHashMap::default(),
            dyn_trans: DynTrans::default(),
        }
    }

    /// Let EUF add transitivity lemmas over fresh equality atoms, numbering their SAT variables
    /// from `next_var` up. Only for a caller that owns every variable from there on.
    pub fn enable_transitivity_lemmas(&mut self, next_var: usize) {
        let d = &mut self.dyn_trans;
        d.next_var = Some(next_var.max(d.next_var.unwrap_or(0)));
        d.cap = 2 * self.atom_of.len() + 1000;
    }

    /// The first SAT variable this theory has not allocated for its own atoms (0 if it
    /// allocates none).
    pub fn next_free_sat_var(&self) -> usize {
        self.dyn_trans.next_var.unwrap_or(0)
    }

    /// Build (and register) a 0-ary constant.
    pub fn mk_const(&mut self, name: &str) -> TermId {
        let id = self.arena.constant(name);
        self.register_terms(id);
        id
    }

    /// Build (and register) the application `name(args)`.
    pub fn mk_app(&mut self, name: &str, args: Vec<TermId>) -> TermId {
        let id = self.arena.func(name, args);
        self.register_terms(id);
        id
    }

    /// Tie SAT variable `var` to the equality atom `a = b`.
    pub fn register_eq_atom(&mut self, var: Var, a: TermId, b: TermId) {
        let vi = var.index();
        if vi >= self.atoms.len() {
            self.atoms.resize(vi + 1, None);
            self.assigned.resize(vi + 1, Lbool::Undef);
            self.neg_witness.resize(vi + 1, None);
        }
        debug_assert!(self.atoms[vi].is_none(), "atom variable registered twice");
        self.atoms[vi] = Some((a, b));
        self.atom_of
            .entry((a.min(b), a.max(b)))
            .or_insert(vi as u32);
        self.term_atoms[a.index()].push(vi as u32);
        if b != a {
            self.term_atoms[b.index()].push(vi as u32);
        }
        // Atoms are otherwise only examined when their classes change; one that is already
        // decided must be reported now.
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            self.implied.push((var.pos(), None));
        } else if let Some(d) = self.apart(ra, rb) {
            self.queue_false(vi, d);
        }
    }

    /// The terms of the equality atom on SAT variable `var`, if it is one.
    pub fn atom(&self, var: Var) -> Option<(TermId, TermId)> {
        self.atoms.get(var.index()).copied().flatten()
    }

    /// The term DAG (for reading terms back, e.g. to build a model).
    pub fn arena(&self) -> &TermArena {
        &self.arena
    }

    /// The representative of `t`'s congruence class in the current state. After a satisfiable
    /// solve, two terms are equal in the model iff they share a class.
    pub fn class_of(&self, t: TermId) -> TermId {
        self.find(t)
    }

    /// Add the e-graph state for `id`, the term just built in the arena (a no-op for a
    /// hash-consed existing term). Arguments are registered before their parent. Registration
    /// happens at level 0, so it is not trailed.
    fn register_terms(&mut self, id: TermId) {
        if id.index() < self.registered {
            return;
        }
        debug_assert_eq!(id.index(), self.registered, "terms registered in order");
        debug_assert!(
            self.levels.is_empty(),
            "terms must be registered before solving (no push active)"
        );

        self.repr.push(id);
        self.size.push(1);
        self.uses.push(Vec::new());
        self.next.push(id);
        self.class_diseqs.push(Vec::new());
        self.term_atoms.push(Vec::new());
        self.proof_parent.push(None);
        self.proof_reason.push(None);
        self.stamp.push(0);
        self.registered += 1;

        // A congruent application already in the table (its arguments were merged at level 0)
        // is merged right away.
        let args: Vec<TermId> = self.arena.args_of(id).to_vec();
        if !args.is_empty() {
            for &arg in &args {
                let r = self.find(arg);
                self.uses[r.index()].push(id);
            }
            let key = self.signature(id);
            match self.sig.get(&key) {
                Some(&other) => self.merge(id, other, Reason::Congruence(id, other)),
                None => {
                    self.sig.insert(key, id);
                }
            }
        }
    }

    /// The class representative. No path compression, so undo stays trivial; union by size
    /// keeps the walk short.
    #[inline]
    fn find(&self, mut t: TermId) -> TermId {
        while self.repr[t.index()] != t {
            t = self.repr[t.index()];
        }
        t
    }

    #[inline]
    fn signature(&self, app: TermId) -> Sig {
        let sym = self.arena.symbol_of(app);
        let args = self
            .arena
            .args_of(app)
            .iter()
            .map(|&a| self.find(a))
            .collect();
        (sym, args)
    }

    #[inline]
    fn set_repr(&mut self, i: usize, v: TermId) {
        self.trail.push(TrailOp::Repr(i, self.repr[i]));
        self.repr[i] = v;
    }
    #[inline]
    fn set_size(&mut self, i: usize, v: u32) {
        self.trail.push(TrailOp::Size(i, self.size[i]));
        self.size[i] = v;
    }

    #[inline]
    fn push_use(&mut self, i: usize, app: TermId) {
        self.uses[i].push(app);
        self.trail.push(TrailOp::UsePush(i));
    }

    #[inline]
    fn set_proof(&mut self, i: usize, parent: Option<TermId>, reason: Option<Reason>) {
        self.trail.push(TrailOp::Proof(
            i,
            self.proof_parent[i],
            self.proof_reason[i],
        ));
        self.proof_parent[i] = parent;
        self.proof_reason[i] = reason;
    }

    fn sig_set(&mut self, key: Sig, app: TermId) {
        match self.sig.insert(key.clone(), app) {
            Some(old) => self.trail.push(TrailOp::SigRestore(key, old)),
            None => self.trail.push(TrailOp::SigInsert(key)),
        }
    }

    fn sig_remove(&mut self, key: &Sig) {
        if let Some(old) = self.sig.remove(key) {
            self.trail.push(TrailOp::SigRestore(key.clone(), old));
        }
    }

    fn push_class_diseq(&mut self, root: usize, d: u32) {
        self.trail
            .push(TrailOp::ClassDiseqs(root, self.class_diseqs[root].len()));
        self.class_diseqs[root].push(d);
    }

    /// Assert the equality `a = b` with the given reason and run closure to a fixpoint.
    fn merge(&mut self, a: TermId, b: TermId, reason: Reason) {
        self.pending.push((a, b, reason));
        self.propagate_pending();
    }

    fn propagate_pending(&mut self) {
        while let Some((a, b, reason)) = self.pending.pop() {
            let ra = self.find(a);
            let rb = self.find(b);
            if ra == rb {
                continue;
            }

            // Union by size: attach the smaller class under the larger root.
            let (small, large) = if self.size[ra.index()] <= self.size[rb.index()] {
                (ra, rb)
            } else {
                (rb, ra)
            };

            // Add the proof edge a — b before changing union-find, re-rooting the proof tree
            // of the endpoint in the smaller class (the trees span exactly the classes).
            if small == ra {
                self.add_proof_edge(a, b, reason);
            } else {
                self.add_proof_edge(b, a, reason);
            }

            // Remove signatures of `small`'s use terms (their arg-reprs are about to change).
            let n_uses = self.uses[small.index()].len();
            for k in 0..n_uses {
                let app = self.uses[small.index()][k];
                let key = self.signature(app);
                self.sig_remove(&key);
            }

            // Re-root the union-find.
            self.set_repr(small.index(), large);
            let new_size = self.size[large.index()] + self.size[small.index()];
            self.set_size(large.index(), new_size);

            // Conflicts and newly decided atoms, while the member circles are still separate.
            if self.conflict.is_none() {
                self.scan_merge(small, large);
            }

            // Splice the member circles and hand `small`'s disequalities to `large`.
            self.next.swap(small.index(), large.index());
            self.trail
                .push(TrailOp::Splice(small.index(), large.index()));
            let n_diseqs = self.class_diseqs[small.index()].len();
            if n_diseqs > 0 {
                self.trail.push(TrailOp::ClassDiseqs(
                    large.index(),
                    self.class_diseqs[large.index()].len(),
                ));
                for k in 0..n_diseqs {
                    let d = self.class_diseqs[small.index()][k];
                    self.class_diseqs[large.index()].push(d);
                }
            }

            // Re-insert / reconcile signatures, moving use terms onto `large`.
            for k in 0..n_uses {
                let app = self.uses[small.index()][k];
                let key = self.signature(app);
                if let Some(&other) = self.sig.get(&key) {
                    // Congruent to an existing application: schedule a merge.
                    if other != app {
                        self.pending
                            .push((app, other, Reason::Congruence(app, other)));
                    }
                } else {
                    self.sig_set(key, app);
                }
                self.push_use(large.index(), app);
            }
        }
    }

    /// An asserted disequality separating the classes rooted at `x` and `y`, if any.
    fn apart(&self, x: TermId, y: TermId) -> Option<u32> {
        let (lx, ly) = (&self.class_diseqs[x.index()], &self.class_diseqs[y.index()]);
        let shorter = if lx.len() <= ly.len() { lx } else { ly };
        shorter.iter().copied().find(|&d| {
            let (p, q, _) = self.diseq[d as usize];
            let (rp, rq) = (self.find(p), self.find(q));
            (rp == x && rq == y) || (rp == y && rq == x)
        })
    }

    /// `small` was just attached under `large` (repr/size updated, member circles not yet
    /// spliced, `class_diseqs` not yet migrated). Record a violated disequality, or queue every
    /// atom the merge newly decides.
    fn scan_merge(&mut self, small: TermId, large: TermId) {
        // A disequality between the two classes sits on both lists; scan the shorter.
        let (ds, dl) = (small.index(), large.index());
        let shorter = if self.class_diseqs[ds].len() <= self.class_diseqs[dl].len() {
            ds
        } else {
            dl
        };
        for k in 0..self.class_diseqs[shorter].len() {
            let d = self.diseq[self.class_diseqs[shorter][k] as usize];
            if self.find(d.0) == self.find(d.1) {
                self.conflict = Some(d);
                return;
            }
        }

        // Atoms with an endpoint in `small`: true if the other endpoint is in `large`, false if
        // it lies in a class `large` was disequal to (classes `small` was disequal to were
        // handled when that disequality or merge happened).
        let mut large_apart: Option<FxHashMap<TermId, u32>> = None;
        let mut t = small;
        loop {
            for k in 0..self.term_atoms[t.index()].len() {
                let vi = self.term_atoms[t.index()][k] as usize;
                if self.assigned[vi] != Lbool::Undef {
                    continue;
                }
                let (a, b) = self.atoms[vi].expect("registered atom");
                let other = if a == t { b } else { a };
                let ro = self.find(other);
                if ro == large {
                    self.implied.push((Var::from_index(vi).pos(), None));
                    continue;
                }
                if self.class_diseqs[dl].is_empty() {
                    continue;
                }
                let apart = large_apart.get_or_insert_with(|| self.apart_roots(large));
                if let Some(&d) = apart.get(&ro) {
                    self.queue_false(vi, d);
                }
            }
            t = self.next[t.index()];
            if t == small {
                break;
            }
        }

        // Atoms between `large` and a class `small` was disequal to (but `large` was not) are
        // false now too.
        let mut done: Vec<TermId> = Vec::new();
        for k in 0..self.class_diseqs[ds].len() {
            let d = self.class_diseqs[ds][k];
            let (p, q, _) = self.diseq[d as usize];
            let (rp, rq) = (self.find(p), self.find(q));
            let other = if rp == large { rq } else { rp };
            if done.contains(&other) {
                continue;
            }
            done.push(other);
            // Skip a class `large` was already apart from: those atoms are decided.
            let apart = large_apart.get_or_insert_with(|| self.apart_roots(large));
            if !apart.contains_key(&other) {
                self.queue_false_between(large, other, d);
            }
        }
    }

    /// The roots of the classes separated from root `r`'s class (as it is listed in
    /// `class_diseqs[r]`), each with one witnessing disequality.
    fn apart_roots(&self, r: TermId) -> FxHashMap<TermId, u32> {
        let mut m = FxHashMap::default();
        for &d in &self.class_diseqs[r.index()] {
            let (p, q, _) = self.diseq[d as usize];
            let (rp, rq) = (self.find(p), self.find(q));
            m.entry(if rp == r { rq } else { rp }).or_insert(d);
        }
        m
    }

    /// Queue as false every unassigned atom joining the class of root `x` to the class of root
    /// `y`, witnessed by disequality `d`, by scanning the smaller class's members (during a
    /// merge, `x = large` still lists only its old members, which is exactly what is wanted).
    fn queue_false_between(&mut self, x: TermId, y: TermId, d: u32) {
        let (scan, target) = if self.size[y.index()] < self.size[x.index()] {
            (y, x)
        } else {
            (x, y)
        };
        let mut t = scan;
        loop {
            for k in 0..self.term_atoms[t.index()].len() {
                let vi = self.term_atoms[t.index()][k] as usize;
                if self.assigned[vi] != Lbool::Undef {
                    continue;
                }
                let (a, b) = self.atoms[vi].expect("registered atom");
                let other = if a == t { b } else { a };
                if self.find(other) == target {
                    self.queue_false(vi, d);
                }
            }
            t = self.next[t.index()];
            if t == scan {
                break;
            }
        }
    }

    /// Queue atom `vi` as false, witnessed by disequality `d`, oriented to the atom.
    fn queue_false(&mut self, vi: usize, d: u32) {
        let (a, _) = self.atoms[vi].expect("registered atom");
        let (p, q, l) = self.diseq[d as usize];
        let w = if self.find(a) == self.find(p) {
            (p, q, l)
        } else {
            (q, p, l)
        };
        self.implied.push((Var::from_index(vi).neg(), Some(w)));
    }

    /// Add an undirected proof edge `a — b` justified by `reason`, re-rooting `a`'s tree.
    fn add_proof_edge(&mut self, a: TermId, b: TermId, reason: Reason) {
        self.reroot_proof(a);
        self.set_proof(a.index(), Some(b), Some(reason));
    }

    /// Reverse the proof-forest path from `t` up to its root so that `t` becomes a root.
    fn reroot_proof(&mut self, t: TermId) {
        let mut prev: Option<(TermId, Reason)> = None;
        let mut cur = t;
        loop {
            let next = self.proof_parent[cur.index()];
            let next_reason = self.proof_reason[cur.index()];
            match prev {
                Some((p, r)) => self.set_proof(cur.index(), Some(p), Some(r)),
                None => {
                    if next.is_none() {
                        break; // already the root
                    }
                    self.set_proof(cur.index(), None, None)
                }
            }
            match (next, next_reason) {
                (Some(n), Some(r)) => {
                    prev = Some((cur, r));
                    cur = n;
                }
                _ => break,
            }
        }
    }

    /// The set of `Input` equality literals justifying `a ≡ b`, collected over the proof path.
    fn explain_eq(&mut self, a: TermId, b: TermId) -> Vec<Lit> {
        let mut out = Vec::new();
        let mut seen: FxHashSet<(TermId, TermId)> = FxHashSet::default();
        let mut work = vec![(a, b)];
        while let Some((x, y)) = work.pop() {
            if x == y {
                continue;
            }
            let lca = self.proof_lca(x, y);
            // The last input edge seen on each side's climb, `(far end, lit)`, for triangles.
            let mut last: [Option<(TermId, Lit)>; 2] = [None, None];
            for (side, start) in [x, y].into_iter().enumerate() {
                let mut cur = start;
                let mut prev: Option<(TermId, Lit)> = None;
                while cur != lca {
                    let parent = self.proof_parent[cur.index()];
                    match self.proof_reason[cur.index()] {
                        Some(Reason::Input(lit)) => {
                            out.push(lit);
                            if let (Some((u, l1)), Some(w)) = (prev, parent) {
                                self.triangle_hit(u, cur, w, l1, lit);
                            }
                            prev = Some((cur, lit));
                            if parent == Some(lca) {
                                last[side] = prev;
                            }
                            cur = parent.expect("path to the common ancestor");
                            continue;
                        }
                        Some(Reason::Congruence(app1, app2)) => {
                            let args1 = self.arena.args_of(app1);
                            let args2 = self.arena.args_of(app2);
                            for (&a1, &a2) in args1.iter().zip(args2) {
                                if a1 != a2 && seen.insert((a1.min(a2), a1.max(a2))) {
                                    work.push((a1, a2));
                                }
                            }
                        }
                        None => debug_assert!(false, "proof edge without reason"),
                    }
                    prev = None;
                    cur = parent.expect("path to the common ancestor");
                }
            }
            if let [Some((u, l1)), Some((w, l2))] = last {
                self.triangle_hit(u, lca, w, l1, l2);
            }
        }
        out.sort_by_key(|l| l.code());
        out.dedup();
        out
    }

    /// Input edges `u — v` (literal `l1`) and `v — w` (`l2`) were adjacent on an explanation.
    fn triangle_hit(&mut self, u: TermId, v: TermId, w: TermId, l1: Lit, l2: Lit) {
        let d = &mut self.dyn_trans;
        if !d.collecting || d.next_var.is_none() || d.made >= d.cap || u == w {
            return;
        }
        let h = d.hits.entry((u.min(w), v, u.max(w))).or_insert(0);
        *h += 1;
        if *h == DynTrans::THRESHOLD {
            d.ready.push((u, w, l1, l2));
            d.made += 1;
        }
    }

    /// The lowest common ancestor of `a` and `b` in the proof forest. Both must be in the same
    /// proof tree (guaranteed when `find(a) == find(b)`).
    fn proof_lca(&mut self, a: TermId, b: TermId) -> TermId {
        self.stamp_now = self.stamp_now.wrapping_add(1);
        if self.stamp_now == 0 {
            self.stamp.iter_mut().for_each(|s| *s = 0);
            self.stamp_now = 1;
        }
        let now = self.stamp_now;
        let mut x = a;
        loop {
            self.stamp[x.index()] = now;
            match self.proof_parent[x.index()] {
                Some(p) => x = p,
                None => break,
            }
        }
        let mut y = b;
        while self.stamp[y.index()] != now {
            y = self.proof_parent[y.index()].expect("terms not in same proof tree");
        }
        y
    }
}

impl Theory for Euf {
    fn assert(&mut self, lit: Lit) {
        let vi = lit.var().index();
        let (a, b) = match self.atoms.get(vi).copied().flatten() {
            Some(p) => p,
            None => return, // not a theory atom we know about
        };
        self.trail.push(TrailOp::Assigned(vi, self.assigned[vi]));
        self.assigned[vi] = Lbool::from_bool(!lit.is_negated());
        if lit.is_negated() {
            // Disequality a != b.
            let d = self.diseq.len() as u32;
            self.diseq.push((a, b, lit));
            self.trail.push(TrailOp::DiseqPush);
            let (ra, rb) = (self.find(a), self.find(b));
            if ra == rb {
                if self.conflict.is_none() {
                    self.conflict = Some((a, b, lit));
                }
                return;
            }
            // Atoms between the classes are decided already if they were apart before.
            let fresh = self.conflict.is_none() && self.apart(ra, rb).is_none();
            self.push_class_diseq(ra.index(), d);
            self.push_class_diseq(rb.index(), d);
            if fresh {
                self.queue_false_between(ra, rb, d);
            }
        } else {
            // Equality a = b.
            self.merge(a, b, Reason::Input(lit));
        }
    }

    fn check(&mut self, _complete: bool) -> Result<(), Vec<Lit>> {
        let Some((a, b, neg_lit)) = self.conflict else {
            return Ok(());
        };
        // a = b follows from the input equalities, yet a != b was asserted.
        self.dyn_trans.collecting = true;
        let mut clause: Vec<Lit> = self.explain_eq(a, b).into_iter().map(|l| !l).collect();
        self.dyn_trans.collecting = false;
        clause.push(!neg_lit);
        clause.sort_by_key(|l| l.code());
        clause.dedup();
        Err(clause)
    }

    fn propagate(&mut self) -> Vec<Lit> {
        // Hand out the atoms the closure decided since the last call (explanations are
        // reconstructed lazily in `explain`). With a conflict pending, nothing: `check` reports
        // it next and the solver backtracks.
        if self.conflict.is_some() {
            self.implied.clear();
            return Vec::new();
        }
        let mut out = Vec::with_capacity(self.implied.len());
        for (lit, witness) in std::mem::take(&mut self.implied) {
            let vi = lit.var().index();
            if self.assigned[vi] != Lbool::Undef {
                continue;
            }
            if lit.is_negated() {
                self.neg_witness[vi] = witness;
            }
            out.push(lit);
        }
        #[cfg(debug_assertions)]
        if out.is_empty() {
            self.debug_check_fixpoint();
        }
        out
    }

    fn explain(&mut self, lit: Lit) -> Vec<Lit> {
        let vi = lit.var().index();
        let (a, b) = self.atoms[vi].expect("explain on a non-atom literal");
        let mut clause = vec![lit];
        if lit.is_negated() {
            // a ≡ p, b ≡ q and p != q.
            let (p, q, neg_lit) =
                self.neg_witness[vi].expect("missing negative-propagation witness");
            for e in self.explain_eq(a, p) {
                clause.push(!e);
            }
            for e in self.explain_eq(b, q) {
                clause.push(!e);
            }
            clause.push(!neg_lit);
        } else {
            for e in self.explain_eq(a, b) {
                clause.push(!e);
            }
        }
        clause.sort_by_key(|l| l.code());
        clause.dedup();
        clause
    }

    fn push(&mut self) {
        self.levels.push(self.trail.len());
    }

    fn lemmas(&mut self) -> Vec<Vec<Lit>> {
        // New atoms are registered only at level 0, where nothing they imply can be lost to a
        // backtrack before `propagate` hands it out.
        if !self.levels.is_empty() || self.dyn_trans.ready.is_empty() {
            return Vec::new();
        }
        let mut out = Vec::new();
        for (u, w, l1, l2) in std::mem::take(&mut self.dyn_trans.ready) {
            let var = match self.atom_of.get(&(u.min(w), u.max(w))) {
                Some(&v) => Var::from_index(v as usize),
                None => {
                    let next = self.dyn_trans.next_var.as_mut().expect("enabled");
                    let v = Var::from_index(*next);
                    *next += 1;
                    self.register_eq_atom(v, u.min(w), u.max(w));
                    v
                }
            };
            out.push(vec![!l1, !l2, var.pos()]);
        }
        out
    }

    fn pop(&mut self, levels: usize) {
        for _ in 0..levels {
            let mark = self.levels.pop().expect("pop below level 0");
            while self.trail.len() > mark {
                let op = self.trail.pop().unwrap();
                self.undo(op);
            }
        }
        if levels > 0 {
            // Both were found at the level just left (the solver drains `implied` and checks
            // before every decision).
            self.implied.clear();
            self.conflict = None;
        }
    }
}

impl Euf {
    /// Debug builds: with nothing left to propagate, no unassigned atom may be decided by the
    /// closure, and a violated disequality must have been noticed.
    #[cfg(debug_assertions)]
    fn debug_check_fixpoint(&self) {
        let mut apart = FxHashSet::default();
        for &(p, q, _) in &self.diseq {
            let (rp, rq) = (self.find(p), self.find(q));
            assert!(rp != rq, "violated disequality not recorded");
            apart.insert((rp.min(rq), rp.max(rq)));
        }
        for (vi, atom) in self.atoms.iter().enumerate() {
            let Some((a, b)) = *atom else { continue };
            if self.assigned[vi] != Lbool::Undef {
                continue;
            }
            let (ra, rb) = (self.find(a), self.find(b));
            assert!(ra != rb, "atom {vi} implied true but not propagated");
            assert!(
                !apart.contains(&(ra.min(rb), ra.max(rb))),
                "atom {vi} implied false but not propagated"
            );
        }
    }

    fn undo(&mut self, op: TrailOp) {
        match op {
            TrailOp::Repr(i, old) => self.repr[i] = old,
            TrailOp::Size(i, old) => self.size[i] = old,
            TrailOp::UsePush(i) => {
                self.uses[i].pop();
            }
            TrailOp::SigInsert(key) => {
                self.sig.remove(&key);
            }
            TrailOp::SigRestore(key, old) => {
                self.sig.insert(key, old);
            }
            TrailOp::Proof(i, p, r) => {
                self.proof_parent[i] = p;
                self.proof_reason[i] = r;
            }
            TrailOp::DiseqPush => {
                self.diseq.pop();
            }
            TrailOp::ClassDiseqs(i, len) => {
                self.class_diseqs[i].truncate(len);
            }
            TrailOp::Splice(i, j) => {
                self.next.swap(i, j);
            }
            TrailOp::Assigned(vi, old) => {
                self.assigned[vi] = old;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    /// An `Euf` plus the current partial assignment, to check that conflict clauses are false.
    struct Harness {
        euf: Euf,
        next_var: usize,
        assign: HashMap<usize, bool>,
    }

    impl Harness {
        fn new() -> Harness {
            Harness {
                euf: Euf::new(),
                next_var: 0,
                assign: HashMap::new(),
            }
        }
        fn c(&mut self, name: &str) -> TermId {
            self.euf.mk_const(name)
        }
        fn f(&mut self, name: &str, args: Vec<TermId>) -> TermId {
            self.euf.mk_app(name, args)
        }
        /// Allocate a fresh equality-atom variable for `a = b`.
        fn atom(&mut self, a: TermId, b: TermId) -> Var {
            let v = Var::from_index(self.next_var);
            self.next_var += 1;
            self.euf.register_eq_atom(v, a, b);
            v
        }
        /// Assert a literal and remember its truth value.
        fn assert(&mut self, lit: Lit) {
            self.assign.insert(lit.var().index(), !lit.is_negated());
            self.euf.assert(lit);
        }
        /// True iff `lit` is currently assigned FALSE.
        fn is_false(&self, lit: Lit) -> bool {
            match self.assign.get(&lit.var().index()) {
                Some(&val) => val == lit.is_negated(),
                None => false,
            }
        }
        fn check(&mut self) -> Result<(), Vec<Lit>> {
            self.euf.check(true)
        }
        fn assert_clause_all_false(&self, clause: &[Lit]) {
            for &l in clause {
                assert!(
                    self.is_false(l),
                    "clause literal {:?} (var {}) is not currently false; assign={:?}",
                    l,
                    l.var().index(),
                    self.assign
                );
            }
        }
    }

    #[test]
    fn direct_congruence_conflict() {
        // a = b  =>  f(a) = f(b); assert f(a) != f(b) => conflict.
        let mut h = Harness::new();
        let a = h.c("a");
        let b = h.c("b");
        let fa = h.f("f", vec![a]);
        let fb = h.f("f", vec![b]);

        let eq_ab = h.atom(a, b);
        let eq_fafb = h.atom(fa, fb);

        h.assert(eq_ab.pos()); // a = b
        h.assert(eq_fafb.neg()); // f(a) != f(b)

        let conflict = h.check().expect_err("expected a conflict");
        h.assert_clause_all_false(&conflict);
        // Clause should contain ¬(a=b) and the positive atom f(a)=f(b).
        assert!(conflict.contains(&eq_ab.neg()));
        assert!(conflict.contains(&eq_fafb.pos()));
    }

    #[test]
    fn transitive_congruence_conflict() {
        // a=b, c=d, b=d, f(a) != f(c) => conflict.
        let mut h = Harness::new();
        let a = h.c("a");
        let b = h.c("b");
        let cc = h.c("c");
        let d = h.c("d");
        let fa = h.f("f", vec![a]);
        let fc = h.f("f", vec![cc]);

        let eq_ab = h.atom(a, b);
        let eq_cd = h.atom(cc, d);
        let eq_bd = h.atom(b, d);
        let eq_fafc = h.atom(fa, fc);

        h.assert(eq_ab.pos());
        h.assert(eq_cd.pos());
        h.assert(eq_bd.pos());
        h.assert(eq_fafc.neg());

        let conflict = h.check().expect_err("expected a conflict");
        h.assert_clause_all_false(&conflict);
        assert!(conflict.contains(&eq_fafc.pos()));
        // a..c equality chain needs a=b, b=d, c=d.
        assert!(conflict.contains(&eq_ab.neg()));
        assert!(conflict.contains(&eq_bd.neg()));
        assert!(conflict.contains(&eq_cd.neg()));
    }

    #[test]
    fn sat_case_no_conflict() {
        // a=b, f(a) != f(c) => no conflict.
        let mut h = Harness::new();
        let a = h.c("a");
        let b = h.c("b");
        let cc = h.c("c");
        let fa = h.f("f", vec![a]);
        let fc = h.f("f", vec![cc]);

        let eq_ab = h.atom(a, b);
        let eq_fafc = h.atom(fa, fc);

        h.assert(eq_ab.pos());
        h.assert(eq_fafc.neg());

        assert!(h.check().is_ok(), "should be satisfiable");
    }

    #[test]
    fn push_pop_basic() {
        // assert a=b at level 0; push; assert a!=b -> conflict; pop(1); assert a=c consistent.
        let mut h = Harness::new();
        let a = h.c("a");
        let b = h.c("b");
        let cc = h.c("c");

        let eq_ab = h.atom(a, b);
        let neq_ab = h.atom(a, b); // separate atom var also for a=b
        let eq_ac = h.atom(a, cc);

        h.assert(eq_ab.pos());
        assert!(h.check().is_ok());

        h.euf.push();
        h.assert(neq_ab.neg()); // a != b, contradicts a = b
        let conflict = h.check().expect_err("expected conflict under push");
        h.assert_clause_all_false(&conflict);

        h.euf.pop(1);
        // The level-1 disequality is undone. a=c is consistent with a=b.
        h.assert(eq_ac.pos());
        assert!(h.check().is_ok(), "after pop, a=c should be consistent");
    }

    #[test]
    fn push_pop_state_restored_across_cycles() {
        // Verify find/merge state is restored across several push/pop cycles.
        let mut h = Harness::new();
        let a = h.c("a");
        let b = h.c("b");
        let cc = h.c("c");
        let fa = h.f("f", vec![a]);
        let fc = h.f("f", vec![cc]);

        let eq_ab = h.atom(a, b);
        let eq_bc = h.atom(b, cc);
        let eq_fafc = h.atom(fa, fc);

        // Baseline: nothing equal.
        assert_ne!(h.euf.find(a), h.euf.find(b));

        for _ in 0..5 {
            h.euf.push();
            h.assert(eq_ab.pos());
            assert_eq!(h.euf.find(a), h.euf.find(b));
            // f(a) and f(c) not yet equal.
            assert_ne!(h.euf.find(fa), h.euf.find(fc));

            h.euf.push();
            h.assert(eq_bc.pos());
            // Now a=b=c, so by congruence f(a)=f(c).
            assert_eq!(h.euf.find(a), h.euf.find(cc));
            assert_eq!(h.euf.find(fa), h.euf.find(fc));

            // f(a) != f(c) must now conflict.
            h.assert(eq_fafc.neg());
            let conflict = h.check().expect_err("congruence conflict");
            h.assert_clause_all_false(&conflict);

            h.euf.pop(2);
            // Fully restored to baseline.
            assert_ne!(h.euf.find(a), h.euf.find(b));
            assert_ne!(h.euf.find(b), h.euf.find(cc));
            assert_ne!(h.euf.find(fa), h.euf.find(fc));
            // assignment record cleared for popped vars (so harness stays consistent)
            h.assign.remove(&eq_ab.pos().var().index());
            h.assign.remove(&eq_bc.pos().var().index());
            h.assign.remove(&eq_fafc.pos().var().index());
        }
    }

    /// Brute-force reference: maintain explicit equalities, compute their congruence closure by
    /// fixpoint, and report whether any asserted disequality is violated.
    struct Reference {
        nconsts: usize,
        // terms: 0..nconsts are constants; nconsts..2*nconsts are f(const_i).
        eqs: Vec<(usize, usize)>,
        diseqs: Vec<(usize, usize)>,
    }
    impl Reference {
        fn nterms(&self) -> usize {
            2 * self.nconsts
        }
        fn fof(&self, i: usize) -> usize {
            // f(const i) lives at nconsts + i (only defined for constants here)
            self.nconsts + i
        }
        /// Returns true iff consistent (no asserted diseq is implied equal).
        fn consistent(&self) -> bool {
            let n = self.nterms();
            // union-find
            let mut parent: Vec<usize> = (0..n).collect();
            fn find(p: &mut [usize], mut x: usize) -> usize {
                while p[x] != x {
                    p[x] = p[p[x]];
                    x = p[x];
                }
                x
            }
            fn union(p: &mut [usize], a: usize, b: usize) {
                let ra = find(p, a);
                let rb = find(p, b);
                if ra != rb {
                    p[ra] = rb;
                }
            }
            for &(a, b) in &self.eqs {
                union(&mut parent, a, b);
            }
            // congruence fixpoint: if const i == const j then f(i) == f(j)
            loop {
                let mut changed = false;
                for i in 0..self.nconsts {
                    for j in (i + 1)..self.nconsts {
                        if find(&mut parent, i) == find(&mut parent, j) {
                            let fi = self.fof(i);
                            let fj = self.fof(j);
                            if find(&mut parent, fi) != find(&mut parent, fj) {
                                union(&mut parent, fi, fj);
                                changed = true;
                            }
                        }
                    }
                }
                if !changed {
                    break;
                }
            }
            for &(a, b) in &self.diseqs {
                if find(&mut parent, a) == find(&mut parent, b) {
                    return false;
                }
            }
            true
        }
    }

    /// Xorshift, for reproducible tests.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    #[test]
    fn fuzz_against_reference() {
        const NCONSTS: usize = 4;
        let mut rng = Rng(0x9E3779B97F4A7C15);

        for _trial in 0..400 {
            let mut h = Harness::new();
            // constants
            let consts: Vec<TermId> = (0..NCONSTS).map(|i| h.c(&format!("c{i}"))).collect();
            // f(c_i)
            let fconsts: Vec<TermId> = (0..NCONSTS).map(|i| h.f("f", vec![consts[i]])).collect();

            // Build a flat list of terms matching the reference numbering.
            let term_of = |idx: usize| -> TermId {
                if idx < NCONSTS {
                    consts[idx]
                } else {
                    fconsts[idx - NCONSTS]
                }
            };

            let nterms = 2 * NCONSTS;
            let mut reference = Reference {
                nconsts: NCONSTS,
                eqs: Vec::new(),
                diseqs: Vec::new(),
            };

            let nassert = 3 + rng.below(8);
            for _ in 0..nassert {
                let i = rng.below(nterms);
                let mut j = rng.below(nterms);
                while j == i {
                    j = rng.below(nterms);
                }
                let positive = rng.below(2) == 0;
                let ti = term_of(i);
                let tj = term_of(j);
                let v = h.atom(ti, tj);
                if positive {
                    reference.eqs.push((i, j));
                    h.assert(v.pos());
                } else {
                    reference.diseqs.push((i, j));
                    h.assert(v.neg());
                }
                // After each assertion, cross-check verdicts.
                let verdict = h.check();
                let euf_ok = verdict.is_ok();
                let ref_ok = reference.consistent();
                assert_eq!(
                    euf_ok, ref_ok,
                    "verdict mismatch: euf_ok={euf_ok} ref_ok={ref_ok}\n eqs={:?} diseqs={:?}",
                    reference.eqs, reference.diseqs
                );
                if let Err(clause) = verdict {
                    // Validate the conflict clause is all-false, then stop (in a real solver
                    // the SAT layer would backtrack past this inconsistent assignment).
                    h.assert_clause_all_false(&clause);
                    break;
                }
            }
        }
    }
}
