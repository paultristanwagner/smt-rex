//! EUF lemmas re-derived by a congruence closure of their own, as `eq_transitive` and
//! `eq_congruent` steps.

use crate::sexp::quote_symbol;
use rustc_hash::{FxHashMap, FxHashSet};

use smtrex_term::TermId;

/// How an EUF node is written in the proof: a constant by its symbol, an application by the
/// name `@t<index>` it is defined under.
pub(super) fn node_text(arena: &smtrex_term::TermArena, t: TermId) -> String {
    if arena.args_of(t).is_empty() {
        quote_symbol(arena.name_of(t)).into_owned()
    } else {
        format!("@t{}", t.index())
    }
}

// ----- re-deriving EUF lemmas -----

#[derive(Clone, Copy)]
pub(super) enum Edge {
    Premise(usize),
    Congruence,
}

/// A congruence closure over the subterms of one lemma, with a proof forest.
pub(super) struct Closure {
    pub(super) repr: FxHashMap<TermId, TermId>,
    pub(super) parent: FxHashMap<TermId, (TermId, Edge)>,
}

impl Closure {
    /// The closure of `premises` over their subterms and those of `goal`.
    pub(super) fn new(
        arena: &smtrex_term::TermArena,
        premises: &[(TermId, TermId, String)],
        goal: [TermId; 2],
    ) -> Closure {
        let mut cc = Closure {
            repr: FxHashMap::default(),
            parent: FxHashMap::default(),
        };
        let mut apps = Vec::new();
        let mut seen = FxHashSet::default();
        let mut stack: Vec<TermId> = premises.iter().flat_map(|&(a, b, _)| [a, b]).collect();
        stack.extend(goal);
        while let Some(t) = stack.pop() {
            if seen.insert(t) {
                if !arena.args_of(t).is_empty() {
                    apps.push(t);
                }
                stack.extend(arena.args_of(t));
            }
        }
        for (i, &(a, b, _)) in premises.iter().enumerate() {
            cc.merge(a, b, Edge::Premise(i));
        }
        // Congruence to a fixpoint: applications with the same symbol and argument classes
        // are merged, one signature table per round.
        loop {
            let mut table: FxHashMap<(smtrex_core::Symbol, Vec<TermId>), TermId> =
                FxHashMap::default();
            let mut merges = Vec::new();
            for &x in &apps {
                let sig = (
                    arena.symbol_of(x),
                    arena.args_of(x).iter().map(|&a| cc.find(a)).collect(),
                );
                match table.get(&sig) {
                    Some(&y) if cc.find(y) != cc.find(x) => merges.push((x, y)),
                    Some(_) => {}
                    None => {
                        table.insert(sig, x);
                    }
                }
            }
            if merges.is_empty() {
                break;
            }
            for (x, y) in merges {
                cc.merge(x, y, Edge::Congruence);
            }
        }
        cc
    }

    pub(super) fn find(&mut self, t: TermId) -> TermId {
        let mut r = t;
        while let Some(&p) = self.repr.get(&r) {
            r = p;
        }
        r
    }

    pub(super) fn merge(&mut self, a: TermId, b: TermId, e: Edge) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return;
        }
        self.repr.insert(ra, rb);
        // Re-root a's proof tree at a, then hang it below b.
        let mut prev: Option<(TermId, Edge)> = None;
        let mut cur = a;
        loop {
            let next = self.parent.remove(&cur);
            if let Some(p) = prev {
                self.parent.insert(cur, p);
            }
            match next {
                Some((n, edge)) => {
                    prev = Some((cur, edge));
                    cur = n;
                }
                None => break,
            }
        }
        self.parent.insert(a, (b, e));
    }

    /// The proof-forest path from `x` to `y` as oriented edges `(from, to, edge)`.
    pub(super) fn path(&self, x: TermId, y: TermId) -> Vec<(TermId, TermId, Edge)> {
        let up = |mut t: TermId| {
            let mut v = vec![t];
            while let Some(&(p, _)) = self.parent.get(&t) {
                t = p;
                v.push(t);
            }
            v
        };
        let (px, py) = (up(x), up(y));
        let on_x: FxHashSet<TermId> = px.iter().copied().collect();
        let lca = *py.iter().find(|t| on_x.contains(t)).expect("same tree");
        let mut out = Vec::new();
        let mut t = x;
        while t != lca {
            let (p, e) = self.parent[&t];
            out.push((t, p, e));
            t = p;
        }
        let mut back = Vec::new();
        let mut t = y;
        while t != lca {
            let (p, e) = self.parent[&t];
            back.push((p, t, e));
            t = p;
        }
        out.extend(back.into_iter().rev());
        out
    }
}

/// How an equality is established inside a lemma proof.
#[derive(Clone)]
pub(super) enum Proved {
    /// It is a premise, written `text`.
    Premise(String),
    /// Step `name` concludes it, written `text`.
    Step(String, String),
}

impl Proved {
    pub(super) fn text(&self) -> &str {
        match self {
            Proved::Premise(t) | Proved::Step(_, t) => t,
        }
    }
}

pub(super) struct LemmaWriter<'c> {
    pub(super) cc: &'c mut Closure,
    pub(super) arena: &'c smtrex_term::TermArena,
    /// The text of each premise.
    pub(super) premises: Vec<String>,
    pub(super) prefix: String,
    /// The steps written, in the order they were finished: `(name, clause literals, line)`.
    pub(super) steps: Vec<(String, Vec<String>, String)>,
    pub(super) memo: FxHashMap<(TermId, TermId), Proved>,
    /// The premises the proof uses.
    pub(super) used: FxHashSet<usize>,
}

impl LemmaWriter<'_> {
    pub(super) fn eq_text(&self, x: TermId, y: TermId) -> String {
        format!(
            "(= {} {})",
            node_text(self.arena, x),
            node_text(self.arena, y)
        )
    }

    pub(super) fn step(&mut self, lits: Vec<String>, rule: &str) -> String {
        let name = format!("{}{}", self.prefix, self.steps.len());
        let line = format!("(step {name} (cl {}) :rule {rule})\n", lits.join(" "));
        self.steps.push((name.clone(), lits, line));
        name
    }

    /// Establish `x = y` (in this orientation unless it is a premise, whose own orientation
    /// the tautology rules accept).
    pub(super) fn prove(&mut self, x: TermId, y: TermId) -> Proved {
        if let Some(p) = self.memo.get(&(x, y)) {
            return p.clone();
        }
        let goal = self.eq_text(x, y);
        let proved = if x == y {
            let name = self.step(vec![goal.clone()], "eq_reflexive");
            Proved::Step(name, goal)
        } else {
            let path = self.cc.path(x, y);
            if let [(u, v, e)] = path[..] {
                self.edge(u, v, e)
            } else {
                let links: Vec<Proved> = path.iter().map(|&(u, v, e)| self.edge(u, v, e)).collect();
                let mut lits: Vec<String> = links
                    .iter()
                    .map(|l| format!("(not {})", l.text()))
                    .collect();
                lits.push(goal.clone());
                let name = self.step(lits, "eq_transitive");
                Proved::Step(name, goal)
            }
        };
        self.memo.insert((x, y), proved.clone());
        proved
    }

    pub(super) fn edge(&mut self, u: TermId, v: TermId, e: Edge) -> Proved {
        match e {
            Edge::Premise(i) => {
                self.used.insert(i);
                Proved::Premise(self.premises[i].clone())
            }
            Edge::Congruence => {
                let (au, av) = (
                    self.arena.args_of(u).to_vec(),
                    self.arena.args_of(v).to_vec(),
                );
                let mut negs = Vec::new();
                // Carcara wants one premise per argument position, identical ones included
                // (those are discharged by eq_reflexive).
                for (p, q) in au.into_iter().zip(av) {
                    let a = self.prove(p, q);
                    negs.push(format!("(not {})", a.text()));
                }
                let goal = self.eq_text(u, v);
                negs.push(goal.clone());
                let name = self.step(negs, "eq_congruent");
                Proved::Step(name, goal)
            }
        }
    }
}
