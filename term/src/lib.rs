//! Hash-consed term DAG for the (uninterpreted-function) fragment.
//!
//! Every distinct term gets a stable [`TermId`]; structurally-equal terms share one id, so term
//! equality is `id == id` and there is no `Rc`/identity-map machinery. A term is an uninterpreted
//! function application `f(t1, …, tn)`; a constant is the 0-ary case `c()`.

use rustc_hash::FxHashMap;
use smtrex_core::{Interner, Symbol};

/// A hash-consed term, identified by a dense 0-based index into the [`TermArena`].
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct TermId(u32);

impl TermId {
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// The id of the `i`-th term built in an arena (`0 <= i < num_terms()`).
    #[inline]
    pub fn from_index(i: usize) -> TermId {
        TermId(i as u32)
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct Node {
    func: Symbol,
    args: Vec<TermId>,
}

#[derive(Default)]
pub struct TermArena {
    nodes: Vec<Node>,
    dedup: FxHashMap<Node, TermId>,
    interner: Interner,
}

impl TermArena {
    pub fn new() -> TermArena {
        TermArena::default()
    }

    /// Intern a function-symbol name.
    pub fn sym(&mut self, name: &str) -> Symbol {
        self.interner.intern(name)
    }

    /// Hash-cons `f(args)`.
    pub fn app(&mut self, func: Symbol, args: Vec<TermId>) -> TermId {
        let node = Node { func, args };
        if let Some(&id) = self.dedup.get(&node) {
            return id;
        }
        let id = TermId(self.nodes.len() as u32);
        self.nodes.push(node.clone());
        self.dedup.insert(node, id);
        id
    }

    /// Convenience: `f(args)` by name.
    pub fn func(&mut self, name: &str, args: Vec<TermId>) -> TermId {
        let f = self.sym(name);
        self.app(f, args)
    }

    /// A 0-ary constant by name.
    pub fn constant(&mut self, name: &str) -> TermId {
        self.func(name, Vec::new())
    }

    #[inline]
    pub fn symbol_of(&self, id: TermId) -> Symbol {
        self.nodes[id.index()].func
    }
    #[inline]
    pub fn args_of(&self, id: TermId) -> &[TermId] {
        &self.nodes[id.index()].args
    }
    #[inline]
    pub fn num_terms(&self) -> usize {
        self.nodes.len()
    }
    pub fn name_of(&self, id: TermId) -> &str {
        self.interner.resolve(self.nodes[id.index()].func)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn hash_consing_shares_structure() {
        let mut a = TermArena::new();
        let x = a.constant("x");
        let y = a.constant("y");
        let fx1 = a.func("f", vec![x, y]);
        let fx2 = a.func("f", vec![x, y]);
        let fy = a.func("f", vec![y, x]);
        assert_eq!(fx1, fx2); // identical terms share an id
        assert_ne!(fx1, fy); // argument order matters
        assert_ne!(x, y);
        assert_eq!(a.args_of(fx1), &[x, y]);
        assert_eq!(a.name_of(fx1), "f");
        // x reused, y reused, f(x,y), f(y,x) => 4 distinct terms
        assert_eq!(a.num_terms(), 4);
    }
}
