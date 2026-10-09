//! The solver-facing theory interface for DPLL(T).
//!
//! A [`Theory`] tracks the theory atoms whose boolean literals the SAT solver assigns, reports
//! theory conflicts (as clauses to learn), propagates theory-implied literals, explains them
//! lazily, and supports `push`/`pop` aligned with the solver's decision levels.

use crate::Lit;

pub trait Theory {
    /// An atom literal was just assigned by the SAT solver. `lit` carries the polarity: a
    /// positive `lit` asserts the atom, a negated `lit` asserts its negation.
    fn assert(&mut self, lit: Lit);

    /// Check theory consistency of the literals asserted so far. `complete` is true when the
    /// boolean assignment is total. Returns `Err(clause)` on a conflict, where `clause` is a
    /// disjunction of literals that is currently entirely false (a valid theory lemma to learn).
    fn check(&mut self, complete: bool) -> Result<(), Vec<Lit>>;

    /// Literals implied true by the theory under the current partial assignment (theory
    /// propagation). The solver enqueues them with this theory as the reason.
    fn propagate(&mut self) -> Vec<Lit>;

    /// Lazy reason for a previously theory-propagated literal `lit`: a clause that currently
    /// asserts `lit` (i.e. `lit` together with the negations of its antecedents).
    fn explain(&mut self, lit: Lit) -> Vec<Lit>;

    /// Enter a new backtracking level (one per solver decision level).
    fn push(&mut self);

    /// Backtrack `levels` levels, undoing everything asserted since.
    fn pop(&mut self, levels: usize);

    /// Clauses the theory wants added to the search, polled after every successful `check`.
    /// They must be valid in the theory (e.g. a branch-and-bound split `x ≤ 2 ∨ x ≥ 3`) and may
    /// use SAT variables the solver has not seen yet; it grows to fit. While a theory still has
    /// lemmas to add, the solver does not report SAT.
    fn lemmas(&mut self) -> Vec<Vec<Lit>> {
        Vec::new()
    }
}

/// The trivial theory: every assignment is consistent (plain SAT solving).
pub struct NoTheory;

impl Theory for NoTheory {
    #[inline]
    fn assert(&mut self, _lit: Lit) {}
    #[inline]
    fn check(&mut self, _complete: bool) -> Result<(), Vec<Lit>> {
        Ok(())
    }
    #[inline]
    fn propagate(&mut self) -> Vec<Lit> {
        Vec::new()
    }
    #[inline]
    fn explain(&mut self, _lit: Lit) -> Vec<Lit> {
        Vec::new()
    }
    #[inline]
    fn push(&mut self) {}
    #[inline]
    fn pop(&mut self, _levels: usize) {}
}
