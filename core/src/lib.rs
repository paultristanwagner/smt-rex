//! Shared primitives for the solver: literals, three-valued logic, string interning, exact
//! rational arithmetic and the DPLL(T) theory interface.

pub mod interner;
pub mod lit;
pub mod rational;
pub mod theory;

pub use interner::{Interner, Symbol};
pub use lit::{Lbool, Lit, Var};
pub use rational::{DeltaRational, Rational};
pub use theory::{NoTheory, Theory};
