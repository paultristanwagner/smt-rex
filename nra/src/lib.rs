//! Nonlinear real arithmetic (QF_NRA) for SMT-Rex.
//!
//! - [`covering`]: cylindrical algebraic coverings, the default decision procedure for
//!   conjunctions of polynomial sign conditions, with small unsatisfiable cores.
//! - [`cad`]: the full cylindrical algebraic decomposition (Hong's projection, exact real
//!   algebraic samples), also used as a test oracle for the coverings.
//! - [`theory`]: the DPLL(T) theory solver [`Nra`] that decides the asserted atoms with them.
//!
//! The exact kernels (signs at real algebraic points, root isolation over them) live in
//! [`smtrex_poly::point`].

pub mod cad;
pub mod covering;
pub mod theory;

pub use theory::{AtomKind, Nra};
