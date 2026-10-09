//! Theory solvers implementing [`smtrex_core::Theory`].
//!
//! - [`euf::Euf`]: equality with uninterpreted functions (congruence closure), QF_UF / QF_EQ.
//! - [`lra::Lra`]: linear real arithmetic (incremental general Simplex), QF_LRA.

pub mod euf;
pub mod lra;

pub use euf::Euf;
pub use lra::Lra;
