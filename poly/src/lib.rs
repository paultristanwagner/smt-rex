//! Exact polynomial algebra for SMT-Rex's nonlinear real arithmetic.
//!
//! Everything is exact (arbitrary-precision integers and rationals), and each algorithm is a
//! textbook one named in its doc comment.
//!
//! - [`UPoly`] / [`QPoly`]: dense univariate polynomials over `Z` and `Q` — arithmetic, Euclidean
//!   and pseudo-division, content, gcd (subresultant PRS), Yun square-free decomposition,
//!   resultant and discriminant.
//! - [`factor`]: irreducible factorisation over `Z` (Yun, then Zassenhaus with Cantor–Zassenhaus
//!   modular factoring and multifactor Hensel lifting).
//! - [`roots`]: Descartes / Vincent–Collins–Akritas real root isolation and refinement.
//! - [`RealAlgebraic`]: real algebraic numbers as (minimal polynomial, root index, isolating
//!   interval), with exact comparison, sign evaluation and field arithmetic (by resultants).
//!   Minimal polynomials are irreducible by construction (they come out of [`factor`]).
//! - [`MPoly`]: sparse multivariate polynomials over `Z` with resultants, discriminants and
//!   principal subresultant coefficients with respect to a variable, gcd (recursive subresultant
//!   PRS), content and square-free part in a variable, and partial evaluation.
//! - [`point`]: exact signs of multivariate polynomials at real algebraic points, and the real
//!   roots of a polynomial in its last variable over such a point (the CAD lifting kernel).
//! - [`stats`]: opt-in counters and a phase profiler for the NRA stack.
//!
//! # Testing
//!
//! `cargo test -p smtrex-poly` checks every kernel against an independent slow algorithm
//! (Bareiss Sylvester determinants, Sturm sequences over `Q`, Euclid over `Q`) or an identity.
//! The differential test against sympy is `tests/sympy/sympy_diff.py`, fed by the case generator
//! `tests/sympy/cases.rs` (the example `sympy_cases`); its docstring says how to run it.

pub mod algebraic;
pub mod factor;
pub mod modp;
pub mod mpoly;
pub mod point;
pub mod qpoly;
pub mod ring;
pub mod rng;
pub mod roots;
pub mod stats;
pub mod upoly;

pub use algebraic::{count_real_roots, isolate_real_roots, real_roots, select_root, RealAlgebraic};
pub use factor::factor;
pub use mpoly::MPoly;
pub use qpoly::QPoly;
pub use roots::Isolation;
pub use upoly::{Factored, UPoly};
