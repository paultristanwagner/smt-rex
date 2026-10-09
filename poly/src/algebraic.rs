//! Real algebraic numbers.
//!
//! An irrational real algebraic number is stored as its *minimal* polynomial `p` (irreducible in
//! `Z[x]`, primitive, positive leading coefficient, degree ≥ 2) together with its root index
//! (position among the real roots of `p`, ascending from 0) and an open isolating interval. The
//! pair (minimal polynomial, index) determines the number, so equality and hashing use exactly
//! that pair and never the interval, which is only a refinable approximation. Rational numbers
//! are stored exactly.
//!
//! Irreducibility is what makes the operations exact and simple: two different minimal
//! polynomials have no common root (their gcd is 1), so two irrational numbers with different
//! minimal polynomials are distinct and interval refinement separates them; a polynomial `q`
//! vanishes at `α` iff `gcd(q, p) ≠ 1`, i.e. iff `p | q`; and `p` has no rational root, so
//! bisection never lands on `α`.

use crate::factor::factor;
use crate::mpoly::MPoly;
use crate::roots::{
    bisect_once, compose_affine, descartes_interval, isolate_squarefree, Isolation,
};
use crate::stats::{self, Counter, Kernel};
use crate::upoly::{sign, UPoly};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};

/// A real algebraic number.
#[derive(Clone, Debug)]
pub enum RealAlgebraic {
    Rational(BigRational),
    Irrational(AlgebraicRoot),
}

/// An irrational real algebraic number; see the module docs for the invariants.
#[derive(Clone, Debug)]
pub struct AlgebraicRoot {
    poly: UPoly,
    index: usize,
    lo: BigRational,
    hi: BigRational,
}

impl AlgebraicRoot {
    /// The minimal polynomial (irreducible, primitive, positive leading coefficient).
    pub fn poly(&self) -> &UPoly {
        &self.poly
    }

    /// Index among the real roots of the minimal polynomial, ascending from 0.
    pub fn index(&self) -> usize {
        self.index
    }

    /// The current isolating interval, open: `lo < α < hi`.
    pub fn interval(&self) -> (&BigRational, &BigRational) {
        (&self.lo, &self.hi)
    }

    /// One bisection step.
    fn bisect(&mut self) {
        let r = bisect_once(&self.poly, &mut self.lo, &mut self.hi);
        assert!(
            r.is_none(),
            "irreducible polynomial of degree ≥ 2 with a rational root"
        );
    }

    /// Exact comparison with a rational: one sign evaluation of the minimal polynomial.
    fn cmp_rational(&self, r: &BigRational) -> Ordering {
        if r <= &self.lo {
            return Ordering::Greater;
        }
        if r >= &self.hi {
            return Ordering::Less;
        }
        let s = self.poly.sign_at(r);
        debug_assert!(s != 0);
        if s == self.poly.sign_at(&self.lo) {
            Ordering::Greater // α ∈ (r, hi)
        } else {
            Ordering::Less
        }
    }
}

impl RealAlgebraic {
    pub fn from_rational(r: BigRational) -> RealAlgebraic {
        RealAlgebraic::Rational(r)
    }

    pub fn from_int(n: i64) -> RealAlgebraic {
        RealAlgebraic::Rational(BigRational::from_integer(BigInt::from(n)))
    }

    /// The `k`-th distinct real root (ascending from 0) of a nonzero `f`, if it exists.
    pub fn root_of(f: &UPoly, k: usize) -> Option<RealAlgebraic> {
        real_roots(f).into_iter().nth(k).map(|(r, _)| r)
    }

    /// The unique distinct real root of `f` in the open interval `(lo, hi)`; `None` if there is
    /// no root or more than one.
    pub fn from_interval(f: &UPoly, lo: &BigRational, hi: &BigRational) -> Option<RealAlgebraic> {
        let mut inside = real_roots(f).into_iter().map(|(r, _)| r).filter(|r| {
            r.cmp_rational(lo) == Ordering::Greater && r.cmp_rational(hi) == Ordering::Less
        });
        let first = inside.next()?;
        if inside.next().is_some() {
            return None;
        }
        Some(first)
    }

    pub fn is_rational(&self) -> bool {
        matches!(self, RealAlgebraic::Rational(_))
    }

    pub fn as_rational(&self) -> Option<&BigRational> {
        match self {
            RealAlgebraic::Rational(r) => Some(r),
            RealAlgebraic::Irrational(_) => None,
        }
    }

    /// The minimal polynomial over `Z` (primitive, positive leading coefficient): `den·x − num`
    /// for a rational.
    pub fn minimal_polynomial(&self) -> UPoly {
        match self {
            RealAlgebraic::Rational(r) => UPoly::new(vec![-r.numer(), r.denom().clone()]),
            RealAlgebraic::Irrational(a) => a.poly.clone(),
        }
    }

    /// Index among the real roots of the minimal polynomial (0 for a rational).
    pub fn root_index(&self) -> usize {
        match self {
            RealAlgebraic::Rational(_) => 0,
            RealAlgebraic::Irrational(a) => a.index,
        }
    }

    /// A rational lower bound (`lo < α`, or `lo = α` for a rational).
    pub fn lower(&self) -> &BigRational {
        match self {
            RealAlgebraic::Rational(r) => r,
            RealAlgebraic::Irrational(a) => &a.lo,
        }
    }

    /// A rational upper bound (`α < hi`, or `hi = α` for a rational).
    pub fn upper(&self) -> &BigRational {
        match self {
            RealAlgebraic::Rational(r) => r,
            RealAlgebraic::Irrational(a) => &a.hi,
        }
    }

    /// Shrink the isolating interval to width `≤ width` by bisection (no-op for a rational).
    pub fn refine(&mut self, width: &BigRational) {
        assert!(width.is_positive());
        if let RealAlgebraic::Irrational(a) = self {
            while &(&a.hi - &a.lo) > width {
                a.bisect();
            }
        }
    }

    /// Exact comparison with a rational.
    pub fn cmp_rational(&self, r: &BigRational) -> Ordering {
        match self {
            RealAlgebraic::Rational(q) => q.cmp(r),
            RealAlgebraic::Irrational(a) => a.cmp_rational(r),
        }
    }

    /// Sign (`-1`, `0`, `1`) of `q(α)`. Exact: `q(α) = 0` iff `gcd(q, p) ≠ 1` for the minimal
    /// polynomial `p`; otherwise a copy of the isolating interval is bisected until Descartes'
    /// test shows `q` has no root in it, and the sign is read at the midpoint.
    pub fn sign_of(&self, q: &UPoly) -> i8 {
        match self {
            RealAlgebraic::Rational(r) => q.sign_at(r),
            RealAlgebraic::Irrational(a) => {
                if q.is_zero() || !q.gcd(&a.poly).is_constant() {
                    return 0;
                }
                if q.is_constant() {
                    return sign(&q.lc());
                }
                let mut a = a.clone();
                while descartes_interval(q, &a.lo, &a.hi) != 0 {
                    a.bisect();
                }
                let mid = (&a.lo + &a.hi) / BigRational::from_integer(BigInt::from(2));
                let s = q.sign_at(&mid);
                debug_assert!(s != 0);
                s
            }
        }
    }

    /// A floating-point approximation (for display and diagnostics only).
    pub fn to_f64(&self) -> f64 {
        let mut a = self.clone();
        let mid = match &mut a {
            RealAlgebraic::Rational(r) => r.clone(),
            RealAlgebraic::Irrational(x) => {
                let w =
                    (&x.hi - &x.lo).abs() * BigRational::new(1.into(), BigInt::from(1u64 << 53));
                let w = if w.is_zero() {
                    BigRational::new(1.into(), 2.into())
                } else {
                    w
                };
                while &x.hi - &x.lo > w {
                    x.bisect();
                }
                (&x.lo + &x.hi) / BigRational::from_integer(BigInt::from(2))
            }
        };
        mid.numer().to_f64().unwrap_or(f64::NAN) / mid.denom().to_f64().unwrap_or(f64::NAN)
    }
}

/// Field arithmetic on real algebraic numbers, by resultants (R. Loos, "Computing in algebraic
/// extensions", in *Computer Algebra*, Springer 1982): for `α` with minimal polynomial `p` and `β`
/// with minimal polynomial `q`,
///
/// - `α + β` is a root of `Res_y(p(y), q(z − y))`,
/// - `α · β` is a root of `Res_y(p(y), y^m q(z / y))` with `m = deg q` (for `α ≠ 0`),
///
/// and both resultants are nonzero (they are, up to a constant, `∏ q(z − αᵢ)` and
/// `∏ αᵢ^m q(z/αᵢ)` over the conjugates `αᵢ ≠ 0` of `α`). The right root is selected by
/// [`select_root`] from interval enclosures of the operation. Operations with a rational operand
/// transform the minimal polynomial directly.
impl RealAlgebraic {
    /// `−self`.
    pub fn neg(&self) -> RealAlgebraic {
        match self {
            RealAlgebraic::Rational(r) => RealAlgebraic::Rational(-r),
            RealAlgebraic::Irrational(a) => {
                let p = a.poly.negate_var().primitive_part();
                let (lo, hi) = (-&a.hi, -&a.lo);
                select_root(&p, |_| (lo.clone(), hi.clone()))
            }
        }
    }

    /// `self + o`.
    pub fn add(&self, o: &RealAlgebraic) -> RealAlgebraic {
        match (self, o) {
            (RealAlgebraic::Rational(a), RealAlgebraic::Rational(b)) => {
                RealAlgebraic::Rational(a + b)
            }
            (RealAlgebraic::Rational(q), RealAlgebraic::Irrational(a))
            | (RealAlgebraic::Irrational(a), RealAlgebraic::Rational(q)) => {
                // α + q is a root of p(z − q), irreducible like p, with the same root index.
                let p = compose_affine(&a.poly, &-q, &BigRational::one()).primitive_part();
                RealAlgebraic::Irrational(AlgebraicRoot {
                    poly: p,
                    index: a.index,
                    lo: &a.lo + q,
                    hi: &a.hi + q,
                })
            }
            (RealAlgebraic::Irrational(a), RealAlgebraic::Irrational(b)) => {
                // y = x0, z = x1: Res_y(p(y), q(z − y)).
                let _k = stats::kernel(Kernel::AlgArith);
                let p = MPoly::from_upoly(&a.poly, 0);
                let zy = &MPoly::var(1) - &MPoly::var(0);
                let q = MPoly::from_upoly(&b.poly, 0).compose(&[zy]);
                let r = p.resultant(&q, 0).to_upoly(1).expect("univariate in z");
                count_op(&r);
                let (mut a, mut b) = (a.clone(), b.clone());
                select_root(&r, |k| {
                    if k > 0 {
                        a.bisect();
                        b.bisect();
                    }
                    (&a.lo + &b.lo, &a.hi + &b.hi)
                })
            }
        }
    }

    /// `self − o`.
    pub fn sub(&self, o: &RealAlgebraic) -> RealAlgebraic {
        self.add(&o.neg())
    }

    /// `self · o`.
    pub fn mul(&self, o: &RealAlgebraic) -> RealAlgebraic {
        match (self, o) {
            (RealAlgebraic::Rational(a), RealAlgebraic::Rational(b)) => {
                RealAlgebraic::Rational(a * b)
            }
            (RealAlgebraic::Rational(q), RealAlgebraic::Irrational(a))
            | (RealAlgebraic::Irrational(a), RealAlgebraic::Rational(q)) => {
                if q.is_zero() {
                    return RealAlgebraic::Rational(BigRational::zero());
                }
                // q·α is a root of p(z / q), irreducible like p.
                let p = compose_affine(&a.poly, &BigRational::zero(), &q.recip()).primitive_part();
                let (x, y) = (&a.lo * q, &a.hi * q);
                if q.is_positive() {
                    RealAlgebraic::Irrational(AlgebraicRoot {
                        poly: p,
                        index: a.index,
                        lo: x,
                        hi: y,
                    })
                } else {
                    select_root(&p, |_| (y.clone(), x.clone()))
                }
            }
            (RealAlgebraic::Irrational(a), RealAlgebraic::Irrational(b)) => {
                // y = x0, z = x1: Res_y(p(y), y^m q(z / y)) = Res_y(p, Σ qᵢ zⁱ y^(m−i)).
                let _k = stats::kernel(Kernel::AlgArith);
                let m = b.poly.degree().expect("nonzero");
                let p = MPoly::from_upoly(&a.poly, 0);
                let q = MPoly::from_terms(
                    b.poly
                        .coeffs()
                        .iter()
                        .enumerate()
                        .map(|(i, c)| (vec![(m - i) as u32, i as u32], c.clone())),
                );
                let r = p.resultant(&q, 0).to_upoly(1).expect("univariate in z");
                count_op(&r);
                let (mut a, mut b) = (a.clone(), b.clone());
                select_root(&r, |k| {
                    if k > 0 {
                        a.bisect();
                        b.bisect();
                    }
                    let c = [&a.lo * &b.lo, &a.lo * &b.hi, &a.hi * &b.lo, &a.hi * &b.hi];
                    let lo = c.iter().min().unwrap().clone();
                    let hi = c.iter().max().unwrap().clone();
                    (lo, hi)
                })
            }
        }
    }

    /// `self^k`.
    pub fn pow(&self, k: usize) -> RealAlgebraic {
        let mut acc = RealAlgebraic::from_int(1);
        for _ in 0..k {
            acc = acc.mul(self);
        }
        acc
    }
}

/// Diagnostics: one operation on two irrationals, with annihilating polynomial `r`.
fn count_op(r: &UPoly) {
    stats::add(Counter::AlgOps, 1);
    stats::max(Counter::AlgOpDegMax, r.degree().unwrap_or(0) as u64);
}

/// The root of a nonzero `r` that `enclose` pins down. `enclose(k)` must return a closed interval
/// `[lo, hi]` containing the wanted root, for `k = 0, 1, 2, …`, with widths tending to zero; the
/// first enclosure that contains exactly one real root of `r` decides. Exact: roots are compared
/// with the enclosure's endpoints exactly, and the roots of `r` are distinct, so a small enough
/// enclosure contains only the wanted one.
pub fn select_root(
    r: &UPoly,
    mut enclose: impl FnMut(u32) -> (BigRational, BigRational),
) -> RealAlgebraic {
    let roots: Vec<RealAlgebraic> = real_roots(r).into_iter().map(|(x, _)| x).collect();
    for k in 0.. {
        let (lo, hi) = enclose(k);
        let mut inside = roots.iter().filter(|x| {
            x.cmp_rational(&lo) != Ordering::Less && x.cmp_rational(&hi) != Ordering::Greater
        });
        let first = inside
            .next()
            .expect("the enclosure must contain a root of the annihilating polynomial");
        if inside.next().is_none() {
            return first.clone();
        }
    }
    unreachable!()
}

/// Exact comparison of two real algebraic numbers. Same minimal polynomial: compare the root
/// indices. Different minimal polynomials: the values differ (irreducible polynomials share no
/// root), so bisect copies of both intervals until they are disjoint.
fn cmp_alg(x: &RealAlgebraic, y: &RealAlgebraic) -> Ordering {
    let _k = stats::kernel(Kernel::AlgCmp);
    match (x, y) {
        (RealAlgebraic::Rational(a), RealAlgebraic::Rational(b)) => a.cmp(b),
        (RealAlgebraic::Rational(a), RealAlgebraic::Irrational(b)) => b.cmp_rational(a).reverse(),
        (RealAlgebraic::Irrational(a), RealAlgebraic::Rational(b)) => a.cmp_rational(b),
        (RealAlgebraic::Irrational(a), RealAlgebraic::Irrational(b)) => {
            if a.poly == b.poly {
                return a.index.cmp(&b.index);
            }
            let (mut a, mut b) = (a.clone(), b.clone());
            loop {
                if a.hi <= b.lo {
                    return Ordering::Less;
                }
                if b.hi <= a.lo {
                    return Ordering::Greater;
                }
                if &a.hi - &a.lo >= &b.hi - &b.lo {
                    a.bisect();
                } else {
                    b.bisect();
                }
            }
        }
    }
}

impl PartialEq for RealAlgebraic {
    /// Value equality: rationals by value, irrationals by (minimal polynomial, root index).
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (RealAlgebraic::Rational(a), RealAlgebraic::Rational(b)) => a == b,
            (RealAlgebraic::Irrational(a), RealAlgebraic::Irrational(b)) => {
                a.index == b.index && a.poly == b.poly
            }
            _ => false,
        }
    }
}

impl Eq for RealAlgebraic {}

impl Hash for RealAlgebraic {
    /// Hashes exactly what `eq` compares; never the interval.
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            RealAlgebraic::Rational(r) => {
                0u8.hash(state);
                r.hash(state);
            }
            RealAlgebraic::Irrational(a) => {
                1u8.hash(state);
                a.poly.hash(state);
                a.index.hash(state);
            }
        }
    }
}

impl PartialOrd for RealAlgebraic {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for RealAlgebraic {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_alg(self, other)
    }
}

impl fmt::Display for RealAlgebraic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RealAlgebraic::Rational(r) => write!(f, "{r}"),
            RealAlgebraic::Irrational(a) => {
                write!(f, "root#{} of {} in ({}, {})", a.index, a.poly, a.lo, a.hi)
            }
        }
    }
}

/// All distinct real roots of `f`, ascending, each with its multiplicity. Irrational
/// roots carry their minimal polynomial (from the factorisation of `f` over `Z`), and all
/// isolating intervals are pairwise disjoint as open intervals (neighbours may share an endpoint,
/// which then lies strictly between the two roots; a rational root never lies inside another
/// root's interval), and no interval endpoint is a root of `f`. Empty for a constant `f`
/// (including zero).
pub fn real_roots(f: &UPoly) -> Vec<(RealAlgebraic, usize)> {
    let mut roots = Vec::new();
    if f.is_constant() {
        return roots;
    }
    for (g, mult) in factor(f).factors {
        if g.degree() == Some(1) {
            let r = BigRational::new(-g.coeff(0), g.coeff(1));
            roots.push((RealAlgebraic::Rational(r), mult));
            continue;
        }
        for (index, iso) in isolate_squarefree(&g).into_iter().enumerate() {
            let r = match iso {
                Isolation::Exact(r) => panic!("irreducible {g} has the rational root {r}"),
                Isolation::Open(lo, hi) => RealAlgebraic::Irrational(AlgebraicRoot {
                    poly: g.clone(),
                    index,
                    lo,
                    hi,
                }),
            };
            roots.push((r, mult));
        }
    }
    roots.sort_by(|a, b| a.0.cmp(&b.0));
    separate(&mut roots);
    // An endpoint chosen while isolating one factor may be a rational root of another factor;
    // bisect it away (bisection only shrinks, so the intervals stay disjoint, and it terminates:
    // the far endpoint converges to the root, dragging the midpoint past the offending point).
    for (r, _) in &mut roots {
        if let RealAlgebraic::Irrational(a) = r {
            while f.sign_at(&a.lo) == 0 || f.sign_at(&a.hi) == 0 {
                a.bisect();
            }
        }
    }
    roots
}

/// Refine neighbouring intervals of a sorted list until each upper end is `≤` the next lower end.
fn separate(roots: &mut [(RealAlgebraic, usize)]) {
    for i in 1..roots.len() {
        let (left, right) = roots.split_at_mut(i);
        let a = &mut left[i - 1].0;
        let b = &mut right[0].0;
        while a.upper() > b.lower() {
            let wa = a.upper() - a.lower();
            let wb = b.upper() - b.lower();
            let target = if wa >= wb { &mut *a } else { &mut *b };
            if let RealAlgebraic::Irrational(x) = target {
                x.bisect();
            }
        }
    }
}

/// Isolating intervals (or exact points) of the distinct real roots of a nonzero `f`, ascending,
/// with multiplicities. A thin view of [`real_roots`].
pub fn isolate_real_roots(f: &UPoly) -> Vec<(Isolation, usize)> {
    real_roots(f)
        .into_iter()
        .map(|(r, m)| {
            let iso = match r {
                RealAlgebraic::Rational(q) => Isolation::Exact(q),
                RealAlgebraic::Irrational(a) => Isolation::Open(a.lo, a.hi),
            };
            (iso, m)
        })
        .collect()
}

/// Number of real roots of a nonzero `f` in the closed interval `[lo, hi]` (`None` = unbounded),
/// counting multiplicity if asked. Exact: every root is compared with the bounds exactly.
pub fn count_real_roots(
    f: &UPoly,
    lo: Option<&BigRational>,
    hi: Option<&BigRational>,
    with_multiplicity: bool,
) -> usize {
    real_roots(f)
        .into_iter()
        .filter(|(r, _)| {
            lo.is_none_or(|l| r.cmp_rational(l) != Ordering::Less)
                && hi.is_none_or(|h| r.cmp_rational(h) != Ordering::Greater)
        })
        .map(|(_, m)| if with_multiplicity { m } else { 1 })
        .sum()
}
