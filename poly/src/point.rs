//! Multivariate polynomials at real algebraic points: exact signs and the real roots of a
//! polynomial whose other variables are fixed to real algebraic numbers. These are the two
//! kernels a CAD lifting step or an NLSAT model-constructing search needs.
//!
//! A point is a slice of [`RealAlgebraic`] numbers, `point[i]` the value of `x_i`. Each
//! coordinate carries its own minimal polynomial over `Q`; no relation between the coordinates is
//! assumed or used, which keeps the methods simple at the price of resultant degrees that
//! multiply.
//!
//! # Exact sign ([`sign_at`])
//!
//! Rational coordinates are substituted exactly. Then a value `v = P(α)` is enclosed by rational
//! interval arithmetic over the isolating intervals; if the enclosure excludes 0 the sign is
//! read off. Otherwise the annihilating polynomial
//!
//! `A(z) = Res_{x₁}(m₁(x₁), Res_{x₂}(m₂(x₂), … Res_{x_k}(m_k(x_k), z − P(x)) …))`
//!
//! is computed (the `m_i` are the minimal polynomials of the irrational coordinates). By the
//! Poisson formula `A(z) = c · ∏ (z − P(β))` over all tuples `β` of roots of the `m_i`, `c ≠ 0`:
//! `A` is nonzero (a product of monic linear factors up to a constant) and `A(v) = 0`. Write
//! `A = z^e · B` with `B(0) ≠ 0`. Every nonzero root of `A` has modulus `> δ = 1 / (1 + max|bᵢ/b₀|)`
//! (Cauchy's bound applied to the reversed `B`). The enclosure is refined until it lies in
//! `(−δ, δ)` — then `v = 0`, since `v` is a root of `A` — or excludes 0. One of the two must
//! happen: the enclosure width tends to zero as the isolating intervals shrink.
//!
//! # Real roots in the last variable ([`roots_at`])
//!
//! For `p(α, y)` the exact degree in `y` is found first (top coefficients whose sign at `α` is 0
//! are dropped; if all vanish, `p` is *nullified* over `α`). Then a nonzero `R ∈ Z[y]` whose real
//! roots include every real root of `G(y) = p(α, y)` is computed:
//!
//! - the iterated resultant `R(y) = Res_{x₁}(m₁, … Res_{x_k}(m_k, p(x, y)))
//!   = c · ∏_β p(β, y)`, which vanishes at every root of `G` (the true point `α` is one of the
//!   tuples `β`). It is nonzero unless some tuple `β` makes `p(β, y)` vanish identically. That
//!   cannot happen with one irrational coordinate (all its conjugates are field embeddings,
//!   which map the nonzero `G` to nonzero polynomials), but it can with several, because the
//!   tuples range over *all* combinations of conjugates, not just the conjugates of the point.
//! - if it is zero: a primitive element `θ = Σ cᵢ αᵢ` (with `c = (1, j, j², …)`), its minimal
//!   polynomial `M` (the irreducible factor of `Res(…, z − Σ cᵢ xᵢ)` that vanishes at `θ`, found
//!   by the exact sign), and `T(y, s)` = the iterated resultant of `p(x, y) + s · M(Σ cᵢ xᵢ)`.
//!   Up to a constant, `T = ∏_β (p(β, y) + s · M(c·β))`. For `β = α` the factor is `G(y)`, so
//!   `G` divides the leading coefficient of `T` in `s`; that coefficient is nonzero as soon as
//!   `T ≠ 0`, which holds when `c` separates the tuples (only finitely many `j` fail, because a
//!   tuple `β` with `M(c·β) = 0` and `p(β, y) ≡ 0` makes `c·β` a conjugate `c·σ(α)` of `θ`
//!   with `β ≠ σ(α)`, a polynomial condition in `j` that is not identically true). So `j` is
//!   increased until `T ≠ 0`.
//!
//! The real roots of `R` are isolated exactly ([`crate::real_roots`], with irreducible minimal
//! polynomials). Separately, the exact number `c` of distinct real roots of `G` is computed from
//! the signs at `α` of the signed subresultant coefficients of `p` and `∂p/∂y`
//! ([`count_real_roots_at`]; only polynomials in the coordinates of `α`, not in `y`, are
//! evaluated). Candidates are then discarded while an interval enclosure of `p` at `(α, r)`
//! excludes 0, refining all intervals, until exactly `c` remain. A true root is never discarded
//! (its enclosure always contains 0) and every other candidate eventually is (its value is
//! nonzero and the enclosures converge to it), so the survivors are exactly the roots. This
//! avoids exact zero tests in `k + 1` coordinates, whose annihilating polynomials have degree
//! `deg R · ∏ deg mᵢ`.

use crate::algebraic::{real_roots, RealAlgebraic};
use crate::mpoly::MPoly;
use crate::stats::{self, Counter, Kernel};
use crate::upoly::UPoly;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// A closed rational interval `[lo, hi]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Interval {
    pub lo: BigRational,
    pub hi: BigRational,
}

impl Interval {
    pub fn point(x: BigRational) -> Interval {
        Interval {
            lo: x.clone(),
            hi: x,
        }
    }

    fn add(&self, o: &Interval) -> Interval {
        Interval {
            lo: &self.lo + &o.lo,
            hi: &self.hi + &o.hi,
        }
    }

    fn mul(&self, o: &Interval) -> Interval {
        if self.lo == self.hi && o.lo == o.hi {
            return Interval::point(&self.lo * &o.lo);
        }
        let c = [
            &self.lo * &o.lo,
            &self.lo * &o.hi,
            &self.hi * &o.lo,
            &self.hi * &o.hi,
        ];
        Interval {
            lo: c.iter().min().unwrap().clone(),
            hi: c.iter().max().unwrap().clone(),
        }
    }

    fn scale(&self, k: &BigInt) -> Interval {
        let k = BigRational::from_integer(k.clone());
        if k.is_negative() {
            Interval {
                lo: &self.hi * &k,
                hi: &self.lo * &k,
            }
        } else {
            Interval {
                lo: &self.lo * &k,
                hi: &self.hi * &k,
            }
        }
    }

    /// `self^e`, tight for even powers of intervals containing 0.
    fn pow(&self, e: u32) -> Interval {
        let p = |x: &BigRational| num_traits::pow(x.clone(), e as usize);
        if e % 2 == 1 || !self.lo.is_negative() {
            return Interval {
                lo: p(&self.lo),
                hi: p(&self.hi),
            };
        }
        if !self.hi.is_positive() {
            return Interval {
                lo: p(&self.hi),
                hi: p(&self.lo),
            };
        }
        let (a, b) = (p(&self.lo), p(&self.hi));
        Interval {
            lo: BigRational::zero(),
            hi: a.max(b),
        }
    }

    /// Sign if the interval excludes zero.
    fn sign(&self) -> Option<i8> {
        if self.lo.is_positive() {
            Some(1)
        } else if self.hi.is_negative() {
            Some(-1)
        } else {
            None
        }
    }
}

/// The isolating interval of a coordinate, closed (a point for a rational).
fn coord_interval(a: &RealAlgebraic) -> Interval {
    Interval {
        lo: a.lower().clone(),
        hi: a.upper().clone(),
    }
}

/// An enclosure of `p(point)`: the natural interval extension over the coordinates' current
/// isolating intervals (closed). Every variable of `p` must be a coordinate of `point`.
pub fn interval_eval(p: &MPoly, point: &[RealAlgebraic]) -> Interval {
    let boxes: Vec<Interval> = point.iter().map(coord_interval).collect();
    let mut acc = Interval::point(BigRational::zero());
    for (m, c) in p.terms() {
        let mut t = Interval::point(BigRational::one());
        for (i, e) in m.iter() {
            t = t.mul(&boxes[i].pow(e));
        }
        acc = acc.add(&t.scale(c));
    }
    acc
}

/// Halve the isolating interval of every irrational coordinate in `vars`.
fn refine_vars(point: &mut [RealAlgebraic], vars: &[usize]) {
    for &v in vars {
        if point[v].is_rational() {
            continue;
        }
        let w = point[v].upper() - point[v].lower();
        let half = w / BigRational::from_integer(BigInt::from(2));
        point[v].refine(&half);
    }
}

/// Substitute every rational coordinate of `point` into `p` (a positive multiple of the exact
/// substitution, so signs and zero sets are kept). Variables in `keep` are left alone.
pub fn substitute_rationals(p: &MPoly, point: &[RealAlgebraic], keep: Option<usize>) -> MPoly {
    let mut q = p.clone();
    for v in p.vars() {
        if Some(v) == keep || v >= point.len() {
            continue;
        }
        if let Some(r) = point[v].as_rational() {
            q = q.eval_var(v, r);
        }
    }
    q
}

/// Iterated resultant of `h` with the minimal polynomials of the coordinates `vars`, eliminating
/// each of them that occurs in `h` (see the module docs). `Res_v(m, h) = h^{deg m}` when `h` does
/// not contain `x_v`, so skipping such variables keeps the zero set.
fn eliminate(mut h: MPoly, vars: &[usize], point: &[RealAlgebraic]) -> MPoly {
    for &v in vars {
        if !h.has_var(v) {
            continue;
        }
        let m = MPoly::from_upoly(&point[v].minimal_polynomial(), v);
        h = m.resultant(&h, v);
        if h.is_zero() {
            return h;
        }
    }
    h
}

/// Number of interval rounds tried before the annihilating polynomial is computed.
const CHEAP_ROUNDS: usize = 6;

/// Exact sign (`-1`, `0`, `1`) of `p` at `point` (see the module docs). Every variable of `p`
/// must be a coordinate of `point`. Refines the isolating intervals of `point` in place (that
/// only makes later calls cheaper; the numbers do not change).
pub fn sign_at(p: &MPoly, point: &mut [RealAlgebraic]) -> i8 {
    let _k = stats::kernel(Kernel::SignInterval);
    stats::add(Counter::SignAt, 1);
    let q = substitute_rationals(p, point, None);
    if let Some(c) = q.as_constant() {
        return sign_int(&c);
    }
    let vars = q.vars();
    for _ in 0..CHEAP_ROUNDS {
        if let Some(s) = interval_eval(&q, point).sign() {
            return s;
        }
        refine_vars(point, &vars);
    }
    // The annihilating polynomial of v = q(point), in the fresh variable z.
    let _k = stats::kernel(Kernel::SignAnnihilator);
    stats::add(Counter::Annihilators, 1);
    let z = point.len().max(q.num_vars());
    let h = &MPoly::var(z) - &q;
    let a = eliminate(h, &vars, point)
        .to_upoly(z)
        .expect("the annihilator is univariate in z");
    stats::max(Counter::AnnihDegMax, a.degree().unwrap_or(0) as u64);
    assert!(!a.is_zero(), "the annihilating polynomial is nonzero");
    let (b, e) = a.strip_x();
    let delta = if e == 0 {
        None
    } else {
        // Nonzero roots of A are roots of B and have modulus > δ.
        let b0 = b.coeff(0).abs();
        let mx = b.coeffs()[1..]
            .iter()
            .map(|c| c.abs())
            .max()
            .unwrap_or_default();
        Some(BigRational::new(b0.clone(), b0 + mx))
    };
    loop {
        let iv = interval_eval(&q, point);
        if let Some(s) = iv.sign() {
            return s;
        }
        if let Some(d) = &delta {
            if iv.lo > -d && &iv.hi < d {
                return 0;
            }
        }
        refine_vars(point, &vars);
    }
}

/// The sign of `p` at `point` when the caller knows it is not zero: interval refinement only.
/// Falls back to [`sign_at`] after many rounds and panics if the value is in fact zero (a broken
/// caller invariant).
pub fn sign_at_nonzero(p: &MPoly, point: &mut [RealAlgebraic]) -> i8 {
    let _k = stats::kernel(Kernel::SignInterval);
    let q = substitute_rationals(p, point, None);
    if let Some(c) = q.as_constant() {
        let s = sign_int(&c);
        assert!(s != 0, "sign_at_nonzero: the value is zero");
        return s;
    }
    let vars = q.vars();
    for _ in 0..64 {
        if let Some(s) = interval_eval(&q, point).sign() {
            return s;
        }
        refine_vars(point, &vars);
    }
    let s = sign_at(&q, point);
    assert!(s != 0, "sign_at_nonzero: the value is zero");
    s
}

fn sign_int(c: &BigInt) -> i8 {
    if c.is_positive() {
        1
    } else if c.is_negative() {
        -1
    } else {
        0
    }
}

/// The real roots of `p` in its variable `x_v` over a point.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Fiber {
    /// `p(point, y)` is the zero polynomial.
    Nullified,
    /// The distinct real roots of the nonzero `p(point, y)`, ascending.
    Roots(Vec<RealAlgebraic>),
}

/// The distinct real roots of `p(point, x_v)` for `v = point.len()` (the variable after the
/// point's last coordinate; every other variable of `p` must be a coordinate). See the module
/// docs for the method and why it is exact. Refines the point's intervals in place.
pub fn roots_at(p: &MPoly, point: &mut Vec<RealAlgebraic>) -> Fiber {
    stats::add(Counter::RootsAt, 1);
    let v = point.len();
    let q = substitute_rationals(p, point, Some(v));
    // The exact degree in y over the point.
    let mut coeffs = q.coeffs_in(v);
    while let Some(c) = coeffs.last() {
        if sign_at(c, point) != 0 {
            break;
        }
        coeffs.pop();
    }
    if coeffs.is_empty() {
        return Fiber::Nullified;
    }
    let d = coeffs.len() - 1;
    if d == 0 {
        return Fiber::Roots(Vec::new());
    }
    let g = MPoly::from_coeffs_in(v, &coeffs);
    let irr: Vec<usize> = g.vars().into_iter().filter(|&x| x != v).collect();
    if irr.is_empty() {
        let u = g.to_upoly(v).expect("univariate");
        let _k = stats::kernel(Kernel::RealRoots);
        return Fiber::Roots(real_roots(&u).into_iter().map(|(r, _)| r).collect());
    }
    if stats::enabled() {
        stats::add(Counter::RootsAtIrr, 1);
        let prod: u64 = irr
            .iter()
            .map(|&x| point[x].minimal_polynomial().degree().unwrap_or(1) as u64)
            .product::<u64>()
            * d as u64;
        stats::max(Counter::PointDegMax, prod);
    }
    let count = {
        let _k = stats::kernel(Kernel::CountRoots);
        count_real_roots_at(&g, v, point)
    };
    if count == 0 {
        return Fiber::Roots(Vec::new());
    }
    let r = {
        let _k = stats::kernel(Kernel::Candidates);
        candidates(&g, v, &irr, point)
    };
    stats::max(Counter::CandDegMax, r.degree().unwrap_or(0) as u64);
    let mut alive: Vec<RealAlgebraic> = {
        let _k = stats::kernel(Kernel::RealRoots);
        real_roots(&r).into_iter().map(|(x, _)| x).collect()
    };
    let _k = stats::kernel(Kernel::SignInterval);
    // Discard candidates at which an enclosure of g excludes 0 until exactly `count` remain:
    // every true root survives (the enclosure contains g's value 0), every other candidate is
    // eventually discarded (its value is nonzero and the enclosures shrink to it).
    loop {
        assert!(
            alive.len() >= count,
            "root isolation lost a root of {g} over {point:?}"
        );
        if alive.len() == count {
            return Fiber::Roots(alive);
        }
        let mut kept = Vec::with_capacity(alive.len());
        for cand in alive {
            point.push(cand);
            let excluded = interval_eval(&g, point).sign().is_some();
            let mut cand = point.pop().unwrap();
            if !excluded {
                if !cand.is_rational() {
                    let w = cand.upper() - cand.lower();
                    cand.refine(&(w / BigRational::from_integer(BigInt::from(2))));
                }
                kept.push(cand);
            }
        }
        alive = kept;
        refine_vars(point, &irr);
    }
}

/// The number of distinct real roots of `g(point, x_v)`, where `g` has the same degree `p ≥ 1`
/// in `x_v` over the point as formally. By the theorem of Sturm–Sylvester in subresultant form
/// (S. Basu, R. Pollack, M.-F. Roy, *Algorithms in Real Algebraic Geometry*, Thm. 4.31 with
/// Cor. 4.10–4.11): the count is the generalised *permanences minus variations* `PmV` of the
/// signed subresultant coefficients `sRes_p, …, sRes_0` of `g` and `∂g/∂x_v`, where
/// `sRes_p = lc(g)`, `sRes_{p−1} = p·lc(g)` and `sRes_j = ε_{p−j} · psc_j(g, g')` for `j < p−1`
/// (`ε_k = (−1)^{k(k−1)/2}` reorders the second row block of the Sylvester–Habicht matrix into
/// the classical one). Subresultants are determinants in the coefficients, so they commute with
/// specialising the lower variables when both leading coefficients survive (`lc(g)(α) ≠ 0`); only
/// signs at the point (exact, [`sign_at`]) of polynomials in the point's coordinates are needed.
pub fn count_real_roots_at(g: &MPoly, v: usize, point: &mut [RealAlgebraic]) -> usize {
    let p = g.degree_in(v).expect("nonzero");
    if p == 0 {
        return 0;
    }
    let lc_sign = sign_at(&g.lc_in(v), point);
    assert!(
        lc_sign != 0,
        "the leading coefficient vanishes at the point"
    );
    let mut seq: Vec<(usize, i8)> = vec![(p, lc_sign), (p - 1, lc_sign)];
    for (j, c) in g.psc(&g.derivative(v), v) {
        let s = sign_at(&c, point);
        if s == 0 {
            continue;
        }
        let k = p - j;
        let eps = if (k * (k - 1) / 2) % 2 == 1 { -1 } else { 1 };
        seq.push((j, s * eps));
    }
    pmv(&seq) as usize
}

/// Generalised permanences minus variations of a sequence given by its nonzero entries
/// `(index, sign)` in decreasing index order (BPR, Notation 4.30): consecutive nonzero entries
/// `s_i, s_j` (`i > j`) contribute `(−1)^{(i−j)(i−j−1)/2} · sign(s_i s_j)` if `i − j` is odd and
/// nothing otherwise.
fn pmv(seq: &[(usize, i8)]) -> i64 {
    let mut total = 0i64;
    for w in seq.windows(2) {
        let (i, a) = w[0];
        let (j, b) = w[1];
        let k = i - j;
        if k % 2 == 1 {
            let eps = if (k * (k - 1) / 2) % 2 == 1 { -1 } else { 1 };
            total += eps * (a as i64) * (b as i64);
        }
    }
    total
}

/// A nonzero polynomial in `x_v` whose real roots include all real roots of `g(point, x_v)`;
/// `g` has the exact degree over the point and the irrational coordinates `irr`.
fn candidates(g: &MPoly, v: usize, irr: &[usize], point: &mut [RealAlgebraic]) -> UPoly {
    let r = eliminate(g.clone(), irr, point);
    if !r.is_zero() {
        return r.to_upoly(v).expect("univariate in the lifted variable");
    }
    // A spurious tuple of conjugates kills every coefficient: use a primitive element.
    let fresh = v + 1;
    for j in 1i64.. {
        let mut theta = MPoly::zero();
        let mut c = BigInt::one();
        for &x in irr {
            theta = &theta + &MPoly::var(x).scale(&c);
            c *= j;
        }
        let pc = eliminate(&MPoly::var(fresh) - &theta, irr, point)
            .to_upoly(fresh)
            .expect("univariate");
        let mut m = None;
        for (f, _) in pc.factor().factors {
            let mf = MPoly::from_upoly(&f, 0).compose(&[theta.clone()]);
            if sign_at(&mf, point) == 0 {
                m = Some(mf);
                break;
            }
        }
        let m = m.expect("some irreducible factor vanishes at the primitive element");
        let t = &(g.clone()) + &(&MPoly::var(fresh) * &m);
        let t = eliminate(t, irr, point);
        if t.is_zero() {
            continue;
        }
        let lc = t.lc_in(fresh);
        return lc.to_upoly(v).expect("univariate in the lifted variable");
    }
    unreachable!()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64, d: i64) -> BigRational {
        BigRational::new(BigInt::from(n), BigInt::from(d))
    }

    fn sqrt(n: i64) -> RealAlgebraic {
        RealAlgebraic::root_of(&UPoly::from_i64s(&[-n, 0, 1]), 1).unwrap()
    }

    #[test]
    fn signs_at_algebraic_points() {
        let x = MPoly::var(0);
        let y = MPoly::var(1);
        // x - y at (√2, √2) is 0; at (√2, √3) negative; x² - 2 at √2 is 0.
        let mut pt = vec![sqrt(2), sqrt(2)];
        assert_eq!(sign_at(&(&x - &y), &mut pt), 0);
        assert_eq!(sign_at(&(&x + &y), &mut pt), 1);
        let mut pt = vec![sqrt(2), sqrt(3)];
        assert_eq!(sign_at(&(&x - &y), &mut pt), -1);
        // x·y − √6: (xy)² − 6 = 0 at (√2, √3).
        let xy = &x * &y;
        assert_eq!(sign_at(&(&(&xy * &xy) - &MPoly::from_i64(6)), &mut pt), 0);
        assert_eq!(sign_at(&(&xy - &MPoly::from_i64(2)), &mut pt), 1);
        let mut pt = vec![RealAlgebraic::from_rational(q(1, 3)), sqrt(2)];
        assert_eq!(
            sign_at(&(&x.scale(&BigInt::from(3)) - &MPoly::from_i64(1)), &mut pt),
            0
        );
    }

    #[test]
    fn roots_over_dependent_coordinates() {
        // (x1 + x0)(x2 - 1) over (√2, −√2) nullifies; over (√2, √2) the root is x2 = 1.
        let x0 = MPoly::var(0);
        let x1 = MPoly::var(1);
        let x2 = MPoly::var(2);
        let p = &(&x1 + &x0) * &(&x2 - &MPoly::from_i64(1));
        let mut pt = vec![sqrt(2), sqrt(2).neg()];
        assert_eq!(roots_at(&p, &mut pt), Fiber::Nullified);
        let mut pt = vec![sqrt(2), sqrt(2)];
        assert_eq!(
            roots_at(&p, &mut pt),
            Fiber::Roots(vec![RealAlgebraic::from_int(1)])
        );
        // Spurious tuple: (x1 - x0)(x2 - 1) + (x1 - x0)·0 over (√2, −√2): the conjugate tuple
        // (√2, √2) kills every coefficient, so the plain resultant is zero.
        let p = &(&x1 - &x0) * &(&x2 - &MPoly::from_i64(1));
        let mut pt = vec![sqrt(2), sqrt(2).neg()];
        assert_eq!(
            roots_at(&p, &mut pt),
            Fiber::Roots(vec![RealAlgebraic::from_int(1)])
        );
        // x2² − x0·x1 over (√2, √2): roots ±√2.
        let p = &(&x2 * &x2) - &(&x0 * &x1);
        let mut pt = vec![sqrt(2), sqrt(2)];
        assert_eq!(
            roots_at(&p, &mut pt),
            Fiber::Roots(vec![sqrt(2).neg(), sqrt(2)])
        );
    }
}
