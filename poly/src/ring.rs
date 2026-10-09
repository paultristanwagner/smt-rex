//! Coefficient rings and the ring-generic dense-polynomial kernels.
//!
//! The pseudo-remainder and the subresultant PRS only need ring operations plus *exact* division,
//! so they are written once over [`Ring`] and used both for `Z[x]` (coefficients [`BigInt`]) and
//! for `Z[y₁,…][x]` (coefficients [`crate::MPoly`]), which is how multivariate resultants are
//! computed. A dense polynomial here is a coefficient slice in ascending degree order with no
//! trailing zeros; the zero polynomial is the empty slice.

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

/// An integral domain with exact division, enough for the subresultant PRS.
pub trait Ring: Clone + PartialEq + std::fmt::Debug {
    fn zero() -> Self;
    fn one() -> Self;
    fn is_zero(&self) -> bool;
    fn add(&self, o: &Self) -> Self;
    fn sub(&self, o: &Self) -> Self;
    fn mul(&self, o: &Self) -> Self;
    fn neg(&self) -> Self;
    /// `self / o` when `o` divides `self` exactly. Panics otherwise: in the callers below a
    /// non-exact division is a bug, never a property of the input.
    fn exact_div(&self, o: &Self) -> Self;
    fn from_i64(n: i64) -> Self;

    /// `self^e` by binary powering.
    fn pow(&self, mut e: usize) -> Self {
        let mut base = self.clone();
        let mut acc = Self::one();
        while e > 0 {
            if e & 1 == 1 {
                acc = acc.mul(&base);
            }
            e >>= 1;
            if e > 0 {
                base = base.mul(&base);
            }
        }
        acc
    }
}

impl Ring for BigInt {
    fn zero() -> Self {
        Zero::zero()
    }
    fn one() -> Self {
        One::one()
    }
    fn is_zero(&self) -> bool {
        Zero::is_zero(self)
    }
    fn add(&self, o: &Self) -> Self {
        self + o
    }
    fn sub(&self, o: &Self) -> Self {
        self - o
    }
    fn mul(&self, o: &Self) -> Self {
        self * o
    }
    fn neg(&self) -> Self {
        -self
    }
    fn exact_div(&self, o: &Self) -> Self {
        let (q, r) = self.div_rem(o);
        assert!(Zero::is_zero(&r), "inexact integer division {self} / {o}");
        q
    }
    fn from_i64(n: i64) -> Self {
        BigInt::from(n)
    }
}

/// Remove trailing zero coefficients.
pub fn trim<R: Ring>(p: &mut Vec<R>) {
    while p.last().is_some_and(|c| c.is_zero()) {
        p.pop();
    }
}

/// Degree of a trimmed dense polynomial; `None` for zero.
pub fn degree<R: Ring>(p: &[R]) -> Option<usize> {
    p.len().checked_sub(1)
}

/// Formal derivative.
pub fn derivative<R: Ring>(p: &[R]) -> Vec<R> {
    let mut d: Vec<R> = p
        .iter()
        .enumerate()
        .skip(1)
        .map(|(i, c)| c.mul(&R::from_i64(i as i64)))
        .collect();
    trim(&mut d);
    d
}

/// Pseudo-remainder `prem(f, g)`: the remainder of `lc(g)^(deg f − deg g + 1) · f` divided by
/// `g`, computed without division (classical pseudo-division, Knuth TAOCP 4.6.1 Algorithm R).
/// Returns `f` unchanged when `deg f < deg g`. Panics if `g` is zero.
pub fn prem<R: Ring>(f: &[R], g: &[R]) -> Vec<R> {
    let dg = degree(g).expect("pseudo-remainder by the zero polynomial");
    let mut r = f.to_vec();
    if r.is_empty() || r.len() - 1 < dg {
        return r;
    }
    let mut n = r.len() - dg; // deg f − deg g + 1 multiplications by lc(g) remain owed
    let lcg = &g[dg];
    while r.len() > dg {
        let dr = r.len() - 1;
        let lcr = r[dr].clone();
        let j = dr - dg;
        for c in r.iter_mut() {
            *c = c.mul(lcg);
        }
        for (i, gi) in g.iter().enumerate() {
            r[i + j] = r[i + j].sub(&gi.mul(&lcr));
        }
        trim(&mut r);
        n -= 1;
    }
    if n > 0 {
        let k = lcg.pow(n);
        for c in r.iter_mut() {
            *c = c.mul(&k);
        }
    }
    r
}

/// The subresultant polynomial remainder sequence of `f` and `g` with `deg f ≥ deg g ≥ 0`
/// (Brown–Traub / Collins subresultant PRS; W. S. Brown, "The Subresultant PRS Algorithm", ACM
/// TOMS 4, 1978). Returns the PRS `[f, g, R₂, …]` and the scalar subresultants, whose last entry
/// is the resultant when the last PRS member is a nonzero constant. All divisions are exact.
pub fn subresultant_prs<R: Ring>(f: &[R], g: &[R]) -> (Vec<Vec<R>>, Vec<R>) {
    let n = degree(f).expect("subresultant PRS of a zero polynomial");
    let m = degree(g).expect("subresultant PRS of a zero polynomial");
    assert!(n >= m);
    let mut prs = vec![f.to_vec(), g.to_vec()];
    let mut d = n - m;
    let b = if (d + 1).is_multiple_of(2) {
        R::one()
    } else {
        R::one().neg()
    };
    let mut h: Vec<R> = prem(f, g).into_iter().map(|c| c.mul(&b)).collect();
    let mut lc = g[m].clone();
    let mut c = lc.pow(d);
    let mut scalars = vec![R::one(), c.clone()];
    c = c.neg();
    let (mut g, mut m) = (g.to_vec(), m);
    while !h.is_empty() {
        let k = h.len() - 1;
        prs.push(h.clone());
        let f = std::mem::replace(&mut g, h);
        d = m - k;
        m = k;
        let b = lc.neg().mul(&c.pow(d));
        h = prem(&f, &g).iter().map(|x| x.exact_div(&b)).collect();
        lc = g[m].clone();
        if d > 1 {
            let q = c.pow(d - 1);
            c = lc.neg().pow(d).exact_div(&q);
        } else {
            c = lc.neg();
        }
        scalars.push(c.neg());
    }
    (prs, scalars)
}

/// Resultant `res(f, g)` (the Sylvester determinant), via the subresultant PRS. Zero if either
/// argument is zero; `res(a, b) = 1` for nonzero constants. Handles `deg f < deg g` with
/// `res(f, g) = (−1)^(deg f · deg g) res(g, f)`.
pub fn resultant<R: Ring>(f: &[R], g: &[R]) -> R {
    let (Some(n), Some(m)) = (degree(f), degree(g)) else {
        return R::zero();
    };
    if n < m {
        let r = resultant(g, f);
        return if (n * m) % 2 == 1 { r.neg() } else { r };
    }
    let (prs, scalars) = subresultant_prs(f, g);
    if degree(prs.last().unwrap()).unwrap() > 0 {
        return R::zero();
    }
    scalars.last().unwrap().clone()
}

/// The principal subresultant coefficients `psc_j(f, g)` for `0 ≤ j < min(deg f, deg g)` that are
/// not identically zero, as `(j, psc_j)` in decreasing `j`, with their exact signs: `psc_j` is the
/// determinant of the square matrix formed by the first `n + m − 2j` columns of the matrix with
/// rows `x^(m−j−1)·f, …, x·f, f, x^(n−j−1)·g, …, x·g, g` (`n = deg f`, `m = deg g`), columns the
/// coefficients of `x^(n+m−j−1), …, x, 1`.
///
/// By the fundamental theorem of subresultants (Brown–Traub), if the subresultant PRS of `f` and
/// `g` (larger degree first) is `f, g, R₂, …, R_r` with degrees `d₀ ≥ d₁ > d₂ > … > d_r`, then
/// `psc_j` is nonzero exactly for `j ∈ {d₂, …, d_r}` and equals the scalar subresultant that
/// [`subresultant_prs`] records for `R_i` (`tests/nra_kernels.rs` checks this against the
/// determinant definition, signs included). Every other `psc_j` with `j < min(n, m)` is the zero
/// polynomial of the coefficient ring, so the list is complete: `psc_0` (the resultant) is missing
/// exactly when `f` and `g` have a common factor of positive degree. For `n < m` the PRS of
/// `(g, f)` is used with `psc_j(f, g) = (−1)^((n−j)(m−j)) psc_j(g, f)` (swapping the two row
/// blocks). Empty if either argument is zero or a constant.
pub fn principal_subresultant_coefficients<R: Ring>(f: &[R], g: &[R]) -> Vec<(usize, R)> {
    let (Some(n), Some(m)) = (degree(f), degree(g)) else {
        return Vec::new();
    };
    if n.min(m) == 0 {
        return Vec::new();
    }
    let swapped = n < m;
    let (a, b) = if swapped { (g, f) } else { (f, g) };
    let (prs, scalars) = subresultant_prs(a, b);
    (2..prs.len())
        .map(|i| {
            let j = degree(&prs[i]).unwrap();
            let s = scalars[i].clone();
            if swapped && ((n - j) * (m - j)) % 2 == 1 {
                (j, s.neg())
            } else {
                (j, s)
            }
        })
        .collect()
}

/// Discriminant `disc(f) = (−1)^(n(n−1)/2) · res(f, f') / lc(f)` with `n = deg f`. Zero for
/// constants and the zero polynomial (sympy's convention); `1` for linear `f`.
pub fn discriminant<R: Ring>(f: &[R]) -> R {
    let n = match degree(f) {
        Some(n) if n >= 1 => n,
        _ => return R::zero(),
    };
    let r = resultant(f, &derivative(f));
    let q = r.exact_div(&f[n]);
    if (n * (n - 1) / 2) % 2 == 1 {
        q.neg()
    } else {
        q
    }
}

/// The nonnegative gcd of `c` (`0` for an empty or all-zero slice).
pub(crate) fn int_gcd_slice(c: &[BigInt]) -> BigInt {
    let mut g = <BigInt as Zero>::zero();
    for x in c {
        g = g.gcd(x);
        if One::is_one(&g) {
            break;
        }
    }
    g.abs()
}
