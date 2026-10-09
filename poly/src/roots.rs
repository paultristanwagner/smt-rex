//! Real root isolation for square-free integer polynomials: Descartes' rule of signs with
//! Vincent–Collins–Akritas bisection (G. E. Collins and A. G. Akritas, "Polynomial real root
//! isolation using Descartes' rule of signs", SYMSAC 1976), plus bisection refinement and the
//! Descartes test on arbitrary rational intervals.
//!
//! Isolating intervals are *open* with dyadic endpoints, and no endpoint is ever a root: every
//! endpoint is the root bound `±2^L`, `0` when `0` is not a root (else `±2^−L'`, a lower bound
//! on the nonzero roots' magnitudes), or a bisection point. A root met exactly at a bisection
//! point is reported exactly, and cells that have such a root on their boundary are bisected
//! further until the boundary root is no longer an endpoint of an output interval.

use crate::qpoly::QPoly;
use crate::upoly::UPoly;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// One isolated real root.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Isolation {
    /// The root is exactly this rational.
    Exact(BigRational),
    /// The open interval `(lo, hi)` contains exactly one root, and neither endpoint is a root.
    Open(BigRational, BigRational),
}

impl Isolation {
    pub fn lower(&self) -> &BigRational {
        match self {
            Isolation::Exact(r) => r,
            Isolation::Open(lo, _) => lo,
        }
    }

    pub fn upper(&self) -> &BigRational {
        match self {
            Isolation::Exact(r) => r,
            Isolation::Open(_, hi) => hi,
        }
    }
}

/// Smallest `L` with every complex root `|z| < 2^L` (Cauchy's bound `1 + max |aᵢ/aₙ|`).
/// Panics on constants.
pub fn root_bound_log2(f: &UPoly) -> u64 {
    let n = f.degree().expect("root bound of zero");
    assert!(n >= 1, "root bound of a constant");
    let an = f.lc().abs();
    let m = f.coeffs()[..n]
        .iter()
        .map(|c| c.abs())
        .max()
        .unwrap_or_default();
    // ceil(m / an) + 1 < 2^bits
    let q = (&m + &an - BigInt::one()) / &an + BigInt::one();
    q.bits()
}

/// Descartes' bound for the number of roots of `f` in `(0, 1)`: the sign variations of
/// `(x+1)^n f(1/(x+1))`. Zero means no root in `(0, 1)`, one means exactly one; in general it
/// exceeds the root count by an even number.
pub fn descartes_unit(f: &UPoly) -> usize {
    f.reverse().shift_one().sign_variations()
}

/// Descartes' bound for the roots of `f` in the open interval `(lo, hi)`, `lo < hi`: the bound
/// of [`descartes_unit`] for `f(lo + (hi − lo)·x)`.
pub fn descartes_interval(f: &UPoly, lo: &BigRational, hi: &BigRational) -> usize {
    if f.is_constant() {
        return 0;
    }
    descartes_unit(&compose_affine(f, lo, &(hi - lo)))
}

/// The integer polynomial proportional to `f(a + b·x)` (Horner composition over `Q`, then
/// cleared denominators).
pub fn compose_affine(f: &UPoly, a: &BigRational, b: &BigRational) -> UPoly {
    let lin = QPoly::new(vec![a.clone(), b.clone()]);
    let mut acc = QPoly::zero();
    for c in f.coeffs().iter().rev() {
        acc = &(&acc * &lin) + &QPoly::new(vec![BigRational::from_integer(c.clone())]);
    }
    acc.to_primitive()
}

/// Isolate all real roots of a square-free `f` of positive degree, in increasing order
/// (Vincent–Collins–Akritas). Roots met exactly (at `0` or at a bisection point) are
/// [`Isolation::Exact`]. The result is undefined for non-square-free input.
pub fn isolate_squarefree(f: &UPoly) -> Vec<Isolation> {
    assert!(!f.is_constant(), "isolating the roots of a constant");
    let (g, k) = f.strip_x();
    let mut out = Vec::new();
    if g.is_constant() {
        if k > 0 {
            out.push(Isolation::Exact(BigRational::zero()));
        }
        return out;
    }
    let l = root_bound_log2(&g);
    let scale = BigRational::from_integer(BigInt::one() << l);
    // Negative roots: roots of g(−x) in (0, 2^L), mirrored.
    let mut neg = vca_unit(&g.negate_var().scale_var_pow2(l));
    neg.reverse();
    for iso in neg {
        out.push(match iso {
            Isolation::Exact(r) => Isolation::Exact(-(r * &scale)),
            Isolation::Open(lo, hi) => Isolation::Open(-(hi * &scale), -(lo * &scale)),
        });
    }
    if k > 0 {
        out.push(Isolation::Exact(BigRational::zero()));
    }
    for iso in vca_unit(&g.scale_var_pow2(l)) {
        out.push(match iso {
            Isolation::Exact(r) => Isolation::Exact(r * &scale),
            Isolation::Open(lo, hi) => Isolation::Open(lo * &scale, hi * &scale),
        });
    }
    if k > 0 {
        // 0 is a root of f, so it must not stay an endpoint: every nonzero root of g has
        // |r| > 2^−L' with L' the root bound of the reversed polynomial (roots 1/r).
        let lb = BigRational::new(
            BigInt::one(),
            BigInt::one() << root_bound_log2(&g.reverse()),
        );
        for iso in &mut out {
            if let Isolation::Open(lo, hi) = iso {
                if lo.is_zero() {
                    *lo = lb.clone();
                } else if hi.is_zero() {
                    *hi = -lb.clone();
                }
            }
        }
    }
    out
}

/// VCA bisection on `(0, 1)` for square-free `q`, results in increasing order.
fn vca_unit(q: &UPoly) -> Vec<Isolation> {
    // Work items: (polynomial whose (0,1) roots are q's roots in (c/2^k, (c+1)/2^k), c, k).
    let mut stack = vec![(q.primitive_part(), BigInt::zero(), 0u64)];
    let mut out: Vec<(BigRational, Isolation)> = Vec::new();
    let dy = |c: &BigInt, k: u64| BigRational::new(c.clone(), BigInt::one() << k);
    while let Some((p, c, k)) = stack.pop() {
        if p.is_constant() {
            continue;
        }
        // An endpoint that is a root of f (a root found exactly at an earlier bisection point)
        // must not end up on an isolating interval: keep bisecting such cells, which shrinks
        // the cell adjacent to that root until it holds no other root (Descartes count 0).
        let endpoint_root = p.coeff(0).is_zero() || p.coeffs().iter().sum::<BigInt>().is_zero();
        match descartes_unit(&p) {
            0 => {}
            1 if !endpoint_root => {
                let lo = dy(&c, k);
                out.push((lo.clone(), Isolation::Open(lo, dy(&(&c + 1), k))));
            }
            _ => {
                let left = p.scale_var_inv_pow2(1);
                let right = left.shift_one();
                let c2: BigInt = &c * 2u32;
                if right.coeff(0).is_zero() {
                    let mid = dy(&(&c2 + 1), k + 1);
                    out.push((mid.clone(), Isolation::Exact(mid)));
                }
                stack.push((left.primitive_part(), c2.clone(), k + 1));
                stack.push((right.primitive_part(), c2 + 1, k + 1));
            }
        }
    }
    out.sort_by(|a, b| a.0.cmp(&b.0));
    out.into_iter().map(|(_, i)| i).collect()
}

/// Bisect an isolating interval `(lo, hi)` of a root of square-free `f` (`f(lo)`, `f(hi)` nonzero
/// with opposite signs) until its width is at most `width`, or until a bisection point is the
/// root. `width` must be positive.
pub fn refine(f: &UPoly, lo: &BigRational, hi: &BigRational, width: &BigRational) -> Isolation {
    assert!(width.is_positive());
    let (mut lo, mut hi) = (lo.clone(), hi.clone());
    let slo = f.sign_at(&lo);
    debug_assert!(
        slo != 0 && slo == -f.sign_at(&hi),
        "not an isolating interval"
    );
    let two = BigRational::from_integer(BigInt::from(2));
    while &(&hi - &lo) > width {
        let mid = (&lo + &hi) / &two;
        let s = f.sign_at(&mid);
        if s == 0 {
            return Isolation::Exact(mid);
        }
        if s == slo {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    Isolation::Open(lo, hi)
}

/// One bisection step of [`refine`], in place. Returns `Some(mid)` if `mid` is the root.
pub(crate) fn bisect_once(
    f: &UPoly,
    lo: &mut BigRational,
    hi: &mut BigRational,
) -> Option<BigRational> {
    let mid = (&*lo + &*hi) / BigRational::from_integer(BigInt::from(2));
    let s = f.sign_at(&mid);
    if s == 0 {
        return Some(mid);
    }
    if s == f.sign_at(lo) {
        *lo = mid;
    } else {
        *hi = mid;
    }
    None
}
