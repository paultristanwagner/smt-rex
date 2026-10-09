//! Helpers shared by the integration tests: constructors and independent slow oracles.
#![allow(dead_code)]

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use smtrex_poly::rng::SplitMix64;
use smtrex_poly::{QPoly, UPoly};

pub fn p(c: &[i64]) -> UPoly {
    UPoly::from_i64s(c)
}

pub fn q(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

pub fn rand_poly(rng: &mut SplitMix64, dmin: usize, dmax: usize, bound: i64) -> UPoly {
    let deg = rng.range(dmin as i64, dmax as i64) as usize;
    let mut c: Vec<i64> = (0..=deg).map(|_| rng.range(-bound, bound)).collect();
    if c[deg] == 0 {
        c[deg] = 1;
    }
    p(&c)
}

/// Determinant by fraction-free Bareiss elimination.
pub fn bareiss_det(mut m: Vec<Vec<BigInt>>) -> BigInt {
    let n = m.len();
    if n == 0 {
        return BigInt::one();
    }
    let mut sign = BigInt::one();
    let mut prev = BigInt::one();
    for k in 0..n - 1 {
        if m[k][k].is_zero() {
            let Some(r) = (k + 1..n).find(|&r| !m[r][k].is_zero()) else {
                return BigInt::zero();
            };
            m.swap(k, r);
            sign = -sign;
        }
        for i in k + 1..n {
            for j in k + 1..n {
                m[i][j] = (&m[i][j] * &m[k][k] - &m[i][k] * &m[k][j]) / &prev;
            }
        }
        prev = m[k][k].clone();
    }
    sign * &m[n - 1][n - 1]
}

/// Resultant as the Sylvester determinant (independent oracle).
pub fn sylvester_resultant(f: &UPoly, g: &UPoly) -> BigInt {
    let (Some(n), Some(m)) = (f.degree(), g.degree()) else {
        return BigInt::zero();
    };
    let size = n + m;
    if size == 0 {
        return BigInt::one();
    }
    let mut mat = vec![vec![BigInt::zero(); size]; size];
    for i in 0..m {
        for j in 0..=n {
            mat[i][i + j] = f.coeff(n - j);
        }
    }
    for i in 0..n {
        for j in 0..=m {
            mat[m + i][i + j] = g.coeff(m - j);
        }
    }
    bareiss_det(mat)
}

/// Number of distinct real roots in the half-open interval `(a, b]` by Sturm's theorem over `Q`
/// (independent of the Descartes code).
pub fn sturm_count(f: &UPoly, a: &BigRational, b: &BigRational) -> usize {
    let f = QPoly::from_upoly(f);
    let mut seq = vec![f.clone(), f.derivative()];
    loop {
        let n = seq.len();
        if seq[n - 1].is_zero() {
            seq.pop();
            break;
        }
        let r = seq[n - 2].divrem(&seq[n - 1]).1;
        seq.push(-&r);
    }
    let var = |x: &BigRational| {
        let signs: Vec<i32> = seq
            .iter()
            .map(|s| {
                let v = s.eval(x);
                if v.is_zero() {
                    0
                } else if v.is_positive() {
                    1
                } else {
                    -1
                }
            })
            .filter(|&s| s != 0)
            .collect();
        signs.windows(2).filter(|w| w[0] != w[1]).count()
    };
    var(a) - var(b)
}
