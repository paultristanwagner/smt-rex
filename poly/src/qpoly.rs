//! Dense univariate polynomials over `Q`.

use crate::upoly::UPoly;
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Zero};
use std::fmt;
use std::ops::{Add, Mul, Neg, Sub};

/// A polynomial in `Q[x]`, ascending coefficients, no trailing zeros.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct QPoly {
    c: Vec<BigRational>,
}

fn trim(c: &mut Vec<BigRational>) {
    while c.last().is_some_and(|x| x.is_zero()) {
        c.pop();
    }
}

impl QPoly {
    pub fn zero() -> QPoly {
        QPoly { c: Vec::new() }
    }

    /// From ascending coefficients (trailing zeros allowed).
    pub fn new(mut c: Vec<BigRational>) -> QPoly {
        trim(&mut c);
        QPoly { c }
    }

    pub fn from_upoly(p: &UPoly) -> QPoly {
        QPoly {
            c: p.coeffs()
                .iter()
                .map(|x| BigRational::from_integer(x.clone()))
                .collect(),
        }
    }

    pub fn coeffs(&self) -> &[BigRational] {
        &self.c
    }

    pub fn coeff(&self, i: usize) -> BigRational {
        self.c.get(i).cloned().unwrap_or_else(BigRational::zero)
    }

    pub fn is_zero(&self) -> bool {
        self.c.is_empty()
    }

    pub fn degree(&self) -> Option<usize> {
        self.c.len().checked_sub(1)
    }

    pub fn lc(&self) -> BigRational {
        self.c.last().cloned().unwrap_or_else(BigRational::zero)
    }

    pub fn scale(&self, k: &BigRational) -> QPoly {
        QPoly::new(self.c.iter().map(|x| x * k).collect())
    }

    /// Divide by the leading coefficient (zero stays zero).
    pub fn monic(&self) -> QPoly {
        if self.is_zero() {
            return QPoly::zero();
        }
        let l = self.lc().recip();
        self.scale(&l)
    }

    /// `(den, p)` with `p` the integer polynomial `den · self` for the least positive common
    /// denominator `den`.
    pub fn clear_denominators(&self) -> (BigInt, UPoly) {
        let mut l = BigInt::one();
        for x in &self.c {
            l = l.lcm(x.denom());
        }
        let p = UPoly::new(self.c.iter().map(|x| (x * &l).to_integer()).collect());
        (l, p)
    }

    /// The primitive integer polynomial with positive leading coefficient that is a rational
    /// multiple of `self`.
    pub fn to_primitive(&self) -> UPoly {
        self.clear_denominators().1.primitive_part()
    }

    pub fn derivative(&self) -> QPoly {
        QPoly::new(
            self.c
                .iter()
                .enumerate()
                .skip(1)
                .map(|(i, c)| c * BigInt::from(i as u64))
                .collect(),
        )
    }

    /// Horner evaluation.
    pub fn eval(&self, x: &BigRational) -> BigRational {
        let mut acc = BigRational::zero();
        for c in self.c.iter().rev() {
            acc = acc * x + c;
        }
        acc
    }

    /// Euclidean division `self = q · g + r` with `deg r < deg g` (schoolbook long division over
    /// the field `Q`). Panics if `g` is zero.
    pub fn divrem(&self, g: &QPoly) -> (QPoly, QPoly) {
        let dg = g.degree().expect("division by the zero polynomial");
        let Some(n) = self.degree() else {
            return (QPoly::zero(), QPoly::zero());
        };
        if n < dg {
            return (QPoly::zero(), self.clone());
        }
        let inv = g.lc().recip();
        let mut r = self.c.clone();
        let mut q = vec![BigRational::zero(); n - dg + 1];
        for i in (0..=n - dg).rev() {
            let t = &r[i + dg] * &inv;
            if t.is_zero() {
                continue;
            }
            for (j, gj) in g.c.iter().enumerate() {
                r[i + j] -= &t * gj;
            }
            q[i] = t;
        }
        r.truncate(dg);
        (QPoly::new(q), QPoly::new(r))
    }

    /// Monic gcd over `Q` (Euclid's algorithm; `gcd(0, 0) = 0`). Coefficient growth makes this
    /// slow for large inputs; [`UPoly::gcd`] is the fast path.
    pub fn gcd(&self, other: &QPoly) -> QPoly {
        let (mut a, mut b) = (self.clone(), other.clone());
        while !b.is_zero() {
            let r = a.divrem(&b).1;
            a = b;
            b = r;
        }
        a.monic()
    }
}

impl fmt::Display for QPoly {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            return f.write_str("0");
        }
        let terms: Vec<String> = self
            .c
            .iter()
            .enumerate()
            .rev()
            .filter(|(_, c)| !c.is_zero())
            .map(|(i, c)| match i {
                0 => format!("({c})"),
                1 => format!("({c})*x"),
                _ => format!("({c})*x^{i}"),
            })
            .collect();
        f.write_str(&terms.join(" + "))
    }
}

impl Add for &QPoly {
    type Output = QPoly;
    fn add(self, o: &QPoly) -> QPoly {
        let n = self.c.len().max(o.c.len());
        QPoly::new((0..n).map(|i| self.coeff(i) + o.coeff(i)).collect())
    }
}

impl Sub for &QPoly {
    type Output = QPoly;
    fn sub(self, o: &QPoly) -> QPoly {
        let n = self.c.len().max(o.c.len());
        QPoly::new((0..n).map(|i| self.coeff(i) - o.coeff(i)).collect())
    }
}

impl Neg for &QPoly {
    type Output = QPoly;
    fn neg(self) -> QPoly {
        QPoly {
            c: self.c.iter().map(|x| -x).collect(),
        }
    }
}

impl Mul for &QPoly {
    type Output = QPoly;
    fn mul(self, o: &QPoly) -> QPoly {
        if self.is_zero() || o.is_zero() {
            return QPoly::zero();
        }
        let mut c = vec![BigRational::zero(); self.c.len() + o.c.len() - 1];
        for (i, a) in self.c.iter().enumerate() {
            for (j, b) in o.c.iter().enumerate() {
                c[i + j] += a * b;
            }
        }
        QPoly::new(c)
    }
}
