//! Dense univariate polynomials over `Z`.

use crate::qpoly::QPoly;
use crate::ring::{self, int_gcd_slice};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Pow, Signed, Zero};
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Mul, Neg, Sub};

/// A polynomial in `Z[x]`, coefficients in ascending degree order with no trailing zeros (the
/// zero polynomial has no coefficients). The representation is canonical, so the derived
/// `Eq`/`Hash` are equality of polynomials.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct UPoly {
    c: Vec<BigInt>,
}

/// `f = content · ∏ fᵢ^kᵢ` with every `fᵢ` primitive, of positive degree and positive leading
/// coefficient. Used for both the square-free decomposition and the irreducible factorisation.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Factored {
    /// The signed content: `0` for the zero polynomial, else `±cont(f)` carrying the sign of
    /// `lc(f)`.
    pub content: BigInt,
    /// Factors with their multiplicities; each producer documents its order.
    pub factors: Vec<(UPoly, usize)>,
}

impl Factored {
    /// Multiply the factorisation back out.
    pub fn expand(&self) -> UPoly {
        let mut p = UPoly::constant(self.content.clone());
        for (f, k) in &self.factors {
            p = &p * &f.pow(*k);
        }
        p
    }
}

impl UPoly {
    /// The zero polynomial.
    pub fn zero() -> UPoly {
        UPoly { c: Vec::new() }
    }

    /// The constant `k`.
    pub fn constant(k: BigInt) -> UPoly {
        UPoly::new(vec![k])
    }

    /// The polynomial `x`.
    pub fn x() -> UPoly {
        UPoly::from_i64s(&[0, 1])
    }

    /// From ascending coefficients (trailing zeros allowed).
    pub fn new(mut c: Vec<BigInt>) -> UPoly {
        ring::trim(&mut c);
        UPoly { c }
    }

    /// From ascending `i64` coefficients.
    pub fn from_i64s(c: &[i64]) -> UPoly {
        UPoly::new(c.iter().map(|&x| BigInt::from(x)).collect())
    }

    /// `∏ (x − rᵢ)` for integer roots.
    pub fn from_roots(roots: &[i64]) -> UPoly {
        roots.iter().fold(UPoly::from_i64s(&[1]), |acc, &r| {
            &acc * &UPoly::from_i64s(&[-r, 1])
        })
    }

    /// Ascending coefficients.
    pub fn coeffs(&self) -> &[BigInt] {
        &self.c
    }

    /// Coefficient of `x^i` (zero beyond the degree).
    pub fn coeff(&self, i: usize) -> BigInt {
        self.c.get(i).cloned().unwrap_or_default()
    }

    pub fn is_zero(&self) -> bool {
        self.c.is_empty()
    }

    /// Constant (including zero).
    pub fn is_constant(&self) -> bool {
        self.c.len() <= 1
    }

    /// Degree; `None` for the zero polynomial.
    pub fn degree(&self) -> Option<usize> {
        ring::degree(&self.c)
    }

    /// Leading coefficient (zero for the zero polynomial).
    pub fn lc(&self) -> BigInt {
        self.c.last().cloned().unwrap_or_default()
    }

    /// Multiply every coefficient by `k`.
    pub fn scale(&self, k: &BigInt) -> UPoly {
        UPoly::new(self.c.iter().map(|x| x * k).collect())
    }

    /// `self^k` by binary powering.
    pub fn pow(&self, mut k: usize) -> UPoly {
        let mut base = self.clone();
        let mut acc = UPoly::from_i64s(&[1]);
        while k > 0 {
            if k & 1 == 1 {
                acc = &acc * &base;
            }
            k >>= 1;
            if k > 0 {
                base = &base * &base;
            }
        }
        acc
    }

    /// Content: the nonnegative gcd of the coefficients (`0` for the zero polynomial).
    pub fn content(&self) -> BigInt {
        int_gcd_slice(&self.c)
    }

    /// Primitive part with a positive leading coefficient, so that
    /// `self = ±content · primitive_part`. Zero stays zero.
    pub fn primitive_part(&self) -> UPoly {
        self.content_primitive().1
    }

    /// The signed content `±cont(f)` (sign of the leading coefficient) and the primitive part
    /// with positive leading coefficient: `f = c · p`.
    pub fn content_primitive(&self) -> (BigInt, UPoly) {
        if self.is_zero() {
            return (BigInt::zero(), UPoly::zero());
        }
        let mut g = self.content();
        if self.lc().is_negative() {
            g = -g;
        }
        let p = UPoly {
            c: self.c.iter().map(|x| x / &g).collect(),
        };
        (g, p)
    }

    /// Formal derivative.
    pub fn derivative(&self) -> UPoly {
        UPoly {
            c: ring::derivative(&self.c),
        }
    }

    /// The homogenised value `d^n · f(num/d)` for `n = deg f` (Horner's rule on the integer
    /// homogenisation, no rational arithmetic). For `d > 0` it has the sign of `f(num/d)`.
    pub fn eval_homogeneous(&self, num: &BigInt, den: &BigInt) -> BigInt {
        if self.is_zero() {
            return BigInt::zero();
        }
        // Σ aᵢ numⁱ den^(n−i): Horner in num with a running power of den.
        let mut acc = BigInt::zero();
        let mut dpow = BigInt::one();
        for (i, c) in self.c.iter().enumerate().rev() {
            acc = acc * num + c * &dpow;
            if i > 0 {
                dpow *= den;
            }
        }
        acc
    }

    /// Value at a rational point.
    pub fn eval(&self, x: &BigRational) -> BigRational {
        let Some(n) = self.degree() else {
            return BigRational::zero();
        };
        let h = self.eval_homogeneous(x.numer(), x.denom());
        BigRational::new(h, Pow::pow(x.denom(), n))
    }

    /// Sign (`-1`, `0`, `1`) of `f(x)` at a rational point.
    pub fn sign_at(&self, x: &BigRational) -> i8 {
        sign(&self.eval_homogeneous(x.numer(), x.denom()))
    }

    /// Exact division in `Z[x]`: `Some(q)` with `self = q · d` if it exists (long division that
    /// requires every leading-coefficient quotient to be integral). Panics if `d` is zero.
    pub fn div_exact(&self, d: &UPoly) -> Option<UPoly> {
        let dd = d.degree().expect("division by the zero polynomial");
        if self.is_zero() {
            return Some(UPoly::zero());
        }
        let n = self.degree().unwrap();
        if n < dd {
            return None;
        }
        let mut r = self.c.clone();
        let mut q = vec![BigInt::zero(); n - dd + 1];
        let lcd = &d.c[dd];
        for i in (0..=n - dd).rev() {
            let top = &r[i + dd];
            if top.is_zero() {
                continue;
            }
            let (qi, rem) = top.div_rem(lcd);
            if !rem.is_zero() {
                return None;
            }
            for (j, dj) in d.c.iter().enumerate() {
                r[i + j] -= &qi * dj;
            }
            q[i] = qi;
        }
        if r.iter().any(|x| !x.is_zero()) {
            return None;
        }
        Some(UPoly::new(q))
    }

    /// Pseudo-remainder `prem(self, g)` (see [`ring::prem`]).
    pub fn prem(&self, g: &UPoly) -> UPoly {
        UPoly::new(ring::prem(&self.c, &g.c))
    }

    /// Quotient and remainder over `Q` (see [`QPoly::divrem`]).
    pub fn divrem_q(&self, g: &UPoly) -> (QPoly, QPoly) {
        QPoly::from_upoly(self).divrem(&QPoly::from_upoly(g))
    }

    /// Greatest common divisor in `Z[x]`, normalised to a positive leading coefficient
    /// (`gcd(0, 0) = 0`). Algorithm: split off contents, run the subresultant PRS
    /// ([`ring::subresultant_prs`]) on the primitive parts and take the primitive part of its
    /// last nonzero member, then multiply by the gcd of the contents.
    pub fn gcd(&self, other: &UPoly) -> UPoly {
        if self.is_zero() {
            return other.primitive_part().scale(&other.content());
        }
        if other.is_zero() {
            return self.primitive_part().scale(&self.content());
        }
        let cg = self.content().gcd(&other.content());
        let (a, b) = (self.primitive_part(), other.primitive_part());
        let (a, b) = if a.degree() >= b.degree() {
            (a, b)
        } else {
            (b, a)
        };
        let g = if b.is_constant() {
            UPoly::from_i64s(&[1])
        } else {
            let (prs, _) = ring::subresultant_prs(&a.c, &b.c);
            UPoly::new(prs.last().unwrap().clone()).primitive_part()
        };
        g.scale(&cg)
    }

    /// Square-free decomposition `f = c · ∏ aᵢ^i` with the `aᵢ` primitive, square-free,
    /// pairwise coprime and of positive leading coefficient (Yun's algorithm, D. Y. Y. Yun, "On
    /// square-free decomposition algorithms", SYMSAC 1976, run over `Z` with exact divisions —
    /// exact because every divisor is primitive, by Gauss's lemma). Factors are returned in
    /// increasing multiplicity; constants are omitted.
    pub fn square_free(&self) -> Factored {
        let (content, f) = self.content_primitive();
        let mut factors = Vec::new();
        if f.degree().unwrap_or(0) == 0 {
            return Factored { content, factors };
        }
        let df = f.derivative();
        let a0 = f.gcd(&df);
        let mut b = f.div_exact(&a0).expect("Yun: gcd divides f");
        let mut c = df.div_exact(&a0).expect("Yun: gcd divides f'");
        let mut d = &c - &b.derivative();
        let mut i = 1;
        while !b.is_constant() {
            let a = b.gcd(&d);
            if !a.is_constant() {
                factors.push((a.clone(), i));
            }
            b = b.div_exact(&a).expect("Yun: a_i divides b_i");
            c = d.div_exact(&a).expect("Yun: a_i divides d_i");
            d = &c - &b.derivative();
            i += 1;
        }
        Factored { content, factors }
    }

    /// The square-free part `f / gcd(f, f')`, primitive with positive leading coefficient.
    pub fn square_free_part(&self) -> UPoly {
        if self.is_constant() {
            return UPoly::from_i64s(&[1]);
        }
        let p = self.primitive_part();
        let g = p.gcd(&p.derivative());
        p.div_exact(&g).unwrap()
    }

    /// Resultant `res(self, other)` (subresultant PRS, [`ring::resultant`]).
    pub fn resultant(&self, other: &UPoly) -> BigInt {
        ring::resultant(&self.c, &other.c)
    }

    /// Discriminant (see [`ring::discriminant`]).
    pub fn discriminant(&self) -> BigInt {
        ring::discriminant(&self.c)
    }

    /// Irreducible factorisation over `Z` (see [`crate::factor::factor`]).
    pub fn factor(&self) -> Factored {
        crate::factor::factor(self)
    }

    /// `f(x + 1)` (Taylor shift by one, the classical `O(n²)` additions scheme).
    pub fn shift_one(&self) -> UPoly {
        let mut a = self.c.clone();
        let n = a.len();
        for i in 0..n.saturating_sub(1) {
            for j in (i..n - 1).rev() {
                let t = a[j + 1].clone();
                a[j] += t;
            }
        }
        UPoly::new(a)
    }

    /// `f(x + k)` for an integer `k` (Taylor shift, `O(n²)`).
    pub fn shift(&self, k: &BigInt) -> UPoly {
        let mut a = self.c.clone();
        let n = a.len();
        for i in 0..n.saturating_sub(1) {
            for j in (i..n - 1).rev() {
                let t = &a[j + 1] * k;
                a[j] += t;
            }
        }
        UPoly::new(a)
    }

    /// `f(−x)`.
    pub fn negate_var(&self) -> UPoly {
        UPoly::new(
            self.c
                .iter()
                .enumerate()
                .map(|(i, c)| if i % 2 == 1 { -c } else { c.clone() })
                .collect(),
        )
    }

    /// `f(2^k · x)`.
    pub fn scale_var_pow2(&self, k: u64) -> UPoly {
        UPoly::new(
            self.c
                .iter()
                .enumerate()
                .map(|(i, c)| c << (k * i as u64))
                .collect(),
        )
    }

    /// `2^(k·n) · f(x / 2^k)` for `n = deg f`: halves the root positions without leaving `Z[x]`.
    pub fn scale_var_inv_pow2(&self, k: u64) -> UPoly {
        let Some(n) = self.degree() else {
            return UPoly::zero();
        };
        UPoly::new(
            self.c
                .iter()
                .enumerate()
                .map(|(i, c)| c << (k * (n - i) as u64))
                .collect(),
        )
    }

    /// `x^n · f(1/x)` for `n = deg f` (coefficient reversal).
    pub fn reverse(&self) -> UPoly {
        let mut c = self.c.clone();
        c.reverse();
        UPoly::new(c)
    }

    /// Number of sign changes in the coefficient sequence, zeros skipped (Descartes' rule).
    pub fn sign_variations(&self) -> usize {
        let mut last = 0i8;
        let mut v = 0;
        for c in &self.c {
            let s = sign(c);
            if s != 0 {
                if last != 0 && s != last {
                    v += 1;
                }
                last = s;
            }
        }
        v
    }

    /// Divide by `x` as often as possible; returns the multiplicity of the root `0`.
    pub fn strip_x(&self) -> (UPoly, usize) {
        let k = self.c.iter().take_while(|c| c.is_zero()).count();
        if self.is_zero() {
            return (UPoly::zero(), 0);
        }
        (
            UPoly {
                c: self.c[k..].to_vec(),
            },
            k,
        )
    }

    /// Format with a variable name.
    pub fn display_with(&self, var: &str) -> String {
        if self.is_zero() {
            return "0".into();
        }
        let mut s = String::new();
        for (i, c) in self.c.iter().enumerate().rev() {
            if c.is_zero() {
                continue;
            }
            let neg = c.is_negative();
            let a = c.abs();
            if s.is_empty() {
                if neg {
                    s.push('-');
                }
            } else {
                s.push_str(if neg { " - " } else { " + " });
            }
            let mono = match i {
                0 => String::new(),
                1 => var.to_string(),
                _ => format!("{var}^{i}"),
            };
            if i == 0 || !a.is_one() {
                s.push_str(&a.to_string());
                if i > 0 {
                    s.push('*');
                }
            }
            s.push_str(&mono);
        }
        s
    }
}

pub(crate) fn sign(x: &BigInt) -> i8 {
    match x.cmp(&BigInt::zero()) {
        Ordering::Less => -1,
        Ordering::Equal => 0,
        Ordering::Greater => 1,
    }
}

impl fmt::Display for UPoly {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.display_with("x"))
    }
}

impl Add for &UPoly {
    type Output = UPoly;
    fn add(self, o: &UPoly) -> UPoly {
        let n = self.c.len().max(o.c.len());
        UPoly::new((0..n).map(|i| self.coeff(i) + o.coeff(i)).collect())
    }
}

impl Sub for &UPoly {
    type Output = UPoly;
    fn sub(self, o: &UPoly) -> UPoly {
        let n = self.c.len().max(o.c.len());
        UPoly::new((0..n).map(|i| self.coeff(i) - o.coeff(i)).collect())
    }
}

impl Neg for &UPoly {
    type Output = UPoly;
    fn neg(self) -> UPoly {
        UPoly {
            c: self.c.iter().map(|x| -x).collect(),
        }
    }
}

impl Mul for &UPoly {
    type Output = UPoly;
    /// Schoolbook multiplication.
    fn mul(self, o: &UPoly) -> UPoly {
        if self.is_zero() || o.is_zero() {
            return UPoly::zero();
        }
        let mut c = vec![BigInt::zero(); self.c.len() + o.c.len() - 1];
        for (i, a) in self.c.iter().enumerate() {
            if a.is_zero() {
                continue;
            }
            for (j, b) in o.c.iter().enumerate() {
                c[i + j] += a * b;
            }
        }
        UPoly::new(c)
    }
}

impl ring::Ring for UPoly {
    fn zero() -> Self {
        UPoly::zero()
    }
    fn one() -> Self {
        UPoly::from_i64s(&[1])
    }
    fn is_zero(&self) -> bool {
        self.c.is_empty()
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
        self.div_exact(o).expect("inexact polynomial division")
    }
    fn from_i64(n: i64) -> Self {
        UPoly::from_i64s(&[n])
    }
}
