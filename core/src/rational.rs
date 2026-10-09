//! Exact rational arithmetic for the arithmetic theories.
//!
//! [`Rational`] is exact and fast in the common case: a value whose numerator and denominator fit
//! in an `i64` is stored inline and computed with `i128` intermediates; anything larger moves to
//! a heap-allocated `BigRational`, and results that fit again move back. The representation is
//! canonical (lowest terms, positive denominator, `Small` whenever the value fits), so the derived
//! `Eq` and `Hash` are value equality.
//!
//! [`DeltaRational`] is `value + delta·δ` for an infinitesimal δ > 0, which Simplex uses to treat
//! strict bounds exactly (`x < c` is `x ≤ c − δ`). Its order is lexicographic.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, ToPrimitive};
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Sub};

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Rational {
    /// `num / den` in lowest terms, `den > 0`.
    Small(i64, i64),
    /// Only for values that do not fit `Small`.
    Big(Box<BigRational>),
}

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

impl Rational {
    pub fn zero() -> Rational {
        Rational::Small(0, 1)
    }

    pub fn one() -> Rational {
        Rational::Small(1, 1)
    }

    pub fn from_int(n: i64) -> Rational {
        Rational::Small(n, 1)
    }

    /// `num / den`. Panics if `den == 0`.
    pub fn new(num: i64, den: i64) -> Rational {
        assert!(den != 0, "zero denominator");
        Rational::from_i128(num as i128, den as i128)
    }

    /// Build from `i128` parts, reducing and choosing the representation.
    fn from_i128(num: i128, den: i128) -> Rational {
        debug_assert!(den != 0);
        if num == 0 {
            return Rational::zero();
        }
        let neg = (num < 0) != (den < 0);
        let (n, d) = (num.unsigned_abs(), den.unsigned_abs());
        let g = gcd_u128(n, d);
        let (n, d) = (n / g, d / g);
        if n <= i64::MAX as u128 && d <= i64::MAX as u128 {
            let n = n as i64;
            return Rational::Small(if neg { -n } else { n }, d as i64);
        }
        let n = BigInt::from(n);
        let n = if neg { -n } else { n };
        Rational::Big(Box::new(BigRational::new_raw(n, BigInt::from(d))))
    }

    /// Build from a `BigRational`, demoting to `Small` if it fits.
    pub fn from_big(r: BigRational) -> Rational {
        // BigRational arithmetic keeps values reduced with a positive denominator.
        if let (Some(n), Some(d)) = (r.numer().to_i64(), r.denom().to_i64()) {
            return Rational::Small(n, d);
        }
        Rational::Big(Box::new(r))
    }

    pub fn to_big(&self) -> BigRational {
        match self {
            Rational::Small(n, d) => BigRational::new_raw(BigInt::from(*n), BigInt::from(*d)),
            Rational::Big(b) => (**b).clone(),
        }
    }

    pub fn is_zero(&self) -> bool {
        matches!(self, Rational::Small(0, _))
    }

    pub fn is_integer(&self) -> bool {
        match self {
            Rational::Small(_, d) => *d == 1,
            Rational::Big(b) => b.is_integer(),
        }
    }

    /// -1, 0 or 1.
    pub fn signum(&self) -> i32 {
        match self {
            Rational::Small(n, _) => n.signum() as i32,
            Rational::Big(b) => {
                if b.is_positive() {
                    1
                } else if b.is_negative() {
                    -1
                } else {
                    0
                }
            }
        }
    }

    pub fn is_positive(&self) -> bool {
        self.signum() > 0
    }

    pub fn is_negative(&self) -> bool {
        self.signum() < 0
    }

    pub fn abs(&self) -> Rational {
        if self.is_negative() {
            -self
        } else {
            self.clone()
        }
    }

    /// The reciprocal. Panics on zero.
    pub fn recip(&self) -> Rational {
        match self {
            Rational::Small(n, d) => {
                assert!(*n != 0, "reciprocal of zero");
                Rational::from_i128(*d as i128, *n as i128)
            }
            Rational::Big(b) => Rational::from_big(b.recip()),
        }
    }

    pub fn floor(&self) -> Rational {
        match self {
            Rational::Small(n, d) => Rational::Small(n.div_euclid(*d), 1),
            Rational::Big(b) => Rational::from_big(b.floor()),
        }
    }

    pub fn ceil(&self) -> Rational {
        match self {
            Rational::Small(n, d) => {
                let f = n.div_euclid(*d);
                Rational::Small(if n.rem_euclid(*d) == 0 { f } else { f + 1 }, 1)
            }
            Rational::Big(b) => Rational::from_big(b.ceil()),
        }
    }

    pub fn numer(&self) -> BigInt {
        match self {
            Rational::Small(n, _) => BigInt::from(*n),
            Rational::Big(b) => b.numer().clone(),
        }
    }

    pub fn denom(&self) -> BigInt {
        match self {
            Rational::Small(_, d) => BigInt::from(*d),
            Rational::Big(b) => b.denom().clone(),
        }
    }

    /// Parse an SMT-LIB numeral (`42`) or decimal (`3.25`). No sign, no exponent.
    pub fn parse_decimal(s: &str) -> Option<Rational> {
        let (int, frac) = match s.split_once('.') {
            Some((i, f)) => (i, f),
            None => (s, ""),
        };
        if int.is_empty() || !int.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        if s.contains('.') && (frac.is_empty() || !frac.bytes().all(|b| b.is_ascii_digit())) {
            return None;
        }
        let digits: BigInt = format!("{int}{frac}").parse().ok()?;
        let den = num_traits::pow(BigInt::from(10), frac.len());
        Some(Rational::from_big(BigRational::new(digits, den)))
    }

    /// `self * a + b`, the inner step of Simplex row updates.
    pub fn mul_add(&self, a: &Rational, b: &Rational) -> Rational {
        &(self * a) + b
    }
}

impl Default for Rational {
    fn default() -> Rational {
        Rational::zero()
    }
}

impl From<i64> for Rational {
    fn from(n: i64) -> Rational {
        Rational::from_int(n)
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Rational) -> Ordering {
        match (self, other) {
            (Rational::Small(a, b), Rational::Small(c, d)) => {
                if b == d {
                    a.cmp(c)
                } else {
                    (*a as i128 * *d as i128).cmp(&(*c as i128 * *b as i128))
                }
            }
            _ => self.to_big().cmp(&other.to_big()),
        }
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Add for &Rational {
    type Output = Rational;
    fn add(self, o: &Rational) -> Rational {
        if let (Rational::Small(a, b), Rational::Small(c, d)) = (self, o) {
            if b == d {
                // Same denominator (often 1): one i128 add, reduction only if needed.
                return Rational::from_i128(*a as i128 + *c as i128, *b as i128);
            }
            let (a, b, c, d) = (*a as i128, *b as i128, *c as i128, *d as i128);
            return Rational::from_i128(a * d + c * b, b * d);
        }
        Rational::from_big(self.to_big() + o.to_big())
    }
}

impl Sub for &Rational {
    type Output = Rational;
    fn sub(self, o: &Rational) -> Rational {
        if let (Rational::Small(a, b), Rational::Small(c, d)) = (self, o) {
            if b == d {
                return Rational::from_i128(*a as i128 - *c as i128, *b as i128);
            }
            let (a, b, c, d) = (*a as i128, *b as i128, *c as i128, *d as i128);
            return Rational::from_i128(a * d - c * b, b * d);
        }
        Rational::from_big(self.to_big() - o.to_big())
    }
}

impl Mul for &Rational {
    type Output = Rational;
    fn mul(self, o: &Rational) -> Rational {
        if let (Rational::Small(a, b), Rational::Small(c, d)) = (self, o) {
            let (a, b, c, d) = (*a as i128, *b as i128, *c as i128, *d as i128);
            return Rational::from_i128(a * c, b * d);
        }
        Rational::from_big(self.to_big() * o.to_big())
    }
}

impl Div for &Rational {
    type Output = Rational;
    /// Panics on division by zero.
    fn div(self, o: &Rational) -> Rational {
        assert!(!o.is_zero(), "division by zero");
        if let (Rational::Small(a, b), Rational::Small(c, d)) = (self, o) {
            let (a, b, c, d) = (*a as i128, *b as i128, *c as i128, *d as i128);
            return Rational::from_i128(a * d, b * c);
        }
        Rational::from_big(self.to_big() / o.to_big())
    }
}

impl Neg for &Rational {
    type Output = Rational;
    fn neg(self) -> Rational {
        match self {
            // -i64::MIN does not fit; route it through i128.
            Rational::Small(n, d) => Rational::from_i128(-(*n as i128), *d as i128),
            Rational::Big(b) => Rational::from_big(-(**b).clone()),
        }
    }
}

macro_rules! owned_ops {
    ($($tr:ident $m:ident),*) => {$(
        impl $tr for Rational {
            type Output = Rational;
            fn $m(self, o: Rational) -> Rational { (&self).$m(&o) }
        }
        impl $tr<&Rational> for Rational {
            type Output = Rational;
            fn $m(self, o: &Rational) -> Rational { (&self).$m(o) }
        }
    )*};
}
owned_ops!(Add add, Sub sub, Mul mul, Div div);

impl Neg for Rational {
    type Output = Rational;
    fn neg(self) -> Rational {
        -&self
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Rational::Small(n, 1) => write!(f, "{n}"),
            Rational::Small(n, d) => write!(f, "{n}/{d}"),
            Rational::Big(b) if b.is_integer() => write!(f, "{}", b.numer()),
            Rational::Big(b) => write!(f, "{}/{}", b.numer(), b.denom()),
        }
    }
}

impl fmt::Debug for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self}")
    }
}

/// `value + delta·δ` for an infinitesimal δ > 0; ordered lexicographically.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct DeltaRational {
    pub value: Rational,
    pub delta: Rational,
}

impl DeltaRational {
    pub fn of(value: Rational) -> Self {
        Self {
            value,
            delta: Rational::zero(),
        }
    }
    pub fn new(value: Rational, delta: Rational) -> Self {
        Self { value, delta }
    }
    pub fn zero() -> Self {
        Self::of(Rational::zero())
    }
    pub fn add(&self, o: &Self) -> Self {
        Self {
            value: &self.value + &o.value,
            delta: &self.delta + &o.delta,
        }
    }
    pub fn sub(&self, o: &Self) -> Self {
        Self {
            value: &self.value - &o.value,
            delta: &self.delta - &o.delta,
        }
    }
    /// Multiply both components by a (non-infinitesimal) rational factor.
    pub fn scale(&self, f: &Rational) -> Self {
        Self {
            value: &self.value * f,
            delta: &self.delta * f,
        }
    }
    pub fn neg(&self) -> Self {
        Self {
            value: -&self.value,
            delta: -&self.delta,
        }
    }
    /// `self + f·o`, without building the intermediate.
    pub fn add_scaled(&self, f: &Rational, o: &Self) -> Self {
        Self {
            value: o.value.mul_add(f, &self.value),
            delta: o.delta.mul_add(f, &self.delta),
        }
    }
    /// The real value for a concrete δ.
    pub fn at(&self, delta: &Rational) -> Rational {
        self.delta.mul_add(delta, &self.value)
    }
}

impl fmt::Display for DeltaRational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.delta.is_zero() {
            write!(f, "{}", self.value)
        } else {
            write!(f, "{}{:+}δ", self.value, self.delta.to_big())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Zero;

    fn r(n: i64, d: i64) -> Rational {
        Rational::new(n, d)
    }

    fn big(n: i128, d: i128) -> BigRational {
        BigRational::new(BigInt::from(n), BigInt::from(d))
    }

    #[test]
    fn canonical_form() {
        assert_eq!(r(2, 4), r(1, 2));
        assert_eq!(r(-2, -4), r(1, 2));
        assert_eq!(r(2, -4), r(-1, 2));
        assert_eq!(r(0, -7), Rational::zero());
        assert!(matches!(r(6, 3), Rational::Small(2, 1)));
        // Overflowing results become Big, and come back when they fit again.
        let m = Rational::from_int(i64::MAX);
        let sq = &m * &m;
        assert!(matches!(sq, Rational::Big(_)));
        assert_eq!(&sq / &m, m);
        assert!(matches!(&sq / &m, Rational::Small(..)));
        assert!(matches!(-Rational::from_int(i64::MIN), Rational::Big(_)));
    }

    #[test]
    fn delta_arithmetic_and_order() {
        let a = DeltaRational::new(r(1, 2), r(1, 1));
        let b = DeltaRational::new(r(1, 3), r(-2, 1));
        assert_eq!(a.add(&b), DeltaRational::new(r(5, 6), r(-1, 1)));
        assert_eq!(a.sub(&b), DeltaRational::new(r(1, 6), r(3, 1)));
        assert_eq!(a.scale(&r(2, 1)), DeltaRational::new(r(1, 1), r(2, 1)));
        assert_eq!(a.neg(), DeltaRational::new(r(-1, 2), r(-1, 1)));
        assert_eq!(a.add_scaled(&r(3, 1), &b), a.add(&b.scale(&r(3, 1))));
        let five = Rational::from_int(5);
        let lt = DeltaRational::new(five.clone(), -Rational::one());
        let eq = DeltaRational::of(five.clone());
        let gt = DeltaRational::new(five, Rational::one());
        assert!(lt < eq && eq < gt);
        assert!(gt < DeltaRational::new(Rational::from_int(6), -Rational::one()));
    }

    #[test]
    fn floor_ceil_parse() {
        assert_eq!(r(-7, 2).floor(), Rational::from_int(-4));
        assert_eq!(r(-7, 2).ceil(), Rational::from_int(-3));
        assert_eq!(r(7, 2).floor(), Rational::from_int(3));
        assert_eq!(r(6, 2).ceil(), Rational::from_int(3));
        assert_eq!(Rational::parse_decimal("3.25"), Some(r(13, 4)));
        assert_eq!(Rational::parse_decimal("42"), Some(Rational::from_int(42)));
        assert_eq!(Rational::parse_decimal("0.0"), Some(Rational::zero()));
        assert_eq!(Rational::parse_decimal("1."), None);
        assert_eq!(Rational::parse_decimal(".5"), None);
        assert_eq!(Rational::parse_decimal("-1"), None);
        assert!(matches!(
            Rational::parse_decimal("123456789012345678901234567890"),
            Some(Rational::Big(_))
        ));
        assert_eq!(r(-3, 4).to_string(), "-3/4");
    }

    /// Every operation agrees with BigRational, on values chosen to straddle the i64 boundary.
    #[test]
    fn agrees_with_bigrational() {
        let mut s = 0x9E3779B97F4A7C15u64;
        let mut next = || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        let pick = |x: u64| -> i128 {
            match x % 6 {
                0 => (x >> 8) as i128 % 20 - 10,
                1 => i64::MAX as i128 - (x >> 8) as i128 % 3,
                2 => i64::MIN as i128 + (x >> 8) as i128 % 3,
                3 => ((x >> 8) as i64) as i128,
                4 => (x >> 40) as i128 + 1,
                _ => -((x >> 33) as i128) - 1,
            }
        };
        for _ in 0..20_000 {
            let (an, ad, bn, bd) = (pick(next()), pick(next()), pick(next()), pick(next()));
            if ad == 0 || bd == 0 {
                continue;
            }
            let (x, y) = (big(an, ad), big(bn, bd));
            let (a, b) = (Rational::from_big(x.clone()), Rational::from_big(y.clone()));
            assert_eq!((&a + &b).to_big(), &x + &y);
            assert_eq!((&a - &b).to_big(), &x - &y);
            assert_eq!((&a * &b).to_big(), &x * &y);
            if !y.is_zero() {
                assert_eq!((&a / &b).to_big(), &x / &y);
            }
            assert_eq!((-&a).to_big(), -x.clone());
            assert_eq!(a.cmp(&b), x.cmp(&y));
            assert_eq!(a.floor().to_big(), x.floor());
            assert_eq!(a.ceil().to_big(), x.ceil());
            // Canonical: equal values have one representation.
            assert_eq!(Rational::from_big(x.clone()), a);
            assert_eq!(a == b, x == y);
        }
    }
}
