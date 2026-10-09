//! Polynomial expressions for the QF_NRA front-end, and their normalisation into NRA atoms.
//!
//! An [`RPoly`] is a polynomial with rational coefficients over the NRA theory's variables,
//! stored as an integer polynomial and a positive common denominator. A comparison `e ⋈ 0` only
//! depends on the numerator's sign, so the atom is the numerator made primitive with a positive
//! leading coefficient ([`MPoly::primitive_sign`]), the relation flipped when that changed its
//! sign. So `2x·y − 4 > 0`, `x·y > 2` and `−x·y < −2` are one atom `(x·y − 2) > 0`.

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};
use smtrex_core::Rational;
use smtrex_nra::AtomKind;
use smtrex_poly::MPoly;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct RPoly {
    /// The numerator.
    pub num: MPoly,
    /// The denominator, positive.
    pub den: BigInt,
}

impl RPoly {
    pub fn constant(q: &Rational) -> RPoly {
        let q = q.to_big();
        RPoly {
            num: MPoly::constant(q.numer().clone()),
            den: q.denom().clone(),
        }
    }

    pub fn var(v: usize) -> RPoly {
        RPoly {
            num: MPoly::var(v),
            den: BigInt::one(),
        }
    }

    /// The value, if the polynomial is constant.
    pub fn as_constant(&self) -> Option<Rational> {
        let c = self.num.as_constant()?;
        Some(Rational::from_big(num_rational::BigRational::new(
            c,
            self.den.clone(),
        )))
    }

    fn reduce(num: MPoly, den: BigInt) -> RPoly {
        let g = num.content().gcd(&den);
        if g.is_one() || g.is_zero() {
            return RPoly { num, den };
        }
        let num = num.div_exact(&MPoly::constant(g.clone())).expect("content");
        RPoly { num, den: den / g }
    }

    pub fn add(&self, o: &RPoly) -> RPoly {
        let num = &self.num.scale(&o.den) + &o.num.scale(&self.den);
        RPoly::reduce(num, &self.den * &o.den)
    }

    pub fn sub(&self, o: &RPoly) -> RPoly {
        self.add(&o.neg())
    }

    pub fn neg(&self) -> RPoly {
        RPoly {
            num: -&self.num,
            den: self.den.clone(),
        }
    }

    pub fn mul(&self, o: &RPoly) -> RPoly {
        RPoly::reduce(&self.num * &o.num, &self.den * &o.den)
    }

    /// `self · q`.
    pub fn scale(&self, q: &Rational) -> RPoly {
        self.mul(&RPoly::constant(q))
    }

    /// `self` with `e` substituted for `x_v`. With `num = Σ c_k·x_v^k` of degree `D` and
    /// `e = n/d`: `Σ c_k·n^k·d^(D−k) / (den·d^D)`.
    pub fn substitute(&self, v: usize, e: &RPoly) -> RPoly {
        let coeffs = self.num.coeffs_in(v);
        let Some(deg) = coeffs.len().checked_sub(1) else {
            return self.clone();
        };
        if deg == 0 {
            return self.clone();
        }
        let mut num = MPoly::zero();
        let mut npow = MPoly::from_i64(1);
        for (k, c) in coeffs.iter().enumerate() {
            let dpow = num_traits::pow(e.den.clone(), deg - k);
            num = &num + &(&(c * &npow) * &MPoly::constant(dpow));
            npow = &npow * &e.num;
        }
        RPoly::reduce(num, &self.den * num_traits::pow(e.den.clone(), deg))
    }

    /// If the equation `self = 0` can be solved for a variable `x` that it contains only
    /// linearly and with a constant coefficient: the lowest such variable and the solution
    /// `x = e` (which does not contain `x`). A variable coefficient is never divided by, so no
    /// side condition is needed.
    pub fn solve_linear(&self) -> Option<(usize, RPoly)> {
        for v in self.num.vars() {
            let coeffs = self.num.coeffs_in(v);
            if coeffs.len() != 2 {
                continue;
            }
            let Some(c) = coeffs[1].as_constant() else {
                continue;
            };
            // c·x + rest = 0  ⇒  x = −rest / c (the denominator of self cancels).
            let rest = RPoly {
                num: -&coeffs[0],
                den: BigInt::one(),
            };
            let c = Rational::from_big(num_rational::BigRational::from_integer(c));
            return Some((v, rest.scale(&c.recip())));
        }
        None
    }

    /// The value at a point (`point[i]` for `x_i`; every variable of the polynomial must have a
    /// coordinate).
    pub fn eval(&self, point: &[smtrex_poly::RealAlgebraic]) -> smtrex_poly::RealAlgebraic {
        use smtrex_poly::RealAlgebraic;
        let mut acc = RealAlgebraic::from_int(0);
        for (m, c) in self.num.terms() {
            let mut t =
                RealAlgebraic::from_rational(num_rational::BigRational::from_integer(c.clone()));
            for (i, e) in m.iter() {
                for _ in 0..e {
                    t = t.mul(&point[i]);
                }
            }
            acc = acc.add(&t);
        }
        acc.mul(&RealAlgebraic::from_rational(
            num_rational::BigRational::new(BigInt::one(), self.den.clone()),
        ))
    }
}

/// A comparison with zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PolyCmp {
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
}

/// The normal form of `e ⋈ 0`.
#[derive(Debug, PartialEq, Eq)]
pub enum PolyNormal {
    /// No variables: simply true or false.
    Const(bool),
    /// The literal of the atom `poly kind 0`, negated when `negated`.
    Atom {
        poly: MPoly,
        kind: AtomKind,
        negated: bool,
    },
}

/// Normalise `e ⋈ 0` (see the module docs). `≤` is `¬(>)`, `≥` is `¬(<)`.
pub fn normalize(e: &RPoly, cmp: PolyCmp) -> PolyNormal {
    if let Some(c) = e.num.as_constant() {
        let s = c.signum();
        let s = if s.is_positive() {
            1
        } else if s.is_negative() {
            -1
        } else {
            0
        };
        return PolyNormal::Const(match cmp {
            PolyCmp::Eq => s == 0,
            PolyCmp::Lt => s < 0,
            PolyCmp::Le => s <= 0,
            PolyCmp::Gt => s > 0,
            PolyCmp::Ge => s >= 0,
        });
    }
    let (sign, poly) = e.num.primitive_sign();
    let cmp = if sign < 0 {
        match cmp {
            PolyCmp::Eq => PolyCmp::Eq,
            PolyCmp::Lt => PolyCmp::Gt,
            PolyCmp::Le => PolyCmp::Ge,
            PolyCmp::Gt => PolyCmp::Lt,
            PolyCmp::Ge => PolyCmp::Le,
        }
    } else {
        cmp
    };
    let (kind, negated) = match cmp {
        PolyCmp::Eq => (AtomKind::Eq, false),
        PolyCmp::Lt => (AtomKind::Lt, false),
        PolyCmp::Gt => (AtomKind::Gt, false),
        PolyCmp::Le => (AtomKind::Gt, true),
        PolyCmp::Ge => (AtomKind::Lt, true),
    };
    PolyNormal::Atom {
        poly,
        kind,
        negated,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equivalent_comparisons_share_one_atom() {
        let x = RPoly::var(0);
        let y = RPoly::var(1);
        let xy = x.mul(&y);
        let two = RPoly::constant(&Rational::from_int(2));
        let a = normalize(
            &xy.scale(&Rational::from_int(2))
                .sub(&two.scale(&Rational::from_int(2))),
            PolyCmp::Gt,
        );
        let b = normalize(&xy.sub(&two), PolyCmp::Gt);
        let c = normalize(&xy.neg().add(&two), PolyCmp::Lt);
        assert_eq!(a, b);
        assert_eq!(b, c);
        let half = Rational::new(1, 2);
        assert_eq!(
            normalize(&x.scale(&half).sub(&RPoly::constant(&half)), PolyCmp::Le),
            normalize(&x.sub(&RPoly::constant(&Rational::one())), PolyCmp::Le)
        );
        assert_eq!(normalize(&two, PolyCmp::Gt), PolyNormal::Const(true));
        assert_eq!(normalize(&x.sub(&x), PolyCmp::Eq), PolyNormal::Const(true));
    }
}
