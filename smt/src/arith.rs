//! Linear expressions for the arithmetic front-end, and their normalisation into bound atoms.
//!
//! A [`Lin`] is `Σ aᵢ·xᵢ + c` over Simplex variables. Comparisons `e ⋈ 0` are normalised so that
//! one canonical term gets one Simplex variable: the term is scaled so its first coefficient is 1
//! (flipping the comparison when that coefficient was negative) and the constant moves to the
//! right. So `2x + 2y ≤ 4`, `x + y ≤ 2` and `-x - y ≥ -2` all become the atom `(x + y) ≤ 2`.

use smtrex_core::Rational;
use smtrex_theory::lra::{AVar, BoundKind};

#[derive(Clone, Debug, PartialEq, Eq, Hash, Default)]
pub struct Lin {
    /// Sorted by variable, no zero coefficients.
    pub terms: Vec<(AVar, Rational)>,
    pub constant: Rational,
}

impl Lin {
    pub fn constant(c: Rational) -> Lin {
        Lin {
            terms: Vec::new(),
            constant: c,
        }
    }

    pub fn var(x: AVar) -> Lin {
        Lin {
            terms: vec![(x, Rational::one())],
            constant: Rational::zero(),
        }
    }

    pub fn is_constant(&self) -> bool {
        self.terms.is_empty()
    }

    /// `self + f·other`.
    pub fn add_scaled(&self, f: &Rational, other: &Lin) -> Lin {
        let mut terms = Vec::with_capacity(self.terms.len() + other.terms.len());
        let (a, b) = (&self.terms, &other.terms);
        let (mut i, mut j) = (0, 0);
        while i < a.len() || j < b.len() {
            if j == b.len() || (i < a.len() && a[i].0 < b[j].0) {
                terms.push(a[i].clone());
                i += 1;
            } else if i == a.len() || b[j].0 < a[i].0 {
                let c = &b[j].1 * f;
                if !c.is_zero() {
                    terms.push((b[j].0, c));
                }
                j += 1;
            } else {
                let c = b[j].1.mul_add(f, &a[i].1);
                if !c.is_zero() {
                    terms.push((a[i].0, c));
                }
                i += 1;
                j += 1;
            }
        }
        Lin {
            terms,
            constant: other.constant.mul_add(f, &self.constant),
        }
    }

    pub fn add(&self, other: &Lin) -> Lin {
        self.add_scaled(&Rational::one(), other)
    }

    pub fn sub(&self, other: &Lin) -> Lin {
        self.add_scaled(&-Rational::one(), other)
    }

    pub fn scale(&self, f: &Rational) -> Lin {
        if f.is_zero() {
            return Lin::default();
        }
        Lin {
            terms: self.terms.iter().map(|(x, c)| (*x, c * f)).collect(),
            constant: &self.constant * f,
        }
    }
}

/// A comparison of a linear expression with zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cmp {
    Le,
    Lt,
    Ge,
    Gt,
}

/// The normal form of `e ⋈ 0`.
#[derive(Debug, PartialEq, Eq)]
pub enum Normal {
    /// The comparison has no variables and is simply true or false.
    Const(bool),
    /// `term ⋈ c` with `term` scaled to leading coefficient 1: the literal is the atom
    /// `term kind c`, negated when `negated`.
    Atom {
        term: Vec<(AVar, Rational)>,
        kind: BoundKind,
        c: Rational,
        negated: bool,
    },
}

/// Normalise `e ⋈ 0`. With `int_vars` (every variable is an integer) the term is scaled to
/// coprime integer coefficients with a positive leading one instead of a leading 1, so the
/// Simplex knows it is integer-valued and can round its bounds: `2x − 2y = 1` becomes
/// `x − y = 1/2`, which rounds to the contradiction `x − y ≤ 0 ∧ x − y ≥ 1`.
pub fn normalize(e: &Lin, cmp: Cmp, int_vars: bool) -> Normal {
    if e.terms.is_empty() {
        let s = e.constant.signum();
        return Normal::Const(match cmp {
            Cmp::Le => s <= 0,
            Cmp::Lt => s < 0,
            Cmp::Ge => s >= 0,
            Cmp::Gt => s > 0,
        });
    }
    // Σ a·x + k ⋈ 0  ⇔  Σ (a/l)·x ⋈' −k/l  where l is the scale (the leading coefficient, or for
    // integer terms the leading coefficient's sign times gcd/lcm); ⋈ flips if l < 0.
    let lead = if int_vars {
        integer_scale(&e.terms)
    } else {
        e.terms[0].1.clone()
    };
    let inv = lead.recip();
    let term: Vec<(AVar, Rational)> = e.terms.iter().map(|(x, a)| (*x, a * &inv)).collect();
    let c = -&(&e.constant * &inv);
    let cmp = if lead.is_negative() {
        match cmp {
            Cmp::Le => Cmp::Ge,
            Cmp::Lt => Cmp::Gt,
            Cmp::Ge => Cmp::Le,
            Cmp::Gt => Cmp::Lt,
        }
    } else {
        cmp
    };
    // t < c is ¬(t ≥ c); t > c is ¬(t ≤ c).
    let (kind, negated) = match cmp {
        Cmp::Le => (BoundKind::Le, false),
        Cmp::Ge => (BoundKind::Ge, false),
        Cmp::Lt => (BoundKind::Ge, true),
        Cmp::Gt => (BoundKind::Le, true),
    };
    Normal::Atom {
        term,
        kind,
        c,
        negated,
    }
}

/// `s` such that dividing every coefficient by `s` gives coprime integers with a positive leading
/// coefficient: `s = ±gcd(numerators) / lcm(denominators)`.
fn integer_scale(terms: &[(AVar, Rational)]) -> Rational {
    use num_integer::Integer;
    let mut g = num_bigint::BigInt::from(0);
    let mut l = num_bigint::BigInt::from(1);
    for (_, c) in terms {
        g = g.gcd(&c.numer());
        l = l.lcm(&c.denom());
    }
    let s = Rational::from_big(num_rational::BigRational::new(g, l));
    if terms[0].1.is_negative() {
        -s
    } else {
        s
    }
}

/// An SMT-LIB real literal: `3.0`, `(- 3.0)`, `(/ 1.0 3.0)`, `(- (/ 1.0 3.0))`.
pub fn real_literal(q: &Rational) -> String {
    let abs = q.abs();
    let body = if abs.is_integer() {
        format!("{}.0", abs.numer())
    } else {
        format!("(/ {}.0 {}.0)", abs.numer(), abs.denom())
    };
    if q.is_negative() {
        format!("(- {body})")
    } else {
        body
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64) -> Rational {
        Rational::from_int(n)
    }

    fn lin(terms: &[(AVar, i64)], c: i64) -> Lin {
        let mut l = Lin::constant(q(c));
        for (x, a) in terms {
            l = l.add_scaled(&q(*a), &Lin::var(*x));
        }
        l
    }

    #[test]
    fn arithmetic() {
        let a = lin(&[(0, 2), (1, 3)], 1);
        let b = lin(&[(1, 3), (2, 1)], -1);
        assert_eq!(a.sub(&b), lin(&[(0, 2), (2, -1)], 2));
        assert_eq!(a.add(&b), lin(&[(0, 2), (1, 6), (2, 1)], 0));
        assert_eq!(a.scale(&q(0)), Lin::default());
    }

    #[test]
    fn equivalent_comparisons_share_one_atom() {
        // 2x + 2y - 4 <= 0,  x + y - 2 <= 0,  -x - y + 2 >= 0
        let forms = [
            normalize(&lin(&[(0, 2), (1, 2)], -4), Cmp::Le, false),
            normalize(&lin(&[(0, 1), (1, 1)], -2), Cmp::Le, false),
            normalize(&lin(&[(0, -1), (1, -1)], 2), Cmp::Ge, false),
        ];
        assert!(forms.iter().all(|f| *f == forms[0]));
        assert_eq!(
            forms[0],
            Normal::Atom {
                term: vec![(0, q(1)), (1, q(1))],
                kind: BoundKind::Le,
                c: q(2),
                negated: false
            }
        );
        // -x < 3  ⇔  x > -3  ⇔  ¬(x ≤ -3)
        assert_eq!(
            normalize(&lin(&[(0, -1)], -3), Cmp::Lt, false),
            Normal::Atom {
                term: vec![(0, q(1))],
                kind: BoundKind::Le,
                c: q(-3),
                negated: true
            }
        );
        assert_eq!(
            normalize(&lin(&[], -1), Cmp::Lt, false),
            Normal::Const(true)
        );
        assert_eq!(
            normalize(&lin(&[], 0), Cmp::Gt, false),
            Normal::Const(false)
        );
    }

    #[test]
    fn integer_terms_get_coprime_integer_coefficients() {
        // 4x - 6y + 1 <= 0  ->  2x - 3y <= -1/2  (the Simplex rounds the bound to -1)
        assert_eq!(
            normalize(&lin(&[(0, 4), (1, -6)], 1), Cmp::Le, true),
            Normal::Atom {
                term: vec![(0, q(2)), (1, q(-3))],
                kind: BoundKind::Le,
                c: Rational::new(-1, 2),
                negated: false
            }
        );
        // -2x + 1 >= 0  ->  x <= 1/2
        assert_eq!(
            normalize(&lin(&[(0, -2)], 1), Cmp::Ge, true),
            Normal::Atom {
                term: vec![(0, q(1))],
                kind: BoundKind::Le,
                c: Rational::new(1, 2),
                negated: false
            }
        );
    }

    #[test]
    fn literals() {
        assert_eq!(real_literal(&q(3)), "3.0");
        assert_eq!(real_literal(&q(-3)), "(- 3.0)");
        assert_eq!(real_literal(&Rational::new(1, 3)), "(/ 1.0 3.0)");
        assert_eq!(real_literal(&Rational::new(-1, 3)), "(- (/ 1.0 3.0))");
    }
}
