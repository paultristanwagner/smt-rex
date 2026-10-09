//! The CAD decision procedure on hand-made systems with known answers, including degenerate
//! projections (squares, common factors, reducible defining polynomials, nullification); every
//! satisfying point is checked exactly.

use num_bigint::BigInt;
use smtrex_nra::cad::{satisfies, solve, Constraint, SignSet};
use smtrex_poly::MPoly;

/// A tiny parser for test polynomials over x, y, z (variables 0, 1, 2): integers, `+ - * ^`,
/// parentheses.
fn poly(s: &str) -> MPoly {
    let toks: Vec<char> = s.chars().filter(|c| !c.is_whitespace()).collect();
    let mut i = 0;
    let p = expr(&toks, &mut i);
    assert_eq!(i, toks.len(), "trailing input in {s}");
    p
}

fn expr(t: &[char], i: &mut usize) -> MPoly {
    let mut acc = if t.get(*i) == Some(&'-') {
        *i += 1;
        -&term(t, i)
    } else {
        term(t, i)
    };
    while let Some(&c) = t.get(*i) {
        if c == '+' {
            *i += 1;
            acc = &acc + &term(t, i);
        } else if c == '-' {
            *i += 1;
            acc = &acc - &term(t, i);
        } else {
            break;
        }
    }
    acc
}

fn term(t: &[char], i: &mut usize) -> MPoly {
    let mut acc = factor(t, i);
    while t.get(*i) == Some(&'*') {
        *i += 1;
        acc = &acc * &factor(t, i);
    }
    acc
}

fn factor(t: &[char], i: &mut usize) -> MPoly {
    let base = match t[*i] {
        '(' => {
            *i += 1;
            let e = expr(t, i);
            assert_eq!(t[*i], ')');
            *i += 1;
            e
        }
        'x' | 'y' | 'z' => {
            let v = (t[*i] as u8 - b'x') as usize;
            *i += 1;
            MPoly::var(v)
        }
        c if c.is_ascii_digit() => {
            let mut n = 0i64;
            while let Some(d) = t.get(*i).and_then(|c| c.to_digit(10)) {
                n = n * 10 + d as i64;
                *i += 1;
            }
            MPoly::constant(BigInt::from(n))
        }
        c => panic!("unexpected {c}"),
    };
    if t.get(*i) == Some(&'^') {
        *i += 1;
        let mut n = 0usize;
        while let Some(d) = t.get(*i).and_then(|c| c.to_digit(10)) {
            n = n * 10 + d as usize;
            *i += 1;
        }
        return base.pow(n);
    }
    base
}

/// `p ⋈ 0` for ⋈ in `= != < <= > >=`.
fn c(p: &str, rel: &str) -> Constraint {
    let allowed = match rel {
        "=" => SignSet::ZERO,
        "!=" => SignSet::NONZERO,
        "<" => SignSet::NEG,
        "<=" => SignSet::NONPOS,
        ">" => SignSet::POS,
        ">=" => SignSet::NONNEG,
        _ => panic!(),
    };
    Constraint {
        poly: poly(p),
        allowed,
    }
}

fn check(cs: &[Constraint], sat: bool) {
    let r = solve(cs, 3);
    match r {
        Some(mut m) => {
            assert!(sat, "expected unsat, got model {m:?}");
            assert!(
                satisfies(cs, &mut m),
                "model {m:?} violates the constraints"
            );
        }
        None => assert!(!sat, "expected sat, got unsat"),
    }
}

#[test]
fn univariate() {
    check(&[c("x^2 - 2", "=")], true);
    check(&[c("x^2", "<")], false);
    check(&[c("(x - 1)^2", "<")], false);
    check(&[c("(x - 1)^2", "<="), c("x - 1", "!=")], false);
    check(&[c("x^3 - 2*x - 1", "="), c("x", ">")], true);
    check(&[c("x^2 - 2", "="), c("x^2 - 3", "=")], false);
}

#[test]
fn degenerate_projections() {
    // sqr_proj_hole: (y² − 2xy + 1)² = 0 ∧ 0 < x < 3/2 is sat (x = y = 1)
    check(
        &[
            c("(y^2 - 2*x*y + 1)^2", "="),
            c("x", ">"),
            c("2*x - 3", "<"),
        ],
        true,
    );
    // common_factor_hole: (y−x)(x²+y²−4) = 0 ∧ (y−x)(y−2x) = 0 ∧ y ≠ x is sat
    check(
        &[
            c("(y - x)*(x^2 + y^2 - 4)", "="),
            c("(y - x)*(y - 2*x)", "="),
            c("y - x", "!="),
        ],
        true,
    );
    // reducible_ran: (x²−2)(x²−3) = 0 ∧ (x²−3)(y−5) = 0 ∧ x² < 5/2 is sat (x = √2, y = 5)
    check(
        &[
            c("(x^2 - 2)*(x^2 - 3)", "="),
            c("(x^2 - 3)*(y - 5)", "="),
            c("2*x^2 - 5", "<"),
        ],
        true,
    );
    // const atom
    check(&[c("x - y", ">"), c("x - x", ">=")], true);
    // nullify3: xz − y = 0 ∧ x = 0 ∧ z > 1 ∧ y = 0 is sat
    check(
        &[c("x*z - y", "="), c("x", "="), c("z - 1", ">"), c("y", "=")],
        true,
    );
    // alg_lift3_sat: x² = 2, y² = 3, z² = 6, z = xy
    check(
        &[
            c("x^2 - 2", "="),
            c("y^2 - 3", "="),
            c("z^2 - 6", "="),
            c("z - x*y", "="),
        ],
        true,
    );
    // alg_lift3: x² = 2, y² = 3, xyz = 1
    check(
        &[c("x^2 - 2", "="), c("y^2 - 3", "="), c("x*y*z - 1", "=")],
        true,
    );
    // alg_lift: x² = 2, y² = x, y > 0, x > 0
    check(
        &[
            c("x^2 - 2", "="),
            c("y^2 - x", "="),
            c("y", ">"),
            c("x", ">"),
        ],
        true,
    );
    // tangent circles meet at (1, 0)
    check(
        &[c("x^2 + y^2 - 1", "="), c("(x - 2)^2 + y^2 - 1", "=")],
        true,
    );
    // open tangent disks do not meet
    check(
        &[c("x^2 + y^2 - 1", "<"), c("(x - 2)^2 + y^2 - 1", "<")],
        false,
    );
    // sphere ∩ plane
    check(
        &[c("x^2 + y^2 + z^2 - 1", "="), c("2*x + 2*y + 2*z - 3", "=")],
        true,
    );
    check(
        &[c("x^2 + y^2 + z^2 - 1", "="), c("x + y + z - 2", "=")],
        false,
    );
    // hyperbola in the wrong quadrant
    check(&[c("x*y - 1", ">"), c("x", "<"), c("y", ">")], false);
    // xy = 1, x = y < 0: x = y = −1
    check(&[c("x*y - 1", "="), c("x - y", "="), c("x", "<")], true);
    // lemniscate (x²+y²)² = 2(x²−y²): the largest y on it is 1/2
    check(
        &[c("(x^2 + y^2)^2 - 2*(x^2 - y^2)", "="), c("3*y - 1", ">")],
        true,
    );
    check(
        &[c("(x^2 + y^2)^2 - 2*(x^2 - y^2)", "="), c("2*y - 1", ">")],
        false,
    );
}

#[test]
fn nullification_and_dependent_coordinates() {
    // (y + x)(z − 1) = 0 with y = −x: nullified over the whole curve, any z.
    check(
        &[
            c("x^2 - 2", "="),
            c("y + x", "="),
            c("(y + x)*(z - 1)", "="),
            c("z - 5", ">"),
        ],
        true,
    );
    // y = x = √2 and z² = xy = 2
    check(
        &[
            c("x^2 - 2", "="),
            c("y - x", "="),
            c("z^2 - x*y", "="),
            c("z", ">"),
        ],
        true,
    );
    check(
        &[c("x^2 - 2", "="), c("y + x", "="), c("z^2 - x*y", "=")],
        false,
    );
}
