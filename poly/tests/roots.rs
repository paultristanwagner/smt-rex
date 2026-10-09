//! Real root isolation, refinement, counting, and real algebraic numbers (checked against Sturm).

mod common;

use common::{p, q, rand_poly, sturm_count};
use num_bigint::BigInt;
use num_traits::Zero;
use smtrex_poly::algebraic::{count_real_roots, real_roots};
use smtrex_poly::rng::SplitMix64;
use smtrex_poly::roots::{isolate_squarefree, refine, Isolation};
use smtrex_poly::RealAlgebraic;
use std::cmp::Ordering;
use std::collections::HashSet;
#[test]
fn isolation_matches_sturm() {
    let mut rng = SplitMix64::new(6);
    for _ in 0..300 {
        let f = rand_poly(&mut rng, 1, 10, 20).square_free_part();
        if f.is_constant() {
            continue;
        }
        let isos = isolate_squarefree(&f);
        let big = q(1 << 40, 1);
        assert_eq!(
            isos.len(),
            sturm_count(&f, &-&big, &big),
            "root count of {f}"
        );
        for w in isos.windows(2) {
            assert!(w[0].upper() <= w[1].lower(), "disjoint, increasing");
        }
        for iso in &isos {
            match iso {
                Isolation::Exact(r) => assert!(f.eval(r).is_zero()),
                Isolation::Open(lo, hi) => {
                    assert!(lo < hi);
                    assert_eq!(sturm_count(&f, lo, hi), 1, "{f} on ({lo}, {hi})");
                    assert!(
                        !f.eval(hi).is_zero() && !f.eval(lo).is_zero(),
                        "{f}: ({lo}, {hi}) {isos:?}"
                    );
                    let tiny = q(1, 1 << 30);
                    match refine(&f, lo, hi, &tiny) {
                        Isolation::Open(a, b) => {
                            assert!(&b - &a <= tiny && lo <= &a && &b <= hi);
                            assert_eq!(sturm_count(&f, &a, &b), 1);
                        }
                        Isolation::Exact(r) => assert!(f.eval(&r).is_zero()),
                    }
                }
            }
        }
    }
}

#[test]
fn close_and_rational_roots() {
    // (x − 1)(1000000x − 1000001): roots 1 and 1 + 1e−6.
    let f = &p(&[-1, 1]) * &p(&[-1_000_001, 1_000_000]);
    let roots = real_roots(&f);
    assert_eq!(roots.len(), 2);
    assert_eq!(roots[0].0, RealAlgebraic::from_int(1));
    assert_eq!(
        roots[1].0,
        RealAlgebraic::from_rational(q(1_000_001, 1_000_000))
    );
    // Two irrational roots 1e-12 apart: x² − 2 and (10^6 x)² − 2·10^12 − 1 … use
    // (x² − 2)((10^6 x)² − (2·10^12 + 1)): √2 and √(2 + 10^−12).
    let g = &p(&[-2, 0, 1]) * &p(&[-2_000_000_000_001, 0, 1_000_000_000_000]);
    let roots = real_roots(&g);
    assert_eq!(roots.len(), 4);
    for w in roots.windows(2) {
        assert_eq!(w[0].0.cmp(&w[1].0), Ordering::Less);
        assert!(w[0].0.upper() <= w[1].0.lower());
    }
    // Multiplicities.
    let h = &p(&[-1, 1]).pow(3) * &p(&[-2, 0, 1]).pow(2);
    let roots = real_roots(&h);
    let mults: Vec<usize> = roots.iter().map(|r| r.1).collect();
    assert_eq!(mults, vec![2, 3, 2]); // −√2, 1, √2
    assert_eq!(count_real_roots(&h, None, None, true), 7);
    assert_eq!(count_real_roots(&h, None, None, false), 3);
    assert_eq!(
        count_real_roots(&h, Some(&q(1, 1)), Some(&q(3, 2)), true),
        5
    );
    assert_eq!(
        count_real_roots(&h, Some(&q(-1, 1)), Some(&q(1, 2)), true),
        0
    );
}

#[test]
fn algebraic_numbers() {
    let sqrt2 = RealAlgebraic::root_of(&p(&[-2, 0, 1]), 1).unwrap();
    let msqrt2 = RealAlgebraic::root_of(&p(&[-2, 0, 1]), 0).unwrap();
    let cbrt3 = RealAlgebraic::root_of(&p(&[-3, 0, 0, 1]), 0).unwrap();
    assert!(msqrt2 < sqrt2);
    assert!(sqrt2 < cbrt3); // 1.414 < 1.442
    assert!(sqrt2 > RealAlgebraic::from_rational(q(1414, 1000)));
    assert!(sqrt2 < RealAlgebraic::from_rational(q(1415, 1000)));
    assert_ne!(
        sqrt2, msqrt2,
        "B6: different roots of one polynomial are different"
    );
    // Same number from a reducible polynomial and a different interval: equal, same hash.
    let other = RealAlgebraic::from_interval(
        &(&p(&[-2, 0, 1]) * &p(&[-3, 0, 1])).scale(&BigInt::from(5)),
        &q(1, 1),
        &q(3, 2),
    )
    .unwrap();
    let mut refined = sqrt2.clone();
    refined.refine(&q(1, 1 << 20));
    assert_eq!(other, sqrt2);
    assert_eq!(refined, sqrt2);
    let set: HashSet<RealAlgebraic> = [sqrt2.clone(), other, refined, msqrt2.clone()].into();
    assert_eq!(set.len(), 2);
    // Signs.
    assert_eq!(sqrt2.sign_of(&p(&[-2, 0, 1])), 0);
    assert_eq!(sqrt2.sign_of(&p(&[-2, 0, 0, 0, 1]).derivative()), 1);
    assert_eq!(sqrt2.sign_of(&(&p(&[-2, 0, 1]) * &p(&[7, 1]))), 0);
    assert_eq!(sqrt2.sign_of(&p(&[-3, 0, 1])), -1);
    assert_eq!(msqrt2.sign_of(&p(&[0, 1])), -1);
    // x³ − 3 at √2: 2√2 − 3 < 0.
    assert_eq!(sqrt2.sign_of(&p(&[-3, 0, 0, 1])), -1);
    // 1 + √2 vs root of x² − 2x − 1 (= 1 ± √2): equal values, same minimal poly.
    let one_plus = RealAlgebraic::root_of(&p(&[-1, -2, 1]), 1).unwrap();
    assert!(one_plus > sqrt2);
    assert_eq!(one_plus.sign_of(&p(&[-1, -2, 1])), 0);
    assert_eq!(RealAlgebraic::from_int(3).sign_of(&p(&[-3, 1])), 0);
    // Rational vs rational and the B3 reproducer: √2 is a root of (x² − 2)(x² − 3) found with
    // minimal polynomial x² − 2.
    let r = real_roots(&(&p(&[-2, 0, 1]) * &p(&[-3, 0, 1])));
    assert_eq!(r[2].0.minimal_polynomial(), p(&[-2, 0, 1]));
}

#[test]
fn algebraic_ordering_is_total_and_consistent() {
    let mut rng = SplitMix64::new(7);
    let mut all = Vec::new();
    for _ in 0..25 {
        let f = rand_poly(&mut rng, 2, 5, 6);
        for (r, _) in real_roots(&f) {
            all.push(r);
        }
    }
    for a in &all {
        for b in &all {
            let ab = a.cmp(b);
            assert_eq!(ab, b.cmp(a).reverse());
            assert_eq!(ab == Ordering::Equal, a == b);
            // Compare against floating point where clearly separated.
            let (fa, fb) = (a.to_f64(), b.to_f64());
            if (fa - fb).abs() > 1e-9 {
                assert_eq!(ab, fa.partial_cmp(&fb).unwrap());
            }
            // b's minimal polynomial vanishes at a iff a is a conjugate of b.
            assert_eq!(
                a.sign_of(&b.minimal_polynomial()) == 0,
                a.minimal_polynomial() == b.minimal_polynomial()
            );
        }
    }
}

#[test]
fn real_root_intervals_avoid_all_roots_of_f() {
    // An interval endpoint chosen for one factor (here 0 or 1) must not be a rational root of
    // another factor of f.
    let f = p(&[1728, -2880, -1728, 4800, -864, -1760, 584, 200, -77, -5, 2]);
    let mut cases = vec![f];
    let mut rng = SplitMix64::new(10);
    for _ in 0..200 {
        let mut g = p(&[1]);
        for _ in 0..rng.range(1, 5) {
            let h = if rng.chance(1, 2) {
                p(&[rng.range(-4, 4), rng.range(1, 2)])
            } else {
                rand_poly(&mut rng, 2, 3, 5)
            };
            let k = rng.range(1, 2) as usize;
            g = &g * &h.pow(k);
        }
        cases.push(g);
    }
    for f in cases {
        if f.is_constant() {
            continue;
        }
        let sqf = f.square_free_part();
        let roots = real_roots(&f);
        assert_eq!(
            roots.len(),
            sturm_count(&sqf, &q(-(1 << 40), 1), &q(1 << 40, 1))
        );
        for (r, _) in &roots {
            if !r.is_rational() {
                let (lo, hi) = (r.lower(), r.upper());
                assert!(
                    f.sign_at(lo) != 0 && f.sign_at(hi) != 0,
                    "{f}: ({lo}, {hi})"
                );
                assert_eq!(sturm_count(&sqf, lo, hi), 1);
            }
        }
    }
}
