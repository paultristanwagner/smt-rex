//! Cylindrical algebraic coverings against the full CAD on random systems:
//! same verdict, satisfying points checked exactly, unsatisfiable cores unsatisfiable by the CAD.

use num_bigint::BigInt;
use smtrex_nra::cad::{satisfies, solve as cad_solve, Constraint, SignSet};
use smtrex_nra::covering::{solve, solve_with, Characterisation, Outcome};
use smtrex_poly::rng::SplitMix64;
use smtrex_poly::MPoly;

fn rand_poly(rng: &mut SplitMix64, nvars: usize, max_deg: u32) -> MPoly {
    let terms = rng.range(1, 4) as usize;
    let mut p = MPoly::zero();
    for _ in 0..terms {
        let mut m = vec![0u32; nvars];
        let mut budget = rng.below(max_deg as u64 + 1) as u32;
        while budget > 0 {
            let v = rng.below(nvars as u64) as usize;
            m[v] += 1;
            budget -= 1;
        }
        p = &p + &MPoly::monomial(m, BigInt::from(rng.range(-3, 3)));
    }
    if rng.chance(1, 4) {
        // a product, for shared factors and higher multiplicities
        let q = rand_poly(rng, nvars, 1);
        p = &p * &q;
    }
    p
}

fn rand_system(rng: &mut SplitMix64) -> (Vec<Constraint>, usize) {
    let nvars = rng.range(1, 3) as usize;
    let k = rng.range(1, 4) as usize;
    let sets = [
        SignSet::ZERO,
        SignSet::NONZERO,
        SignSet::NEG,
        SignSet::NONPOS,
        SignSet::POS,
        SignSet::NONNEG,
    ];
    let cs = (0..k)
        .map(|_| Constraint {
            poly: rand_poly(rng, nvars, 3),
            allowed: sets[rng.below(6) as usize],
        })
        .collect();
    (cs, nvars)
}

#[test]
fn coverings_agree_with_cad() {
    let mut rng = SplitMix64::new(2024);
    let (mut sat, mut unsat) = (0, 0);
    for it in 0..1500 {
        let (cs, n) = rand_system(&mut rng);
        let want = cad_solve(&cs, n).is_some();
        let (got, _) = solve(&cs, n, None);
        match got {
            Outcome::Sat(mut m) => {
                assert!(want, "case {it}: coverings sat, CAD unsat: {cs:?}");
                assert!(
                    satisfies(&cs, &mut m),
                    "case {it}: bad model {m:?} for {cs:?}"
                );
                sat += 1;
            }
            Outcome::Unsat(core) => {
                assert!(!want, "case {it}: coverings unsat, CAD sat: {cs:?}");
                let sub: Vec<Constraint> = core.iter().map(|&i| cs[i].clone()).collect();
                assert!(
                    cad_solve(&sub, n).is_none(),
                    "case {it}: core {core:?} of {cs:?} is satisfiable"
                );
                unsat += 1;
            }
        }
    }
    assert!(sat > 200 && unsat > 200, "sat {sat}, unsat {unsat}");
}

#[test]
fn hints_are_used() {
    // x² = 2 with hint √2-ish: any model works, but a free hint value is taken as is.
    let x = MPoly::var(0);
    let y = MPoly::var(1);
    let cs = vec![Constraint {
        poly: &(&x * &x) - &(&y * &y),
        allowed: SignSet::POS,
    }];
    let hint = vec![
        smtrex_poly::RealAlgebraic::from_int(5),
        smtrex_poly::RealAlgebraic::from_int(3),
    ];
    let (got, _) = solve(&cs, 2, Some(&hint));
    match got {
        Outcome::Sat(m) => assert_eq!(m, hint),
        Outcome::Unsat(_) => panic!(),
    }
}

/// Both characterisations on random systems in three variables (where nullification, and so
/// the single-level fallback, can happen) against the CAD.
#[test]
fn characterisations_agree_with_cad_in_three_variables() {
    let mut rng = SplitMix64::new(77);
    let sets = [
        SignSet::ZERO,
        SignSet::NONZERO,
        SignSet::NEG,
        SignSet::NONPOS,
        SignSet::POS,
        SignSet::NONNEG,
    ];
    for it in 0..400 {
        let k = rng.range(1, 4) as usize;
        let cs: Vec<Constraint> = (0..k)
            .map(|_| Constraint {
                poly: rand_poly(&mut rng, 3, 2),
                allowed: sets[rng.below(6) as usize],
            })
            .collect();
        let want = cad_solve(&cs, 3).is_some();
        for mode in [Characterisation::SingleLevel, Characterisation::Hong] {
            let (got, _) = solve_with(&cs, 3, None, mode);
            match got {
                Outcome::Sat(mut m) => {
                    assert!(want, "case {it} {mode:?}: coverings sat, CAD unsat: {cs:?}");
                    assert!(satisfies(&cs, &mut m), "case {it} {mode:?}: bad model");
                }
                Outcome::Unsat(core) => {
                    assert!(
                        !want,
                        "case {it} {mode:?}: coverings unsat, CAD sat: {cs:?}"
                    );
                    let sub: Vec<Constraint> = core.iter().map(|&i| cs[i].clone()).collect();
                    assert!(cad_solve(&sub, 3).is_none(), "case {it} {mode:?}: bad core");
                }
            }
        }
    }
}

/// `z·y − x = 0` nullifies over `x = y = 0` ([ÁDEK21] §4.4.6): the single-level
/// characterisation must fall back and still decide correctly.
#[test]
fn nullification_falls_back() {
    let (x, y, z) = (MPoly::var(0), MPoly::var(1), MPoly::var(2));
    let cs = vec![
        Constraint {
            poly: &(&z * &y) - &x,
            allowed: SignSet::ZERO,
        },
        Constraint {
            poly: x.clone(),
            allowed: SignSet::ZERO,
        },
        Constraint {
            poly: y.clone(),
            allowed: SignSet::ZERO,
        },
        Constraint {
            poly: &(&z * &z) - &MPoly::from_i64(2),
            allowed: SignSet::ZERO,
        },
    ];
    let want = cad_solve(&cs, 3).is_some();
    let (got, _) = solve_with(&cs, 3, None, Characterisation::SingleLevel);
    assert_eq!(matches!(got, Outcome::Sat(_)), want);
}
