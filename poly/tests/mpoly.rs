//! Multivariate polynomials: arithmetic, coefficients, resultants, discriminants, evaluation.

mod common;

use common::{p, q, sylvester_resultant};
use num_bigint::BigInt;
use smtrex_poly::rng::SplitMix64;
use smtrex_poly::MPoly;
fn rand_mpoly(rng: &mut SplitMix64, nvars: usize, terms: usize, deg: u32, bound: i64) -> MPoly {
    MPoly::from_terms((0..terms).map(|_| {
        let m: Vec<u32> = (0..nvars)
            .map(|_| rng.below(deg as u64 + 1) as u32)
            .collect();
        (m, BigInt::from(rng.range(-bound, bound)))
    }))
}

#[test]
fn mpoly_arithmetic_and_coeffs() {
    let x = MPoly::var(0);
    let y = MPoly::var(1);
    let f = &(&x * &y) + &(&y * &y); // xy + y²
    assert_eq!(f.degree_in(1), Some(2));
    assert_eq!(f.degree_in(0), Some(1));
    assert_eq!(f.main_var(), Some(1));
    let c = f.coeffs_in(1);
    assert_eq!(c, vec![MPoly::zero(), x.clone(), MPoly::from_i64(1)]);
    assert_eq!(MPoly::from_coeffs_in(1, &c), f);
    assert_eq!((&f * &x).div_exact(&x), Some(f.clone()));
    assert_eq!(f.div_exact(&(&x + &MPoly::from_i64(1))), None);
    // eval y = 1/2: x/2 + 1/4, times 4 → 2x + 1
    assert_eq!(
        f.eval_var(1, &q(1, 2)),
        &x.scale(&BigInt::from(2)) + &MPoly::from_i64(1)
    );
    let mut rng = SplitMix64::new(8);
    for _ in 0..100 {
        let a = rand_mpoly(&mut rng, 3, 5, 3, 9);
        let b = rand_mpoly(&mut rng, 3, 5, 3, 9);
        let pt = [
            q(rng.range(-5, 5), 1),
            q(rng.range(-5, 5), 3),
            q(rng.range(-5, 5), 2),
        ];
        assert_eq!(
            (&a * &b).eval_rational(&pt),
            a.eval_rational(&pt) * b.eval_rational(&pt)
        );
        assert_eq!(
            (&a + &b).eval_rational(&pt),
            a.eval_rational(&pt) + b.eval_rational(&pt)
        );
        for v in 0..3 {
            assert_eq!(MPoly::from_coeffs_in(v, &a.coeffs_in(v)), a);
        }
        if !b.is_zero() {
            assert_eq!((&a * &b).div_exact(&b), Some(a.clone()));
        }
    }
}

#[test]
fn mpoly_resultant_specialises() {
    // Res_y(f, g)(x = a) = Res_y(f(a, y), g(a, y)) whenever the leading coefficients in y
    // survive the substitution.
    let mut rng = SplitMix64::new(9);
    let mut checked = 0;
    for _ in 0..200 {
        let f = rand_mpoly(&mut rng, 2, 5, 3, 7);
        let g = rand_mpoly(&mut rng, 2, 4, 3, 7);
        let r = f.resultant(&g, 1);
        assert!(!r.has_var(1));
        let d = f.discriminant(1);
        assert!(!d.has_var(1));
        for a in -3..=3 {
            let fa = f.eval_var_int(0, &BigInt::from(a)).to_upoly(1).unwrap();
            let ga = g.eval_var_int(0, &BigInt::from(a)).to_upoly(1).unwrap();
            if fa.degree() != f.degree_in(1) || ga.degree() != g.degree_in(1) {
                continue;
            }
            let ra = r.eval_var_int(0, &BigInt::from(a)).as_constant().unwrap();
            assert_eq!(ra, fa.resultant(&ga));
            assert_eq!(ra, sylvester_resultant(&fa, &ga));
            let da = d.eval_var_int(0, &BigInt::from(a)).as_constant().unwrap();
            assert_eq!(da, fa.discriminant());
            checked += 1;
        }
    }
    assert!(checked > 200);
    // Circle and line: Res_y(x² + y² − 1, y − x) = 2x² − 1.
    let x = MPoly::var(0);
    let y = MPoly::var(1);
    let circle = &(&(&x * &x) + &(&y * &y)) - &MPoly::from_i64(1);
    let r = circle.resultant(&(&y - &x), 1);
    assert_eq!(r.to_upoly(0).unwrap(), p(&[-1, 0, 2]));
    // Disc_y(x² + y² − 1) = −4(x² − 1)
    assert_eq!(circle.discriminant(1).to_upoly(0).unwrap(), p(&[4, 0, -4]));
}
