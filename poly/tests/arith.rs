//! Univariate arithmetic over Z and Q: division, gcd, resultant, discriminant, Yun.

mod common;

use common::{p, q, rand_poly, sylvester_resultant};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use smtrex_poly::rng::SplitMix64;
use smtrex_poly::{QPoly, UPoly};
#[test]
fn arithmetic_basics() {
    let a = p(&[1, 2, 3]);
    let b = p(&[-1, 0, 1]);
    assert_eq!(&a + &b, p(&[0, 2, 4]));
    assert_eq!(&a - &a, UPoly::zero());
    assert_eq!(&a * &b, p(&[-1, -2, -2, 2, 3]));
    assert_eq!(a.derivative(), p(&[2, 6]));
    assert_eq!(p(&[6, 4, 2]).content(), BigInt::from(2));
    assert_eq!(p(&[-6, 4, -2]).primitive_part(), p(&[3, -2, 1]));
    assert_eq!(a.eval(&q(1, 2)), q(11, 4));
    assert_eq!(UPoly::zero().degree(), None);
    assert_eq!(p(&[0, 0, 0]), UPoly::zero());
    let (qq, r) = p(&[1, 0, 0, 1]).divrem_q(&p(&[0, 2]));
    assert_eq!(qq, QPoly::new(vec![q(0, 1), q(0, 1), q(1, 2)]));
    assert_eq!(r, QPoly::new(vec![q(1, 1)]));
    assert_eq!(p(&[1, 0, 1]).prem(&p(&[1, 2])), p(&[5]));
}

#[test]
fn divrem_and_prem_identities() {
    let mut rng = SplitMix64::new(1);
    for _ in 0..300 {
        let f = rand_poly(&mut rng, 0, 8, 30);
        let g = rand_poly(&mut rng, 0, 4, 30);
        let (qq, r) = f.divrem_q(&g);
        let gq = QPoly::from_upoly(&g);
        assert_eq!(&(&qq * &gq) + &r, QPoly::from_upoly(&f));
        assert!(r.degree() < g.degree() || r.is_zero());
        // prem = lc^(n−m+1) f mod g
        let pr = f.prem(&g);
        if f.degree() >= g.degree() {
            let k = f.degree().unwrap() - g.degree().unwrap() + 1;
            let scaled = QPoly::from_upoly(&f.scale(&num_traits::pow(g.lc(), k)));
            assert_eq!(QPoly::from_upoly(&pr), scaled.divrem(&gq).1);
        }
        // exact division round-trip
        assert_eq!((&f * &g).div_exact(&g), Some(f.clone()));
    }
}

#[test]
fn gcd_properties() {
    let mut rng = SplitMix64::new(2);
    for _ in 0..300 {
        let a = rand_poly(&mut rng, 0, 5, 20);
        let b = rand_poly(&mut rng, 0, 5, 20);
        let c = rand_poly(&mut rng, 0, 3, 20);
        let (fa, fb) = (&a * &c, &b * &c);
        let g = fa.gcd(&fb);
        assert!(g.lc().is_positive());
        assert!(fa.div_exact(&g).is_some(), "gcd divides");
        assert!(fb.div_exact(&g).is_some());
        assert!(
            g.div_exact(&c.primitive_part()).is_some(),
            "common factor divides gcd"
        );
        // Cofactors are coprime: their gcd is a constant.
        let (ca, cb) = (fa.div_exact(&g).unwrap(), fb.div_exact(&g).unwrap());
        assert!(ca.gcd(&cb).is_constant());
        // Agrees with the gcd over Q.
        let gq = QPoly::from_upoly(&fa).gcd(&QPoly::from_upoly(&fb));
        assert_eq!(gq.to_primitive(), g.primitive_part());
    }
    assert_eq!(UPoly::zero().gcd(&UPoly::zero()), UPoly::zero());
    assert_eq!(UPoly::zero().gcd(&p(&[-4, -2])), p(&[4, 2]));
    assert_eq!(p(&[6]).gcd(&p(&[4, 8])), p(&[2]));
}

#[test]
fn resultant_matches_sylvester() {
    let mut rng = SplitMix64::new(3);
    for _ in 0..400 {
        let f = rand_poly(&mut rng, 0, 6, 9);
        let g = rand_poly(&mut rng, 0, 6, 9);
        assert_eq!(
            f.resultant(&g),
            sylvester_resultant(&f, &g),
            "res({f}, {g})"
        );
    }
    // Shared root ⇒ zero; zero polynomial ⇒ zero.
    assert!(p(&[-1, 0, 1]).resultant(&p(&[-1, 1])).is_zero());
    assert!(UPoly::zero().resultant(&p(&[1, 1])).is_zero());
    assert_eq!(p(&[3]).resultant(&p(&[1, 0, 1])), BigInt::from(9));
}

#[test]
fn discriminant_known() {
    // ax² + bx + c → b² − 4ac
    assert_eq!(p(&[3, 5, 2]).discriminant(), BigInt::from(25 - 24));
    // x³ + px + q → −4p³ − 27q²
    assert_eq!(
        p(&[2, -3, 0, 1]).discriminant(),
        BigInt::from(-4 * -27 - 27 * 4)
    );
    assert!(p(&[1, -2, 1]).discriminant().is_zero());
    assert_eq!(p(&[5, 7]).discriminant(), BigInt::one());
    assert!(p(&[5]).discriminant().is_zero());
}

#[test]
fn square_free_decomposition() {
    let mut rng = SplitMix64::new(4);
    for _ in 0..200 {
        let mut f = p(&[rng.range(-3, 3).max(1)]);
        for k in 1..4 {
            if rng.chance(2, 3) {
                let g = rand_poly(&mut rng, 1, 3, 6);
                f = &f * &g.pow(k);
            }
        }
        if rng.chance(1, 2) {
            f = -&f;
        }
        let d = f.square_free();
        assert_eq!(d.expand(), f, "sqf({f}) round-trips");
        for (i, (a, k)) in d.factors.iter().enumerate() {
            assert!(a.lc().is_positive() && a.content().is_one());
            assert!(a.gcd(&a.derivative()).is_constant(), "factor square-free");
            for (b, l) in &d.factors[i + 1..] {
                assert!(a.gcd(b).is_constant(), "factors coprime");
                assert!(k < l, "multiplicities increase");
            }
        }
    }
    let d = p(&[1, -3, 3, -1]).square_free(); // −(x − 1)^3
    assert_eq!(d.content, BigInt::from(-1));
    assert_eq!(d.factors, vec![(p(&[-1, 1]), 3)]);
}
