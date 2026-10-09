//! Irreducible factorisation over Z: known answers, cyclotomics, Swinnerton-Dyer, random products.

mod common;

use common::{p, rand_poly};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use smtrex_poly::rng::SplitMix64;
use smtrex_poly::{factor, MPoly, UPoly};
fn cyclotomic(n: usize) -> UPoly {
    // Φ_n = (x^n − 1) / ∏_{d | n, d < n} Φ_d
    let mut c = vec![0i64; n + 1];
    c[0] = -1;
    c[n] = 1;
    let mut f = p(&c);
    for d in 1..n {
        if n.is_multiple_of(d) {
            f = f.div_exact(&cyclotomic(d)).unwrap();
        }
    }
    f
}

/// Swinnerton-Dyer polynomial for the first `k` primes: irreducible of degree 2^k, but it splits
/// into factors of degree ≤ 2 modulo every prime — the worst case for Zassenhaus recombination.
fn swinnerton_dyer(k: usize) -> UPoly {
    let primes = [2i64, 3, 5, 7, 11];
    // Build as a multivariate product then eliminate: Π (x ± √p1 ± … ± √pk) computed by
    // repeated resultants: S_{j}(x) = Res_y(S_{j-1}(x − y), y² − p_j).
    let mut s = MPoly::var(0); // in x0
    for &pr in &primes[..k] {
        // s(x0 − x1)
        let shifted = substitute_linear(&s, 0, &(&MPoly::var(0) - &MPoly::var(1)));
        let y2 = &(&MPoly::var(1) * &MPoly::var(1)) - &MPoly::from_i64(pr);
        s = shifted.resultant(&y2, 1);
    }
    s.to_upoly(0).unwrap().primitive_part()
}

/// Substitute polynomial `r` for variable `v`.
fn substitute_linear(f: &MPoly, v: usize, r: &MPoly) -> MPoly {
    let coeffs = f.coeffs_in(v);
    let mut acc = MPoly::zero();
    for c in coeffs.iter().rev() {
        acc = &(&acc * r) + c;
    }
    acc
}

fn check_factorisation(f: &UPoly) -> smtrex_poly::Factored {
    let fac = factor(f);
    assert_eq!(fac.expand(), *f, "factor({f}) round-trips");
    for (g, _) in &fac.factors {
        assert!(g.lc().is_positive() && g.content().is_one() && !g.is_constant());
    }
    fac
}

#[test]
fn factor_known_answers() {
    assert_eq!(factor(&UPoly::zero()).content, BigInt::zero());
    assert!(factor(&p(&[-7])).factors.is_empty());
    let f = p(&[-2, 0, 2]); // 2x² − 2 = 2 (x − 1)(x + 1)
    let fac = check_factorisation(&f);
    assert_eq!(fac.content, BigInt::from(2));
    assert_eq!(fac.factors, vec![(p(&[-1, 1]), 1), (p(&[1, 1]), 1)]);
    // x⁴ + 4 = (x² − 2x + 2)(x² + 2x + 2)
    assert_eq!(check_factorisation(&p(&[4, 0, 0, 0, 1])).factors.len(), 2);
    // x⁴ + 1 irreducible over Z although it splits mod every prime
    assert_eq!(check_factorisation(&p(&[1, 0, 0, 0, 1])).factors.len(), 1);
    // The audit's B3 polynomial: (x² − 2)(x² − 3) must split.
    let fac = check_factorisation(&(&p(&[-2, 0, 1]) * &p(&[-3, 0, 1])));
    assert_eq!(fac.factors, vec![(p(&[-3, 0, 1]), 1), (p(&[-2, 0, 1]), 1)]);
    // Repeated factors with x.
    let f = &(&p(&[0, 1]).pow(3) * &p(&[1, 1, 1]).pow(2)) * &p(&[-5, 3]);
    let fac = check_factorisation(&f.scale(&BigInt::from(-6)));
    assert_eq!(fac.content, BigInt::from(-6));
    assert_eq!(fac.factors.len(), 3);
}

#[test]
fn factor_cyclotomic() {
    for n in 1..=40usize {
        let mut c = vec![0i64; n + 1];
        c[0] = -1;
        c[n] = 1;
        let fac = check_factorisation(&p(&c));
        let divisors = (1..=n).filter(|d| n % d == 0).count();
        assert_eq!(fac.factors.len(), divisors, "x^{n} − 1");
        for d in (1..=n).filter(|d| n % d == 0) {
            assert!(
                fac.factors.iter().any(|(g, _)| *g == cyclotomic(d)),
                "Φ_{d} in x^{n} − 1"
            );
        }
    }
}

#[test]
fn factor_swinnerton_dyer() {
    for k in 1..=4 {
        let s = swinnerton_dyer(k);
        assert_eq!(s.degree(), Some(1 << k));
        let fac = check_factorisation(&s);
        assert_eq!(fac.factors.len(), 1, "S_{k} is irreducible");
        // S_k · S_k(x+1) has exactly two irreducible factors.
        let t = &s * &s.shift_one();
        assert_eq!(check_factorisation(&t).factors.len(), 2);
    }
}

#[test]
fn factor_random_products() {
    let mut rng = SplitMix64::new(5);
    for _ in 0..150 {
        let k = 1 + rng.below(4) as usize;
        let mut f = p(&[1]);
        let mut parts = Vec::new();
        for _ in 0..k {
            let g = rand_poly(&mut rng, 1, 4, 12);
            f = &f * &g;
            parts.push(g);
        }
        let fac = check_factorisation(&f);
        // Each random part is a product of the reported irreducibles.
        let total: usize = fac.factors.iter().map(|(_, m)| m).sum();
        assert!(total >= parts.iter().filter(|g| !g.is_constant()).count());
        for (g, _) in &fac.factors {
            // irreducible factors are irreducible: re-factoring gives back one factor
            assert_eq!(factor(g).factors, vec![(g.clone(), 1)]);
        }
    }
}
