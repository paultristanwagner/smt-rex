//! The kernels for nonlinear real arithmetic: principal subresultant coefficients,
//! multivariate gcd / content / square-free part, real algebraic arithmetic, and signs and roots
//! at real algebraic points. Each is checked against an independent slow oracle or an identity.

mod common;

use common::{bareiss_det, p, q, rand_poly};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use smtrex_poly::point::{count_real_roots_at, roots_at, sign_at, Fiber};
use smtrex_poly::ring::principal_subresultant_coefficients;
use smtrex_poly::rng::SplitMix64;
use smtrex_poly::{real_roots, MPoly, RealAlgebraic, UPoly};

/// `psc_j(f, g)` as the determinant of the square matrix formed by the first `n + m − 2j`
/// columns of the `j`-th subresultant matrix (rows `x^(m−j−1) f, …, f, x^(n−j−1) g, …, g`).
fn psc_det(f: &UPoly, g: &UPoly, j: usize) -> BigInt {
    let (n, m) = (f.degree().unwrap(), g.degree().unwrap());
    let cols = n + m - 2 * j;
    let width = n + m - j;
    let mut mat = Vec::new();
    for i in 0..(m - j) {
        // x^(m-j-1-i) f: coefficient of x^e at column width-1-e
        let shift = m - j - 1 - i;
        let mut row = vec![BigInt::zero(); width];
        for (e, c) in f.coeffs().iter().enumerate() {
            row[width - 1 - (e + shift)] = c.clone();
        }
        mat.push(row);
    }
    for i in 0..(n - j) {
        let shift = n - j - 1 - i;
        let mut row = vec![BigInt::zero(); width];
        for (e, c) in g.coeffs().iter().enumerate() {
            row[width - 1 - (e + shift)] = c.clone();
        }
        mat.push(row);
    }
    let sq: Vec<Vec<BigInt>> = mat.into_iter().map(|r| r[..cols].to_vec()).collect();
    bareiss_det(sq)
}

#[test]
fn psc_matches_determinants() {
    let mut rng = SplitMix64::new(31);
    let mut defective = 0;
    for it in 0..400 {
        let mut f = rand_poly(&mut rng, 1, 6, 5);
        let mut g = rand_poly(&mut rng, 1, 6, 5);
        if it % 3 == 0 {
            // a common factor makes low-order psc vanish
            let c = rand_poly(&mut rng, 1, 2, 3);
            f = &f * &c;
            g = &g * &c;
        }
        let (n, m) = (f.degree().unwrap(), g.degree().unwrap());
        let got = principal_subresultant_coefficients(f.coeffs(), g.coeffs());
        for j in 0..n.min(m) {
            let want = psc_det(&f, &g, j);
            match got.iter().find(|(k, _)| *k == j) {
                Some((_, v)) => assert_eq!(*v, want, "psc_{j}({f}, {g})"),
                None => {
                    assert!(want.is_zero(), "psc_{j}({f}, {g}) = {want} missing");
                    defective += 1;
                }
            }
        }
        assert!(got.iter().all(|(k, _)| *k < n.min(m)));
    }
    assert!(defective > 50, "the test exercises vanishing psc");
}

fn rand_mpoly(rng: &mut SplitMix64, nvars: usize, terms: usize, deg: u32, bound: i64) -> MPoly {
    MPoly::from_terms((0..terms).map(|_| {
        let m: Vec<u32> = (0..nvars)
            .map(|_| rng.below(deg as u64 + 1) as u32)
            .collect();
        (m, BigInt::from(rng.range(-bound, bound)))
    }))
}

#[test]
fn mpoly_gcd_properties() {
    let mut rng = SplitMix64::new(77);
    for it in 0..300 {
        let nv = 1 + (it % 3);
        let a = rand_mpoly(&mut rng, nv, 3, 2, 5);
        let b = rand_mpoly(&mut rng, nv, 3, 2, 5);
        let c = rand_mpoly(&mut rng, nv, 2, 2, 4);
        if c.is_zero() {
            continue;
        }
        let (ac, bc) = (&a * &c, &b * &c);
        let g = ac.gcd(&bc);
        if ac.is_zero() && bc.is_zero() {
            assert!(g.is_zero());
            continue;
        }
        assert!(g.leading_coeff().is_positive());
        assert!(ac.div_exact(&g).is_some(), "gcd {g} divides {ac}");
        assert!(bc.div_exact(&g).is_some(), "gcd {g} divides {bc}");
        // c divides the gcd (up to the integer content of c)
        assert!(
            g.div_exact(&c.primitive()).is_some(),
            "{} | gcd({ac}, {bc}) = {g}",
            c.primitive()
        );
        // the cofactors are coprime
        if !g.is_zero() {
            let (x, y) = (ac.div_exact(&g).unwrap(), bc.div_exact(&g).unwrap());
            let h = x.gcd(&y);
            assert!(h.is_constant(), "cofactors {x}, {y} of gcd {g} share {h}");
        }
        // symmetric
        assert_eq!(g, bc.gcd(&ac));
    }
}

#[test]
fn content_and_square_free_part() {
    let mut rng = SplitMix64::new(78);
    let x0 = MPoly::var(0);
    for _ in 0..150 {
        let a = rand_mpoly(&mut rng, 3, 3, 2, 4);
        let b = rand_mpoly(&mut rng, 3, 3, 2, 4);
        if a.degree_in(2).unwrap_or(0) == 0 || b.is_zero() {
            continue;
        }
        let k = rand_mpoly(&mut rng, 2, 2, 2, 3); // free of x2
        if k.is_zero() {
            continue;
        }
        let f = &(&(&a * &a) * &b) * &k;
        let (cont, pp) = f.content_primitive_in(2);
        assert_eq!(&cont * &pp, f);
        assert!(cont.div_exact(&k.primitive()).is_some() || k.is_constant());
        // pp is primitive: its content is 1
        assert!(pp.content_primitive_in(2).0.is_one_poly());
        let s = pp.square_free_part_in(2);
        // a's primitive part in x2 divides s exactly once (a | s, a² ∤ s when a is squarefree)
        let (_, ap) = a.content_primitive_in(2);
        if ap.degree_in(2).unwrap_or(0) > 0 {
            let sa = ap.square_free_part_in(2);
            assert!(s.div_exact(&sa).is_some(), "{sa} | sqf({f}) = {s}");
        }
        // s is square-free in x2: gcd(s, ∂s) is free of x2
        let g = s.gcd(&s.derivative(2));
        assert_eq!(g.degree_in(2).unwrap_or(0), 0, "sqf part {s} of {f}");
        let _ = &x0;
    }
}

trait IsOnePoly {
    fn is_one_poly(&self) -> bool;
}
impl IsOnePoly for MPoly {
    fn is_one_poly(&self) -> bool {
        self.as_constant().is_some_and(|c| c.is_one())
    }
}

fn approx(a: &RealAlgebraic) -> f64 {
    a.to_f64()
}

#[test]
fn algebraic_arithmetic() {
    let mut rng = SplitMix64::new(5);
    let mut irr = 0;
    for _ in 0..150 {
        let pick = |rng: &mut SplitMix64| loop {
            let f = rand_poly(rng, 1, 4, 6);
            let rs = real_roots(&f);
            if rs.is_empty() {
                continue;
            }
            return rs[rng.below(rs.len() as u64) as usize].0.clone();
        };
        let a = pick(&mut rng);
        let b = pick(&mut rng);
        for (r, want) in [
            (a.add(&b), approx(&a) + approx(&b)),
            (a.mul(&b), approx(&a) * approx(&b)),
            (a.sub(&b), approx(&a) - approx(&b)),
            (a.neg(), -approx(&a)),
        ] {
            if !r.is_rational() {
                irr += 1;
            }
            assert!(
                (r.to_f64() - want).abs() <= 1e-9 * (1.0 + want.abs()),
                "{a} op {b} = {r}, want ≈ {want}"
            );
            // exact: the result is a root of its minimal polynomial (sign 0)
            assert_eq!(r.sign_of(&r.minimal_polynomial()), 0);
        }
        // identities
        assert_eq!(a.sub(&a), RealAlgebraic::from_int(0));
        assert_eq!(a.add(&b).sub(&b), a);
        assert_eq!(a.mul(&b), b.mul(&a));
    }
    assert!(irr > 100);
    // √2 · √2 = 2, √2 · √3 = √6, √2 + √3 has minimal polynomial x⁴ − 10x² + 1
    let s2 = RealAlgebraic::root_of(&p(&[-2, 0, 1]), 1).unwrap();
    let s3 = RealAlgebraic::root_of(&p(&[-3, 0, 1]), 1).unwrap();
    assert_eq!(s2.mul(&s2), RealAlgebraic::from_int(2));
    assert_eq!(
        s2.mul(&s3),
        RealAlgebraic::root_of(&p(&[-6, 0, 1]), 1).unwrap()
    );
    assert_eq!(s2.add(&s3).minimal_polynomial(), p(&[1, 0, -10, 0, 1]));
    assert_eq!(
        s2.add(&RealAlgebraic::from_rational(q(1, 2))).to_f64(),
        2f64.sqrt() + 0.5
    );
}

/// The value of an integer polynomial at a point, approximately (test oracle only).
fn approx_eval(f: &MPoly, pt: &[RealAlgebraic]) -> f64 {
    let xs: Vec<f64> = pt.iter().map(|a| a.to_f64()).collect();
    f.terms()
        .map(|(m, c)| {
            let c: f64 = c.to_string().parse().unwrap();
            m.iter().fold(c, |acc, (i, e)| acc * xs[i].powi(e as i32))
        })
        .sum()
}

/// The exact value as a real algebraic number, by the (independent) algebraic arithmetic.
fn exact_eval(f: &MPoly, pt: &[RealAlgebraic]) -> RealAlgebraic {
    let mut acc = RealAlgebraic::from_int(0);
    for (m, c) in f.terms() {
        let mut t = RealAlgebraic::from_rational(BigRational::from_integer(c.clone()));
        for (i, e) in m.iter() {
            t = t.mul(&pt[i].pow(e as usize));
        }
        acc = acc.add(&t);
    }
    acc
}

fn random_point(rng: &mut SplitMix64, n: usize) -> Vec<RealAlgebraic> {
    (0..n)
        .map(|_| {
            if rng.chance(1, 4) {
                return RealAlgebraic::from_rational(q(rng.range(-4, 4), rng.range(1, 3)));
            }
            let k = rng.range(2, 5);
            let f = if rng.chance(1, 2) {
                p(&[-k, 0, 1])
            } else {
                p(&[-k, 0, 0, 1])
            };
            let rs = real_roots(&f);
            rs[rng.below(rs.len() as u64) as usize].0.clone()
        })
        .collect()
}

#[test]
fn sign_at_points_matches_algebraic_arithmetic() {
    let mut rng = SplitMix64::new(11);
    let mut zeros = 0;
    for it in 0..250 {
        let n = 1 + it % 3;
        let mut pt = random_point(&mut rng, n);
        // Often build f to vanish at the point: f = g − g(pt) is not integral, so use products
        // with a polynomial that vanishes, e.g. x_i² − k or x_i − x_j when equal.
        let mut f = rand_mpoly(&mut rng, n, 3, 2, 4);
        if rng.chance(1, 2) {
            let i = rng.below(n as u64) as usize;
            let m = MPoly::from_upoly(&pt[i].minimal_polynomial(), i);
            f = &(&f * &m) + &(&rand_mpoly(&mut rng, n, 1, 1, 2) * &m);
        }
        if n >= 2 && rng.chance(1, 3) {
            // x0·x1 − (x0·x1 evaluated exactly) via its minimal polynomial
            let v = pt[0].mul(&pt[1]);
            let m = v.minimal_polynomial();
            let xy = &MPoly::var(0) * &MPoly::var(1);
            f = &f + &MPoly::from_upoly(&m, 0).compose(&[xy]);
        }
        let want = exact_eval(&f, &pt);
        let want_sign = match want.cmp_rational(&BigRational::zero()) {
            std::cmp::Ordering::Less => -1,
            std::cmp::Ordering::Equal => 0,
            std::cmp::Ordering::Greater => 1,
        };
        let got = sign_at(&f, &mut pt);
        assert_eq!(
            got,
            want_sign,
            "sign of {f} at {pt:?}: value {want} ≈ {}",
            approx_eval(&f, &pt)
        );
        if got == 0 {
            zeros += 1;
        }
    }
    assert!(zeros > 40, "the test exercises zero signs ({zeros})");
}

#[test]
fn roots_at_points_are_exact_roots() {
    let mut rng = SplitMix64::new(12);
    for it in 0..150 {
        let n = 1 + it % 2;
        let mut pt = random_point(&mut rng, n);
        let y = MPoly::var(n);
        // p = (y - x0)(y² - x_{n-1}·y - 1) · ... plus a random factor
        let mut f = &y - &MPoly::var(0);
        if rng.chance(1, 2) {
            f = &f * &(&(&y * &y) - &(&MPoly::var(n - 1) * &y));
        }
        let g = &rand_mpoly(&mut rng, n + 1, 3, 2, 3) + &y;
        f = &f * &g;
        let fiber = roots_at(&f, &mut pt);
        let Fiber::Roots(roots) = fiber else {
            panic!("{f} nullified at {pt:?}");
        };
        // every reported root is a root (exact, by algebraic arithmetic) and they are sorted
        for w in roots.windows(2) {
            assert!(w[0] < w[1]);
        }
        let x0 = pt[0].clone();
        assert!(
            roots.contains(&x0),
            "y = x0 is a root of {f} at {pt:?}: {roots:?}"
        );
        for r in &roots {
            let mut full = pt.clone();
            full.push(r.clone());
            assert_eq!(sign_at(&f, &mut full), 0);
        }
        // No root is missed: every real root of the iterated resultant at which f vanishes
        // (decided by the annihilator-based exact sign, not by root counting) is reported.
        let mut r = f.clone();
        for (i, a) in pt.iter().enumerate() {
            if r.has_var(i) {
                r = MPoly::from_upoly(&a.minimal_polynomial(), i).resultant(&r, i);
            }
        }
        if r.is_zero() {
            continue;
        }
        let r = r.to_upoly(n).unwrap();
        let mut want = Vec::new();
        for (c, _) in real_roots(&r) {
            let mut full = pt.clone();
            full.push(c.clone());
            if sign_at(&f, &mut full) == 0 {
                want.push(c);
            }
        }
        assert_eq!(roots, want, "roots of {f} over {pt:?}");
    }
}

#[test]
fn real_root_counts_by_subresultants() {
    let mut rng = SplitMix64::new(13);
    for _ in 0..400 {
        // univariate: compare with root isolation
        let f = rand_poly(&mut rng, 1, 7, 6);
        let mf = MPoly::from_upoly(&f, 0);
        assert_eq!(
            count_real_roots_at(&mf, 0, &mut []),
            real_roots(&f).len(),
            "real roots of {f}"
        );
        // bivariate at a rational point (leading coefficient kept)
        let g = rand_mpoly(&mut rng, 2, 4, 3, 5);
        if g.degree_in(1).unwrap_or(0) == 0 {
            continue;
        }
        let x = q(rng.range(-5, 5), rng.range(1, 3));
        let gx = g.eval_var(0, &x).to_upoly(1).unwrap();
        if gx.degree() != g.degree_in(1) {
            continue;
        }
        let mut pt = vec![RealAlgebraic::from_rational(x)];
        assert_eq!(
            count_real_roots_at(&g, 1, &mut pt),
            real_roots(&gx).len(),
            "real roots of {g} at {pt:?}"
        );
    }
}

#[test]
fn coprime_in_agrees_with_gcd() {
    let mut rng = SplitMix64::new(4242);
    let small = |rng: &mut SplitMix64| -> MPoly {
        // a random polynomial in x0, x1, x2 with small degree and coefficients
        let mut p = MPoly::zero();
        for _ in 0..1 + rng.next_u64() % 4 {
            let mut m = MPoly::from_i64((rng.next_u64() % 7) as i64 - 3);
            for v in 0..3 {
                m = &m * &MPoly::var(v).pow((rng.next_u64() % 3) as usize);
            }
            p = &p + &m;
        }
        p
    };
    let mut checked = 0;
    for _ in 0..3000 {
        let (a, b, c) = (small(&mut rng), small(&mut rng), small(&mut rng));
        // half the pairs share the factor c
        let (f, g) = if rng.next_u64().is_multiple_of(2) {
            (&a * &c, &b * &c)
        } else {
            (a, b)
        };
        if f.is_zero() || g.is_zero() {
            continue;
        }
        for v in 0..3 {
            let exact = f.gcd(&g).degree_in(v).unwrap_or(0) == 0;
            assert_eq!(f.coprime_in(&g, v), exact, "{f:?} {g:?} in x{v}");
            checked += 1;
        }
    }
    assert!(checked > 5000);
}
