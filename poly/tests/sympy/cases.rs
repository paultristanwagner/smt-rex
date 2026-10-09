//! Case generator for the sympy differential test (`tests/sympy/sympy_diff.py`).
//!
//! `cargo run --release -p smtrex-poly --example sympy_cases -- <kernel|all> <seed> <count>`
//! prints one JSON object per line: the inputs and SMT-Rex's answer. The Python script recomputes
//! every answer with sympy and reports mismatches. Kernels: `gcd sqf factor res disc roots count
//! ran sign mres mdisc meval mgcd msqf psc ranop msign mroots`.
//!
//! Inputs mix uniform random polynomials with adversarial families: repeated factors, close
//! roots (rational and irrational, down to 10^−12 apart), irrational roots, cyclotomic and
//! Swinnerton-Dyer polynomials (degree 8 and 16, irreducible but split modulo every prime),
//! products of shifted Swinnerton-Dyer polynomials, Wilkinson-style products of many linear
//! factors, Mignotte-style polynomials, large coefficients, degree up to 40, and zero/constant
//! edge cases.

use num_bigint::BigInt;
use num_rational::BigRational;
use smtrex_poly::point::{roots_at, sign_at, Fiber};
use smtrex_poly::rng::SplitMix64;
use smtrex_poly::{count_real_roots, real_roots, MPoly, RealAlgebraic, UPoly};
use std::cmp::Ordering;
use std::fmt::Write;

fn p(c: &[i64]) -> UPoly {
    UPoly::from_i64s(c)
}

fn big(s: &str) -> BigInt {
    s.parse().unwrap()
}

fn json_poly(f: &UPoly) -> String {
    let v: Vec<String> = f.coeffs().iter().map(|c| c.to_string()).collect();
    format!("[{}]", v.join(","))
}

fn json_rat(r: &BigRational) -> String {
    format!("\"{}/{}\"", r.numer(), r.denom())
}

fn json_mpoly(f: &MPoly) -> String {
    let v: Vec<String> = f
        .terms()
        .map(|(m, c)| {
            let e: Vec<String> = m.to_dense().iter().map(|x| x.to_string()).collect();
            format!("[[{}],{}]", e.join(","), c)
        })
        .collect();
    format!("[{}]", v.join(","))
}

fn rand_dense(rng: &mut SplitMix64, deg: usize, bound: i64) -> UPoly {
    let mut c: Vec<i64> = (0..=deg).map(|_| rng.range(-bound, bound)).collect();
    if c[deg] == 0 {
        c[deg] = 1;
    }
    p(&c)
}

fn rand_big_dense(rng: &mut SplitMix64, deg: usize) -> UPoly {
    UPoly::new(
        (0..=deg)
            .map(|_| {
                let a = BigInt::from(rng.range(-1_000_000_000, 1_000_000_000));
                let b = BigInt::from(rng.range(0, 1_000_000_000_000));
                a * BigInt::from(1_000_000_000_000i64) + b + 1
            })
            .collect(),
    )
}

fn shift(f: &UPoly, k: i64) -> UPoly {
    f.shift(&BigInt::from(k))
}

fn cyclo_like(rng: &mut SplitMix64) -> UPoly {
    let n = rng.range(1, 30) as usize;
    let mut c = vec![0i64; n + 1];
    c[n] = 1;
    c[0] = if rng.chance(1, 2) { -1 } else { 1 };
    let f = p(&c);
    if rng.chance(1, 3) {
        // x^{2n} + x^n + 1 style
        let mut d = vec![0i64; 2 * n + 1];
        d[0] = 1;
        d[n] = 1;
        d[2 * n] = 1;
        return p(&d);
    }
    f
}

/// Swinnerton-Dyer polynomials S_3 (degree 8) and S_4 (degree 16), fixed coefficients.
fn swinnerton_dyer(k: usize) -> UPoly {
    let primes = [2i64, 3, 5, 7];
    let mut s = MPoly::var(0);
    for &pr in &primes[..k] {
        let lin = &MPoly::var(0) - &MPoly::var(1);
        let coeffs = s.coeffs_in(0);
        let mut acc = MPoly::zero();
        for c in coeffs.iter().rev() {
            acc = &(&acc * &lin) + c;
        }
        let y2 = &(&MPoly::var(1) * &MPoly::var(1)) - &MPoly::from_i64(pr);
        s = acc.resultant(&y2, 1);
    }
    s.to_upoly(0).unwrap().primitive_part()
}

/// One polynomial from a random family.
fn gen_upoly(rng: &mut SplitMix64) -> UPoly {
    match rng.below(16) {
        0 => {
            let d = rng.below(4) as usize;
            rand_dense(rng, d, 5)
        }
        1 | 2 => {
            let d = rng.below(13) as usize;
            rand_dense(rng, d, 20)
        }
        3 => {
            // repeated factors
            let mut f = p(&[rng.range(1, 6)]);
            for k in 1..=3 {
                if rng.chance(2, 3) {
                    let d = 1 + rng.below(3) as usize;
                    f = &f * &rand_dense(rng, d, 7).pow(k);
                }
            }
            if rng.chance(1, 2) {
                f = -&f;
            }
            f
        }
        4 => {
            // close rational roots (ax − b)(ax − b − 1), a large
            let a = 10i64.pow(rng.range(2, 9) as u32);
            let b = rng.range(-3, 3) * a + rng.range(-5, 5);
            let mut f = &p(&[-b, a]) * &p(&[-b - 1, a]);
            if rng.chance(1, 2) {
                f = &f * &p(&[-2, 0, 1]);
            }
            f
        }
        5 => {
            // close irrational roots √n and √(n + 10^−2k)
            let n = rng.range(2, 9);
            let k = rng.range(1, 6) as u32;
            let s = 10i64.pow(2 * k);
            &p(&[-n, 0, 1]) * &p(&[-(n * s + 1), 0, s])
        }
        6 => {
            // irrational roots x^d − n
            let d = rng.range(2, 7) as usize;
            let mut c = vec![0i64; d + 1];
            c[0] = -rng.range(2, 50);
            c[d] = rng.range(1, 4);
            p(&c)
        }
        7 => cyclo_like(rng),
        8 => {
            let s = swinnerton_dyer(3);
            match rng.below(4) {
                0 => s,
                1 => &s * &shift(&s, rng.range(1, 3)),
                2 => &s * &p(&[-2, 0, 1]),
                _ => &s * &rand_dense(rng, 2, 5),
            }
        }
        9 => {
            if rng.chance(1, 8) {
                // degree 32, 16 modular factors: the recombination worst case
                let s = swinnerton_dyer(4);
                &s * &shift(&s, 1)
            } else if rng.chance(1, 4) {
                swinnerton_dyer(4)
            } else {
                let s = swinnerton_dyer(3);
                &s.pow(2) * &p(&[-1, 1])
            }
        }
        10 => {
            // Wilkinson-style: many linear factors, some repeated
            let n = rng.range(3, 20);
            let roots: Vec<i64> = (0..n).map(|_| rng.range(-12, 12)).collect();
            UPoly::from_roots(&roots)
        }
        11 => {
            // Mignotte: x^n − 2(ax − 1)^2 has two roots very close to 1/a
            let n = rng.range(3, 12) as usize;
            let a = rng.range(3, 60);
            let mut c = vec![0i64; n + 1];
            c[n] = 1;
            let sq = p(&[-1, a]).pow(2).scale(&BigInt::from(2));
            &p(&c) - &sq
        }
        12 => {
            // high degree, small coefficients
            let d = rng.range(20, 40) as usize;
            rand_dense(rng, d, 3)
        }
        13 => {
            // big coefficients
            let d = rng.below(7) as usize;
            rand_big_dense(rng, d)
        }
        14 => {
            // edge: zero, constants, x^k, x^k · stuff
            match rng.below(5) {
                0 => UPoly::zero(),
                1 => p(&[rng.range(-9, 9)]),
                2 => UPoly::x().pow(rng.range(1, 5) as usize),
                3 => &UPoly::x().pow(rng.range(1, 3) as usize) * &rand_dense(rng, 3, 5),
                _ => UPoly::constant(big("-123456789012345678901234567890")),
            }
        }
        _ => {
            // product of random irreducible-ish pieces
            let mut f = p(&[1]);
            for _ in 0..rng.range(1, 4) {
                let d = 1 + rng.below(5) as usize;
                f = &f * &rand_dense(rng, d, 9);
            }
            f
        }
    }
}

fn nonzero(rng: &mut SplitMix64) -> UPoly {
    loop {
        let f = gen_upoly(rng);
        if !f.is_zero() {
            return f;
        }
    }
}

/// Small enough for Sylvester-size resultants in sympy to stay quick.
fn gen_small(rng: &mut SplitMix64) -> UPoly {
    loop {
        let f = gen_upoly(rng);
        if f.degree().unwrap_or(0) <= 16 {
            return f;
        }
    }
}

fn rand_rat(rng: &mut SplitMix64) -> BigRational {
    let d = [1i64, 2, 3, 4, 7, 1000][rng.below(6) as usize];
    BigRational::new(BigInt::from(rng.range(-6 * d, 6 * d)), BigInt::from(d))
}

fn rand_mpoly(rng: &mut SplitMix64, nvars: usize) -> MPoly {
    let terms = rng.range(1, 6) as usize;
    let deg = rng.range(1, 3) as u64;
    MPoly::from_terms((0..terms).map(|_| {
        let m: Vec<u32> = (0..nvars).map(|_| rng.below(deg + 1) as u32).collect();
        (m, BigInt::from(rng.range(-9, 9)))
    }))
}

fn emit(kernel: &str, rng: &mut SplitMix64) -> String {
    let mut s = String::new();
    match kernel {
        "gcd" => {
            let c = gen_small(rng);
            let mut f = gen_upoly(rng);
            let mut g = gen_small(rng);
            if rng.chance(2, 3) && !c.is_zero() {
                f = &f * &c;
                g = &g * &c;
            }
            let r = f.gcd(&g);
            write!(
                s,
                r#"{{"k":"gcd","f":{},"g":{},"r":{}}}"#,
                json_poly(&f),
                json_poly(&g),
                json_poly(&r)
            )
            .unwrap();
        }
        "sqf" | "factor" => {
            let f = gen_upoly(rng);
            let d = if kernel == "sqf" {
                f.square_free()
            } else {
                f.factor()
            };
            let fs: Vec<String> = d
                .factors
                .iter()
                .map(|(g, k)| format!("[{},{}]", json_poly(g), k))
                .collect();
            write!(
                s,
                r#"{{"k":"{kernel}","f":{},"c":{},"r":[{}]}}"#,
                json_poly(&f),
                d.content,
                fs.join(",")
            )
            .unwrap();
        }
        "res" => {
            let f = gen_small(rng);
            let g = gen_small(rng);
            write!(
                s,
                r#"{{"k":"res","f":{},"g":{},"r":{}}}"#,
                json_poly(&f),
                json_poly(&g),
                f.resultant(&g)
            )
            .unwrap();
        }
        "disc" => {
            let f = gen_upoly(rng);
            write!(
                s,
                r#"{{"k":"disc","f":{},"r":{}}}"#,
                json_poly(&f),
                f.discriminant()
            )
            .unwrap();
        }
        "roots" => {
            let f = nonzero(rng);
            let rs: Vec<String> = real_roots(&f)
                .iter()
                .map(|(r, m)| format!("[{},{},{}]", json_rat(r.lower()), json_rat(r.upper()), m))
                .collect();
            write!(
                s,
                r#"{{"k":"roots","f":{},"r":[{}]}}"#,
                json_poly(&f),
                rs.join(",")
            )
            .unwrap();
        }
        "count" => {
            let f = nonzero(rng);
            // Bounds: random rationals, sometimes exactly a rational root or unbounded.
            let roots = real_roots(&f);
            let pick = |rng: &mut SplitMix64| -> Option<BigRational> {
                match rng.below(5) {
                    0 => None,
                    1 => roots
                        .iter()
                        .find_map(|(r, _)| r.as_rational().cloned())
                        .or(Some(rand_rat(rng))),
                    _ => Some(rand_rat(rng)),
                }
            };
            let (mut a, mut b) = (pick(rng), pick(rng));
            if let (Some(x), Some(y)) = (&a, &b) {
                if x > y {
                    std::mem::swap(&mut a, &mut b);
                }
            }
            let n = count_real_roots(&f, a.as_ref(), b.as_ref(), false);
            let m = count_real_roots(&f, a.as_ref(), b.as_ref(), true);
            let js = |x: &Option<BigRational>| x.as_ref().map_or("null".to_string(), json_rat);
            write!(
                s,
                r#"{{"k":"count","f":{},"a":{},"b":{},"n":{},"m":{}}}"#,
                json_poly(&f),
                js(&a),
                js(&b),
                n,
                m
            )
            .unwrap();
        }
        "ran" | "sign" => {
            // Two real roots, from polynomials that often share factors or have close roots.
            let pick_root = |rng: &mut SplitMix64| -> (UPoly, usize, RealAlgebraic) {
                loop {
                    let f = nonzero(rng);
                    let rs = real_roots(&f);
                    if rs.is_empty() || f.degree().unwrap() > 24 {
                        continue;
                    }
                    let i = rng.below(rs.len() as u64) as usize;
                    return (f, i, rs[i].0.clone());
                }
            };
            let (f, i, a) = pick_root(rng);
            if kernel == "ran" {
                let (g, j, b) = if rng.chance(1, 3) {
                    // same polynomial, or a multiple sharing the root's factor
                    let g = &f * &gen_small(rng);
                    let g = if g.is_zero() { f.clone() } else { g };
                    let rs = real_roots(&g);
                    let j = rng.below(rs.len() as u64) as usize;
                    (g, j, rs[j].0.clone())
                } else {
                    pick_root(rng)
                };
                let c = match a.cmp(&b) {
                    Ordering::Less => -1,
                    Ordering::Equal => 0,
                    Ordering::Greater => 1,
                };
                write!(
                    s,
                    r#"{{"k":"ran","f":{},"i":{},"g":{},"j":{},"r":{},"eq":{}}}"#,
                    json_poly(&f),
                    i,
                    json_poly(&g),
                    j,
                    c,
                    a == b
                )
                .unwrap();
            } else {
                // q is random, or a multiple of a factor of f, or vanishes nearby
                let q = match rng.below(3) {
                    0 => &gen_small(rng) * &f.square_free_part(),
                    _ => gen_small(rng),
                };
                write!(
                    s,
                    r#"{{"k":"sign","f":{},"i":{},"q":{},"r":{}}}"#,
                    json_poly(&f),
                    i,
                    json_poly(&q),
                    a.sign_of(&q)
                )
                .unwrap();
            }
        }
        "mres" | "mdisc" | "meval" => {
            let nv = rng.range(2, 3) as usize;
            let f = rand_mpoly(rng, nv);
            let v = rng.below(nv as u64) as usize;
            match kernel {
                "mres" => {
                    let g = rand_mpoly(rng, nv);
                    write!(
                        s,
                        r#"{{"k":"mres","f":{},"g":{},"v":{},"r":{}}}"#,
                        json_mpoly(&f),
                        json_mpoly(&g),
                        v,
                        json_mpoly(&f.resultant(&g, v))
                    )
                    .unwrap();
                }
                "mdisc" => {
                    write!(
                        s,
                        r#"{{"k":"mdisc","f":{},"v":{},"r":{}}}"#,
                        json_mpoly(&f),
                        v,
                        json_mpoly(&f.discriminant(v))
                    )
                    .unwrap();
                }
                _ => {
                    let x = rand_rat(rng);
                    write!(
                        s,
                        r#"{{"k":"meval","f":{},"v":{},"x":{},"r":{}}}"#,
                        json_mpoly(&f),
                        v,
                        json_rat(&x),
                        json_mpoly(&f.eval_var(v, &x))
                    )
                    .unwrap();
                }
            }
        }
        "mgcd" => {
            let nv = rng.range(2, 3) as usize;
            let (a, b, c) = (
                rand_mpoly(rng, nv),
                rand_mpoly(rng, nv),
                rand_mpoly(rng, nv),
            );
            let (f, g) = if rng.chance(3, 4) {
                (&a * &c, &b * &c)
            } else {
                (a, b)
            };
            write!(
                s,
                r#"{{"k":"mgcd","f":{},"g":{},"r":{}}}"#,
                json_mpoly(&f),
                json_mpoly(&g),
                json_mpoly(&f.gcd(&g))
            )
            .unwrap();
        }
        "msqf" => {
            let nv = rng.range(2, 3) as usize;
            let (a, b) = (rand_mpoly(rng, nv), rand_mpoly(rng, nv));
            let k = rand_mpoly(rng, nv - 1);
            let f = &(&(&a * &a) * &b) * &k;
            let v = nv - 1;
            let (cont, pp) = f.content_primitive_in(v);
            write!(
                s,
                r#"{{"k":"msqf","f":{},"v":{},"c":{},"r":{}}}"#,
                json_mpoly(&f),
                v,
                json_mpoly(&cont),
                json_mpoly(&pp.square_free_part_in(v))
            )
            .unwrap();
        }
        "psc" => {
            let nv = rng.range(1, 2) as usize;
            let mut f = rand_mpoly(rng, nv);
            let mut g = rand_mpoly(rng, nv);
            if rng.chance(1, 3) {
                let c = rand_mpoly(rng, nv);
                f = &f * &c;
                g = &g * &c;
            }
            let v = nv - 1;
            let ps: Vec<String> = f
                .psc(&g, v)
                .iter()
                .map(|(j, p)| format!("[{j},{}]", json_mpoly(p)))
                .collect();
            write!(
                s,
                r#"{{"k":"psc","f":{},"g":{},"v":{},"r":[{}]}}"#,
                json_mpoly(&f),
                json_mpoly(&g),
                v,
                ps.join(",")
            )
            .unwrap();
        }
        "ranop" => {
            let pick_root = |rng: &mut SplitMix64| -> (UPoly, usize, RealAlgebraic) {
                loop {
                    let f = gen_small(rng);
                    if f.degree().unwrap_or(0) == 0 || f.degree().unwrap() > 4 {
                        continue;
                    }
                    let rs = real_roots(&f);
                    if rs.is_empty() {
                        continue;
                    }
                    let i = rng.below(rs.len() as u64) as usize;
                    return (f, i, rs[i].0.clone());
                }
            };
            let (f, i, a) = pick_root(rng);
            let (g, j, b) = pick_root(rng);
            let op = if rng.chance(1, 2) { "add" } else { "mul" };
            let r = if op == "add" { a.add(&b) } else { a.mul(&b) };
            write!(
                s,
                r#"{{"k":"ranop","op":"{op}","f":{},"i":{},"g":{},"j":{},"r":{},"ri":{}}}"#,
                json_poly(&f),
                i,
                json_poly(&g),
                j,
                json_poly(&r.minimal_polynomial()),
                r.root_index()
            )
            .unwrap();
        }
        "msign" | "mroots" => {
            // A point built like a CAD sample: each coordinate a root of a random polynomial in
            // the previous coordinates (or a rational), so coordinates are algebraically related.
            let k = rng.range(1, 3) as usize;
            let mut pt: Vec<RealAlgebraic> = Vec::new();
            let mut defining: Vec<MPoly> = Vec::new();
            while pt.len() < k {
                let i = pt.len();
                if rng.chance(1, 5) {
                    let x = rand_rat(rng);
                    defining.push(
                        &MPoly::var(i).scale(x.denom()) - &MPoly::constant(x.numer().clone()),
                    );
                    pt.push(RealAlgebraic::from_rational(x));
                    continue;
                }
                let mut lp = rand_mpoly(rng, i + 1);
                lp = &lp + &MPoly::var(i).pow(rng.range(1, 2) as usize);
                if let Fiber::Roots(rs) = roots_at(&lp, &mut pt) {
                    if !rs.is_empty() {
                        let r = rs[rng.below(rs.len() as u64) as usize].clone();
                        defining.push(lp);
                        pt.push(r);
                    }
                }
            }
            let jpt: Vec<String> = pt
                .iter()
                .map(|a| {
                    format!(
                        "[{},{}]",
                        json_poly(&a.minimal_polynomial()),
                        a.root_index()
                    )
                })
                .collect();
            if kernel == "msign" {
                let mut f = rand_mpoly(rng, k);
                if rng.chance(1, 2) {
                    // often vanish: a multiple of a defining polynomial
                    let d = &defining[rng.below(k as u64) as usize];
                    f = &(&f * d) + &(&rand_mpoly(rng, k) * d);
                    if rng.chance(1, 3) {
                        f = &f + &MPoly::from_i64(rng.range(-1, 1));
                    }
                }
                let sgn = sign_at(&f, &mut pt);
                write!(
                    s,
                    r#"{{"k":"msign","pt":[{}],"f":{},"r":{}}}"#,
                    jpt.join(","),
                    json_mpoly(&f),
                    sgn
                )
                .unwrap();
            } else {
                let y = MPoly::var(k);
                let mut f = &rand_mpoly(rng, k + 1) + &y.pow(rng.range(1, 3) as usize);
                if rng.chance(1, 2) {
                    // a factor vanishing over the point: nullification or degree drop
                    let d = &defining[rng.below(k as u64) as usize];
                    f = &(&(d * &y) + &rand_mpoly(rng, k + 1)) * &(&y - &MPoly::var(0));
                }
                let r = match roots_at(&f, &mut pt) {
                    Fiber::Nullified => "null".to_string(),
                    Fiber::Roots(rs) => format!(
                        "[{}]",
                        rs.iter()
                            .map(|a| format!(
                                "[{},{}]",
                                json_poly(&a.minimal_polynomial()),
                                a.root_index()
                            ))
                            .collect::<Vec<_>>()
                            .join(",")
                    ),
                };
                write!(
                    s,
                    r#"{{"k":"mroots","pt":[{}],"f":{},"r":{}}}"#,
                    jpt.join(","),
                    json_mpoly(&f),
                    r
                )
                .unwrap();
            }
        }
        other => panic!("unknown kernel {other}"),
    }
    s
}

const KERNELS: [&str; 18] = [
    "gcd", "sqf", "factor", "res", "disc", "roots", "count", "ran", "sign", "mres", "mdisc",
    "meval", "mgcd", "msqf", "psc", "ranop", "msign", "mroots",
];

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let kernel = args.get(1).map(String::as_str).unwrap_or("all");
    let seed: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1);
    let count: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(100);
    let kernels: Vec<&str> = if kernel == "all" {
        KERNELS.to_vec()
    } else {
        vec![kernel]
    };
    for k in kernels {
        let tag = k
            .bytes()
            .fold(0u64, |h, b| h.wrapping_mul(131).wrapping_add(b as u64));
        let mut rng = SplitMix64::new(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ tag);
        for _ in 0..count {
            println!("{}", emit(k, &mut rng));
        }
    }
}
