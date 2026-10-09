//! Factorisation in `Z[x]`: square-free decomposition (Yun), then the Berlekamp–Zassenhaus
//! scheme on each square-free part — factor modulo a suitable prime `p` (distinct-degree plus
//! Cantor–Zassenhaus), lift the modular factorisation to `p^(2^j)` with multifactor quadratic
//! Hensel lifting, and recombine lifted factors by subset trials with exact trial division.
//!
//! The result is correct for every admissible prime (one not dividing `lc(f) · disc(f)`, so `f`
//! stays square-free of the same degree): the modulus exceeds twice the Landau–Mignotte bound, so
//! every true factor is the symmetric residue of some subset product, and subsets are tried in
//! increasing size, so every accepted factor is irreducible. Recombination is exponential in the
//! number of modular factors in the worst case (e.g. Swinnerton-Dyer polynomials); van Hoeij's
//! lattice-reduction recombination would avoid that.

use crate::modp::{Field, Fp};
use crate::rng::SplitMix64;
use crate::upoly::{Factored, UPoly};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, ToPrimitive, Zero};

/// Number of admissible primes tried; the one with the fewest modular factors is used.
const PRIME_TRIALS: usize = 6;

/// Irreducible factorisation `f = content · ∏ fᵢ^kᵢ` over `Z`: every `fᵢ` irreducible in `Z[x]`,
/// primitive, with positive leading coefficient. Factors are sorted by (degree, coefficients),
/// then multiplicity. `factor(0)` has content `0` and no factors; a constant `c` gives `(c, [])`.
pub fn factor(f: &UPoly) -> Factored {
    let sqf = f.square_free();
    let mut factors = Vec::new();
    for (g, k) in &sqf.factors {
        for h in factor_squarefree(g) {
            factors.push((h, *k));
        }
    }
    factors.sort_by(|(a, ka), (b, kb)| {
        a.degree()
            .cmp(&b.degree())
            .then_with(|| a.coeffs().cmp(b.coeffs()))
            .then(ka.cmp(kb))
    });
    Factored {
        content: sqf.content,
        factors,
    }
}

/// Irreducible factors of a primitive square-free `f` with positive leading coefficient and
/// positive degree (Zassenhaus). Each factor is primitive with positive leading coefficient.
pub fn factor_squarefree(f: &UPoly) -> Vec<UPoly> {
    let n = f.degree().expect("factor_squarefree(0)");
    assert!(n >= 1);
    if n == 1 {
        return vec![f.clone()];
    }
    // Pull out the factor x: it is the only factor whose constant term vanishes.
    if f.coeff(0).is_zero() {
        let (g, k) = f.strip_x();
        debug_assert_eq!(k, 1, "square-free input");
        let mut out = vec![UPoly::x()];
        if !g.is_constant() {
            out.extend(factor_squarefree(&g));
        }
        return out;
    }
    let lc = f.lc();
    let mut rng = SplitMix64::new(0x5eed_f00d ^ n as u64);

    // Pick the admissible prime with the fewest modular factors.
    let mut best: Option<(Field, Vec<Fp>)> = None;
    let mut found = 0;
    for p in odd_primes() {
        if (&lc % BigInt::from(p)).is_zero() {
            continue;
        }
        let fld = Field::new(p);
        let fp = fld.reduce(f.coeffs());
        if fld.gcd(&fp, &fld.derivative(&fp)).len() != 1 {
            continue; // not square-free mod p
        }
        let facs = fld.factor_squarefree(&fld.monic(&fp), &mut rng);
        if facs.len() == 1 {
            return vec![f.clone()]; // irreducible mod p, hence over Z
        }
        if best.as_ref().is_none_or(|(_, b)| facs.len() < b.len()) {
            best = Some((fld, facs));
        }
        found += 1;
        if found >= PRIME_TRIALS {
            break;
        }
    }
    let (fld, modular) = best.expect("some prime is admissible");
    let p = BigInt::from(fld.p);

    // Modulus M = p^(2^j) > 2 · |lc(f)| · 2^n · ‖f‖₂  (Landau–Mignotte, with the lc multiplier).
    let norm2 = f
        .coeffs()
        .iter()
        .map(|c| c * c)
        .fold(BigInt::zero(), |a, b| a + b)
        .sqrt()
        + 1u32;
    let bound = lc.abs() * (BigInt::one() << n) * norm2;
    let mut m = p.clone();
    while m <= &bound * 2u32 {
        m = &m * &m;
    }
    let lifted = hensel_lift_tree(f, &modular, fld, &m);
    debug_assert!({
        let mut prod = vec![lc.clone()];
        for u in &lifted {
            prod = zm_mul(&prod, u, &m);
        }
        prod == zm_reduce(f.coeffs(), &m)
    });
    recombine(f, lifted, &m)
}

/// Odd primes 3, 5, 7, … by trial division (the factoriser needs only a handful).
fn odd_primes() -> impl Iterator<Item = u64> {
    (3u64..(1 << 31)).step_by(2).filter(|&n| {
        let mut d = 3;
        while d * d <= n {
            if n % d == 0 {
                return false;
            }
            d += 2;
        }
        true
    })
}

/// Zassenhaus recombination: try subsets of the lifted monic factors in increasing size; a subset
/// `S` gives the candidate `pp(symmetric(lc(f*) · ∏_S uᵢ mod M))`, accepted iff it divides the
/// remaining cofactor `f*` exactly (von zur Gathen–Gerhard, MCA Algorithm 15.19, with trial
/// division in place of the norm test).
fn recombine(f: &UPoly, mut lifted: Vec<Vec<BigInt>>, m: &BigInt) -> Vec<UPoly> {
    let half = m >> 1u32;
    let mut out = Vec::new();
    let mut rest = f.clone();
    let mut s = 1;
    'outer: while 2 * s <= lifted.len() {
        let lc = rest.lc();
        let c0 = rest.coeff(0);
        let target0 = &lc * &c0; // the constant term of a candidate divides lc(f*)·f*(0)
        let mut comb: Vec<usize> = (0..s).collect();
        loop {
            // Constant-term filter, then the full candidate.
            let mut k0 = lc.mod_floor(m);
            for &i in &comb {
                k0 = (k0 * lifted[i].first().cloned().unwrap_or_default()).mod_floor(m);
            }
            let k0 = symmetric(k0, m, &half);
            let plausible = c0.is_zero() || (!k0.is_zero() && (&target0 % &k0).is_zero());
            if plausible {
                let mut prod = vec![lc.mod_floor(m)];
                for &i in &comb {
                    prod = zm_mul(&prod, &lifted[i], m);
                }
                let cand = UPoly::new(prod.into_iter().map(|c| symmetric(c, m, &half)).collect())
                    .primitive_part();
                if !cand.is_constant() {
                    if let Some(q) = rest.div_exact(&cand) {
                        out.push(cand);
                        rest = q;
                        for &i in comb.iter().rev() {
                            lifted.remove(i);
                        }
                        continue 'outer; // same size s on the smaller set
                    }
                }
            }
            if !next_combination(&mut comb, lifted.len()) {
                break;
            }
        }
        s += 1;
    }
    if !rest.is_constant() {
        out.push(rest.primitive_part());
    }
    out
}

/// Advance `comb` (strictly increasing indices below `n`) to the next combination of the same
/// size in lexicographic order; `false` when it was the last.
fn next_combination(comb: &mut [usize], n: usize) -> bool {
    let k = comb.len();
    let mut i = k;
    while i > 0 {
        i -= 1;
        if comb[i] < n - k + i {
            comb[i] += 1;
            for j in i + 1..k {
                comb[j] = comb[j - 1] + 1;
            }
            return true;
        }
    }
    false
}

fn symmetric(c: BigInt, m: &BigInt, half: &BigInt) -> BigInt {
    if &c > half {
        c - m
    } else {
        c
    }
}

// Arithmetic in (Z/m)[x], coefficients in [0, m).

fn zm_trim(v: &mut Vec<BigInt>) {
    while v.last().is_some_and(|c| c.is_zero()) {
        v.pop();
    }
}

fn zm_reduce(a: &[BigInt], m: &BigInt) -> Vec<BigInt> {
    let mut v: Vec<BigInt> = a.iter().map(|c| c.mod_floor(m)).collect();
    zm_trim(&mut v);
    v
}

fn zm_add(a: &[BigInt], b: &[BigInt], m: &BigInt) -> Vec<BigInt> {
    let n = a.len().max(b.len());
    let z = BigInt::zero();
    let mut v: Vec<BigInt> = (0..n)
        .map(|i| (a.get(i).unwrap_or(&z) + b.get(i).unwrap_or(&z)).mod_floor(m))
        .collect();
    zm_trim(&mut v);
    v
}

fn zm_sub(a: &[BigInt], b: &[BigInt], m: &BigInt) -> Vec<BigInt> {
    let n = a.len().max(b.len());
    let z = BigInt::zero();
    let mut v: Vec<BigInt> = (0..n)
        .map(|i| (a.get(i).unwrap_or(&z) - b.get(i).unwrap_or(&z)).mod_floor(m))
        .collect();
    zm_trim(&mut v);
    v
}

fn zm_mul(a: &[BigInt], b: &[BigInt], m: &BigInt) -> Vec<BigInt> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut v = vec![BigInt::zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        if x.is_zero() {
            continue;
        }
        for (j, y) in b.iter().enumerate() {
            v[i + j] += x * y;
        }
    }
    zm_reduce(&v, m)
}

fn zm_scale(a: &[BigInt], k: &BigInt, m: &BigInt) -> Vec<BigInt> {
    zm_reduce(&a.iter().map(|c| c * k).collect::<Vec<_>>(), m)
}

/// Division by a monic `b` in `(Z/m)[x]`.
fn zm_divrem_monic(a: &[BigInt], b: &[BigInt], m: &BigInt) -> (Vec<BigInt>, Vec<BigInt>) {
    let db = b.len() - 1;
    debug_assert!(b[db].is_one());
    if a.len() < b.len() {
        return (Vec::new(), a.to_vec());
    }
    let mut r = a.to_vec();
    let mut q = vec![BigInt::zero(); a.len() - db];
    for i in (0..q.len()).rev() {
        let t = r[i + db].mod_floor(m);
        if t.is_zero() {
            continue;
        }
        for (j, bj) in b.iter().enumerate() {
            r[i + j] = (&r[i + j] - &t * bj).mod_floor(m);
        }
        q[i] = t;
    }
    r.truncate(db);
    zm_trim(&mut r);
    zm_trim(&mut q);
    (q, r)
}

fn lift_fp(a: &[u64]) -> Vec<BigInt> {
    a.iter().map(|&x| BigInt::from(x)).collect()
}

fn inverse_mod(a: &BigInt, m: &BigInt) -> BigInt {
    let e = a.mod_floor(m).extended_gcd(m);
    assert!(
        e.gcd.is_one(),
        "leading coefficient not invertible modulo p^k"
    );
    e.x.mod_floor(m)
}

/// One quadratic Hensel step (MCA Algorithm 15.10): from `f ≡ g·h`, `s·g + t·h ≡ 1 (mod m)` with
/// `h` monic, `deg s < deg h`, `deg t < deg g`, produce the same relations modulo `m²`.
#[allow(clippy::type_complexity)]
fn hensel_step(
    f: &[BigInt],
    g: &[BigInt],
    h: &[BigInt],
    s: &[BigInt],
    t: &[BigInt],
    m2: &BigInt,
) -> (Vec<BigInt>, Vec<BigInt>, Vec<BigInt>, Vec<BigInt>) {
    let e = zm_sub(&zm_reduce(f, m2), &zm_mul(g, h, m2), m2);
    let (q, r) = zm_divrem_monic(&zm_mul(s, &e, m2), h, m2);
    let g2 = zm_add(&zm_add(g, &zm_mul(t, &e, m2), m2), &zm_mul(&q, g, m2), m2);
    let h2 = zm_add(h, &r, m2);
    let b = zm_sub(
        &zm_add(&zm_mul(s, &g2, m2), &zm_mul(t, &h2, m2), m2),
        &[BigInt::one()],
        m2,
    );
    let (c, d) = zm_divrem_monic(&zm_mul(s, &b, m2), &h2, m2);
    let s2 = zm_sub(s, &d, m2);
    let t2 = zm_sub(&zm_sub(t, &zm_mul(t, &b, m2), m2), &zm_mul(&c, &g2, m2), m2);
    (g2, h2, s2, t2)
}

/// Multifactor Hensel lifting along a balanced factor tree (MCA Algorithm 15.17): returns monic
/// `u₁…u_r` modulo `m = p^(2^j)` with `f ≡ lc(f) · ∏ uᵢ (mod m)` and `uᵢ ≡ (modular factor i)`.
fn hensel_lift_tree(f: &UPoly, modular: &[Fp], fld: Field, m: &BigInt) -> Vec<Vec<BigInt>> {
    let mut out = Vec::new();
    lift_node(&zm_reduce(f.coeffs(), m), modular, fld, m, &mut out);
    out
}

fn lift_node(fz: &[BigInt], facs: &[Fp], fld: Field, m: &BigInt, out: &mut Vec<Vec<BigInt>>) {
    if facs.len() == 1 {
        let inv = inverse_mod(fz.last().unwrap(), m);
        out.push(zm_scale(fz, &inv, m));
        return;
    }
    let p = BigInt::from(fld.p);
    let k = facs.len() / 2;
    let (left, right) = facs.split_at(k);
    let lcp = (fz.last().unwrap() % &p).to_u64().unwrap();
    let mut g0: Fp = vec![lcp];
    for u in left {
        g0 = fld.mul(&g0, u);
    }
    let mut h0: Fp = vec![1];
    for u in right {
        h0 = fld.mul(&h0, u);
    }
    let (one, s0, t0) = fld.xgcd(&g0, &h0);
    assert_eq!(one, vec![1], "modular factors must be coprime");
    let (mut g, mut h, mut s, mut t) = (lift_fp(&g0), lift_fp(&h0), lift_fp(&s0), lift_fp(&t0));
    let mut cur = p.clone();
    while &cur < m {
        let m2 = &cur * &cur;
        (g, h, s, t) = hensel_step(fz, &g, &h, &s, &t, &m2);
        cur = m2;
    }
    debug_assert_eq!(&cur, m);
    lift_node(&g, left, fld, m, out);
    lift_node(&h, right, fld, m, out);
}
