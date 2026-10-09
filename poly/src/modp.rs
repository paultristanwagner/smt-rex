//! Dense polynomials over the prime field `F_p` (word-size `p < 2^31`) and their factorisation:
//! distinct-degree factorisation followed by Cantor–Zassenhaus equal-degree splitting.

use crate::rng::SplitMix64;
use num_bigint::{BigInt, BigUint};
use num_traits::{One, ToPrimitive};

/// A polynomial over `F_p`, ascending coefficients in `[0, p)`, no trailing zeros.
pub type Fp = Vec<u64>;

/// Arithmetic context for one prime.
#[derive(Clone, Copy, Debug)]
pub struct Field {
    pub p: u64,
}

impl Field {
    pub fn new(p: u64) -> Field {
        assert!((3..(1 << 31)).contains(&p), "word-size odd prime expected");
        Field { p }
    }

    #[inline]
    fn mulm(&self, a: u64, b: u64) -> u64 {
        a * b % self.p
    }

    /// `a^e mod p`.
    pub fn powm(&self, mut a: u64, mut e: u64) -> u64 {
        let mut r = 1;
        a %= self.p;
        while e > 0 {
            if e & 1 == 1 {
                r = self.mulm(r, a);
            }
            a = self.mulm(a, a);
            e >>= 1;
        }
        r
    }

    /// Multiplicative inverse (Fermat). Panics on zero.
    pub fn inv(&self, a: u64) -> u64 {
        assert!(!a.is_multiple_of(self.p), "inverse of zero mod p");
        self.powm(a, self.p - 2)
    }

    /// Reduce an integer polynomial mod p.
    pub fn reduce(&self, c: &[BigInt]) -> Fp {
        let pb = BigInt::from(self.p);
        let mut v: Fp = c
            .iter()
            .map(|x| {
                let r = x % &pb;
                let r = if r < BigInt::from(0) { r + &pb } else { r };
                r.to_u64().unwrap()
            })
            .collect();
        trim(&mut v);
        v
    }

    pub fn add(&self, a: &[u64], b: &[u64]) -> Fp {
        let n = a.len().max(b.len());
        let mut v: Fp = (0..n)
            .map(|i| (a.get(i).copied().unwrap_or(0) + b.get(i).copied().unwrap_or(0)) % self.p)
            .collect();
        trim(&mut v);
        v
    }

    pub fn sub(&self, a: &[u64], b: &[u64]) -> Fp {
        let n = a.len().max(b.len());
        let mut v: Fp = (0..n)
            .map(|i| {
                (a.get(i).copied().unwrap_or(0) + self.p - b.get(i).copied().unwrap_or(0)) % self.p
            })
            .collect();
        trim(&mut v);
        v
    }

    pub fn mul(&self, a: &[u64], b: &[u64]) -> Fp {
        if a.is_empty() || b.is_empty() {
            return Vec::new();
        }
        let mut v = vec![0u64; a.len() + b.len() - 1];
        for (i, &x) in a.iter().enumerate() {
            if x == 0 {
                continue;
            }
            for (j, &y) in b.iter().enumerate() {
                v[i + j] = (v[i + j] + x * y) % self.p;
            }
        }
        trim(&mut v);
        v
    }

    pub fn scale(&self, a: &[u64], k: u64) -> Fp {
        let mut v: Fp = a.iter().map(|&x| self.mulm(x, k % self.p)).collect();
        trim(&mut v);
        v
    }

    /// Euclidean division over the field. Panics if `b` is zero.
    pub fn divrem(&self, a: &[u64], b: &[u64]) -> (Fp, Fp) {
        let db = b
            .len()
            .checked_sub(1)
            .expect("division by zero polynomial mod p");
        if a.len() < b.len() {
            return (Vec::new(), a.to_vec());
        }
        let inv = self.inv(b[db]);
        let mut r = a.to_vec();
        let mut q = vec![0u64; a.len() - db];
        for i in (0..q.len()).rev() {
            let t = self.mulm(r[i + db], inv);
            if t == 0 {
                continue;
            }
            for (j, &bj) in b.iter().enumerate() {
                r[i + j] = (r[i + j] + self.p - self.mulm(t, bj)) % self.p;
            }
            q[i] = t;
        }
        r.truncate(db);
        trim(&mut r);
        trim(&mut q);
        (q, r)
    }

    pub fn rem(&self, a: &[u64], b: &[u64]) -> Fp {
        self.divrem(a, b).1
    }

    pub fn monic(&self, a: &[u64]) -> Fp {
        match a.last() {
            None => Vec::new(),
            Some(&l) => self.scale(a, self.inv(l)),
        }
    }

    /// Monic gcd (Euclid).
    pub fn gcd(&self, a: &[u64], b: &[u64]) -> Fp {
        let (mut a, mut b) = (a.to_vec(), b.to_vec());
        while !b.is_empty() {
            let r = self.rem(&a, &b);
            a = b;
            b = r;
        }
        self.monic(&a)
    }

    /// Extended Euclid: `(g, s, t)` with `s·a + t·b = g` monic, `deg s < deg b − deg g`,
    /// `deg t < deg a − deg g` (for nonconstant inputs).
    pub fn xgcd(&self, a: &[u64], b: &[u64]) -> (Fp, Fp, Fp) {
        let (mut r0, mut r1) = (a.to_vec(), b.to_vec());
        let (mut s0, mut s1): (Fp, Fp) = (vec![1], Vec::new());
        let (mut t0, mut t1): (Fp, Fp) = (Vec::new(), vec![1]);
        while !r1.is_empty() {
            let (q, r) = self.divrem(&r0, &r1);
            r0 = std::mem::replace(&mut r1, r);
            let s2 = self.sub(&s0, &self.mul(&q, &s1));
            s0 = std::mem::replace(&mut s1, s2);
            let t2 = self.sub(&t0, &self.mul(&q, &t1));
            t0 = std::mem::replace(&mut t1, t2);
        }
        let l = self.inv(*r0.last().expect("xgcd(0, 0)"));
        (self.scale(&r0, l), self.scale(&s0, l), self.scale(&t0, l))
    }

    pub fn derivative(&self, a: &[u64]) -> Fp {
        let mut v: Fp = a
            .iter()
            .enumerate()
            .skip(1)
            .map(|(i, &c)| self.mulm(c, i as u64 % self.p))
            .collect();
        trim(&mut v);
        v
    }

    /// `base^e mod m` by square-and-multiply.
    pub fn powmod(&self, base: &[u64], e: &BigUint, m: &[u64]) -> Fp {
        let mut r: Fp = self.rem(&[1], m);
        let b = self.rem(base, m);
        for i in (0..e.bits()).rev() {
            r = self.rem(&self.mul(&r, &r), m);
            if e.bit(i) {
                r = self.rem(&self.mul(&r, &b), m);
            }
        }
        r
    }

    /// Distinct-degree factorisation of a monic square-free `f`: pairs `(g_d, d)` where `g_d` is
    /// the product of all irreducible factors of degree `d` (von zur Gathen–Gerhard, Modern
    /// Computer Algebra, Algorithm 14.3).
    pub fn ddf(&self, f: &[u64]) -> Vec<(Fp, usize)> {
        let mut out = Vec::new();
        let mut f = f.to_vec();
        let x: Fp = vec![0, 1];
        let mut h = self.rem(&x, &f);
        let pe = BigUint::from(self.p);
        let mut d = 1;
        while f.len() > 2 * d {
            // f.len() − 1 = deg f ≥ 2d
            h = self.powmod(&h, &pe, &f);
            let g = self.gcd(&f, &self.sub(&h, &x));
            if g.len() > 1 {
                f = self.divrem(&f, &g).0;
                h = self.rem(&h, &f);
                out.push((g, d));
            }
            d += 1;
        }
        if f.len() > 1 {
            let d = f.len() - 1;
            out.push((f, d));
        }
        out
    }

    /// Split a monic product of distinct irreducibles of degree `d` (odd `p`, Cantor–Zassenhaus
    /// equal-degree factorisation, MCA Algorithm 14.8 with random splitting polynomials).
    pub fn edf(&self, g: &[u64], d: usize, rng: &mut SplitMix64) -> Vec<Fp> {
        let n = g.len() - 1;
        if n == d {
            return vec![g.to_vec()];
        }
        let e: BigUint = (BigUint::from(self.p).pow(d as u32) - BigUint::one()) >> 1;
        loop {
            let mut a: Fp = (0..n).map(|_| rng.below(self.p)).collect();
            trim(&mut a);
            if a.len() < 2 {
                continue;
            }
            let b = self.sub(&self.powmod(&a, &e, g), &[1]);
            let h = self.gcd(g, &b);
            if h.len() > 1 && h.len() < g.len() {
                let rest = self.divrem(g, &h).0;
                let mut out = self.edf(&h, d, rng);
                out.extend(self.edf(&self.monic(&rest), d, rng));
                return out;
            }
        }
    }

    /// Monic irreducible factors of a monic square-free `f` of positive degree.
    pub fn factor_squarefree(&self, f: &[u64], rng: &mut SplitMix64) -> Vec<Fp> {
        let mut out = Vec::new();
        for (g, d) in self.ddf(f) {
            out.extend(self.edf(&g, d, rng));
        }
        out
    }
}

pub fn trim(v: &mut Fp) {
    while v.last() == Some(&0) {
        v.pop();
    }
}
