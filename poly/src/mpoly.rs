//! Sparse multivariate polynomials over `Z`.
//!
//! Variables are indices `0, 1, 2, …`; the index order is the fixed variable order (for CAD and
//! NLSAT the main variable of a polynomial is its highest-index variable, see
//! [`MPoly::main_var`]). A monomial stores only the variables with a nonzero exponent, so a term
//! in `x_10000` is as small as one in `x_0`, and `Eq`/`Hash` are polynomial equality. Terms are
//! kept in a `BTreeMap` under the lexicographic order of exponent vectors (variable 0 most
//! significant), which is a monomial order, so the last term is the leading term for exact
//! division.
//!
//! There is no multivariate factorisation: projection bases are built from square-free parts
//! and gcds.

use crate::ring;
use crate::upoly::UPoly;
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::cmp::Ordering;
use std::collections::btree_map::Entry;
use std::collections::BTreeMap;
use std::fmt;
use std::ops::{Add, Mul, Neg, Sub};

/// A power product `Π x_v^e`: the pairs `(v, e)` with `e > 0`, by increasing `v`.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct Monomial(Vec<(u32, u32)>);

impl Monomial {
    /// From a dense exponent vector: `dense[v]` is the exponent of `x_v`.
    pub fn from_dense(dense: &[u32]) -> Monomial {
        Monomial(
            dense
                .iter()
                .enumerate()
                .filter(|(_, &e)| e > 0)
                .map(|(v, &e)| (v as u32, e))
                .collect(),
        )
    }

    /// The dense exponent vector, up to the highest variable.
    pub fn to_dense(&self) -> Vec<u32> {
        (0..self.num_vars()).map(|v| self.exp(v)).collect()
    }

    /// The exponent of `x_v`.
    pub fn exp(&self, v: usize) -> u32 {
        match self.0.binary_search_by_key(&(v as u32), |&(w, _)| w) {
            Ok(i) => self.0[i].1,
            Err(_) => 0,
        }
    }

    /// The pairs `(v, e)` with `e > 0`, by increasing `v`.
    pub fn iter(&self) -> impl Iterator<Item = (usize, u32)> + '_ {
        self.0.iter().map(|&(v, e)| (v as usize, e))
    }

    /// Whether this is the empty product `1`.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// One more than the highest variable (0 for `1`).
    pub fn num_vars(&self) -> usize {
        self.0.last().map_or(0, |&(v, _)| v as usize + 1)
    }

    pub fn degree(&self) -> usize {
        self.0.iter().map(|&(_, e)| e as usize).sum()
    }

    /// `self` with the exponent of `x_v` replaced by `e`.
    fn with_exp(&self, v: usize, e: u32) -> Monomial {
        let mut m = self.0.clone();
        match m.binary_search_by_key(&(v as u32), |&(w, _)| w) {
            Ok(i) if e == 0 => {
                m.remove(i);
            }
            Ok(i) => m[i].1 = e,
            Err(_) if e == 0 => {}
            Err(i) => m.insert(i, (v as u32, e)),
        }
        Monomial(m)
    }

    fn mul(&self, o: &Monomial) -> Monomial {
        let (a, b) = (&self.0, &o.0);
        let mut out = Vec::with_capacity(a.len() + b.len());
        let (mut i, mut j) = (0, 0);
        while i < a.len() || j < b.len() {
            if j == b.len() || (i < a.len() && a[i].0 < b[j].0) {
                out.push(a[i]);
                i += 1;
            } else if i == a.len() || b[j].0 < a[i].0 {
                out.push(b[j]);
                j += 1;
            } else {
                out.push((a[i].0, a[i].1 + b[j].1));
                i += 1;
                j += 1;
            }
        }
        Monomial(out)
    }

    /// `self / o`, if `o` divides `self`.
    fn div(&self, o: &Monomial) -> Option<Monomial> {
        let mut out = Vec::with_capacity(self.0.len());
        let mut j = 0;
        for &(v, e) in &self.0 {
            match o.0.get(j) {
                Some(&(w, _)) if w < v => return None,
                Some(&(w, f)) if w == v => {
                    let d = e.checked_sub(f)?;
                    if d > 0 {
                        out.push((v, d));
                    }
                    j += 1;
                }
                _ => out.push((v, e)),
            }
        }
        (j == o.0.len()).then_some(Monomial(out))
    }
}

/// The lexicographic order of the dense exponent vectors, variable 0 most significant: at the
/// first variable whose exponents differ, the larger exponent wins.
impl Ord for Monomial {
    fn cmp(&self, o: &Monomial) -> Ordering {
        for (&(va, ea), &(vb, eb)) in self.0.iter().zip(&o.0) {
            if va != vb {
                // The one with the lower variable has a positive exponent where the other has 0.
                return vb.cmp(&va);
            }
            if ea != eb {
                return ea.cmp(&eb);
            }
        }
        self.0.len().cmp(&o.0.len())
    }
}

impl PartialOrd for Monomial {
    fn partial_cmp(&self, o: &Monomial) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}

/// A polynomial in `Z[x₀, x₁, …]`.
#[derive(Clone, PartialEq, Eq, Hash, Debug, Default)]
pub struct MPoly {
    terms: BTreeMap<Monomial, BigInt>,
}

impl MPoly {
    pub fn zero() -> MPoly {
        MPoly {
            terms: BTreeMap::new(),
        }
    }

    pub fn constant(c: BigInt) -> MPoly {
        let mut p = MPoly::zero();
        p.add_term(Monomial::default(), c);
        p
    }

    pub fn from_i64(c: i64) -> MPoly {
        MPoly::constant(BigInt::from(c))
    }

    /// The variable `x_i`.
    pub fn var(i: usize) -> MPoly {
        let mut p = MPoly::zero();
        p.add_term(Monomial(vec![(i as u32, 1)]), BigInt::one());
        p
    }

    /// `c · x^m` for the dense exponent vector `m`.
    pub fn monomial(m: Vec<u32>, c: BigInt) -> MPoly {
        let mut p = MPoly::zero();
        p.add_term(Monomial::from_dense(&m), c);
        p
    }

    /// From `(dense exponents, coefficient)` pairs; like terms are combined.
    pub fn from_terms<I: IntoIterator<Item = (Vec<u32>, BigInt)>>(terms: I) -> MPoly {
        let mut p = MPoly::zero();
        for (m, c) in terms {
            p.add_term(Monomial::from_dense(&m), c);
        }
        p
    }

    /// Embed a univariate polynomial as a polynomial in `x_v`.
    pub fn from_upoly(p: &UPoly, v: usize) -> MPoly {
        let mut out = MPoly::zero();
        for (k, c) in p.coeffs().iter().enumerate() {
            out.add_term(Monomial::default().with_exp(v, k as u32), c.clone());
        }
        out
    }

    fn add_term(&mut self, m: Monomial, c: BigInt) {
        if c.is_zero() {
            return;
        }
        match self.terms.entry(m) {
            Entry::Occupied(mut o) => {
                *o.get_mut() += c;
                if o.get().is_zero() {
                    o.remove();
                }
            }
            Entry::Vacant(v) => {
                v.insert(c);
            }
        }
    }

    /// Terms in increasing lexicographic order.
    pub fn terms(&self) -> impl Iterator<Item = (&Monomial, &BigInt)> {
        self.terms.iter()
    }

    pub fn num_terms(&self) -> usize {
        self.terms.len()
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// A constant (including zero).
    pub fn is_constant(&self) -> bool {
        self.terms.keys().all(|m| m.is_empty())
    }

    /// The constant value, if constant.
    pub fn as_constant(&self) -> Option<BigInt> {
        if self.is_zero() {
            return Some(BigInt::zero());
        }
        if self.is_constant() {
            return self.terms.get(&Monomial::default()).cloned();
        }
        None
    }

    /// One more than the highest variable index that occurs (0 for constants).
    pub fn num_vars(&self) -> usize {
        self.terms.keys().map(Monomial::num_vars).max().unwrap_or(0)
    }

    /// Whether `x_v` occurs.
    pub fn has_var(&self, v: usize) -> bool {
        self.terms.keys().any(|m| m.exp(v) > 0)
    }

    /// The variables that occur, ascending.
    pub fn vars(&self) -> Vec<usize> {
        let mut vs: Vec<usize> = self
            .terms
            .keys()
            .flat_map(|m| m.iter().map(|(v, _)| v))
            .collect();
        vs.sort_unstable();
        vs.dedup();
        vs
    }

    /// The highest-index variable that occurs (`None` for constants).
    pub fn main_var(&self) -> Option<usize> {
        self.num_vars().checked_sub(1)
    }

    /// Degree in `x_v` (`None` for the zero polynomial).
    pub fn degree_in(&self, v: usize) -> Option<usize> {
        self.terms.keys().map(|m| m.exp(v) as usize).max()
    }

    /// Total degree (`None` for zero).
    pub fn total_degree(&self) -> Option<usize> {
        self.terms.keys().map(Monomial::degree).max()
    }

    /// Coefficients as polynomials in the other variables: `self = Σ_k c_k · x_v^k`, returned
    /// as `[c_0, …, c_d]` for `d = deg_v`. Empty for zero.
    pub fn coeffs_in(&self, v: usize) -> Vec<MPoly> {
        let Some(d) = self.degree_in(v) else {
            return Vec::new();
        };
        let mut out = vec![MPoly::zero(); d + 1];
        for (m, c) in &self.terms {
            let k = m.exp(v) as usize;
            out[k].add_term(m.with_exp(v, 0), c.clone());
        }
        out
    }

    /// Inverse of [`MPoly::coeffs_in`]: `Σ_k c_k · x_v^k` (the `c_k` must not contain `x_v`).
    pub fn from_coeffs_in(v: usize, coeffs: &[MPoly]) -> MPoly {
        let mut out = MPoly::zero();
        for (k, c) in coeffs.iter().enumerate() {
            for (m, a) in &c.terms {
                debug_assert!(m.exp(v) == 0);
                out.add_term(m.with_exp(v, k as u32), a.clone());
            }
        }
        out
    }

    /// Leading coefficient with respect to `x_v`.
    pub fn lc_in(&self, v: usize) -> MPoly {
        self.coeffs_in(v).pop().unwrap_or_default()
    }

    /// Partial derivative by `x_v`.
    pub fn derivative(&self, v: usize) -> MPoly {
        let mut out = MPoly::zero();
        for (m, c) in &self.terms {
            let e = m.exp(v);
            if e == 0 {
                continue;
            }
            out.add_term(m.with_exp(v, e - 1), c * BigInt::from(e));
        }
        out
    }

    pub fn scale(&self, k: &BigInt) -> MPoly {
        if k.is_zero() {
            return MPoly::zero();
        }
        MPoly {
            terms: self.terms.iter().map(|(m, c)| (m.clone(), c * k)).collect(),
        }
    }

    pub fn pow(&self, k: usize) -> MPoly {
        ring::Ring::pow(self, k)
    }

    /// Content: the nonnegative gcd of the integer coefficients.
    pub fn content(&self) -> BigInt {
        let mut g = BigInt::zero();
        for c in self.terms.values() {
            g = g.gcd(c);
        }
        g
    }

    /// Exact division: `Some(q)` with `self = q · d` if it exists in `Z[x₀, …]` (multivariate
    /// division by leading terms under the lexicographic monomial order, which succeeds iff the
    /// division is exact). Panics if `d` is zero.
    pub fn div_exact(&self, d: &MPoly) -> Option<MPoly> {
        let (dm, dc) = d
            .terms
            .iter()
            .next_back()
            .expect("division by the zero polynomial");
        let mut r = self.clone();
        let mut q = MPoly::zero();
        while let Some((rm, rc)) = r.terms.iter().next_back() {
            let m = rm.div(dm)?;
            let (c, rem) = rc.div_rem(dc);
            if !rem.is_zero() {
                return None;
            }
            let mut t = MPoly::zero();
            t.add_term(m, c);
            r = &r - &(&t * d);
            q = &q + &t;
        }
        Some(q)
    }

    /// Resultant with respect to `x_v` (subresultant PRS over the coefficient ring
    /// `Z[other variables]`, [`ring::resultant`]). The result does not contain `x_v`.
    pub fn resultant(&self, other: &MPoly, v: usize) -> MPoly {
        ring::resultant(&self.coeffs_in(v), &other.coeffs_in(v))
    }

    /// Discriminant with respect to `x_v` ([`ring::discriminant`]); zero if `deg_v ≤ 0`.
    pub fn discriminant(&self, v: usize) -> MPoly {
        ring::discriminant(&self.coeffs_in(v))
    }

    /// The nonzero principal subresultant coefficients of `self` and `other` with respect to
    /// `x_v`, up to sign ([`ring::principal_subresultant_coefficients`]): `(j, psc_j)` for
    /// `j < min(deg_v self, deg_v other)`, every omitted `psc_j` being identically zero.
    pub fn psc(&self, other: &MPoly, v: usize) -> Vec<(usize, MPoly)> {
        ring::principal_subresultant_coefficients(&self.coeffs_in(v), &other.coeffs_in(v))
    }

    /// The coefficient of the lexicographically largest term (zero for zero). Its sign is the
    /// normalisation used by [`MPoly::normalize`] and [`MPoly::gcd`].
    pub fn leading_coeff(&self) -> BigInt {
        self.terms
            .iter()
            .next_back()
            .map(|(_, c)| c.clone())
            .unwrap_or_default()
    }

    /// `±self` with a positive [`MPoly::leading_coeff`] (zero stays zero).
    pub fn normalize_sign(&self) -> MPoly {
        if self.leading_coeff().is_negative() {
            -self
        } else {
            self.clone()
        }
    }

    /// `self / ±content`: integer content 1 and a positive [`MPoly::leading_coeff`] (zero stays
    /// zero). The result is a positive or negative rational multiple of `self`; see
    /// [`MPoly::primitive_sign`].
    pub fn primitive(&self) -> MPoly {
        self.primitive_sign().1
    }

    /// `(s, p)` with `self = s · |content| · p`, `s = ±1` (`0` for zero) and `p` primitive with a
    /// positive leading coefficient.
    pub fn primitive_sign(&self) -> (i8, MPoly) {
        if self.is_zero() {
            return (0, MPoly::zero());
        }
        let mut g = self.content();
        let s = if self.leading_coeff().is_negative() {
            g = -g;
            -1
        } else {
            1
        };
        let p = MPoly {
            terms: self
                .terms
                .iter()
                .map(|(m, c)| (m.clone(), c / &g))
                .collect(),
        };
        (s, p)
    }

    /// Greatest common divisor in `Z[x₀, x₁, …]`, normalised to a positive
    /// [`MPoly::leading_coeff`] (`gcd(0, 0) = 0`). Recursive in the highest variable `v` that
    /// occurs: `gcd(a, b) = gcd(cont_v a, cont_v b) · pp_v(last nonzero member of the
    /// subresultant PRS of pp_v a and pp_v b)`, which is Gauss's lemma for the UFD
    /// `Z[x₀, …, x_{v−1}][x_v]` (G. E. Collins, "Subresultants and reduced polynomial remainder
    /// sequences", J. ACM 14, 1967). Contents are gcds over fewer variables, so the recursion ends
    /// at integer gcds.
    pub fn gcd(&self, other: &MPoly) -> MPoly {
        if self.is_zero() {
            return other.normalize_sign();
        }
        if other.is_zero() {
            return self.normalize_sign();
        }
        let v = match (self.main_var(), other.main_var()) {
            (None, None) => {
                return MPoly::constant(self.leading_coeff().gcd(&other.leading_coeff()).abs())
            }
            (a, b) => a.max(b).unwrap(),
        };
        let (ca, pa) = self.content_primitive_in(v);
        let (cb, pb) = other.content_primitive_in(v);
        let c = ca.gcd(&cb);
        let (da, db) = (pa.degree_in(v).unwrap(), pb.degree_in(v).unwrap());
        if da == 0 || db == 0 {
            return c;
        }
        if self == other {
            return (&c * &pa).normalize_sign();
        }
        let (a, b) = if da >= db { (pa, pb) } else { (pb, pa) };
        let (prs, _) = ring::subresultant_prs(&a.coeffs_in(v), &b.coeffs_in(v));
        let last = MPoly::from_coeffs_in(v, prs.last().unwrap());
        let g = if last.degree_in(v) == Some(0) {
            MPoly::from_i64(1)
        } else {
            last.content_primitive_in(v).1
        };
        (&c * &g).normalize_sign()
    }

    /// Whether `self` and `other` have no common factor of positive degree in `x_v`, i.e.
    /// `deg_v gcd(self, other) = 0` — the same answer as `self.gcd(other).degree_in(v) == Some(0)`,
    /// usually without computing the gcd.
    ///
    /// Specialisation test: substitute integers for every other variable at a point where both
    /// leading coefficients in `x_v` stay nonzero. A common factor `h` with `deg_v h > 0` divides
    /// both leading coefficients through its own, so `h` keeps its degree at that point and still
    /// divides both specialisations; hence a univariate gcd of degree 0 proves coprimality. When
    /// a few points cannot prove it, the exact gcd decides.
    pub fn coprime_in(&self, other: &MPoly, v: usize) -> bool {
        let (da, db) = (
            self.degree_in(v).unwrap_or(0),
            other.degree_in(v).unwrap_or(0),
        );
        if da == 0 || db == 0 {
            return true;
        }
        let n = self.num_vars().max(other.num_vars());
        for attempt in 0..3i64 {
            let point: Vec<BigInt> = (0..n)
                .map(|w| BigInt::from((w as i64 * 7 + attempt * 13 + 2) % 23 - 11))
                .collect();
            let (ua, ub) = (self.specialise(v, &point), other.specialise(v, &point));
            // Both leading coefficients must survive, or the test proves nothing.
            if ua.degree() != Some(da) || ub.degree() != Some(db) {
                continue;
            }
            if ua.gcd(&ub).degree() == Some(0) {
                return true;
            }
        }
        self.gcd(other).degree_in(v).unwrap_or(0) == 0
    }

    /// The univariate polynomial in `x_v` left after substituting `point[w]` for every other
    /// variable `x_w`, in one pass over the terms.
    fn specialise(&self, v: usize, point: &[BigInt]) -> UPoly {
        let mut coeffs = vec![BigInt::zero(); self.degree_in(v).map_or(0, |d| d + 1)];
        for (m, c) in &self.terms {
            let mut t = c.clone();
            let mut k = 0;
            for (w, e) in m.iter() {
                if w == v {
                    k = e as usize;
                } else {
                    t *= num_traits::pow(point[w].clone(), e as usize);
                }
            }
            coeffs[k] += t;
        }
        UPoly::new(coeffs)
    }

    /// The content with respect to `x_v` — the gcd of the coefficients of `self` as a polynomial
    /// in `x_v`, a polynomial in the other variables — normalised as by [`MPoly::gcd`], and the
    /// primitive part `self / content`. Zero gives `(0, 0)`. The primitive part is `self` divided
    /// by a positive-leading polynomial, so `self = content · primitive` exactly.
    pub fn content_primitive_in(&self, v: usize) -> (MPoly, MPoly) {
        if self.is_zero() {
            return (MPoly::zero(), MPoly::zero());
        }
        let coeffs = self.coeffs_in(v);
        let mut g = MPoly::zero();
        for c in coeffs.iter().rev() {
            if c.is_zero() {
                continue;
            }
            g = g.gcd(c);
            if g.is_constant() && g.leading_coeff().is_one() {
                break;
            }
        }
        let p = self
            .div_exact(&g)
            .expect("the content divides every coefficient");
        (g, p)
    }

    /// The square-free part with respect to `x_v` of a polynomial primitive in `x_v`:
    /// `self / gcd(self, ∂self/∂x_v)`, normalised. It has the same zero set as `self` and no
    /// repeated factor involving `x_v`. A polynomial of degree 0 in `x_v` gives `1`.
    pub fn square_free_part_in(&self, v: usize) -> MPoly {
        if self.degree_in(v).unwrap_or(0) == 0 {
            return MPoly::from_i64(1);
        }
        let d = self.derivative(v);
        let g = self.gcd(&d);
        self.div_exact(&g)
            .expect("the gcd divides the polynomial")
            .normalize_sign()
    }

    /// Rename variables: `x_i` becomes `x_{map[i]}` (every occurring variable must be mapped).
    pub fn map_vars(&self, map: &[usize]) -> MPoly {
        let mut out = MPoly::zero();
        for (m, c) in &self.terms {
            let mut nm: Vec<(u32, u32)> = m.iter().map(|(i, e)| (map[i] as u32, e)).collect();
            nm.sort_unstable();
            // Merge variables mapped to the same one.
            nm.dedup_by(|b, a| {
                if a.0 == b.0 {
                    a.1 += b.1;
                    true
                } else {
                    false
                }
            });
            out.add_term(Monomial(nm), c.clone());
        }
        out
    }

    /// Substitute polynomials for variables: `x_i` becomes `subs[i]` (every occurring variable
    /// must have an entry). Term by term, with cached powers.
    pub fn compose(&self, subs: &[MPoly]) -> MPoly {
        let mut powers: Vec<Vec<MPoly>> = vec![vec![MPoly::from_i64(1)]; subs.len()];
        let mut out = MPoly::zero();
        for (m, c) in &self.terms {
            let mut t = MPoly::constant(c.clone());
            for (i, e) in m.iter() {
                while powers[i].len() <= e as usize {
                    let next = &powers[i][powers[i].len() - 1] * &subs[i];
                    powers[i].push(next);
                }
                t = &t * &powers[i][e as usize];
            }
            out = &out + &t;
        }
        out
    }

    /// Substitute the rational `r = n/d` (`d > 0`) for `x_v` and clear the denominator:
    /// returns `d^D · self(x_v = n/d)` with `D = deg_v(self)`, a positive multiple of the
    /// substitution, so it has the same zero set and signs.
    pub fn eval_var(&self, v: usize, r: &BigRational) -> MPoly {
        let coeffs = self.coeffs_in(v);
        let Some(dd) = coeffs.len().checked_sub(1) else {
            return MPoly::zero();
        };
        let (n, d) = (r.numer(), r.denom());
        let mut out = MPoly::zero();
        let mut npow = BigInt::one();
        for (k, c) in coeffs.iter().enumerate() {
            let w = &npow * num_traits::pow(d.clone(), dd - k);
            out = &out + &c.scale(&w);
            npow *= n;
        }
        out
    }

    /// Substitute the integer `a` for `x_v` exactly.
    pub fn eval_var_int(&self, v: usize, a: &BigInt) -> MPoly {
        self.eval_var(v, &BigRational::from_integer(a.clone()))
    }

    /// Exact value at a rational point for all variables (`point[i]` for `x_i`; missing
    /// variables must not occur).
    pub fn eval_rational(&self, point: &[BigRational]) -> BigRational {
        let mut acc = BigRational::zero();
        for (m, c) in &self.terms {
            let mut t = BigRational::from_integer(c.clone());
            for (i, e) in m.iter() {
                t *= num_traits::pow(point[i].clone(), e as usize);
            }
            acc += t;
        }
        acc
    }

    /// The univariate polynomial in `x_v`, if no other variable occurs.
    pub fn to_upoly(&self, v: usize) -> Option<UPoly> {
        let coeffs = self.coeffs_in(v);
        let mut c = Vec::with_capacity(coeffs.len());
        for k in coeffs {
            c.push(k.as_constant()?);
        }
        Some(UPoly::new(c))
    }

    /// Format with variable names `names[i]` (falls back to `x{i}`).
    pub fn display_with(&self, names: &[&str]) -> String {
        if self.is_zero() {
            return "0".into();
        }
        let mut s = String::new();
        for (m, c) in self.terms.iter().rev() {
            let neg = c.is_negative();
            if s.is_empty() {
                if neg {
                    s.push('-');
                }
            } else {
                s.push_str(if neg { " - " } else { " + " });
            }
            let a = c.abs();
            let vars: Vec<String> = m
                .iter()
                .map(|(i, e)| {
                    let n = names
                        .get(i)
                        .map(|s| s.to_string())
                        .unwrap_or(format!("x{i}"));
                    if e == 1 {
                        n
                    } else {
                        format!("{n}^{e}")
                    }
                })
                .collect();
            if vars.is_empty() {
                s.push_str(&a.to_string());
            } else {
                if !a.is_one() {
                    s.push_str(&format!("{a}*"));
                }
                s.push_str(&vars.join("*"));
            }
        }
        s
    }
}

impl fmt::Display for MPoly {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.display_with(&[]))
    }
}

impl Add for &MPoly {
    type Output = MPoly;
    fn add(self, o: &MPoly) -> MPoly {
        let mut out = self.clone();
        for (m, c) in &o.terms {
            out.add_term(m.clone(), c.clone());
        }
        out
    }
}

impl Sub for &MPoly {
    type Output = MPoly;
    fn sub(self, o: &MPoly) -> MPoly {
        let mut out = self.clone();
        for (m, c) in &o.terms {
            out.add_term(m.clone(), -c);
        }
        out
    }
}

impl Neg for &MPoly {
    type Output = MPoly;
    fn neg(self) -> MPoly {
        MPoly {
            terms: self.terms.iter().map(|(m, c)| (m.clone(), -c)).collect(),
        }
    }
}

impl Mul for &MPoly {
    type Output = MPoly;
    fn mul(self, o: &MPoly) -> MPoly {
        let mut acc: BTreeMap<Monomial, BigInt> = BTreeMap::new();
        for (ma, ca) in &self.terms {
            for (mb, cb) in &o.terms {
                *acc.entry(ma.mul(mb)).or_default() += ca * cb;
            }
        }
        acc.retain(|_, c| !c.is_zero());
        MPoly { terms: acc }
    }
}

impl ring::Ring for MPoly {
    fn zero() -> Self {
        MPoly::zero()
    }
    fn one() -> Self {
        MPoly::from_i64(1)
    }
    fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }
    fn add(&self, o: &Self) -> Self {
        self + o
    }
    fn sub(&self, o: &Self) -> Self {
        self - o
    }
    fn mul(&self, o: &Self) -> Self {
        self * o
    }
    fn neg(&self) -> Self {
        -self
    }
    fn exact_div(&self, o: &Self) -> Self {
        self.div_exact(o).expect("inexact multivariate division")
    }
    fn from_i64(n: i64) -> Self {
        MPoly::from_i64(n)
    }
}

#[cfg(test)]
mod monomial_tests {
    use super::Monomial;
    use crate::rng::SplitMix64;

    /// The lexicographic order of dense exponent vectors, trailing zeros ignored.
    fn dense_cmp(a: &[u32], b: &[u32]) -> std::cmp::Ordering {
        let n = a.len().max(b.len());
        let at = |x: &[u32], i: usize| x.get(i).copied().unwrap_or(0);
        (0..n)
            .map(|i| at(a, i).cmp(&at(b, i)))
            .find(|o| o.is_ne())
            .unwrap_or(std::cmp::Ordering::Equal)
    }

    #[test]
    fn sparse_order_is_dense_lex_order_and_arithmetic_agrees() {
        let mut rng = SplitMix64::new(31);
        let dense = |rng: &mut SplitMix64| -> Vec<u32> {
            let n = rng.below(6) as usize;
            (0..n).map(|_| rng.below(3) as u32).collect()
        };
        for _ in 0..20000 {
            let (a, b) = (dense(&mut rng), dense(&mut rng));
            let (ma, mb) = (Monomial::from_dense(&a), Monomial::from_dense(&b));
            assert_eq!(ma.cmp(&mb), dense_cmp(&a, &b), "{a:?} {b:?}");
            let n = a.len().max(b.len());
            let prod: Vec<u32> = (0..n)
                .map(|i| a.get(i).unwrap_or(&0) + b.get(i).unwrap_or(&0))
                .collect();
            assert_eq!(ma.mul(&mb), Monomial::from_dense(&prod));
            assert_eq!(ma.mul(&mb).div(&mb), Some(ma.clone()));
            let divides = (0..n).all(|i| b.get(i).unwrap_or(&0) <= a.get(i).unwrap_or(&0));
            assert_eq!(ma.div(&mb).is_some(), divides, "{a:?} / {b:?}");
            assert_eq!(Monomial::from_dense(&ma.to_dense()), ma);
        }
    }
}
