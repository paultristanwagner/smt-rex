//! A complete decision procedure for conjunctions of polynomial sign conditions: cylindrical
//! algebraic decomposition (G. E. Collins, *Quantifier elimination for real closed fields by
//! cylindrical algebraic decomposition*, 1975) with Hong's projection operator (H. Hong, *An
//! improvement of the projection operator in cylindrical algebraic decomposition*, ISSAC 1990),
//! over a square-free, pairwise coprime basis, with exact real algebraic sample points.
//!
//! # Projection
//!
//! Variables are ordered `x₀ < x₁ < … < x_{n−1}`; level `k` holds the polynomials whose main
//! (highest) variable is `x_k`. Every polynomial entering level `k` is split into its content
//! with respect to `x_k` (a polynomial in lower variables, passed down to its own level) and its
//! primitive part, whose square-free part joins the level. The level's polynomials are then
//! refined into a *basis*: square-free, primitive, pairwise coprime polynomials of positive
//! degree in `x_k` such that every input polynomial's square-free part is a product of basis
//! elements ([`coprime_basis`], gcd-based factor refinement). On a connected set a product of
//! sign-invariant polynomials is sign-invariant, and a polynomial whose square-free part is such
//! a product either vanishes on the whole set or nowhere, so it is sign-invariant too. Hence
//! sign-invariance of the basis implies sign-invariance of every polynomial that was added.
//!
//! The projection of a level-`k` basis `A` is Hong's
//!
//! `PROJ_H(A) = ⋃_{F ∈ A} ⋃_{F* ∈ RED(F)} ({ldcf F*} ∪ PSC(F*, ∂F*/∂x_k))
//!            ∪ ⋃_{F < G ∈ A} ⋃_{F* ∈ RED(F)} PSC(F*, G)`
//!
//! where `RED(F)` are the reducta of `F` (`F` with leading terms successively removed) and
//! `PSC(F, G)` is the set of all principal subresultant coefficients `psc_j(F, G)`,
//! `0 ≤ j < min(deg F, deg G)`. Collins' and Hong's theorem: if every element of `PROJ_H(A)` is
//! sign-invariant on a connected set `S ⊆ R^k`, then the elements of `A` are delineable on `S`
//! and their sections are either disjoint or identical — for *any* finite set `A`, with no
//! well-orientedness condition and no restriction on nullification (a polynomial whose
//! coefficients all vanish on `S` is identically zero on the cylinder over `S`, hence
//! sign-invariant). Reducta are cut off after the first one whose leading coefficient is a
//! nonzero constant: its degree is then fixed, so the remaining reducta never become the
//! effective polynomial (the usual truncation, e.g. in QEPCAD).
//!
//! Identically-zero elements of `PSC` are trivially sign-invariant, so leaving them out is exact,
//! not an approximation. The degenerate cases are handled by the nonzero higher subresultant
//! coefficients and the reducta, which McCallum's operator omits. As a check of the basis,
//! `psc₀(F, ∂F)` (the discriminant, up to `ldcf F`) and `psc₀(F, G)` (the resultant) of basis
//! elements are asserted nonzero: they vanish identically only for a non-square-free `F` or
//! non-coprime `F, G`.
//!
//! # Lifting
//!
//! Sample points are built level by level. Over a sample `α ∈ R^k` the real roots of every
//! level-`k` basis element are isolated exactly ([`roots_at`]: resultants against the coordinates'
//! minimal polynomials for candidates, then a subresultant root count), merged and sorted; the
//! cells of the stack are the sections (the roots, as real algebraic numbers with irreducible
//! minimal polynomials) and the sectors between them (rational sample points). Since the basis is
//! sign-invariant on every cell, the sign of an input polynomial on a cell is its sign at the
//! cell's sample point: zero iff one of the basis elements dividing it vanishes there (known from
//! the root isolation), otherwise found by interval refinement ([`sign_at_nonzero`]). A constraint
//! whose main variable is `x_k` is checked as soon as level `k` is sampled, so a violated
//! constraint prunes the whole cylinder above the cell.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use rustc_hash::FxHashSet;
use smtrex_poly::point::{roots_at, sign_at, sign_at_nonzero, Fiber};
use smtrex_poly::stats as st;
use smtrex_poly::{MPoly, RealAlgebraic};
use std::cmp::Ordering;

/// A set of allowed signs: bit 0 negative, bit 1 zero, bit 2 positive.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SignSet(pub u8);

impl SignSet {
    pub const NEG: SignSet = SignSet(1);
    pub const ZERO: SignSet = SignSet(2);
    pub const POS: SignSet = SignSet(4);
    pub const NONZERO: SignSet = SignSet(5);
    pub const NONNEG: SignSet = SignSet(6);
    pub const NONPOS: SignSet = SignSet(3);
    pub const ANY: SignSet = SignSet(7);

    pub fn allows(self, s: i8) -> bool {
        let bit = match s.cmp(&0) {
            Ordering::Less => 1,
            Ordering::Equal => 2,
            Ordering::Greater => 4,
        };
        self.0 & bit != 0
    }

    pub fn intersect(self, o: SignSet) -> SignSet {
        SignSet(self.0 & o.0)
    }

    pub fn is_empty(self) -> bool {
        self.0 == 0
    }
}

/// A sign condition `poly ∈ allowed`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Constraint {
    pub poly: MPoly,
    pub allowed: SignSet,
}

/// Decide the conjunction of `constraints` over the reals. The polynomials may use any
/// variables; returns a satisfying assignment indexed by variable (`num_vars` entries,
/// variables that occur in no constraint get 0) or `None` if the conjunction is unsatisfiable.
pub fn solve(constraints: &[Constraint], num_vars: usize) -> Option<Vec<RealAlgebraic>> {
    // Constant constraints decide themselves.
    let mut rest = Vec::new();
    for c in constraints {
        match c.poly.as_constant() {
            Some(k) => {
                let s = if k.is_positive() {
                    1
                } else if k.is_negative() {
                    -1
                } else {
                    0
                };
                if !c.allowed.allows(s) {
                    return None;
                }
            }
            None => rest.push(c.clone()),
        }
    }
    let mut used: Vec<usize> = rest.iter().flat_map(|c| c.poly.vars()).collect();
    used.sort_unstable();
    used.dedup();
    let order = variable_order(&rest, &used);
    // level k <-> original variable order[k]
    let mut to_level = vec![usize::MAX; num_vars.max(used.last().map_or(0, |v| v + 1))];
    for (k, &v) in order.iter().enumerate() {
        to_level[v] = k;
    }
    let local: Vec<Constraint> = rest
        .iter()
        .map(|c| Constraint {
            poly: c.poly.map_vars(&to_level),
            allowed: c.allowed,
        })
        .collect();
    let n = order.len();
    let mut model = vec![RealAlgebraic::from_int(0); num_vars.max(to_level.len())];
    if n == 0 {
        model.truncate(num_vars);
        return Some(model);
    }
    let bases = {
        let _o = st::outer(st::Outer::CadProject);
        project(local.iter().map(|c| c.poly.clone()).collect(), n)
    };
    let mut search = Search::new(&bases, &local);
    let found = {
        let _o = st::outer(st::Outer::CadLift);
        search.lift(0)
    };
    st::add(st::Counter::CadCells, search.cells as u64);
    if !found {
        return None;
    }
    for (k, &v) in order.iter().enumerate() {
        model[v] = search.point[k].clone();
    }
    model.truncate(num_vars);
    Some(model)
}

/// Brown's heuristic, reversed for the lifting order: the variable projected first (the
/// highest level) has the lowest degree, then the lowest total degree of the terms containing
/// it, then the fewest such terms. Returns the variables from level 0 up.
pub(crate) fn variable_order(cs: &[Constraint], used: &[usize]) -> Vec<usize> {
    let key = |v: usize| {
        let mut deg = 0usize;
        let mut tdeg = 0usize;
        let mut terms = 0usize;
        for c in cs {
            for (m, _) in c.poly.terms() {
                let e = m.exp(v) as usize;
                if e > 0 {
                    deg = deg.max(e);
                    tdeg = tdeg.max(m.degree());
                    terms += 1;
                }
            }
        }
        (deg, tdeg, terms)
    };
    let mut vs: Vec<(usize, (usize, usize, usize))> = used.iter().map(|&v| (v, key(v))).collect();
    // Level 0 gets the largest key, the top level the smallest.
    vs.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
    vs.into_iter().map(|(v, _)| v).collect()
}

/// Add `p` to the projection set: its content with respect to its main variable goes down
/// (recursively), its square-free primitive part joins its level.
fn add_poly(pending: &mut [FxHashSet<MPoly>], p: &MPoly) {
    if p.is_constant() {
        return;
    }
    let v = p.main_var().unwrap();
    let (c, pp) = p.content_primitive_in(v);
    pending[v].insert(pp.square_free_part_in(v).primitive());
    add_poly(pending, &c);
}

/// The projection: the basis of every level, level 0 first. Each basis element at level `k` has
/// main variable `x_k`.
pub fn project(polys: Vec<MPoly>, n: usize) -> Vec<Vec<MPoly>> {
    let mut pending: Vec<FxHashSet<MPoly>> = vec![FxHashSet::default(); n];
    for p in &polys {
        add_poly(&mut pending, p);
    }
    let mut bases = vec![Vec::new(); n];
    for k in (0..n).rev() {
        let mut level: Vec<MPoly> = pending[k].drain().collect();
        level.sort_by(poly_order);
        let basis = coprime_basis(level, k);
        if k > 0 {
            for q in hong_projection(&basis, k) {
                add_poly(&mut pending, &q);
            }
        }
        bases[k] = basis;
    }
    bases
}

/// A deterministic order on polynomials: by degree in the main variable, then number of terms,
/// then the terms.
pub(crate) fn poly_order(a: &MPoly, b: &MPoly) -> Ordering {
    let ka = (a.total_degree(), a.num_terms());
    let kb = (b.total_degree(), b.num_terms());
    ka.cmp(&kb).then_with(|| a.terms().cmp(b.terms()))
}

/// Factor refinement: square-free primitive polynomials of positive degree in `x_v` into a
/// pairwise coprime set of square-free primitive polynomials (positive degree in `x_v`, positive
/// leading coefficient) such that every input is a product of elements of the set. Splitting
/// keeps this invariant: `f` and a basis element `b` with `g = gcd(f, b)` of positive degree
/// become `g`, `b/g` and `f/g`, all square-free, with `g` coprime to `b/g` and to `f/g` because
/// `b` and `f` are square-free.
pub fn coprime_basis(polys: Vec<MPoly>, v: usize) -> Vec<MPoly> {
    let _k = st::kernel(st::Kernel::Gcd);
    let mut basis: Vec<MPoly> = Vec::new();
    let mut todo: Vec<MPoly> = polys;
    todo.reverse();
    while let Some(f) = todo.pop() {
        let mut f = f;
        if f.degree_in(v).unwrap_or(0) == 0 {
            continue;
        }
        let mut i = 0;
        while i < basis.len() {
            if f.coprime_in(&basis[i], v) {
                i += 1;
                continue;
            }
            let g = f.gcd(&basis[i]);
            let b = basis.swap_remove(i);
            let bg = b.div_exact(&g).expect("gcd divides the basis element");
            f = f.div_exact(&g).expect("gcd divides f");
            if bg.degree_in(v).unwrap_or(0) > 0 {
                todo.push(bg.primitive());
            }
            todo.push(g.primitive());
            if f.degree_in(v).unwrap_or(0) == 0 {
                break;
            }
            // f is coprime to basis[..i] already (it only lost factors); continue at i.
        }
        if f.degree_in(v).unwrap_or(0) > 0 {
            basis.push(f.primitive());
        }
    }
    basis.sort_by(poly_order);
    basis
}

/// The reducta of `f` in `x_v` that Hong's operator needs: `f`, then `f` without its leading
/// term, and so on, up to and including the first whose leading coefficient is a nonzero
/// constant, and stopping before degree 0.
fn reducta(f: &MPoly, v: usize) -> Vec<MPoly> {
    let mut coeffs = f.coeffs_in(v);
    let mut out = Vec::new();
    while coeffs.len() >= 2 {
        let lc = coeffs.last().unwrap();
        if lc.is_zero() {
            coeffs.pop();
            continue;
        }
        let constant = lc.is_constant();
        out.push(MPoly::from_coeffs_in(v, &coeffs));
        if constant {
            break;
        }
        coeffs.pop();
    }
    out
}

/// Hong's projection of a level-`v` basis (see the module docs). Constants and zero
/// polynomials are omitted (they are sign-invariant everywhere).
pub fn hong_projection(basis: &[MPoly], v: usize) -> Vec<MPoly> {
    let _k = st::kernel(st::Kernel::Psc);
    let mut out: Vec<MPoly> = Vec::new();
    let mut push = |p: MPoly| {
        if !p.is_constant() {
            out.push(p);
        }
    };
    let reds: Vec<Vec<MPoly>> = basis.iter().map(|f| reducta(f, v)).collect();
    for (f, rs) in basis.iter().zip(&reds) {
        // Every coefficient down to the cut-off is the leading coefficient of a reductum; the
        // trailing coefficient is the reductum of degree 0 when no cut-off happened.
        let coeffs = f.coeffs_in(v);
        let last_deg = rs.last().map(|r| r.degree_in(v).unwrap()).unwrap_or(0);
        let cut = rs.last().is_some_and(|r| r.lc_in(v).is_constant());
        for (i, c) in coeffs.iter().enumerate().rev() {
            if i < last_deg && cut {
                break;
            }
            push(c.clone());
        }
        for (k, r) in rs.iter().enumerate() {
            let d = r.derivative(v);
            let psc = r.psc(&d, v);
            if k == 0 {
                assert!(
                    psc.last().is_some_and(|(j, _)| *j == 0) || r.degree_in(v) == Some(1),
                    "basis element {f} is not square-free in x{v}"
                );
            }
            for (_, p) in psc {
                push(p);
            }
        }
    }
    for i in 0..basis.len() {
        for j in i + 1..basis.len() {
            let g = &basis[j];
            for (k, r) in reds[i].iter().enumerate() {
                let psc = r.psc(g, v);
                if k == 0 {
                    assert!(
                        psc.last().is_some_and(|(j, _)| *j == 0),
                        "basis elements {} and {g} are not coprime in x{v}",
                        basis[i]
                    );
                }
                for (_, p) in psc {
                    push(p);
                }
            }
        }
    }
    out
}

/// One cell of a stack: its sample coordinate and the basis elements vanishing on it.
struct Cell {
    value: RealAlgebraic,
    zeros: Vec<usize>,
}

struct Search<'a> {
    bases: &'a [Vec<MPoly>],
    constraints: &'a [Constraint],
    /// Constraints by the level of their main variable.
    by_level: Vec<Vec<usize>>,
    /// Per constraint: the basis elements `(level, index)` that divide its polynomial.
    factors: Vec<Vec<(usize, usize)>>,
    /// Per level: whether each basis element vanishes at the current sample.
    zero: Vec<Vec<bool>>,
    point: Vec<RealAlgebraic>,
    cells: usize,
}

impl<'a> Search<'a> {
    fn new(bases: &'a [Vec<MPoly>], constraints: &'a [Constraint]) -> Search<'a> {
        let n = bases.len();
        let mut by_level = vec![Vec::new(); n];
        let mut factors = Vec::with_capacity(constraints.len());
        for (i, c) in constraints.iter().enumerate() {
            by_level[c.poly.main_var().unwrap()].push(i);
            let mut fs = Vec::new();
            for (k, basis) in bases.iter().enumerate() {
                for (j, b) in basis.iter().enumerate() {
                    if c.poly.div_exact(b).is_some() {
                        fs.push((k, j));
                    }
                }
            }
            assert!(
                !fs.is_empty(),
                "constraint polynomial {} has no basis factor",
                c.poly
            );
            factors.push(fs);
        }
        Search {
            bases,
            constraints,
            by_level,
            factors,
            zero: bases.iter().map(|b| vec![false; b.len()]).collect(),
            point: Vec::new(),
            cells: 0,
        }
    }

    /// Search the stack over the current sample (of length `k`) for a satisfying point.
    fn lift(&mut self, k: usize) -> bool {
        if k == self.bases.len() {
            return true;
        }
        let mut roots: Vec<(RealAlgebraic, usize)> = Vec::new();
        let mut nullified = Vec::new();
        for (j, b) in self.bases[k].iter().enumerate() {
            match roots_at(b, &mut self.point) {
                Fiber::Nullified => nullified.push(j),
                Fiber::Roots(rs) => roots.extend(rs.into_iter().map(|r| (r, j))),
            }
        }
        roots.sort_by(|a, b| a.0.cmp(&b.0));
        let mut sections: Vec<Cell> = Vec::new();
        for (r, j) in roots {
            match sections.last_mut() {
                Some(c) if c.value == r => c.zeros.push(j),
                _ => sections.push(Cell {
                    value: r,
                    zeros: vec![j],
                }),
            }
        }
        let mut cells = Vec::with_capacity(2 * sections.len() + 1);
        // Sectors and sections in increasing order.
        cells.push(Cell {
            value: RealAlgebraic::from_rational(below(sections.first().map(|c| &c.value))),
            zeros: Vec::new(),
        });
        for i in 0..sections.len() {
            let next = sections.get(i + 1).map(|c| c.value.clone());
            let here = sections[i].value.clone();
            cells.push(Cell {
                value: here.clone(),
                zeros: std::mem::take(&mut sections[i].zeros),
            });
            let v = match next {
                Some(nx) => between(&here, &nx),
                None => above(&here),
            };
            cells.push(Cell {
                value: RealAlgebraic::from_rational(v),
                zeros: Vec::new(),
            });
        }
        // On a sector only the nullified level-k basis elements vanish. An equation none of whose
        // factors can vanish there (no lower-level factor vanishes at the sample, no level-k
        // factor is nullified) holds on no sector: then only sections are tried.
        let wants_zero = self.by_level[k].iter().any(|&c| {
            self.constraints[c].allowed == SignSet::ZERO
                && !self.factors[c]
                    .iter()
                    .any(|&(l, j)| (l < k && self.zero[l][j]) || (l == k && nullified.contains(&j)))
        });
        let order: Vec<usize> = if wants_zero {
            (0..cells.len())
                .filter(|i| i % 2 == 1)
                .chain((0..cells.len()).filter(|i| i % 2 == 0))
                .collect()
        } else {
            (0..cells.len())
                .filter(|i| i % 2 == 0)
                .chain((0..cells.len()).filter(|i| i % 2 == 1))
                .collect()
        };
        for i in order {
            if wants_zero && i % 2 == 0 {
                // A sector: every equation's basis factors are nonzero here.
                break;
            }
            self.cells += 1;
            for z in self.zero[k].iter_mut() {
                *z = false;
            }
            for &j in cells[i].zeros.iter().chain(&nullified) {
                self.zero[k][j] = true;
            }
            self.point.push(cells[i].value.clone());
            if self.check_level(k) && self.lift(k + 1) {
                return true;
            }
            self.point.pop();
        }
        false
    }

    /// Whether every constraint whose main variable is `x_k` holds at the current sample.
    fn check_level(&mut self, k: usize) -> bool {
        for idx in 0..self.by_level[k].len() {
            let c = self.by_level[k][idx];
            let vanishes = self.factors[c].iter().any(|&(l, j)| self.zero[l][j]);
            let s = if vanishes {
                0
            } else {
                sign_at_nonzero(&self.constraints[c].poly, &mut self.point)
            };
            if !self.constraints[c].allowed.allows(s) {
                return false;
            }
        }
        true
    }
}

/// A simple rational below `r` (or 0 with no root).
pub(crate) fn below(r: Option<&RealAlgebraic>) -> BigRational {
    let Some(r) = r else {
        return BigRational::zero();
    };
    if r.cmp_rational(&BigRational::zero()) == Ordering::Greater {
        return BigRational::zero();
    }
    let f = r.lower().floor();
    if r.is_rational() || &f == r.lower() {
        f - BigRational::one()
    } else {
        f
    }
}

/// A simple rational above `r`.
pub(crate) fn above(r: &RealAlgebraic) -> BigRational {
    if r.cmp_rational(&BigRational::zero()) == Ordering::Less {
        return BigRational::zero();
    }
    let c = r.upper().ceil();
    if r.is_rational() || &c == r.upper() {
        c + BigRational::one()
    } else {
        c
    }
}

/// A simple rational strictly between `a < b`.
pub(crate) fn between(a: &RealAlgebraic, b: &RealAlgebraic) -> BigRational {
    let (mut a, mut b) = (a.clone(), b.clone());
    loop {
        if a.upper() < b.lower() {
            return simplest_between(a.upper(), b.lower());
        }
        let wa = a.upper() - a.lower();
        let wb = b.upper() - b.lower();
        let half = |w: BigRational| w / BigRational::from_integer(BigInt::from(2));
        if wa >= wb && !a.is_rational() {
            a.refine(&half(wa));
        } else if !b.is_rational() {
            b.refine(&half(wb));
        } else {
            a.refine(&half(wa));
        }
    }
}

/// The simplest rational (smallest denominator, then smallest numerator magnitude) in the open
/// interval `(lo, hi)`, `lo < hi` (Stern–Brocot descent).
pub fn simplest_between(lo: &BigRational, hi: &BigRational) -> BigRational {
    debug_assert!(lo < hi);
    if lo.is_negative() && hi.is_positive() {
        return BigRational::zero();
    }
    if !hi.is_positive() {
        return -simplest_between(&-hi, &-lo);
    }
    // 0 <= lo < hi
    let fl = lo.floor();
    let next = &fl + BigRational::one();
    if &next < hi {
        return next;
    }
    // fl <= lo < hi <= fl + 1
    let (a, b) = (lo - &fl, hi - &fl);
    // simplest in (a, b) ⊂ [0, 1]: 1 / simplest in (1/b, 1/a)
    let inner = if a.is_zero() {
        // (1/b, ∞): the least integer > 1/b
        (b.recip()).floor() + BigRational::one()
    } else {
        simplest_between(&b.recip(), &a.recip())
    };
    fl + inner.recip()
}

/// Exact check that `point` satisfies every constraint (no CAD involved; used to reuse models).
pub fn satisfies(constraints: &[Constraint], point: &mut [RealAlgebraic]) -> bool {
    constraints
        .iter()
        .all(|c| c.allowed.allows(sign_at(&c.poly, point)))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn q(n: i64, d: i64) -> BigRational {
        BigRational::new(BigInt::from(n), BigInt::from(d))
    }

    #[test]
    fn simplest_rationals() {
        assert_eq!(simplest_between(&q(-1, 2), &q(3, 1)), q(0, 1));
        assert_eq!(simplest_between(&q(1, 3), &q(1, 2)), q(2, 5));
        assert_eq!(simplest_between(&q(3, 2), &q(7, 3)), q(2, 1));
        assert_eq!(simplest_between(&q(-7, 3), &q(-3, 2)), q(-2, 1));
        assert_eq!(simplest_between(&q(0, 1), &q(1, 1000)), q(1, 1001));
        assert_eq!(simplest_between(&q(2, 1), &q(3, 1)), q(5, 2));
    }
}
