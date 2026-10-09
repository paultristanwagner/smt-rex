//! Model-constructing, conflict-driven decision of a conjunction of polynomial sign conditions:
//! cylindrical algebraic *coverings* (E. Ábrahám, J. H. Davenport, M. England, G. Kremer,
//! *Deciding the consistency of non-linear real arithmetic constraints with a conflict driven
//! search using cylindrical algebraic coverings*, JLAMP 2021; [ÁDEK21] below), the
//! conjunction-level analogue of NLSAT's model construction (de Moura & Jovanović 2012).
//!
//! Variables are assigned in order `x₀, x₁, …`. At level `i`, with `x₀ … x_{i−1}` fixed to a
//! sample `p`, every constraint whose main variable is `x_i` excludes the intervals of `x_i` where
//! it is false (exact root isolation over `p`). A value outside all excluded intervals is chosen
//! and the search moves up a level. If level `i + 1` turns out to be covered — every value of
//! `x_{i+1}` excluded — the covering is *characterised*: the polynomials behind its intervals are
//! projected ([`Characterisation`]: the single-level operator of [ÁDEK21] by default, or Hong's
//! projection over a square-free coprime basis as in [`crate::cad`]) and the cell of the
//! projection's level-`i` polynomials around `p_i` (a root, or the open interval between the
//! nearest roots below and above) becomes a new excluded interval at level `i`. A covering of
//! level 0 proves the conjunction unsatisfiable, and the constraints behind its intervals
//! (transitively) form an unsatisfiable core.
//!
//! # Why a characterised interval is excluded
//!
//! The argument for [`Characterisation::Hong`]; the single-level one is [ÁDEK21] §4.5. Every
//! excluded interval `I` at level `ℓ` carries polynomials `Q_I` (main variable `≤ ℓ`) with the
//! invariant: *if `D ⊆ R^{ℓ+1}` is connected, contains the sample `(p, t)` from which `I` was
//! built, and every element of `Q_I` is sign-invariant on `D`, then no point of
//! `D × R^{n−ℓ−1}` satisfies all constraints of levels `≥ ℓ`.*
//!
//! For a constraint interval, `Q_I` is the constraint's polynomial, and sign-invariance keeps the
//! constraint false. For a characterised interval `J` at level `i`, `Q_J` is the basis
//! `B₀ … B_i` of the projection closure of `P = ⋃ Q_I` over the covering `O` at level `i + 1`,
//! and `J` is a cell of `B_i` over `p`. Take such a `D`. By Collins'/Hong's theorem `B_{i+1}` is
//! delineable on `D`. Every interval of `O` is bounded by roots of polynomials whose square-free
//! parts are products of `B_{i+1}` elements, so it continues over `D` as a fixed union of stack
//! cells, and together these still cover every fibre. A constraint interval of `O` stays false
//! on its cells (its polynomial is in `P`). A characterised interval `I ∈ O` lies within one
//! stack cell of `B'_{i+1} ⊆ Q_I` at the sample; the elements of `Q_I ⊆ P` have square-free
//! parts that are products of `B` elements, so they are sign-invariant on the region `I` sweeps
//! over `D`, which is connected and contains `I`'s sample, and the invariant of `I` applies.
//! Hence no point over `D` satisfies the constraints. ∎ With the empty prefix, a covering of
//! level 0 excludes every point.
//!
//! Termination: every characterised interval contains the sample it was built from, so each
//! sample is chosen once, and only finitely many cells can arise (all polynomials are factors of
//! iterated projections of products of the finitely many irreducible factors involved).

use crate::cad::{
    above, below, between, coprime_basis, poly_order, project, variable_order, Constraint,
};
use num_rational::BigRational;
use rustc_hash::{FxHashMap, FxHashSet};
use smtrex_poly::point::{roots_at, sign_at, sign_at_nonzero, Fiber};
use smtrex_poly::stats as st;
use smtrex_poly::{MPoly, RealAlgebraic};
use std::cmp::Ordering;

/// The result of [`solve`].
#[derive(Clone, Debug)]
pub enum Outcome {
    /// A satisfying point, indexed by variable.
    Sat(Vec<RealAlgebraic>),
    /// An unsatisfiable core: indices into the constraint slice.
    Unsat(Vec<usize>),
}

/// Statistics of one decision.
#[derive(Clone, Debug, Default)]
pub struct CoverStats {
    pub samples: usize,
    pub characterisations: usize,
    /// Restarts with [`Characterisation::Hong`] after a nullification.
    pub fallbacks: usize,
}

#[derive(Clone, Debug)]
enum Lo {
    NegInf,
    /// `≥ r`
    Incl(RealAlgebraic),
    /// `> r`
    Excl(RealAlgebraic),
}

#[derive(Clone, Debug)]
enum Hi {
    PosInf,
    /// `≤ r`
    Incl(RealAlgebraic),
    /// `< r`
    Excl(RealAlgebraic),
}

/// An excluded interval with its justification.
#[derive(Clone, Debug)]
struct Excl {
    lo: Lo,
    hi: Hi,
    /// Constraints (local indices) behind the interval.
    origins: Vec<usize>,
    /// The interval's polynomials with main variable `x_ℓ` (its level): the square-free
    /// coprime basis whose roots over the sample delimit it (`P_i` in [ÁDEK21]).
    main: Vec<MPoly>,
    /// Its polynomials with a lower main variable (`P_⊥`). With [`Characterisation::Hong`],
    /// `main ∪ lower` is the set `Q_I` of the module docs.
    lower: Vec<MPoly>,
    /// The elements of `main` vanishing at the lower and the upper bound (`L`, `U`).
    lo_polys: Vec<MPoly>,
    hi_polys: Vec<MPoly>,
}

impl Excl {
    fn contains(&self, x: &RealAlgebraic) -> bool {
        let lo_ok = match &self.lo {
            Lo::NegInf => true,
            Lo::Incl(r) => x >= r,
            Lo::Excl(r) => x > r,
        };
        lo_ok
            && match &self.hi {
                Hi::PosInf => true,
                Hi::Incl(r) => x <= r,
                Hi::Excl(r) => x < r,
            }
    }
}

/// Decide the conjunction. `hint` is a point to prefer when sampling (e.g. the previous model).
/// The characterisation is chosen by the environment ([`Characterisation`]).
pub fn solve(
    constraints: &[Constraint],
    num_vars: usize,
    hint: Option<&[RealAlgebraic]>,
) -> (Outcome, CoverStats) {
    solve_with(constraints, num_vars, hint, Characterisation::from_env())
}

/// [`solve`] with the given characterisation (falling back to [`Characterisation::Hong`] on a
/// nullification).
pub fn solve_with(
    constraints: &[Constraint],
    num_vars: usize,
    hint: Option<&[RealAlgebraic]>,
    mode: Characterisation,
) -> (Outcome, CoverStats) {
    let mut stats = CoverStats::default();
    let mut rest = Vec::new();
    let mut rest_idx = Vec::new();
    for (i, c) in constraints.iter().enumerate() {
        match c.poly.as_constant() {
            Some(k) => {
                let s = match k.sign() {
                    num_bigint::Sign::Minus => -1,
                    num_bigint::Sign::NoSign => 0,
                    num_bigint::Sign::Plus => 1,
                };
                if !c.allowed.allows(s) {
                    return (Outcome::Unsat(vec![i]), stats);
                }
            }
            None => {
                rest.push(c.clone());
                rest_idx.push(i);
            }
        }
    }
    let mut used: Vec<usize> = rest.iter().flat_map(|c| c.poly.vars()).collect();
    used.sort_unstable();
    used.dedup();
    let order = variable_order(&rest, &used);
    let width = num_vars.max(used.last().map_or(0, |v| v + 1));
    let mut to_level = vec![usize::MAX; width];
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
    let mut model = vec![RealAlgebraic::from_int(0); width];
    if n == 0 {
        model.truncate(num_vars);
        return (Outcome::Sat(model), stats);
    }
    let hint: Option<Vec<RealAlgebraic>> = hint.map(|h| {
        order
            .iter()
            .map(|&v| {
                h.get(v)
                    .cloned()
                    .unwrap_or_else(|| RealAlgebraic::from_int(0))
            })
            .collect()
    });
    let mut mode = mode;
    loop {
        let mut s = Search {
            mode,
            constraints: &local,
            by_level: {
                let mut b = vec![Vec::new(); n];
                for (i, c) in local.iter().enumerate() {
                    b[c.poly.main_var().unwrap()].push(i);
                }
                b
            },
            n,
            point: Vec::new(),
            hint: hint.clone(),
            projections: FxHashMap::default(),
            stats: CoverStats::default(),
        };
        let r = s.cover(0);
        stats.samples += s.stats.samples;
        stats.characterisations += s.stats.characterisations;
        match r {
            Ok(()) => {
                for (k, &v) in order.iter().enumerate() {
                    model[v] = s.point[k].clone();
                }
                model.truncate(num_vars);
                return (Outcome::Sat(model), stats);
            }
            Err(Stop::Covered(cov)) => {
                let mut core: Vec<usize> = minimal_cover(&cov)
                    .iter()
                    .flat_map(|e| e.origins.iter().map(|&o| rest_idx[o]))
                    .collect();
                core.sort_unstable();
                core.dedup();
                return (Outcome::Unsat(core), stats);
            }
            Err(Stop::Nullified) => {
                debug_assert_eq!(mode, Characterisation::SingleLevel);
                stats.fallbacks += 1;
                st::add(st::Counter::Nullifications, 1);
                mode = Characterisation::Hong;
            }
        }
    }
}

/// How a covering of level `i + 1` is generalised to an excluded interval at level `i`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Characterisation {
    /// The single-level characterisation of [ÁDEK21] §4.4 (Algorithms 4–6): discriminants and
    /// required coefficients of the covering's polynomials, and only the resultants that keep
    /// each bound the closest one and adjacent intervals overlapping. A subset of McCallum's
    /// projection, so valid only without nullification; a nullification anywhere makes
    /// [`solve`] start over with [`Characterisation::Hong`]. The default.
    SingleLevel,
    /// The full Hong projection closure of the covering's polynomials, every level down to 0:
    /// complete for any input, but far more polynomials. Selected with
    /// `SMTREX_NRA_CHAR=hong`.
    Hong,
}

impl Characterisation {
    fn from_env() -> Characterisation {
        if std::env::var("SMTREX_NRA_CHAR").is_ok_and(|v| v == "hong") {
            Characterisation::Hong
        } else {
            Characterisation::SingleLevel
        }
    }
}

/// Why [`Search::cover`] found no satisfying extension.
enum Stop {
    /// The intervals cover the line.
    Covered(Vec<Excl>),
    /// A polynomial vanished identically over the sample, which the single-level
    /// characterisation cannot handle.
    Nullified,
}

struct Search<'a> {
    mode: Characterisation,
    constraints: &'a [Constraint],
    by_level: Vec<Vec<usize>>,
    n: usize,
    point: Vec<RealAlgebraic>,
    hint: Option<Vec<RealAlgebraic>>,
    /// Projection bases by level and (sorted) input polynomial set: the same set can reach
    /// coverings at different levels, and the closure depends on the level.
    projections: FxHashMap<(usize, Vec<MPoly>), Vec<Vec<MPoly>>>,
    stats: CoverStats,
}

impl Search<'_> {
    /// Find a satisfying extension of the current sample (of length `i`), or a covering of
    /// level `i` by excluded intervals.
    fn cover(&mut self, i: usize) -> Result<(), Stop> {
        let mut excl = {
            let _o = st::outer(st::Outer::CovIntervals);
            self.constraint_intervals(i)?
        };
        loop {
            let sampled = {
                let _o = st::outer(st::Outer::CovSample);
                self.sample_outside(&excl, i)
            };
            let Some(s) = sampled else {
                return Err(Stop::Covered(excl));
            };
            self.stats.samples += 1;
            st::add(st::Counter::Samples, 1);
            if !s.is_rational() {
                st::add(st::Counter::IrrationalSamples, 1);
                st::max(
                    st::Counter::SampleDegMax,
                    s.minimal_polynomial().degree().unwrap_or(0) as u64,
                );
            }
            self.point.push(s);
            if i + 1 == self.n {
                return Ok(());
            }
            match self.cover(i + 1) {
                Ok(()) => return Ok(()),
                Err(Stop::Covered(cov)) => {
                    let cov = minimal_cover(&cov);
                    let j = match self.mode {
                        Characterisation::Hong => self.characterise(i, &cov),
                        Characterisation::SingleLevel => self.characterise_single(i, &cov)?,
                    };
                    self.point.pop();
                    excl.push(j);
                }
                Err(Stop::Nullified) => return Err(Stop::Nullified),
            }
        }
    }

    /// The intervals of `x_i` (over the current sample) where some level-`i` constraint is
    /// false.
    fn constraint_intervals(&mut self, i: usize) -> Result<Vec<Excl>, Stop> {
        let mut out = Vec::new();
        for idx in 0..self.by_level[i].len() {
            let c = self.by_level[i][idx];
            let poly = self.constraints[c].poly.clone();
            let allowed = self.constraints[c].allowed;
            // The interval's polynomials: the constraint itself for the Hong closure; for the
            // single-level characterisation its square-free coprime factors in x_i, with the
            // content (whose sign the constraint's truth also depends on) one level down.
            let (main, lower) = match self.mode {
                Characterisation::Hong => (vec![poly.clone()], Vec::new()),
                Characterisation::SingleLevel => {
                    let mut levels = Levels::default();
                    levels.add(&poly, i);
                    levels.finish(i)
                }
            };
            let fiber = roots_at(&poly, &mut self.point);
            let roots = match fiber {
                Fiber::Nullified => {
                    if !allowed.allows(0) {
                        if self.mode == Characterisation::SingleLevel {
                            return Err(Stop::Nullified);
                        }
                        out.push(Excl {
                            lo: Lo::NegInf,
                            hi: Hi::PosInf,
                            origins: vec![c],
                            main,
                            lower,
                            lo_polys: Vec::new(),
                            hi_polys: Vec::new(),
                        });
                    }
                    continue;
                }
                Fiber::Roots(r) => r,
            };
            // Cells: sector 0, root 0, sector 1, …, root m−1, sector m; truth on each.
            let m = roots.len();
            let mut truth = Vec::with_capacity(2 * m + 1);
            for k in 0..=m {
                let sample = match (k.checked_sub(1).map(|j| &roots[j]), roots.get(k)) {
                    (None, None) => BigRational::from_integer(0.into()),
                    (None, Some(r)) => below(Some(r)),
                    (Some(l), None) => above(l),
                    (Some(l), Some(r)) => between(l, r),
                };
                self.point.push(RealAlgebraic::from_rational(sample));
                let s = sign_at_nonzero(&poly, &mut self.point);
                self.point.pop();
                truth.push(allowed.allows(s));
                if k < m {
                    truth.push(allowed.allows(0));
                }
            }
            // Maximal runs of false cells.
            let mut k = 0;
            while k < truth.len() {
                if truth[k] {
                    k += 1;
                    continue;
                }
                let start = k;
                while k < truth.len() && !truth[k] {
                    k += 1;
                }
                let end = k - 1;
                // cell index 2j is sector j (between roots j−1 and j), 2j+1 is root j
                let lo = if start % 2 == 0 {
                    match (start / 2).checked_sub(1) {
                        None => Lo::NegInf,
                        Some(j) => Lo::Excl(roots[j].clone()),
                    }
                } else {
                    Lo::Incl(roots[start / 2].clone())
                };
                let hi = if end % 2 == 0 {
                    match roots.get(end / 2) {
                        None => Hi::PosInf,
                        Some(r) => Hi::Excl(r.clone()),
                    }
                } else {
                    Hi::Incl(roots[end / 2].clone())
                };
                let (lo_polys, hi_polys) = match self.mode {
                    Characterisation::Hong => (Vec::new(), Vec::new()),
                    Characterisation::SingleLevel => (
                        self.vanishing_at(&main, lo_value(&lo)),
                        self.vanishing_at(&main, hi_value(&hi)),
                    ),
                };
                out.push(Excl {
                    lo,
                    hi,
                    origins: vec![c],
                    main: main.clone(),
                    lower: lower.clone(),
                    lo_polys,
                    hi_polys,
                });
            }
        }
        Ok(out)
    }

    /// The elements of `polys` (main variable `x_i`, `i = point.len()`) that vanish at
    /// `(point, r)`; none for an infinite bound.
    fn vanishing_at(&mut self, polys: &[MPoly], r: Option<&RealAlgebraic>) -> Vec<MPoly> {
        let Some(r) = r else {
            return Vec::new();
        };
        self.point.push(r.clone());
        let out = polys
            .iter()
            .filter(|p| sign_at(p, &mut self.point) == 0)
            .cloned()
            .collect();
        self.point.pop();
        out
    }

    /// A value of `x_i` in no excluded interval, if there is one: the hint if it is free, else
    /// a simple point of the first gap.
    fn sample_outside(&self, excl: &[Excl], i: usize) -> Option<RealAlgebraic> {
        if let Some(h) = self.hint.as_ref().map(|h| &h[i]) {
            if !excl.iter().any(|e| e.contains(h)) {
                return Some(h.clone());
            }
        }
        let mut sorted: Vec<&Excl> = excl.iter().collect();
        sorted.sort_by(|a, b| cmp_lo(&a.lo, &b.lo));
        // `frontier`: everything below it is covered. None = nothing covered yet.
        let mut frontier: Option<Hi> = None;
        for e in sorted {
            match gap(frontier.as_ref(), &e.lo) {
                Some(s) => {
                    if st::enabled() && lo_value(&e.lo) == Some(&s) {
                        st::add(st::Counter::PointGaps, 1);
                        if !s.is_rational() {
                            st::add(st::Counter::IrrationalPointGaps, 1);
                        }
                    }
                    return Some(s);
                }
                None => {
                    frontier = Some(match frontier {
                        None => e.hi.clone(),
                        Some(f) => max_hi(f, e.hi.clone()),
                    });
                }
            }
            if matches!(frontier, Some(Hi::PosInf)) {
                return None;
            }
        }
        Some(match frontier {
            None => RealAlgebraic::from_int(0),
            Some(Hi::PosInf) => return None,
            Some(Hi::Incl(r) | Hi::Excl(r)) => RealAlgebraic::from_rational(above(&r)),
        })
    }

    /// The single-level characterisation ([`Characterisation::SingleLevel`]): the excluded
    /// interval at level `i` around `point[i]` justified by the covering `cov` of level `i + 1`
    /// (already minimal, ordered by [`minimal_cover`]).
    ///
    /// [ÁDEK21] Algorithm 4, over one square-free coprime basis `B` of all the covering's
    /// level-`i+1` polynomials (so every resultant below is of coprime polynomials):
    /// - every interval's lower-level polynomials, passed down;
    /// - discriminants and *required coefficients* (Algorithm 6: leading coefficients down to the
    ///   first nonzero at the sample) of `B`: each element stays delineable;
    /// - `res(p, q)` for `p` defining a bound of an interval and `q` one of its polynomials with a
    ///   root beyond that bound: the bound stays the closest;
    /// - `res(p, q)` for `p` at the upper bound of an interval and `q` at the lower bound of the
    ///   next: adjacent intervals keep overlapping.
    ///
    /// Then Algorithm 5: the interval of `x_i` around `point[i]` between the nearest roots of the
    /// level-`i` part of that set.
    fn characterise_single(&mut self, i: usize, cov: &[Excl]) -> Result<Excl, Stop> {
        self.stats.characterisations += 1;
        st::add(st::Counter::Characterisations, 1);
        let _o = st::outer(st::Outer::CovProject);
        let v = i + 1;
        debug_assert_eq!(self.point.len(), v);
        let mut origins: Vec<usize> = cov.iter().flat_map(|e| e.origins.iter().copied()).collect();
        origins.sort_unstable();
        origins.dedup();

        // One coprime basis for the whole covering, with each element's roots over the sample.
        let mut all: Vec<MPoly> = cov.iter().flat_map(|e| e.main.iter().cloned()).collect();
        all.sort_by(poly_order);
        all.dedup();
        let basis = coprime_basis(all, v);
        let mut roots: Vec<Vec<RealAlgebraic>> = Vec::with_capacity(basis.len());
        for b in &basis {
            match roots_at(b, &mut self.point) {
                Fiber::Nullified => return Err(Stop::Nullified),
                Fiber::Roots(r) => roots.push(r),
            }
        }
        // Per interval: its basis elements, and those at its bounds.
        let divides = |b: &MPoly, ps: &[MPoly]| ps.iter().any(|p| !b.coprime_in(p, v));
        let at = |k: usize, r: Option<&RealAlgebraic>| r.is_some_and(|r| roots[k].contains(r));
        struct Parts {
            main: Vec<usize>,
            lo: Vec<usize>,
            hi: Vec<usize>,
        }
        let parts: Vec<Parts> = cov
            .iter()
            .map(|e| {
                let main: Vec<usize> = (0..basis.len())
                    .filter(|&k| divides(&basis[k], &e.main))
                    .collect();
                let lo = main
                    .iter()
                    .copied()
                    .filter(|&k| at(k, lo_value(&e.lo)) && divides(&basis[k], &e.lo_polys))
                    .collect();
                let hi = main
                    .iter()
                    .copied()
                    .filter(|&k| at(k, hi_value(&e.hi)) && divides(&basis[k], &e.hi_polys))
                    .collect();
                Parts { main, lo, hi }
            })
            .collect();

        let mut levels = Levels::default();
        for e in cov {
            for p in &e.lower {
                levels.add(p, i);
            }
        }
        for (k, b) in basis.iter().enumerate() {
            if !parts.iter().any(|q| q.main.contains(&k)) {
                continue;
            }
            levels.add(&b.discriminant(v), i);
            let mut coeffs = b.coeffs_in(v);
            loop {
                let Some(c) = coeffs.pop() else {
                    return Err(Stop::Nullified);
                };
                levels.add(&c, i);
                if sign_at(&c, &mut self.point) != 0 {
                    break;
                }
            }
        }
        let mut pairs: FxHashSet<(usize, usize)> = FxHashSet::default();
        for (e, q) in cov.iter().zip(&parts) {
            for &p in &q.lo {
                let l = lo_value(&e.lo).expect("a bound polynomial at a finite bound");
                for &o in &q.main {
                    if o != p && roots[o].iter().any(|r| r <= l) {
                        pairs.insert((p.min(o), p.max(o)));
                    }
                }
            }
            for &p in &q.hi {
                let u = hi_value(&e.hi).expect("a bound polynomial at a finite bound");
                for &o in &q.main {
                    if o != p && roots[o].iter().any(|r| r >= u) {
                        pairs.insert((p.min(o), p.max(o)));
                    }
                }
            }
        }
        for w in parts.windows(2) {
            for &p in &w[0].hi {
                for &q in &w[1].lo {
                    if p != q {
                        pairs.insert((p.min(q), p.max(q)));
                    }
                }
            }
        }
        let mut pairs: Vec<_> = pairs.into_iter().collect();
        pairs.sort_unstable();
        for (p, q) in pairs {
            let _k = st::kernel(st::Kernel::Psc);
            levels.add(&basis[p].resultant(&basis[q], v), i);
        }
        let (main, lower) = levels.finish(i);

        // Algorithm 5: the cell of the level-i polynomials around point[i].
        let _o = st::outer(st::Outer::CovCell);
        let s = self.point[i].clone();
        let mut prefix: Vec<RealAlgebraic> = self.point[..i].to_vec();
        let mut lo: Option<RealAlgebraic> = None;
        let mut hi: Option<RealAlgebraic> = None;
        let mut on_root = false;
        let mut level_roots: Vec<Vec<RealAlgebraic>> = Vec::with_capacity(main.len());
        for b in &main {
            let rs = match roots_at(b, &mut prefix) {
                Fiber::Nullified => return Err(Stop::Nullified),
                Fiber::Roots(rs) => rs,
            };
            for r in &rs {
                match r.cmp(&s) {
                    Ordering::Equal => on_root = true,
                    Ordering::Less => {
                        if lo.as_ref().is_none_or(|l| r > l) {
                            lo = Some(r.clone());
                        }
                    }
                    Ordering::Greater => {
                        if hi.as_ref().is_none_or(|h| r < h) {
                            hi = Some(r.clone());
                        }
                    }
                }
            }
            level_roots.push(rs);
        }
        let bound = |r: &Option<RealAlgebraic>| -> Vec<MPoly> {
            match r {
                None => Vec::new(),
                Some(r) => (0..main.len())
                    .filter(|&k| level_roots[k].contains(r))
                    .map(|k| main[k].clone())
                    .collect(),
            }
        };
        let (lo, hi, lo_polys, hi_polys) = if on_root {
            let at_s = bound(&Some(s.clone()));
            (Lo::Incl(s.clone()), Hi::Incl(s), at_s.clone(), at_s)
        } else {
            let (lp, hp) = (bound(&lo), bound(&hi));
            (
                lo.map_or(Lo::NegInf, Lo::Excl),
                hi.map_or(Hi::PosInf, Hi::Excl),
                lp,
                hp,
            )
        };
        Ok(Excl {
            lo,
            hi,
            origins,
            main,
            lower,
            lo_polys,
            hi_polys,
        })
    }

    /// The excluded interval at level `i` around the current sample `point[i]` that the
    /// covering `cov` of level `i + 1` justifies (see the module docs).
    fn characterise(&mut self, i: usize, cov: &[Excl]) -> Excl {
        self.stats.characterisations += 1;
        let mut set: FxHashSet<MPoly> = FxHashSet::default();
        let mut origins: Vec<usize> = Vec::new();
        for e in cov {
            set.extend(e.main.iter().cloned());
            set.extend(e.lower.iter().cloned());
            origins.extend(e.origins.iter().copied());
        }
        origins.sort_unstable();
        origins.dedup();
        let mut polys: Vec<MPoly> = set.into_iter().collect();
        polys.sort_by(|a, b| a.terms().cmp(b.terms()));
        st::add(st::Counter::Characterisations, 1);
        let key = (i, polys);
        let bases = match self.projections.get(&key) {
            Some(b) => {
                st::add(st::Counter::ProjCacheHits, 1);
                b.clone()
            }
            None => {
                let _o = st::outer(st::Outer::CovProject);
                st::add(st::Counter::Projections, 1);
                st::add(st::Counter::ProjInSum, key.1.len() as u64);
                st::max(st::Counter::ProjInMax, key.1.len() as u64);
                let b = project(key.1.clone(), i + 2);
                if st::enabled() {
                    record_projection(&b);
                }
                self.projections.insert(key, b.clone());
                b
            }
        };
        let _o = st::outer(st::Outer::CovCell);
        // The cell of B_i around point[i] over point[..i].
        let s = self.point[i].clone();
        let mut prefix: Vec<RealAlgebraic> = self.point[..i].to_vec();
        let mut lo: Lo = Lo::NegInf;
        let mut hi: Hi = Hi::PosInf;
        let mut on_root: Option<RealAlgebraic> = None;
        for b in &bases[i] {
            let Fiber::Roots(rs) = roots_at(b, &mut prefix) else {
                continue; // nullified over the prefix: zero on the whole fibre
            };
            for r in rs {
                match r.cmp(&s) {
                    Ordering::Equal => on_root = Some(r),
                    Ordering::Less => {
                        if lo_value(&lo).is_none_or(|l| &r > l) {
                            lo = Lo::Excl(r);
                        }
                    }
                    Ordering::Greater => {
                        if hi_value(&hi).is_none_or(|h| &r < h) {
                            hi = Hi::Excl(r);
                        }
                    }
                }
            }
        }
        let (lo, hi) = match on_root {
            Some(r) => (Lo::Incl(r.clone()), Hi::Incl(r)),
            None => (lo, hi),
        };
        Excl {
            lo,
            hi,
            origins,
            main: bases[i].clone(),
            lower: bases[..i].iter().flatten().cloned().collect(),
            lo_polys: Vec::new(),
            hi_polys: Vec::new(),
        }
    }
}

/// Diagnostics: the size of a projection result.
fn record_projection(bases: &[Vec<MPoly>]) {
    let out: usize = bases.iter().map(Vec::len).sum();
    let deg = bases.iter().flatten().filter_map(MPoly::total_degree).max();
    st::add(st::Counter::ProjOutSum, out as u64);
    st::max(st::Counter::ProjOutMax, out as u64);
    st::max(st::Counter::ProjDegMax, deg.unwrap_or(0) as u64);
}

/// Order of lower bounds: −∞ first, then by value, `≥ r` before `> r`.
fn cmp_lo(a: &Lo, b: &Lo) -> Ordering {
    match (a, b) {
        (Lo::NegInf, Lo::NegInf) => Ordering::Equal,
        (Lo::NegInf, _) => Ordering::Less,
        (_, Lo::NegInf) => Ordering::Greater,
        (Lo::Incl(x), Lo::Incl(y)) | (Lo::Excl(x), Lo::Excl(y)) => x.cmp(y),
        (Lo::Incl(x), Lo::Excl(y)) => x.cmp(y).then(Ordering::Less),
        (Lo::Excl(x), Lo::Incl(y)) => x.cmp(y).then(Ordering::Greater),
    }
}

/// The larger of two upper bounds.
fn max_hi(a: Hi, b: Hi) -> Hi {
    if cmp_hi(&a, &b) == Ordering::Less {
        b
    } else {
        a
    }
}

/// A point that is neither covered below `frontier` nor by an interval starting at `lo` (if the
/// two leave a gap), else `None`.
/// Rationals are preferred: a gap with interior gets its simplest interior rational, and only a
/// one-point gap `[a, a]` yields the (possibly irrational) point itself.
fn gap(frontier: Option<&Hi>, lo: &Lo) -> Option<RealAlgebraic> {
    let (a, a_covered, b, b_covered) = match (frontier, lo) {
        (_, Lo::NegInf) | (Some(Hi::PosInf), _) => return None,
        (None, Lo::Incl(b) | Lo::Excl(b)) => {
            return Some(RealAlgebraic::from_rational(below(Some(b))));
        }
        (Some(Hi::Incl(a)), Lo::Incl(b)) => (a, true, b, true),
        (Some(Hi::Incl(a)), Lo::Excl(b)) => (a, true, b, false),
        (Some(Hi::Excl(a)), Lo::Incl(b)) => (a, false, b, true),
        (Some(Hi::Excl(a)), Lo::Excl(b)) => (a, false, b, false),
    };
    match a.cmp(b) {
        Ordering::Less => Some(RealAlgebraic::from_rational(between(a, b))),
        // A one-point gap between two open bounds.
        Ordering::Equal if !a_covered && !b_covered => Some(a.clone()),
        _ => None,
    }
}

/// The finite value of a lower bound.
fn lo_value(l: &Lo) -> Option<&RealAlgebraic> {
    match l {
        Lo::NegInf => None,
        Lo::Incl(r) | Lo::Excl(r) => Some(r),
    }
}

/// The finite value of an upper bound.
fn hi_value(h: &Hi) -> Option<&RealAlgebraic> {
    match h {
        Hi::PosInf => None,
        Hi::Incl(r) | Hi::Excl(r) => Some(r),
    }
}

/// Order of upper bounds: by value, `< r` before `≤ r`, `+∞` last.
fn cmp_hi(a: &Hi, b: &Hi) -> Ordering {
    match (a, b) {
        (Hi::PosInf, Hi::PosInf) => Ordering::Equal,
        (Hi::PosInf, _) => Ordering::Greater,
        (_, Hi::PosInf) => Ordering::Less,
        (Hi::Incl(x), Hi::Incl(y)) | (Hi::Excl(x), Hi::Excl(y)) => x.cmp(y),
        (Hi::Excl(x), Hi::Incl(y)) => x.cmp(y).then(Ordering::Less),
        (Hi::Incl(x), Hi::Excl(y)) => x.cmp(y).then(Ordering::Greater),
    }
}

/// A minimal sub-covering of the line, ordered: greedily, from `−∞`, the interval reaching
/// furthest among those that leave no gap ([ÁDEK21] §4.4.1 `compute_cover`). No chosen interval
/// lies inside another, so both bounds increase strictly along the result — which the
/// single-level characterisation needs for soundness ([ÁDEK21] §4.5). It also gives smaller
/// cores.
fn minimal_cover(cov: &[Excl]) -> Vec<Excl> {
    let mut out: Vec<Excl> = Vec::new();
    let mut frontier: Option<Hi> = None;
    loop {
        let best = cov
            .iter()
            .filter(|e| gap(frontier.as_ref(), &e.lo).is_none())
            .max_by(|a, b| cmp_hi(&a.hi, &b.hi));
        let Some(best) = best else {
            unreachable!("the intervals cover the line");
        };
        if let Some(f) = &frontier {
            assert!(
                cmp_hi(&best.hi, f) == Ordering::Greater,
                "the intervals cover the line"
            );
        }
        frontier = Some(best.hi.clone());
        out.push(best.clone());
        if matches!(best.hi, Hi::PosInf) {
            return out;
        }
    }
}

/// Polynomials sorted into the level `i` and the levels below it, after the standard CAD
/// simplifications ([ÁDEK21] §4.4.3): constants dropped; each polynomial split into its content
/// in its main variable (recursively, one level down) and its square-free primitive part.
#[derive(Default)]
struct Levels {
    main: FxHashSet<MPoly>,
    lower: FxHashSet<MPoly>,
}

impl Levels {
    fn add(&mut self, p: &MPoly, i: usize) {
        if p.is_constant() {
            return;
        }
        let v = p.main_var().unwrap();
        debug_assert!(v <= i);
        let (c, pp) = p.content_primitive_in(v);
        let q = pp.square_free_part_in(v).primitive();
        if v == i {
            self.main.insert(q);
        } else {
            self.lower.insert(q);
        }
        self.add(&c, i);
    }

    /// The level-`i` polynomials as a square-free coprime basis, and the lower ones, sorted.
    fn finish(self, i: usize) -> (Vec<MPoly>, Vec<MPoly>) {
        let mut main: Vec<MPoly> = self.main.into_iter().collect();
        main.sort_by(poly_order);
        let main = coprime_basis(main, i);
        let mut lower: Vec<MPoly> = self.lower.into_iter().collect();
        lower.sort_by(poly_order);
        (main, lower)
    }
}
