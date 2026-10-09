//! Linear arithmetic: atoms tied to the Simplex's normal form, and Farkas coefficients.

use crate::arith::{normalize, real_literal, Cmp, Lin, Normal};
use crate::sexp::{quote_symbol, Sexp};
use rustc_hash::FxHashMap;
use smtrex_core::{Lit, Rational, Theory, Var};
use smtrex_theory::lra::{AVar, BoundKind, Lra};

use super::*;

impl Encoder<'_> {
    /// The linear expression a `Real` term denotes.
    pub(super) fn lin(&mut self, t: &Sexp) -> Result<Lin, String> {
        match t {
            Sexp::Atom(a) if a.starts_with(|c: char| c.is_ascii_digit()) => {
                let q =
                    Rational::parse_decimal(a).ok_or_else(|| format!("'{a}' is not a number"))?;
                Ok(Lin::constant(q))
            }
            Sexp::Atom(a) => {
                if self.problem.sort_of(t)? != "Real" {
                    return Err(format!("'{a}' is not a Real"));
                }
                let x = match self.real_vars.get(a) {
                    Some(&x) => x,
                    None => {
                        let x = self.b.lra().new_var(false);
                        self.real_vars.insert(a.clone(), x);
                        self.real_names.insert(x, quote_symbol(a).into_owned());
                        x
                    }
                };
                Ok(Lin::var(x))
            }
            Sexp::List(l) => {
                let head = l.first().and_then(Sexp::as_atom).ok_or("malformed term")?;
                let args = &l[1..];
                match head {
                    "+" => {
                        let mut acc = Lin::default();
                        for a in args {
                            acc = acc.add(&self.lin(a)?);
                        }
                        Ok(acc)
                    }
                    "-" if args.len() == 1 => Ok(self.lin(&args[0])?.scale(&-Rational::one())),
                    "-" => {
                        let mut acc = self.lin(&args[0])?;
                        for a in &args[1..] {
                            acc = acc.sub(&self.lin(a)?);
                        }
                        Ok(acc)
                    }
                    "*" => {
                        let mut acc = Lin::constant(Rational::one());
                        for a in args {
                            let x = self.lin(a)?;
                            acc = if acc.is_constant() {
                                x.scale(&acc.constant)
                            } else if x.is_constant() {
                                acc.scale(&x.constant)
                            } else {
                                return Err(format!("{t} is not linear"));
                            };
                        }
                        Ok(acc)
                    }
                    "/" => {
                        let mut acc = self.lin(&args[0])?;
                        for a in &args[1..] {
                            let d = self.lin(a)?;
                            if !d.is_constant() || d.constant.is_zero() {
                                return Err(format!("{t}: division by a non-constant or zero"));
                            }
                            acc = acc.scale(&d.constant.recip());
                        }
                        Ok(acc)
                    }
                    "ite" if args.len() == 3 => self.arith_ite(t, args),
                    _ => Err(format!(
                        "'{head}' in arithmetic is not supported with proofs yet"
                    )),
                }
            }
        }
    }

    /// An arithmetic `ite` term `T = (ite c a b)`: a Simplex variable written as `T` itself
    /// (opaque to `la_generic`), with `c → T = a` and `¬c → T = b` from `ite_intro`.
    pub(super) fn arith_ite(&mut self, t: &Sexp, args: &[Sexp]) -> Result<Lin, String> {
        let key = real_text(t);
        if let Some(&x) = self.real_vars.get(&key) {
            return Ok(Lin::var(x));
        }
        let x = self.b.lra().new_var(false);
        self.real_vars.insert(key.clone(), x);
        self.real_names.insert(x, key.clone());
        let c = self.lit(&args[0])?;
        let (ta, tb) = (real_text(&args[1]), real_text(&args[2]));
        let eq_a = self.arith_eq(&format!("(= {key} {ta})"), t, &args[1])?;
        let eq_b = self.arith_eq(&format!("(= {key} {tb})"), t, &args[2])?;
        let u = format!(
            "(ite {} {} {})",
            self.render(c),
            self.render(eq_a),
            self.render(eq_b)
        );
        let ite = key;
        self.clause(
            vec![N(c), L(eq_a)],
            How::Ite {
                ite: ite.clone(),
                u: u.clone(),
                then: true,
            },
        );
        self.clause(
            vec![L(c), L(eq_b)],
            How::Ite {
                ite,
                u,
                then: false,
            },
        );
        Ok(Lin::var(x))
    }

    /// The literal of the Simplex atom for `e ⋈ 0`, or `None` if it has no variables. The
    /// atom's term is written in the theory's normal form.
    pub(super) fn bound_lit(&mut self, e: &Lin, cmp: Cmp) -> Option<Lit> {
        let Normal::Atom {
            term,
            kind,
            c,
            negated,
        } = normalize(e, cmp, false)
        else {
            return None;
        };
        let x = self.b.lra().term_var(&term);
        let l = self.b.bound_atom(x, kind, c.clone());
        if self
            .terms
            .get(l.var().index())
            .and_then(Option::as_ref)
            .is_none()
        {
            let text = self.bound_text(&term, kind, &c);
            self.set_term(l.var(), text, false);
        }
        Some(if negated { !l } else { l })
    }

    pub(super) fn bound_text(
        &self,
        term: &[(AVar, Rational)],
        kind: BoundKind,
        c: &Rational,
    ) -> String {
        let op = match kind {
            BoundKind::Le => "<=",
            BoundKind::Ge => ">=",
        };
        format!("({op} {} {})", self.sum_text(term), real_literal(c))
    }

    pub(super) fn sum_text(&self, term: &[(AVar, Rational)]) -> String {
        let parts: Vec<String> = term
            .iter()
            .map(|(x, a)| {
                let name = &self.real_names[x];
                if *a == Rational::one() {
                    name.clone()
                } else {
                    format!("(* {} {name})", real_literal(a))
                }
            })
            .collect();
        match parts.len() {
            1 => parts.into_iter().next().unwrap(),
            _ => format!("(+ {})", parts.join(" ")),
        }
    }

    /// An inequality atom written `key` in the input, meaning `e ⋈ 0`: the Simplex atom itself
    /// if it is written that way, else a variable tied to it by two `la_generic` clauses.
    pub(super) fn arith_atom(&mut self, key: &str, e: Lin, cmp: Cmp) -> Lit {
        let target = self.bound_lit(&e, cmp);
        if let Some(t) = target {
            if !t.is_negated() && self.render(t) == key {
                return t;
            }
        }
        let r = self.new_leaf(key.to_string());
        let truth = matches!(normalize(&e, cmp, false), Normal::Const(true));
        self.meanings.insert(r.var(), (e, Rel::Cmp(cmp)));
        match target {
            Some(t) => {
                self.clause(vec![L(!r), L(t)], How::Lra);
                self.clause(vec![L(r), L(!t)], How::Lra);
            }
            // No variables: the atom is simply true or false.
            None => self.clause(vec![L(if truth { r } else { !r })], How::Lra),
        }
        r
    }

    /// `(= a b)` over the reals: tied to the two Simplex atoms `a − b ≤ 0` and `a − b ≥ 0`;
    /// the direction from the bounds back to the equality is `la_disequality`.
    pub(super) fn arith_eq(&mut self, key: &str, a: &Sexp, b: &Sexp) -> Result<Lit, String> {
        let e = self.lin(a)?.sub(&self.lin(b)?);
        let r = self.new_leaf(key.to_string());
        self.meanings.insert(r.var(), (e.clone(), Rel::Eq));
        let (ta, tb) = (real_text(a), real_text(b));
        let p = self.new_leaf(format!("(<= {ta} {tb})"));
        self.meanings
            .insert(p.var(), (e.clone(), Rel::Cmp(Cmp::Le)));
        let q = self.new_leaf(format!("(<= {tb} {ta})"));
        self.meanings
            .insert(q.var(), (e.scale(&-Rational::one()), Rel::Cmp(Cmp::Le)));
        self.clause(vec![L(r), L(!p), L(!q)], How::Diseq);
        match (self.bound_lit(&e, Cmp::Le), self.bound_lit(&e, Cmp::Ge)) {
            (Some(le), Some(ge)) => {
                self.clause(vec![L(!r), L(le)], How::Lra);
                self.clause(vec![L(!r), L(ge)], How::Lra);
                self.clause(vec![L(!le), L(p)], How::Lra);
                self.clause(vec![L(!ge), L(q)], How::Lra);
            }
            // a − b is a constant: the sides are equal everywhere (both bounds hold) or nowhere.
            _ if e.constant.is_zero() => {
                self.clause(vec![L(p)], How::Lra);
                self.clause(vec![L(q)], How::Lra);
            }
            _ => self.clause(vec![L(!r)], How::Lra),
        }
        Ok(r)
    }

    /// The linear constraint a variable stands for.
    pub(super) fn meaning(&self, v: Var) -> Option<(Lin, Rel)> {
        if let Some((e, rel)) = self.meanings.get(&v) {
            return Some((e.clone(), *rel));
        }
        let (term, kind, c) = self.b.lra_ref().atom_of(v)?;
        let mut e = Lin::constant(-c);
        for (x, a) in term {
            e = e.add_scaled(&a, &Lin::var(x));
        }
        let cmp = match kind {
            BoundKind::Le => Cmp::Le,
            BoundKind::Ge => Cmp::Ge,
        };
        Some((e, Rel::Cmp(cmp)))
    }

    /// Farkas coefficients for the clause `lits`, as `la_generic` expects them: the negation of
    /// each literal, written `lin (≤|<|=) 0`, times its coefficient (nonnegative except for
    /// equalities), sums to a false constant comparison. Found by a linear program on a fresh
    /// Simplex, so a clause that does not follow is reported instead of certified.
    pub(super) fn farkas(&self, lits: &[Lit]) -> Result<Vec<Rational>, String> {
        // (lin, strict, equality) of each negated literal, oriented to ≤ / <.
        let mut rows: Vec<(Lin, bool, bool)> = Vec::new();
        for &l in lits {
            let (e, rel) = self
                .meaning(l.var())
                .ok_or_else(|| format!("{} is not arithmetic", self.render(l)))?;
            let cmp = match rel {
                Rel::Cmp(cmp) => cmp,
                Rel::Eq if l.is_negated() => {
                    rows.push((e, false, true));
                    continue;
                }
                Rel::Eq => return Err("a positive equality in an arithmetic lemma".to_string()),
            };
            // The literal true means `e cmp 0`; its negation is the opposite comparison.
            let neg = if l.is_negated() {
                cmp
            } else {
                match cmp {
                    Cmp::Le => Cmp::Gt,
                    Cmp::Lt => Cmp::Ge,
                    Cmp::Ge => Cmp::Lt,
                    Cmp::Gt => Cmp::Le,
                }
            };
            let minus = -Rational::one();
            rows.push(match neg {
                Cmp::Le => (e, false, false),
                Cmp::Lt => (e, true, false),
                Cmp::Ge => (e.scale(&minus), false, false),
                Cmp::Gt => (e.scale(&minus), true, false),
            });
        }
        let ys = solve_farkas(&rows).ok_or_else(|| {
            format!(
                "arithmetic clause {} does not follow",
                self.render_clause(lits)
            )
        })?;
        // Carcara reads each negated inequality in `≥`/`>` form, the negation of the `≤`/`<`
        // rows above, and an equality as written: so only the equalities' signs change.
        Ok(ys
            .into_iter()
            .zip(&rows)
            .map(|(y, (_, _, eq))| if *eq { -y } else { y })
            .collect())
    }
}

/// Coefficients `y` for the rows `(lin, strict, equality)` (each meaning `lin ≤ 0`, `< 0` or
/// `= 0`) with `Σ y·lin` free of variables and `Σ y·lin ≤ 0` false: `y ≥ 0` except on
/// equalities, and either the constant sum is positive, or zero with a strict row in the
/// combination. Two linear programs on a fresh Simplex.
pub(super) fn solve_farkas(rows: &[(Lin, bool, bool)]) -> Option<Vec<Rational>> {
    let strict: Vec<usize> = (0..rows.len()).filter(|&i| rows[i].1).collect();
    // First a positive constant, then (with a strict row) a zero one.
    if let Some(y) = farkas_lp(rows, false, &[]) {
        return Some(y);
    }
    if strict.is_empty() {
        return None;
    }
    farkas_lp(rows, true, &strict)
}

pub(super) fn farkas_lp(
    rows: &[(Lin, bool, bool)],
    zero: bool,
    strict: &[usize],
) -> Option<Vec<Rational>> {
    let mut lp = Lra::new();
    let mut sat = 0usize;
    let mut assert = |lp: &mut Lra, x: AVar, kind: BoundKind, c: Rational| {
        let v = Var::from_index(sat);
        sat += 1;
        lp.register_atom(v, x, kind, c);
        lp.assert(v.pos());
    };
    let ys: Vec<AVar> = rows.iter().map(|_| lp.new_var(false)).collect();
    for (i, (_, _, eq)) in rows.iter().enumerate() {
        if !eq {
            assert(&mut lp, ys[i], BoundKind::Ge, Rational::zero());
        }
    }
    // Σ y·coefficient = 0 for every variable.
    let mut columns: FxHashMap<AVar, Vec<(AVar, Rational)>> = FxHashMap::default();
    for (i, (lin, _, _)) in rows.iter().enumerate() {
        for (x, a) in &lin.terms {
            columns.entry(*x).or_default().push((ys[i], a.clone()));
        }
    }
    for col in columns.values() {
        let s = lp.term_var(col);
        assert(&mut lp, s, BoundKind::Le, Rational::zero());
        assert(&mut lp, s, BoundKind::Ge, Rational::zero());
    }
    // The constant: Σ y·k ≥ 1, or = 0 with Σ (strict y) ≥ 1.
    let constant: Vec<(AVar, Rational)> = rows
        .iter()
        .enumerate()
        .filter(|(_, (lin, _, _))| !lin.constant.is_zero())
        .map(|(i, (lin, _, _))| (ys[i], lin.constant.clone()))
        .collect();
    if zero {
        if !constant.is_empty() {
            let k = lp.term_var(&constant);
            assert(&mut lp, k, BoundKind::Le, Rational::zero());
            assert(&mut lp, k, BoundKind::Ge, Rational::zero());
        }
        let s: Vec<(AVar, Rational)> = strict.iter().map(|&i| (ys[i], Rational::one())).collect();
        let t = lp.term_var(&s);
        assert(&mut lp, t, BoundKind::Ge, Rational::one());
    } else {
        if constant.is_empty() {
            return None;
        }
        let k = lp.term_var(&constant);
        assert(&mut lp, k, BoundKind::Ge, Rational::one());
    }
    lp.check(true).ok()?;
    let model = lp.model();
    Some(ys.iter().map(|&y| model[y as usize].clone()).collect())
}

/// An arithmetic term as text with its integer numerals written as reals (`3` as `3.0`):
/// QF_LRA has no integers, and Carcara accepts integer literals only in the problem file.
pub(super) fn real_text(t: &Sexp) -> String {
    fn go(t: &Sexp) -> Sexp {
        match t {
            Sexp::Atom(a) if !a.is_empty() && a.bytes().all(|b| b.is_ascii_digit()) => {
                Sexp::Atom(format!("{a}.0"))
            }
            Sexp::Atom(_) => t.clone(),
            Sexp::List(l) => Sexp::List(l.iter().map(go).collect()),
        }
    }
    go(t).to_string()
}
