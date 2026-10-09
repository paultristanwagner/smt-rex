//! QF_NRA: polynomial atoms, their linear abstraction, and real equation elimination.

use crate::arith::{Cmp, Lin};
use crate::nlarith::{normalize as nl_normalize, PolyCmp, PolyNormal, RPoly};
use crate::sexp::Sexp;
use smtrex_core::Lit;
use smtrex_nra::AtomKind;
use smtrex_poly::MPoly;

use super::*;

impl Encoder<'_> {
    /// The polynomial a `Real`-sorted term denotes (QF_NRA).
    pub(crate) fn rpoly(&mut self, t: &Sexp) -> Result<RPoly, String> {
        if let Some(b) = self.resolve(t)? {
            return match b {
                Bound::Poly(p) => Ok(p),
                other => Err(format!(
                    "expected a Real, got a value of sort {}",
                    other.sort()
                )),
            };
        }
        let l = match t {
            Sexp::Atom(a) => {
                if a.starts_with(|c: char| c.is_ascii_digit()) {
                    let q = smtrex_core::Rational::parse_decimal(a)
                        .ok_or_else(|| format!("'{a}' is not a number"))?;
                    return Ok(RPoly::constant(&q));
                }
                let declared = self.sigs.get(a.as_str());
                if declared.is_none() && !self.defs.contains_key(a.as_str()) {
                    if let Some(q) = negative_number(a) {
                        return Ok(RPoly::constant(&q));
                    }
                }
                if declared.is_some_and(|(_, s)| s == "Int") {
                    return Err(format!(
                        "'{a}' is an Int: QF_NRA is real arithmetic (QF_NIA is not supported)"
                    ));
                }
                let v = match self.poly_vars.get(a.as_str()) {
                    Some(&v) => v,
                    None => {
                        let v = self.builder.nra().new_var();
                        self.poly_vars.insert(a.clone(), v);
                        v
                    }
                };
                if let Some(e) = self.poly_subst.get(&v) {
                    return Ok(e.clone());
                }
                return Ok(RPoly::var(v));
            }
            Sexp::List(l) => l,
        };
        let head = l
            .first()
            .and_then(Sexp::as_atom)
            .ok_or("empty application")?;
        let args = &l[1..];
        match head {
            "+" => {
                let mut acc = RPoly::constant(&smtrex_core::Rational::zero());
                for a in args {
                    acc = acc.add(&self.rpoly(a)?);
                }
                Ok(acc)
            }
            "-" => {
                let first = self.rpoly(&args[0])?;
                if args.len() == 1 {
                    return Ok(first.neg());
                }
                let mut acc = first;
                for a in &args[1..] {
                    acc = acc.sub(&self.rpoly(a)?);
                }
                Ok(acc)
            }
            "*" => {
                let mut acc = RPoly::constant(&smtrex_core::Rational::one());
                for a in args {
                    acc = acc.mul(&self.rpoly(a)?);
                }
                Ok(acc)
            }
            "/" => {
                let mut acc = self.rpoly(&args[0])?;
                for a in &args[1..] {
                    let d = self.rpoly(a)?;
                    let Some(c) = d.as_constant() else {
                        return Err(format!(
                            "division by the non-constant {a} in {t}: SMT-Rex supports `/` by \
                             constants only"
                        ));
                    };
                    if c.is_zero() {
                        return Err(format!("division by zero in {t} is not supported"));
                    }
                    acc = acc.scale(&c.recip());
                }
                Ok(acc)
            }
            "ite" => {
                let c = self.bool(&args[0])?;
                if c == self.true_lit {
                    return self.rpoly(&args[1]);
                }
                if c == !self.true_lit {
                    return self.rpoly(&args[2]);
                }
                let a = self.rpoly(&args[1])?;
                let b = self.rpoly(&args[2])?;
                if a == b {
                    return Ok(a);
                }
                // A fresh variable v with c -> v = a and !c -> v = b.
                let v = RPoly::var(self.builder.nra().new_var());
                for (guard, branch) in [(c, a), (!c, b)] {
                    let eq = self.poly_cmp(&v.sub(&branch), PolyCmp::Eq);
                    self.builder.add_clause(vec![!guard, eq]);
                }
                Ok(v)
            }
            "div" | "mod" | "abs" => Err(format!(
                "'{head}' is integer arithmetic: QF_NRA is real arithmetic, in {t}"
            )),
            other => Err(format!("unsupported arithmetic operator '{other}'")),
        }
    }

    /// The literal for `e ⋈ 0` (QF_NRA).
    pub(crate) fn poly_cmp(&mut self, e: &RPoly, cmp: PolyCmp) -> Lit {
        match nl_normalize(e, cmp) {
            PolyNormal::Const(true) => self.true_lit,
            PolyNormal::Const(false) => !self.true_lit,
            PolyNormal::Atom {
                poly,
                kind,
                negated,
            } => {
                let l = self.builder.poly_atom(poly.clone(), kind);
                if self.linear_abstraction && self.abstracted.insert(l.var()) {
                    self.link_linear_abstraction(&poly, kind, l);
                }
                if negated {
                    !l
                } else {
                    l
                }
            }
        }
    }

    /// Tie the NRA atom `atom ⟺ (poly kind 0)` to its linear abstraction: every monomial is an
    /// LRA variable, so `poly` is a linear term `ℓ` and `atom ⟺ ℓ kind 0`. Any real point
    /// satisfies the abstraction, so every Simplex conflict is a conflict of the original
    /// constraints; the NRA theory still decides each atom exactly.
    pub(crate) fn link_linear_abstraction(&mut self, poly: &MPoly, kind: AtomKind, atom: Lit) {
        let mut lin = Lin::default();
        for (m, c) in poly.terms() {
            let c =
                smtrex_core::Rational::from_big(num_rational::BigRational::from_integer(c.clone()));
            if m.is_empty() {
                lin = lin.add(&Lin::constant(c));
                continue;
            }
            let x = match self.monomials.get(m) {
                Some(&x) => x,
                None => {
                    let x = self.builder.lra().new_var(false);
                    self.monomials.insert(m.clone(), x);
                    x
                }
            };
            lin = lin.add_scaled(&c, &Lin::var(x));
        }
        let l = match kind {
            AtomKind::Eq => self.arith_eq(&lin),
            AtomKind::Lt => self.arith_cmp(&lin, Cmp::Lt),
            AtomKind::Gt => self.arith_cmp(&lin, Cmp::Gt),
        };
        self.builder.add_clause(vec![!atom, l]);
        self.builder.add_clause(vec![atom, !l]);
    }

    // ----- arithmetic -----

    /// Real equation elimination (QF_NRA): for a top-level `(= a b)` between plain real terms,
    /// solve `a − b = 0` for a variable it contains linearly with a constant coefficient and
    /// substitute the solution; the eliminated value is recomputed for the model. Solutions
    /// over `SMTREX_NRA_ELIM_TERMS` terms (default 64) are skipped; `0` disables it.
    pub(crate) fn eliminate_real(&mut self, assertion: &Sexp) -> Result<(), String> {
        let limit: usize = std::env::var("SMTREX_NRA_ELIM_TERMS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(64);
        let Some([Sexp::Atom(eq), a, b]) = assertion.as_list() else {
            return Ok(());
        };
        if limit == 0 || eq != "=" || !self.plain_real(a) || !self.plain_real(b) {
            return Ok(());
        }
        let d = self.rpoly(a)?.sub(&self.rpoly(b)?);
        let Some((x, e)) = d.solve_linear() else {
            return Ok(());
        };
        if e.num.num_terms() > limit {
            return Ok(());
        }
        // Keep every substitution in terms of variables that are not eliminated.
        for v in self.poly_subst.values_mut() {
            if v.num.has_var(x) {
                *v = v.substitute(x, &e);
            }
        }
        self.poly_subst.insert(x, e);
        Ok(())
    }

    /// A term built only from declared `Real` constants, numerals, decimals, `+`, `-`, `*` and
    /// `/` by a numeral.
    pub(crate) fn plain_real(&self, t: &Sexp) -> bool {
        match t {
            Sexp::Atom(a) if a.starts_with(|c: char| c.is_ascii_digit()) => true,
            Sexp::Atom(a) => {
                self.sigs
                    .get(a.as_str())
                    .is_some_and(|(ps, s)| ps.is_empty() && s == "Real")
                    && self.lookup(a).is_none()
            }
            Sexp::List(l) => match l.first().and_then(Sexp::as_atom) {
                Some("+" | "-" | "*") => l[1..].iter().all(|x| self.plain_real(x)),
                Some("/") if l.len() >= 3 => {
                    self.plain_real(&l[1])
                        && l[2..].iter().all(|x| {
                            matches!(x, Sexp::Atom(a) if a.starts_with(|c: char| c.is_ascii_digit()))
                        })
                }
                _ => false,
            },
        }
    }
}
