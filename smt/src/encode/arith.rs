//! Linear arithmetic: expressions, comparisons, integer equation elimination.

use crate::arith::{normalize, Cmp, Lin, Normal};
use crate::nlarith::PolyCmp;
use crate::sexp::Sexp;
use smtrex_core::Lit;

use super::*;

impl Encoder<'_> {
    /// The linear expression a `Real`-sorted term denotes.
    pub(crate) fn lin(&mut self, t: &Sexp) -> Result<Lin, String> {
        if let Some(b) = self.resolve(t)? {
            return match b {
                Bound::Arith(l) => Ok(l),
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
                    return Ok(Lin::constant(q));
                }
                if !self.sigs.contains_key(a.as_str()) && !self.defs.contains_key(a.as_str()) {
                    if let Some(q) = negative_number(a) {
                        return Ok(Lin::constant(q));
                    }
                }
                let x = match self.real_vars.get(a.as_str()) {
                    Some(&x) => x,
                    None => {
                        let is_int = self.sigs.get(a.as_str()).is_some_and(|(_, s)| s == "Int");
                        let x = self.builder.lra().new_var(is_int);
                        self.real_vars.insert(a.clone(), x);
                        x
                    }
                };
                if let Some(e) = self.subst.get(&x) {
                    return Ok(e.clone());
                }
                return Ok(Lin::var(x));
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
                let mut acc = Lin::default();
                for a in args {
                    acc = acc.add(&self.lin(a)?);
                }
                Ok(acc)
            }
            "-" => {
                let first = self.lin(&args[0])?;
                if args.len() == 1 {
                    return Ok(first.scale(&-smtrex_core::Rational::one()));
                }
                let mut acc = first;
                for a in &args[1..] {
                    acc = acc.sub(&self.lin(a)?);
                }
                Ok(acc)
            }
            "*" => {
                let mut acc = Lin::constant(smtrex_core::Rational::one());
                for a in args {
                    let f = self.lin(a)?;
                    acc = if acc.is_constant() {
                        f.scale(&acc.constant)
                    } else if f.is_constant() {
                        acc.scale(&f.constant)
                    } else {
                        return Err(format!(
                            "non-linear multiplication {t}: SMT-Rex does linear arithmetic only"
                        ));
                    };
                }
                Ok(acc)
            }
            "/" => {
                let mut acc = self.lin(&args[0])?;
                for a in &args[1..] {
                    let d = self.lin(a)?;
                    if !d.is_constant() {
                        return Err(format!(
                            "division by a non-constant in {t}: SMT-Rex does linear arithmetic only"
                        ));
                    }
                    if d.constant.is_zero() {
                        return Err(format!("division by zero in {t} is not supported"));
                    }
                    acc = acc.scale(&d.constant.recip());
                }
                Ok(acc)
            }
            "div" | "mod" => {
                // SMT-LIB's Euclidean division by a non-zero integer constant k: t = k·q + r with
                // 0 ≤ r < |k|. Only q gets a variable; the remainder is the expression t − k·q
                // itself, so no free remainder variable is left for branch and bound to chase.
                let tl = self.lin(&args[0])?;
                let k = self.lin(&args[1])?;
                if !k.is_constant() || !k.constant.is_integer() {
                    return Err(format!(
                        "'{head}' by a non-constant in {t}: SMT-Rex does linear arithmetic only"
                    ));
                }
                if k.constant.is_zero() {
                    return Err(format!("'{head}' by zero in {t} is not supported"));
                }
                let key = (tl.clone(), k.constant.clone());
                let (q, r) = match self.divmods.get(&key) {
                    Some(qr) => qr.clone(),
                    None => {
                        let q = Lin::var(self.builder.lra().new_var(true));
                        let r = tl.sub(&q.scale(&k.constant));
                        let r_lo = self.arith_cmp(&r, Cmp::Ge);
                        let r_hi = self.arith_cmp(
                            &r.sub(&Lin::constant(
                                &k.constant.abs() - &smtrex_core::Rational::one(),
                            )),
                            Cmp::Le,
                        );
                        for l in [r_lo, r_hi] {
                            self.builder.add_clause(vec![l]);
                        }
                        self.divmods.insert(key, (q.clone(), r.clone()));
                        (q, r)
                    }
                };
                Ok(if head == "div" { q } else { r })
            }
            "abs" => {
                let a = self.lin(&args[0])?;
                let v = Lin::var(self.builder.lra().new_var(true));
                let nonneg = self.arith_cmp(&a, Cmp::Ge);
                for (guard, branch) in [
                    (nonneg, a.clone()),
                    (!nonneg, a.scale(&-smtrex_core::Rational::one())),
                ] {
                    let d = v.sub(&branch);
                    let le = self.arith_cmp(&d, Cmp::Le);
                    let ge = self.arith_cmp(&d, Cmp::Ge);
                    self.builder.add_clause(vec![!guard, le]);
                    self.builder.add_clause(vec![!guard, ge]);
                }
                Ok(v)
            }
            "ite" => {
                let c = self.bool(&args[0])?;
                if c == self.true_lit {
                    return self.lin(&args[1]);
                }
                if c == !self.true_lit {
                    return self.lin(&args[2]);
                }
                let a = self.lin(&args[1])?;
                let b = self.lin(&args[2])?;
                if a == b {
                    return Ok(a);
                }
                // A fresh variable v with c -> v = a and !c -> v = b; integer if both branches are.
                let is_int = self.lin_is_int(&a) && self.lin_is_int(&b);
                let v = Lin::var(self.builder.lra().new_var(is_int));
                for (guard, branch) in [(c, a), (!c, b)] {
                    let d = v.sub(&branch);
                    let le = self.arith_cmp(&d, Cmp::Le);
                    let ge = self.arith_cmp(&d, Cmp::Ge);
                    self.builder.add_clause(vec![!guard, le]);
                    self.builder.add_clause(vec![!guard, ge]);
                }
                Ok(v)
            }
            other => Err(format!("unsupported arithmetic operator '{other}'")),
        }
    }

    /// Integer equality elimination: for a top-level `(= a b)` between plain linear integer
    /// terms, solve `a − b = 0` for a variable with coefficient ±1 and substitute it in what is
    /// encoded afterwards. Normalisation then sees the equation's structure in the coefficients,
    /// and branch and bound cannot chase the eliminated variable.
    pub(crate) fn eliminate(&mut self, assertion: &Sexp) -> Result<(), String> {
        let Some([Sexp::Atom(eq), a, b]) = assertion.as_list() else {
            return Ok(());
        };
        if eq != "=" || !self.plain_int(a) || !self.plain_int(b) {
            return Ok(());
        }
        let d = self.lin(a)?.sub(&self.lin(b)?);
        let unit = d.terms.iter().find(|(x, c)| {
            c.abs() == smtrex_core::Rational::one()
                && self.builder.lra().is_int(*x)
                && self.real_vars.values().any(|v| v == x)
        });
        let Some((x, c)) = unit.cloned() else {
            return Ok(());
        };
        // c·x + rest = 0  ⇒  x = −rest / c
        let rest = d.sub(&Lin::var(x).scale(&c));
        let e = rest.scale(&-c.recip());
        // Keep every substitution in terms of variables that are not eliminated.
        for v in self.subst.values_mut() {
            if let Some(k) = v
                .terms
                .iter()
                .find(|(y, _)| *y == x)
                .map(|(_, k)| k.clone())
            {
                *v = v.sub(&Lin::var(x).scale(&k)).add_scaled(&k, &e);
            }
        }
        self.subst.insert(x, e);
        Ok(())
    }

    /// A term built only from declared `Int` constants, numerals, `+`, `-` and `*`.
    pub(crate) fn plain_int(&self, t: &Sexp) -> bool {
        match t {
            Sexp::Atom(a) if a.starts_with(|c: char| c.is_ascii_digit()) => !a.contains('.'),
            Sexp::Atom(a) => {
                self.sigs
                    .get(a.as_str())
                    .is_some_and(|(ps, s)| ps.is_empty() && s == "Int")
                    && self.lookup(a).is_none()
            }
            Sexp::List(l) => match l.first().and_then(Sexp::as_atom) {
                Some("+" | "-" | "*") => l[1..].iter().all(|x| self.plain_int(x)),
                // An ite whose condition is a constant is the branch it picks.
                Some("ite") if l.len() == 4 => match const_bool(&l[1]) {
                    Some(true) => self.plain_int(&l[2]),
                    Some(false) => self.plain_int(&l[3]),
                    None => false,
                },
                _ => false,
            },
        }
    }

    /// The value of an eliminated variable, from the Simplex values of the others.
    pub(crate) fn eliminated_value(
        &self,
        x: smtrex_theory::lra::AVar,
        values: &[smtrex_core::Rational],
    ) -> Option<smtrex_core::Rational> {
        let e = self.subst.get(&x)?;
        Some(e.terms.iter().fold(e.constant.clone(), |acc, (y, c)| {
            values[*y as usize].mul_add(c, &acc)
        }))
    }

    /// Whether every variable of `e` is an integer and every coefficient and the constant are
    /// integral, so `e` only takes integer values.
    pub(crate) fn lin_is_int(&mut self, e: &Lin) -> bool {
        e.constant.is_integer()
            && e.terms
                .iter()
                .all(|(x, c)| c.is_integer() && self.builder.lra().is_int(*x))
    }

    /// The literal for `e ⋈ 0`.
    pub(crate) fn arith_cmp(&mut self, e: &Lin, cmp: Cmp) -> Lit {
        let int_vars = e.terms.iter().all(|(x, _)| self.builder.lra().is_int(*x));
        match normalize(e, cmp, int_vars) {
            Normal::Const(true) => self.true_lit,
            Normal::Const(false) => !self.true_lit,
            Normal::Atom {
                term,
                kind,
                c,
                negated,
            } => {
                let x = self.builder.lra().term_var(&term);
                let l = self.builder.bound_atom(x, kind, c);
                if negated {
                    !l
                } else {
                    l
                }
            }
        }
    }

    /// The literal for `e = 0`, as `e ≤ 0 ∧ e ≥ 0`.
    pub(crate) fn arith_eq(&mut self, e: &Lin) -> Lit {
        let le = self.arith_cmp(e, Cmp::Le);
        let ge = self.arith_cmp(e, Cmp::Ge);
        self.tseitin_and(vec![le, ge])
    }

    /// `(<= a b c ...)` and friends: the conjunction over adjacent pairs.
    pub(crate) fn compare(&mut self, head: &str, args: &[Sexp]) -> Result<Lit, String> {
        if self.nra {
            let cmp = match head {
                "<=" => PolyCmp::Le,
                "<" => PolyCmp::Lt,
                ">=" => PolyCmp::Ge,
                _ => PolyCmp::Gt,
            };
            let ps = args
                .iter()
                .map(|a| self.rpoly(a))
                .collect::<Result<Vec<_>, _>>()?;
            let mut conj = Vec::with_capacity(ps.len() - 1);
            for w in ps.windows(2) {
                conj.push(self.poly_cmp(&w[0].sub(&w[1]), cmp));
            }
            return Ok(self.tseitin_and(conj));
        }
        let cmp = match head {
            "<=" => Cmp::Le,
            "<" => Cmp::Lt,
            ">=" => Cmp::Ge,
            _ => Cmp::Gt,
        };
        let lins = args
            .iter()
            .map(|a| self.lin(a))
            .collect::<Result<Vec<_>, _>>()?;
        let mut conj = Vec::with_capacity(lins.len() - 1);
        for w in lins.windows(2) {
            conj.push(self.arith_cmp(&w[0].sub(&w[1]), cmp));
        }
        Ok(self.tseitin_and(conj))
    }
}
