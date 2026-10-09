//! Sort checking of terms against the declarations in scope.

use crate::bv::{self, Op};
use crate::sexp::Sexp;

use super::Script;

/// The sort of a numeral literal such as `3`: it adapts to `Int` or `Real` from context.
pub(crate) const NUMERAL: &str = "Numeral";

/// The common sort of two sorts, letting a numeral take the sort of the other side.
pub(crate) fn unify(a: &str, b: &str) -> Option<String> {
    if a == b {
        Some(a.to_string())
    } else if a == NUMERAL && (b == "Int" || b == "Real") {
        Some(b.to_string())
    } else if b == NUMERAL && (a == "Int" || a == "Real") {
        Some(a.to_string())
    } else {
        None
    }
}

pub(crate) fn is_arith(sort: &str) -> bool {
    matches!(sort, "Int" | "Real" | NUMERAL)
}

/// The value of a negative numeral or decimal written as one token, `-2` or `-1.5`. Strictly
/// these are simple symbols in SMT-LIB, but z3 reads them as numbers, and benchmarks rely on
/// it; SMT-Rex does too, for symbols that are not declared.
pub(crate) fn negative_number(a: &str) -> Option<smtrex_core::Rational> {
    let rest = a.strip_prefix('-')?;
    if !rest.starts_with(|c: char| c.is_ascii_digit()) {
        return None;
    }
    smtrex_core::Rational::parse_decimal(rest).map(|q| -q)
}

impl Script {
    /// Sort-check `t` and return its sort. `local` holds the `let`-bound and parameter names in
    /// scope (innermost last). With `register_names`, `(! t :named n)` declares `n` (assertions
    /// only; elsewhere names are rejected).
    pub(super) fn check_term(
        &mut self,
        t: &Sexp,
        local: &mut Vec<(String, String)>,
        register_names: bool,
    ) -> Result<String, String> {
        let list = match t {
            Sexp::Atom(a) => return self.check_symbol(a, local),
            Sexp::List(l) => l,
        };
        if let Some(s) = self.check_bv(t, local, register_names)? {
            return Ok(s);
        }
        let Some(Sexp::Atom(head)) = list.first() else {
            return Err(format!("cannot apply {t}"));
        };
        let args = &list[1..];
        let bool_s = || "Bool".to_string();
        match head.as_str() {
            "not" | "and" | "or" | "=>" | "xor" => {
                let need = if head == "not" { 1..=1 } else { 1..=usize::MAX };
                if !need.contains(&args.len()) {
                    return Err(format!("wrong number of arguments to '{head}' in {t}"));
                }
                for a in args {
                    let s = self.check_term(a, local, register_names)?;
                    if s != "Bool" {
                        return Err(format!("'{head}' expects Bool arguments, got {s} in {t}"));
                    }
                }
                Ok(bool_s())
            }
            "=" | "distinct" => {
                if args.len() < 2 {
                    return Err(format!("'{head}' needs at least two arguments in {t}"));
                }
                let mut sort = self.check_term(&args[0], local, register_names)?;
                for a in &args[1..] {
                    let s = self.check_term(a, local, register_names)?;
                    sort = unify(&sort, &s)
                        .ok_or_else(|| format!("'{head}' mixes sorts {sort} and {s} in {t}"))?;
                }
                Ok(bool_s())
            }
            "ite" => {
                let [c, a, b] = args else {
                    return Err(format!("'ite' expects 3 arguments in {t}"));
                };
                if self.check_term(c, local, register_names)? != "Bool" {
                    return Err(format!("the condition of 'ite' must be a Bool in {t}"));
                }
                let sa = self.check_term(a, local, register_names)?;
                let sb = self.check_term(b, local, register_names)?;
                unify(&sa, &sb)
                    .ok_or_else(|| format!("the branches of 'ite' have sorts {sa} and {sb} in {t}"))
            }
            "let" => {
                let [Sexp::List(bindings), body] = args else {
                    return Err(format!("malformed let: {t}"));
                };
                if bindings.is_empty() {
                    return Err("let needs at least one binding".to_string());
                }
                let mut bound = Vec::with_capacity(bindings.len());
                for b in bindings {
                    let Some([Sexp::Atom(name), expr]) = b.as_list() else {
                        return Err(format!("malformed let binding {b}"));
                    };
                    if bound.iter().any(|(n, _)| n == name) {
                        return Err(format!("'{name}' is bound twice in one let"));
                    }
                    bound.push((name.clone(), self.check_term(expr, local, register_names)?));
                }
                let depth = local.len();
                local.extend(bound);
                let s = self.check_term(body, local, register_names);
                local.truncate(depth);
                s
            }
            "!" => {
                let Some((inner, attrs)) = args.split_first() else {
                    return Err("'!' expects a term".to_string());
                };
                let s = self.check_term(inner, local, register_names)?;
                for w in attrs.windows(2) {
                    if let [Sexp::Atom(k), Sexp::Atom(n)] = w {
                        if k == ":named" {
                            if !register_names {
                                return Err(":named is only allowed in assertions".to_string());
                            }
                            self.fresh_symbol(n)?;
                            self.named.insert(n.clone(), s.clone());
                            let n = n.clone();
                            self.frame().named.push(n);
                        }
                    }
                }
                Ok(s)
            }
            "+" | "-" | "*" | "/" | "<=" | "<" | ">=" | ">" | "div" | "mod" | "abs" => {
                let comparison = matches!(head.as_str(), "<=" | "<" | ">=" | ">");
                let (min, max) = match head.as_str() {
                    "abs" => (1, 1),
                    "div" | "mod" => (2, 2),
                    "/" | "<=" | "<" | ">=" | ">" => (2, usize::MAX),
                    _ => (1, usize::MAX),
                };
                if args.len() < min || args.len() > max {
                    return Err(format!("wrong number of arguments to '{head}' in {t}"));
                }
                let mut sort = NUMERAL.to_string();
                for a in args {
                    let s = self.check_term(a, local, register_names)?;
                    if !is_arith(&s) {
                        return Err(format!(
                            "'{head}' expects numeric arguments, got {s} in {t}"
                        ));
                    }
                    sort = unify(&sort, &s).ok_or_else(|| {
                        format!("'{head}' mixes Int and Real in {t}; QF_LIRA is not supported")
                    })?;
                }
                let int_only = matches!(head.as_str(), "div" | "mod" | "abs");
                if int_only && sort == "Real" {
                    return Err(format!("'{head}' is only defined on Int, in {t}"));
                }
                if head == "/" && sort == "Int" {
                    return Err(format!("'/' is real division; use div on Int, in {t}"));
                }
                Ok(if comparison {
                    bool_s()
                } else if int_only {
                    "Int".to_string()
                } else if head == "/" {
                    "Real".to_string()
                } else {
                    sort
                })
            }
            f => {
                let (params, ret): (Vec<String>, String) = if let Some(d) = self.defs.get(f) {
                    (
                        d.params.iter().map(|(_, s)| s.clone()).collect(),
                        d.ret.clone(),
                    )
                } else if let Some((ps, r)) = self.sigs.get(f) {
                    (ps.clone(), r.clone())
                } else if local.iter().any(|(n, _)| n == f) {
                    return Err(format!("'{f}' is a variable, not a function, in {t}"));
                } else {
                    return Err(format!("unknown function '{f}'"));
                };
                if params.len() != args.len() {
                    return Err(format!(
                        "'{f}' expects {} arguments, got {} in {t}",
                        params.len(),
                        args.len()
                    ));
                }
                for (a, p) in args.iter().zip(&params) {
                    let s = self.check_term(a, local, register_names)?;
                    if unify(&s, p).as_deref() != Some(p.as_str()) {
                        return Err(format!(
                            "'{f}' expects an argument of sort {p}, got {s} in {t}"
                        ));
                    }
                }
                Ok(ret)
            }
        }
    }

    /// Sort-check a bit-vector literal or operator application; `None` if `t` is neither.
    pub(super) fn check_bv(
        &mut self,
        t: &Sexp,
        local: &mut Vec<(String, String)>,
        register_names: bool,
    ) -> Result<Option<String>, String> {
        if let Some((_, w)) = bv::literal(t)? {
            return Ok(Some(bv::sort_name(w)));
        }
        let Sexp::List(l) = t else {
            return Ok(None);
        };
        let Some(op) = l.first().map(Op::parse).transpose()?.flatten() else {
            return Ok(None);
        };
        let mut widths = Vec::with_capacity(l.len() - 1);
        for a in &l[1..] {
            let s = self.check_term(a, local, register_names)?;
            let w = bv::width(&s).ok_or_else(|| {
                format!("'{}' expects bit-vector arguments, got {s} in {t}", l[0])
            })?;
            widths.push(w);
        }
        let ret = op.check(&widths).map_err(|e| format!("{e} in {t}"))?;
        Ok(Some(ret.sort_name()))
    }

    pub(super) fn check_symbol(
        &self,
        a: &str,
        local: &[(String, String)],
    ) -> Result<String, String> {
        if a == "true" || a == "false" {
            return Ok("Bool".to_string());
        }
        if let Some((_, w)) = bv::literal(&Sexp::Atom(a.to_string()))? {
            return Ok(bv::sort_name(w));
        }
        if let Some((_, s)) = local.iter().rev().find(|(n, _)| n == a) {
            return Ok(s.clone());
        }
        if let Some(s) = self.named.get(a) {
            return Ok(s.clone());
        }
        let (params, ret) = if let Some(d) = self.defs.get(a) {
            (d.params.len(), &d.ret)
        } else if let Some((ps, r)) = self.sigs.get(a) {
            (ps.len(), r)
        } else if a.starts_with(|c: char| c.is_ascii_digit()) {
            return match smtrex_core::Rational::parse_decimal(a) {
                Some(_) if a.contains('.') => Ok("Real".to_string()),
                Some(_) => Ok(NUMERAL.to_string()),
                None => Err(format!("'{a}' is not a numeral or decimal")),
            };
        } else if negative_number(a).is_some() {
            return Ok(if a.contains('.') {
                "Real".to_string()
            } else {
                NUMERAL.to_string()
            });
        } else {
            return Err(format!("unknown symbol '{a}'"));
        };
        if params != 0 {
            return Err(format!(
                "'{a}' is a function of {params} arguments; apply it"
            ));
        }
        Ok(ret.clone())
    }
}
