use super::{Atoms, Formula, Linear, Rel, Term};
use smtrex_core::Rational;
use smtrex_smt::sexp::Sexp;

/// An SMT-LIB rendering of a parsed formula: declarations plus one assertion. User names are
/// kept as they are unless they collide with an SMT-LIB reserved word, in which case they get a
/// suffix no identifier in the short language can contain (see [`Smt::symbol`]).
pub struct Smt {
    pub commands: Vec<Sexp>,
}

impl Smt {
    /// The SMT-LIB symbol used for user name `name`.
    pub fn symbol(&self, name: &str) -> String {
        smt_symbol(name)
    }

    /// `t` as an SMT-LIB term.
    pub fn term(&self, t: &Term) -> Sexp {
        term_sexp(t)
    }
}

const RESERVED: &[&str] = &[
    "true", "false", "not", "and", "or", "=>", "xor", "=", "distinct", "ite", "let", "!", "Bool",
    "_", "as", "forall", "exists", "match", "par", "U", "Real",
];

fn smt_symbol(name: &str) -> String {
    if RESERVED.contains(&name) {
        format!("{name}!user")
    } else {
        name.to_string()
    }
}

fn atom(s: &str) -> Sexp {
    Sexp::Atom(s.to_string())
}

fn list(items: Vec<Sexp>) -> Sexp {
    Sexp::List(items)
}

fn term_sexp(t: &Term) -> Sexp {
    if t.args.is_empty() {
        return atom(&smt_symbol(&t.name));
    }
    let mut items = vec![atom(&smt_symbol(&t.name))];
    items.extend(t.args.iter().map(term_sexp));
    list(items)
}

/// A rational constant: `3`, `(/ 1 2)`, `(- 3)`, `(- (/ 1 2))`.
fn rational_sexp(q: &Rational) -> Sexp {
    let a = q.abs();
    let mag = if a.is_integer() {
        atom(&a.numer().to_string())
    } else {
        list(vec![
            atom("/"),
            atom(&a.numer().to_string()),
            atom(&a.denom().to_string()),
        ])
    };
    if q.is_negative() {
        list(vec![atom("-"), mag])
    } else {
        mag
    }
}

fn linear_sexp(l: &Linear) -> Sexp {
    let mut items: Vec<Sexp> = l
        .coeffs
        .iter()
        .map(|(x, c)| {
            if *c == Rational::one() {
                atom(&smt_symbol(x))
            } else {
                list(vec![atom("*"), rational_sexp(c), atom(&smt_symbol(x))])
            }
        })
        .collect();
    if !l.constant.is_zero() || items.is_empty() {
        items.push(rational_sexp(&l.constant));
    }
    if items.len() == 1 {
        items.pop().unwrap()
    } else {
        items.insert(0, atom("+"));
        list(items)
    }
}

fn formula_sexp(f: &Formula) -> Sexp {
    match f {
        Formula::Const(b) => atom(if *b { "true" } else { "false" }),
        Formula::Var(v) => atom(&smt_symbol(v)),
        Formula::Eq { lhs, rhs, equal } => {
            let eq = list(vec![atom("="), term_sexp(lhs), term_sexp(rhs)]);
            if *equal {
                eq
            } else {
                list(vec![atom("not"), eq])
            }
        }
        Formula::Cmp { lhs, rel, rhs } => {
            let op = match rel {
                Rel::Le => "<=",
                Rel::Lt => "<",
                Rel::Ge => ">=",
                Rel::Gt => ">",
                Rel::Eq | Rel::Ne => "=",
            };
            let c = list(vec![atom(op), linear_sexp(lhs), linear_sexp(rhs)]);
            if *rel == Rel::Ne {
                list(vec![atom("not"), c])
            } else {
                c
            }
        }
        Formula::Not(a) => list(vec![atom("not"), formula_sexp(a)]),
        Formula::And(xs) => {
            let mut items = vec![atom("and")];
            items.extend(xs.iter().map(formula_sexp));
            list(items)
        }
        Formula::Or(xs) => {
            let mut items = vec![atom("or")];
            items.extend(xs.iter().map(formula_sexp));
            list(items)
        }
        Formula::Implies(a, b) => list(vec![atom("=>"), formula_sexp(a), formula_sexp(b)]),
        Formula::Iff(a, b) => list(vec![atom("="), formula_sexp(a), formula_sexp(b)]),
        // Removed by `split_objective` before translation.
        Formula::Objective { .. } => atom("true"),
    }
}

/// Take a `min(...)`/`max(...)` objective out of a formula. It must be a top-level conjunct
/// (`(x <= 3) & (max(x))`); there can be at most one.
pub fn split_objective(f: &Formula) -> Result<(Formula, Option<(bool, Linear)>), String> {
    let nested = |g: &Formula| {
        let mut found = false;
        g.walk(&mut |h| found |= matches!(h, Formula::Objective { .. }));
        found
    };
    let misplaced = "min(...) and max(...) must be conjuncts at the top level, e.g. \
                     (x <= 3) & (max(x))";
    match f {
        Formula::Objective { maximize, term } => {
            Ok((Formula::Const(true), Some((*maximize, term.clone()))))
        }
        Formula::And(xs) => {
            let mut objective = None;
            let mut rest = Vec::with_capacity(xs.len());
            for x in xs {
                match x {
                    Formula::Objective { maximize, term } => {
                        if objective.replace((*maximize, term.clone())).is_some() {
                            return Err("only one min(...) or max(...) at a time".to_string());
                        }
                    }
                    other if nested(other) => return Err(misplaced.to_string()),
                    other => rest.push(other.clone()),
                }
            }
            let rest = if rest.is_empty() {
                Formula::Const(true)
            } else {
                Formula::And(rest)
            };
            Ok((rest, objective))
        }
        other if nested(other) => Err(misplaced.to_string()),
        other => Ok((other.clone(), None)),
    }
}

/// Translate to SMT-LIB: declarations for every variable / constant / function, and the formula
/// as one assertion. Fails if a function is used with two different arities.
pub fn to_smtlib(f: &Formula, atoms: Atoms) -> Result<Smt, String> {
    let mut commands = Vec::new();
    match atoms {
        Atoms::Prop => {
            for v in f.vars() {
                commands.push(list(vec![
                    atom("declare-const"),
                    atom(&smt_symbol(&v)),
                    atom("Bool"),
                ]));
            }
        }
        Atoms::Equality | Atoms::Functions => {
            commands.push(list(vec![atom("declare-sort"), atom("U"), atom("0")]));
            let mut arity: Vec<(String, usize)> = Vec::new();
            for t in f.terms() {
                match arity.iter().find(|(n, _)| *n == t.name) {
                    Some((_, a)) if *a != t.args.len() => {
                        return Err(format!(
                            "'{}' is used with {} and with {} arguments",
                            t.name,
                            a,
                            t.args.len()
                        ));
                    }
                    Some(_) => {}
                    None => arity.push((t.name.clone(), t.args.len())),
                }
            }
            for (name, n) in &arity {
                commands.push(list(vec![
                    atom("declare-fun"),
                    atom(&smt_symbol(name)),
                    list(vec![atom("U"); *n]),
                    atom("U"),
                ]));
            }
        }
        Atoms::Arith => {
            commands.push(list(vec![atom("set-logic"), atom("QF_LRA")]));
            for x in f.reals() {
                commands.push(list(vec![
                    atom("declare-const"),
                    atom(&smt_symbol(&x)),
                    atom("Real"),
                ]));
            }
        }
    }
    let (f, objective) = split_objective(f)?;
    commands.push(list(vec![atom("assert"), formula_sexp(&f)]));
    if let Some((maximize, term)) = objective {
        let cmd = if maximize { "maximize" } else { "minimize" };
        commands.push(list(vec![atom(cmd), linear_sexp(&term)]));
    }
    Ok(Smt { commands })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formula::parse;

    #[test]
    fn arithmetic_translation() {
        let f = parse("x + 2y - 1/2z <= -3 | x != 0.25", Atoms::Arith).unwrap();
        let smt = to_smtlib(&f, Atoms::Arith).unwrap();
        let shown: Vec<String> = smt.commands.iter().map(|c| c.to_string()).collect();
        assert_eq!(
            shown,
            [
                "(set-logic QF_LRA)",
                "(declare-const x Real)",
                "(declare-const y Real)",
                "(declare-const z Real)",
                "(assert (or (<= (+ x (* 2 y) (* (- (/ 1 2)) z)) (- 3)) (not (= x (/ 1 4)))))",
            ]
        );
    }

    #[test]
    fn arity_clash_is_an_error() {
        let f = parse("f(a) = f(a, b)", Atoms::Functions).unwrap();
        assert!(to_smtlib(&f, Atoms::Functions).is_err());
    }

    #[test]
    fn reserved_names_are_renamed() {
        let f = parse("and | not", Atoms::Prop).unwrap();
        let smt = to_smtlib(&f, Atoms::Prop).unwrap();
        assert_eq!(smt.symbol("and"), "and!user");
        assert_eq!(smt.symbol("x"), "x");
    }
}
