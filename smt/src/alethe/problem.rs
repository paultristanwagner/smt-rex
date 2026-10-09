//! The script being proved: declarations and assertions with `let`, `!` and `define-fun`
//! expanded.

use crate::sexp::{parse_script, Sexp};
use rustc_hash::FxHashMap;

pub(super) struct Def {
    params: Vec<String>,
    body: Sexp,
}

pub(super) struct Problem {
    /// Function and constant signatures: argument sorts, result sort.
    pub(super) sigs: FxHashMap<String, (Vec<String>, String)>,
    /// The assertions with `let`, `!` and `define-fun` expanded.
    pub(super) asserts: Vec<Sexp>,
}

/// Terms larger than this after expansion are not proved (expansion can be exponential).
pub(super) const MAX_NODES: usize = 2_000_000;

impl Problem {
    pub(super) fn read(src: &str) -> Result<Problem, String> {
        let mut sigs = FxHashMap::default();
        let mut defs: FxHashMap<String, Def> = FxHashMap::default();
        let mut asserts = Vec::new();
        let mut checks = 0;
        for cmd in parse_script(src)? {
            let items = cmd.as_list().ok_or("expected a command")?;
            let head = items.first().and_then(Sexp::as_atom).unwrap_or("");
            match head {
                "set-info" | "set-option" | "exit" | "get-model" | "get-value" | "get-info"
                | "get-proof" | "echo" => {}
                "set-logic" => {
                    let logic = items.get(1).and_then(Sexp::as_atom).unwrap_or("");
                    if logic != "QF_UF" && logic != "QF_LRA" {
                        return Err(format!("proofs support QF_UF and QF_LRA, not {logic}"));
                    }
                }
                "declare-sort" => {
                    if items.get(2).and_then(Sexp::as_atom) != Some("0") {
                        return Err("proofs support sorts of arity 0 only".to_string());
                    }
                }
                "declare-const" => {
                    let [_, Sexp::Atom(n), s] = items else {
                        return Err(format!("malformed {cmd}"));
                    };
                    sigs.insert(n.clone(), (Vec::new(), sort_name(s)));
                }
                "declare-fun" => {
                    let [_, Sexp::Atom(n), Sexp::List(args), s] = items else {
                        return Err(format!("malformed {cmd}"));
                    };
                    let args = args.iter().map(sort_name).collect();
                    sigs.insert(n.clone(), (args, sort_name(s)));
                }
                "define-fun" => {
                    let [_, Sexp::Atom(n), Sexp::List(params), s, body] = items else {
                        return Err(format!("malformed {cmd}"));
                    };
                    let mut names = Vec::new();
                    let mut sorts = Vec::new();
                    for p in params {
                        let Some([Sexp::Atom(pn), ps]) = p.as_list() else {
                            return Err(format!("malformed parameter in {cmd}"));
                        };
                        names.push(pn.clone());
                        sorts.push(sort_name(ps));
                    }
                    let mut nodes = 0;
                    let body = expand(body, &[], &defs, &mut nodes)?;
                    defs.insert(
                        n.clone(),
                        Def {
                            params: names,
                            body,
                        },
                    );
                    sigs.insert(n.clone(), (sorts, sort_name(s)));
                }
                "assert" => {
                    if checks > 0 {
                        return Err("proofs support one check-sat, at the end".to_string());
                    }
                    let mut nodes = 0;
                    asserts.push(expand(&items[1], &[], &defs, &mut nodes)?);
                }
                "check-sat" => checks += 1,
                other => return Err(format!("'{other}' is not supported with proofs")),
            }
        }
        if checks != 1 {
            return Err("proofs need exactly one check-sat".to_string());
        }
        Ok(Problem { sigs, asserts })
    }

    pub(super) fn sort_of(&self, t: &Sexp) -> Result<String, String> {
        match t {
            Sexp::Atom(a) if a == "true" || a == "false" => Ok("Bool".to_string()),
            Sexp::Atom(a) if a.starts_with(|c: char| c.is_ascii_digit()) => Ok("Real".to_string()),
            Sexp::Atom(a) => self
                .sigs
                .get(a)
                .map(|(_, s)| s.clone())
                .ok_or_else(|| format!("undeclared symbol '{a}'")),
            Sexp::List(l) => match l.first().and_then(Sexp::as_atom) {
                Some(
                    "and" | "or" | "not" | "=>" | "xor" | "=" | "distinct" | "<=" | "<" | ">="
                    | ">",
                ) => Ok("Bool".to_string()),
                Some("+" | "-" | "*" | "/") => Ok("Real".to_string()),
                Some("ite") => self.sort_of(l.get(2).ok_or("ite expects 3 arguments")?),
                Some(f) => self
                    .sigs
                    .get(f)
                    .map(|(_, s)| s.clone())
                    .ok_or_else(|| format!("undeclared function '{f}'")),
                None => Err(format!("malformed term {t}")),
            },
        }
    }
}

pub(super) fn sort_name(s: &Sexp) -> String {
    s.to_string()
}

/// `t` with `let`s, `!` and defined functions replaced by what they stand for.
pub(super) fn expand(
    t: &Sexp,
    env: &[(String, Sexp)],
    defs: &FxHashMap<String, Def>,
    nodes: &mut usize,
) -> Result<Sexp, String> {
    *nodes += 1;
    if *nodes > MAX_NODES {
        return Err("the expanded assertions are too large to prove".to_string());
    }
    match t {
        Sexp::Atom(a) => {
            if let Some((_, v)) = env.iter().rev().find(|(n, _)| n == a) {
                return Ok(v.clone());
            }
            match defs.get(a) {
                Some(d) if d.params.is_empty() => Ok(d.body.clone()),
                _ => Ok(t.clone()),
            }
        }
        Sexp::List(l) => {
            let head = l.first().and_then(Sexp::as_atom);
            match head {
                Some("let") => {
                    let (Some(bindings), Some(body)) = (l.get(1).and_then(Sexp::as_list), l.get(2))
                    else {
                        return Err(format!("malformed let {t}"));
                    };
                    let mut inner = env.to_vec();
                    for b in bindings {
                        let Some([Sexp::Atom(n), e]) = b.as_list() else {
                            return Err(format!("malformed let binding in {t}"));
                        };
                        inner.push((n.clone(), expand(e, env, defs, nodes)?));
                    }
                    expand(body, &inner, defs, nodes)
                }
                Some("!") => expand(l.get(1).ok_or("! expects a term")?, env, defs, nodes),
                Some(f) if defs.get(f).is_some_and(|d| !d.params.is_empty()) => {
                    let d = &defs[f];
                    if d.params.len() != l.len() - 1 {
                        return Err(format!("'{f}' expects {} arguments", d.params.len()));
                    }
                    let mut args = Vec::with_capacity(d.params.len());
                    for (p, a) in d.params.iter().zip(&l[1..]) {
                        args.push((p.clone(), expand(a, env, defs, nodes)?));
                    }
                    expand(&d.body, &args, defs, nodes)
                }
                _ => Ok(Sexp::List(
                    l.iter()
                        .map(|x| expand(x, env, defs, nodes))
                        .collect::<Result<_, _>>()?,
                )),
            }
        }
    }
}
