//! The propositional commands: `sat`, `allsat`, `tseitin`.

use super::{Session, WIDTH};
use crate::formula::{self, Atoms, Smt};
use crate::style::{human, natural_key, wrap};
use smtrex_smt::model::Value;
use smtrex_smt::script::{Answer, Response, Script};
use smtrex_smt::sexp::Sexp;
use std::io::{self, Write};
use std::time::Instant;

const ALLSAT_DEFAULT: usize = 100;

impl Session {
    pub(super) fn sat(&mut self, input: &str, out: &mut dyn Write) -> io::Result<()> {
        let Some(f) = self.parse(input, Atoms::Prop, out)? else {
            return Ok(());
        };
        let smt = formula::to_smtlib(&f, Atoms::Prop).expect("propositional translation");
        let (mut script, r, took) = match self.solve(&smt) {
            Ok(x) => x,
            Err(e) => return self.fail(&e, out),
        };
        writeln!(out, "{}", self.verdict(&r, took))?;
        if r.answer == Answer::Sat {
            let vars = f.vars();
            match bool_values(&mut script, &smt, &vars) {
                Ok(vals) => writeln!(out, "{}", self.assignment(&vars, &vals))?,
                Err(e) => self.fail(&e, out)?,
            }
        }
        Ok(())
    }

    /// `a=1  b=0 ...` sorted naturally, wrapped.
    fn assignment(&self, vars: &[String], vals: &[bool]) -> String {
        let mut pairs: Vec<(&String, bool)> = vars.iter().zip(vals.iter().copied()).collect();
        pairs.sort_by_key(|(v, _)| natural_key(v));
        let items: Vec<(String, usize)> = pairs
            .iter()
            .map(|(v, b)| {
                let text = format!("{v}={}", if *b { 1 } else { 0 });
                let shown = if *b {
                    self.style.yes(&text)
                } else {
                    self.style.no(&text)
                };
                (shown, text.chars().count())
            })
            .collect();
        if items.is_empty() {
            return self.style.dim("  (no variables)");
        }
        wrap(&items, "  ", WIDTH)
    }

    pub(super) fn allsat(&mut self, input: &str, out: &mut dyn Write) -> io::Result<()> {
        let (limit, input) = match input.strip_prefix("-n") {
            Some(rest) => {
                let rest = rest.trim_start();
                let (num, tail) = rest.split_once(char::is_whitespace).unwrap_or((rest, ""));
                match num.parse::<usize>() {
                    Ok(n) if n > 0 => (n, tail.trim()),
                    _ => {
                        return writeln!(
                            out,
                            "{} -n needs a positive number",
                            self.style.error("usage:")
                        )
                    }
                }
            }
            None => (ALLSAT_DEFAULT, input),
        };
        if input.is_empty() {
            return writeln!(
                out,
                "{} allsat [-n <limit>] <formula>",
                self.style.error("usage:")
            );
        }
        let Some(f) = self.parse(input, Atoms::Prop, out)? else {
            return Ok(());
        };
        let smt = formula::to_smtlib(&f, Atoms::Prop).expect("propositional translation");
        let vars = f.vars();
        let mut script = self.fresh_script();
        for c in &smt.commands {
            if let Err(e) = script.exec(c) {
                return self.fail(&e, out);
            }
        }
        let start = Instant::now();
        let mut found = 0;
        let check = Sexp::List(vec![Sexp::Atom("check-sat".into())]);
        let exhausted = loop {
            let r = match script.exec(&check) {
                Ok(Some(Response::Check(r))) => r,
                Ok(_) => unreachable!("check-sat always answers"),
                Err(e) => return self.fail(&e, out),
            };
            match r.answer {
                Answer::Unsat => break true,
                Answer::Unknown => {
                    writeln!(out, "{}", self.verdict(&r, start.elapsed()))?;
                    break false;
                }
                Answer::Sat => {}
            }
            if found == limit {
                break false;
            }
            let vals = match bool_values(&mut script, &smt, &vars) {
                Ok(v) => v,
                Err(e) => return self.fail(&e, out),
            };
            found += 1;
            writeln!(out, "{}", self.assignment(&vars, &vals))?;
            if vars.is_empty() {
                break true;
            }
            // Block this assignment and look for the next one.
            let lits: Vec<Sexp> = vars
                .iter()
                .zip(&vals)
                .map(|(v, &b)| {
                    let a = Sexp::Atom(smt.symbol(v));
                    if b {
                        Sexp::List(vec![Sexp::Atom("not".into()), a])
                    } else {
                        a
                    }
                })
                .collect();
            let mut or = vec![Sexp::Atom("or".into())];
            or.extend(lits);
            let block = Sexp::List(vec![Sexp::Atom("assert".into()), Sexp::List(or)]);
            if let Err(e) = script.exec(&block) {
                return self.fail(&e, out);
            }
        };
        let took = self.style.dim(&format!("({})", human(start.elapsed())));
        let summary = match (found, exhausted) {
            (0, true) => self.style.unsat("unsat: no models"),
            (n, true) => self
                .style
                .sat(&format!("{n} model{}", if n == 1 { "" } else { "s" })),
            (n, false) if n == limit => {
                format!(
                    "{}  {}",
                    self.style.sat(&format!("{n} models shown")),
                    self.style.dim(&format!(
                        "there are more; allsat -n {} to see more",
                        10 * limit
                    ))
                )
            }
            (n, false) => self
                .style
                .unknown(&format!("{n} models found before stopping")),
        };
        writeln!(out, "{summary}  {took}")
    }

    pub(super) fn tseitin(&mut self, input: &str, out: &mut dyn Write) -> io::Result<()> {
        let Some(f) = self.parse(input, Atoms::Prop, out)? else {
            return Ok(());
        };
        let cnf = formula::tseitin(&f);
        let originals = f.vars();
        let mut helpers: Vec<&str> = cnf
            .iter()
            .flatten()
            .map(|(v, _)| v.as_str())
            .filter(|v| !originals.iter().any(|o| o == v))
            .collect();
        helpers.sort_by_key(|v| natural_key(v));
        helpers.dedup();
        writeln!(out, "{}", formula::show_cnf(&cnf))?;
        writeln!(
            out,
            "{}",
            self.style.dim(&format!(
                "{} clauses, {} helper variable{}",
                cnf.len(),
                helpers.len(),
                if helpers.len() == 1 { "" } else { "s" }
            ))
        )
    }
}

/// The truth values of propositional variables `vars` in `script`'s current model.
fn bool_values(script: &mut Script, smt: &Smt, vars: &[String]) -> Result<Vec<bool>, String> {
    if vars.is_empty() {
        return Ok(Vec::new());
    }
    let sexps: Vec<Sexp> = vars.iter().map(|v| Sexp::Atom(smt.symbol(v))).collect();
    script
        .values(&sexps)?
        .into_iter()
        .map(|v| match v {
            Value::Bool(b) => Ok(b),
            _ => Err("internal error: a propositional variable is not a Bool".into()),
        })
        .collect()
}
