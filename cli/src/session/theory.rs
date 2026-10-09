//! The theory commands: `smt` (QF_EQ, QF_EQUF, QF_LRA) and `simplex`.

use super::{Session, WIDTH};
use crate::formula::{self, Atoms, Formula, Smt};
use crate::style::{natural_key, wrap};
use smtrex_smt::model::Value;
use smtrex_smt::script::{Answer, CheckResult, OptValue, Script};
use smtrex_smt::sexp::Sexp;
use std::io::{self, Write};

/// Logics SMT-Rex decides only in SMT-LIB form.
const NO_SHORT_SYNTAX: &[(&str, &str)] = &[
    ("QF_LIA", "linear integer arithmetic"),
    ("QF_BV", "bit-vectors"),
    ("QF_NRA", "non-linear real arithmetic"),
];

impl Session {
    /// The optimum line for an objective, e.g. `max x + y = 14/5`, `max x: unbounded above`,
    /// `max x: no maximum (supremum 3, never reached)`.
    fn optimum(&self, r: &CheckResult, term: &formula::Linear) -> Option<String> {
        let o = r.objective.as_ref()?;
        let word = if o.maximize { "max" } else { "min" };
        let num = |v: &Value| match v {
            Value::Real(q) | Value::Int(q) => q.to_string(),
            other => format!("{other:?}"),
        };
        let line = match &o.value {
            OptValue::Exact(v) => format!("{word} {term} = {}", self.style.bold(&num(v))),
            OptValue::Unbounded => format!(
                "{word} {term}: {}",
                self.style.unknown(if o.maximize {
                    "unbounded above"
                } else {
                    "unbounded below"
                })
            ),
            OptValue::NotAttained(v) => format!(
                "{word} {term}: {} ({} {}, never reached)",
                self.style.unknown(if o.maximize {
                    "no maximum"
                } else {
                    "no minimum"
                }),
                if o.maximize { "supremum" } else { "infimum" },
                num(v)
            ),
        };
        Some(format!("  {line}"))
    }

    /// Print the optimum line, if `f` has an objective and the answer carries one.
    fn show_optimum(&self, f: &Formula, r: &CheckResult, out: &mut dyn Write) -> io::Result<()> {
        if let Ok((_, Some((_, term)))) = formula::split_objective(f) {
            if let Some(line) = self.optimum(r, &term) {
                writeln!(out, "{line}")?;
            }
        }
        Ok(())
    }

    /// The exact values of real variables `vars` in `script`'s model: `x=7  y=-9/4 ...`, sorted
    /// naturally, wrapped.
    fn real_model(
        &self,
        script: &mut Script,
        smt: &Smt,
        vars: &[String],
        out: &mut dyn Write,
    ) -> io::Result<()> {
        if vars.is_empty() {
            return writeln!(out, "{}", self.style.dim("  (no variables)"));
        }
        let sexps: Vec<Sexp> = vars.iter().map(|v| Sexp::Atom(smt.symbol(v))).collect();
        let values = match script.values(&sexps) {
            Ok(v) => v,
            Err(e) => return self.fail(&e, out),
        };
        let mut pairs: Vec<(&String, String)> = Vec::new();
        for (v, val) in vars.iter().zip(values) {
            match val {
                Value::Real(q) => pairs.push((v, q.to_string())),
                _ => return self.fail("internal error: a real variable is not a Real", out),
            }
        }
        pairs.sort_by_key(|(v, _)| natural_key(v));
        let items: Vec<(String, usize)> = pairs
            .iter()
            .map(|(v, q)| {
                let text = format!("{v}={q}");
                (self.style.yes(&text), text.chars().count())
            })
            .collect();
        writeln!(out, "{}", wrap(&items, "  ", WIDTH))
    }

    pub(super) fn smt(&mut self, input: &str, out: &mut dyn Write) -> io::Result<()> {
        let (logic, rest) = input.split_once(char::is_whitespace).unwrap_or((input, ""));
        let logic_uc = logic.to_ascii_uppercase();
        let atoms = match logic_uc.as_str() {
            "QF_EQ" => Atoms::Equality,
            "QF_EQUF" | "QF_UF" => Atoms::Functions,
            "QF_LRA" => Atoms::Arith,
            other => {
                let msg = match NO_SHORT_SYNTAX.iter().find(|(l, _)| *l == other) {
                    Some((l, what)) => format!(
                        "{l} ({what}) has no short syntax yet; SMT-Rex decides it in SMT-LIB \
                         form: type the commands directly, or use smtlib <file>."
                    ),
                    None => format!(
                        "unknown logic '{logic}'. The short syntax covers QF_EQ, QF_EQUF and \
                         QF_LRA."
                    ),
                };
                return self.fail(&msg, out);
            }
        };
        let rest = rest.trim();
        if rest.is_empty() {
            return writeln!(
                out,
                "{} smt {logic_uc} <formula>",
                self.style.error("usage:")
            );
        }
        let Some(f) = self.parse(rest, atoms, out)? else {
            return Ok(());
        };
        let smt = match formula::to_smtlib(&f, atoms) {
            Ok(s) => s,
            Err(e) => return self.fail(&e, out),
        };
        let (mut script, r, took) = match self.solve(&smt) {
            Ok(x) => x,
            Err(e) => return self.fail(&e, out),
        };
        writeln!(out, "{}", self.verdict(&r, took))?;
        if r.answer != Answer::Sat {
            return Ok(());
        }
        if atoms == Atoms::Arith {
            self.show_optimum(&f, &r, out)?;
            return self.real_model(&mut script, &smt, &f.reals(), out);
        }
        // Group the formula's terms by value: one line per domain element.
        let terms = f.terms();
        let sexps: Vec<Sexp> = terms.iter().map(|t| smt.term(t)).collect();
        let values = match script.values(&sexps) {
            Ok(v) => v,
            Err(e) => return self.fail(&e, out),
        };
        let mut classes: Vec<(Value, Vec<String>)> = Vec::new();
        for (t, v) in terms.iter().zip(values) {
            match classes.iter_mut().find(|(c, _)| *c == v) {
                Some((_, ts)) => ts.push(t.to_string()),
                None => classes.push((v, vec![t.to_string()])),
            }
        }
        let width = classes.len().saturating_sub(1).to_string().len();
        for (i, (_, ts)) in classes.iter().enumerate() {
            let label = self.style.accent(&format!("e{i:<width$}"));
            writeln!(out, "  {label}  {}", ts.join(" = "))?;
        }
        Ok(())
    }

    /// `simplex`: a conjunction of linear constraints, with an optional objective. A feasible
    /// problem is sat even when the objective is unbounded.
    pub(super) fn simplex(&mut self, input: &str, out: &mut dyn Write) -> io::Result<()> {
        let mut constraints = match formula::parse_constraints(input) {
            Ok(c) => c,
            Err(e) => return self.syntax_error(input, &e, out),
        };
        let f = if constraints.len() == 1 {
            constraints.pop().unwrap()
        } else {
            Formula::And(constraints)
        };
        let smt = match formula::to_smtlib(&f, Atoms::Arith) {
            Ok(s) => s,
            Err(e) => return self.fail(&e, out),
        };
        let (mut script, r, took) = match self.solve(&smt) {
            Ok(x) => x,
            Err(e) => return self.fail(&e, out),
        };
        writeln!(out, "{}", self.verdict(&r, took))?;
        if r.answer == Answer::Sat {
            self.show_optimum(&f, &r, out)?;
            self.real_model(&mut script, &smt, &f.reals(), out)?;
        }
        Ok(())
    }
}
