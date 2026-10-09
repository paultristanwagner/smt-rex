//! The theory commands: `smt` (QF_UF, QF_LRA, QF_LIA, QF_NRA) and `simplex`.

use super::{Session, WIDTH};
use crate::formula::{self, Atoms, Formula, Smt};
use crate::style::{natural_key, wrap};
use smtrex_smt::model::{RealAlgebraic, Value};
use smtrex_smt::script::{Answer, CheckResult, OptValue, Script};
use smtrex_smt::sexp::Sexp;
use std::io::{self, Write};

/// The logics of the short syntax, as `smt` accepts them.
const LOGICS: &[(&str, Atoms)] = &[
    ("QF_UF", Atoms::Functions),
    ("QF_EQUF", Atoms::Functions),
    ("QF_EQ", Atoms::Equality),
    ("QF_LRA", Atoms::Arith),
    ("QF_LIA", Atoms::Int),
    ("QF_NRA", Atoms::Poly),
];

/// The value of variable `x` for people: `x≈0.754878 (root 2 of 4x^6 - 8x^4 + 8x^2 - 3)`.
fn algebraic_text(x: &str, a: &RealAlgebraic) -> String {
    let p = a.minimal_polynomial();
    let mut poly = String::new();
    for (k, c) in p.coeffs().iter().enumerate().rev() {
        let c = c.to_string();
        if c == "0" {
            continue;
        }
        let (neg, mag) = match c.strip_prefix('-') {
            Some(m) => (true, m.to_string()),
            None => (false, c),
        };
        poly.push_str(match (poly.is_empty(), neg) {
            (true, true) => "-",
            (true, false) => "",
            (false, true) => " - ",
            (false, false) => " + ",
        });
        let mag = if mag == "1" && k > 0 {
            String::new()
        } else {
            mag
        };
        poly.push_str(&match k {
            0 => mag,
            1 => format!("{mag}{x}"),
            _ => format!("{mag}{x}^{k}"),
        });
    }
    let approx = format!("{:.6}", a.to_f64());
    let approx = approx.trim_end_matches('0').trim_end_matches('.');
    format!("{x}≈{approx} (root {} of {poly})", a.root_index() + 1)
}

impl Session {
    /// The optimum line for an objective, e.g. `max x + y = 14/5`, `max x: unbounded above`,
    /// `max x: no maximum (supremum 3, never reached)`.
    fn optimum(&self, r: &CheckResult, term: &formula::Linear, smt: &Smt) -> Option<String> {
        let o = r.objective.as_ref()?;
        let word = if o.maximize { "max" } else { "min" };
        let num = |v: &Value| match v {
            Value::Real(q) | Value::Int(q) => (q / &smt.objective_scale).to_string(),
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
    fn show_optimum(
        &self,
        f: &Formula,
        r: &CheckResult,
        smt: &Smt,
        out: &mut dyn Write,
    ) -> io::Result<()> {
        if let Ok((_, Some((_, term)))) = formula::split_objective(f) {
            if let Some(line) = self.optimum(r, &term, smt) {
                writeln!(out, "{line}")?;
            }
        }
        Ok(())
    }

    /// The exact values of numeric variables `vars` in `script`'s model: `x=7  y=-9/4 ...`,
    /// sorted naturally, wrapped; an irrational value gets its own line.
    fn numeric_model(
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
        let mut irrational: Vec<(&String, String)> = Vec::new();
        for (v, val) in vars.iter().zip(values) {
            match val {
                Value::Real(q) | Value::Int(q) => pairs.push((v, q.to_string())),
                Value::Algebraic(a) => irrational.push((v, algebraic_text(v, &a))),
                _ => return self.fail("internal error: a numeric variable has no number", out),
            }
        }
        pairs.sort_by_key(|(v, _)| natural_key(v));
        irrational.sort_by_key(|(v, _)| natural_key(v));
        let items: Vec<(String, usize)> = pairs
            .iter()
            .map(|(v, q)| {
                let text = format!("{v}={q}");
                (self.style.yes(&text), text.chars().count())
            })
            .collect();
        if !items.is_empty() {
            writeln!(out, "{}", wrap(&items, "  ", WIDTH))?;
        }
        for (_, text) in irrational {
            writeln!(out, "  {}", self.style.yes(&text))?;
        }
        Ok(())
    }

    pub(super) fn smt(&mut self, input: &str, out: &mut dyn Write) -> io::Result<()> {
        let (logic, rest) = input.split_once(char::is_whitespace).unwrap_or((input, ""));
        let logic_uc = logic.to_ascii_uppercase();
        let Some(&(_, atoms)) = LOGICS.iter().find(|(l, _)| *l == logic_uc) else {
            let msg = if logic_uc == "QF_BV" {
                "QF_BV has no short syntax; type SMT-LIB commands instead, e.g.\n  \
                 (declare-const x (_ BitVec 8))"
                    .to_string()
            } else {
                format!(
                    "unknown logic '{logic}'; the short syntax has QF_UF, QF_LRA, QF_LIA, QF_NRA"
                )
            };
            return self.fail(&msg, out);
        };
        let rest = rest.trim();
        if rest.is_empty() {
            return writeln!(
                out,
                "{} smt {logic_uc} <formula>",
                self.style.usage("usage:")
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
        if atoms.arithmetic() {
            self.show_optimum(&f, &r, &smt, out)?;
            return self.numeric_model(&mut script, &smt, &f.numeric_vars(), out);
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
            self.show_optimum(&f, &r, &smt, out)?;
            self.numeric_model(&mut script, &smt, &f.numeric_vars(), out)?;
        }
        Ok(())
    }
}
