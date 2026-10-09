//! The interactive session: one line in, formatted output out. Shared by the prompt, `read`,
//! and `smt-rex -e`.
//!
//! Short-syntax commands (`sat`, `smt`, ...) are translated to SMT-LIB and solved by the same
//! engine as SMT-LIB input, so they get its sort checking and its self-checked models. Each runs
//! in a fresh solver; raw SMT-LIB lines share one persistent script.

mod help;
mod prop;
#[cfg(test)]
mod tests;
mod theory;

use help::find_command;
pub use help::COMMANDS;

use crate::batch::{solve_dimacs, DimacsResult};
use crate::formula::{self, Atoms, Formula, ParseError, Smt};
use crate::style::{human, wrap, Style};
use smtrex_smt::script::{Answer, CheckResult, Response, Script};
use smtrex_smt::sexp::{parse_script, Sexp};
use std::io::{self, Write};
use std::path::Path;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Instant;

/// What the caller should do after a line.
#[derive(Debug, PartialEq, Eq)]
pub enum Flow {
    Continue,
    Exit,
}

pub struct Session {
    style: Style,
    /// The persistent SMT-LIB state for raw `(...)` input.
    script: Script,
    stop: Arc<AtomicBool>,
    /// Nesting depth of `read`, to refuse files that read themselves forever.
    read_depth: usize,
}

const WIDTH: usize = 78;

impl Session {
    pub fn new(style: Style, stop: Arc<AtomicBool>) -> Session {
        let mut script = Script::new();
        script.set_stop_flag(stop.clone());
        Session {
            style,
            script,
            stop,
            read_depth: 0,
        }
    }

    pub fn style(&self) -> Style {
        self.style
    }

    /// A fresh script that honours Ctrl-C.
    fn fresh_script(&self) -> Script {
        let mut s = Script::new();
        s.set_stop_flag(self.stop.clone());
        s
    }

    /// Run one input line (or one complete multi-line SMT-LIB form).
    pub fn run_line(&mut self, line: &str, out: &mut dyn Write) -> io::Result<Flow> {
        self.stop.store(false, Ordering::Relaxed);
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            return Ok(Flow::Continue);
        }
        if line.starts_with('(') {
            return self.smtlib_input(line, out);
        }
        let (word, rest) = match line.split_once(char::is_whitespace) {
            Some((w, r)) => (w, r.trim()),
            None => (line, ""),
        };
        let Some(cmd) = find_command(word) else {
            writeln!(
                out,
                "{} unknown command '{word}'. Type {} for the list.",
                self.style.error("error:"),
                self.style.bold("help")
            )?;
            return Ok(Flow::Continue);
        };
        let needs_arg = !matches!(cmd.name, "clear" | "help" | "exit");
        if needs_arg && rest.is_empty() {
            writeln!(out, "{} {}", self.style.error("usage:"), cmd.usage)?;
            return Ok(Flow::Continue);
        }
        match cmd.name {
            "sat" => self.sat(rest, out)?,
            "allsat" => self.allsat(rest, out)?,
            "smt" => self.smt(rest, out)?,
            "simplex" => self.simplex(rest, out)?,
            "tseitin" => self.tseitin(rest, out)?,
            "smtlib" => self.smtlib_file(rest, out)?,
            "dimacs" => self.dimacs(rest, out)?,
            "read" => return self.read(rest, out),
            "clear" => write!(out, "\x1b[2J\x1b[H")?,
            "help" => self.help(rest, out)?,
            "exit" => return Ok(Flow::Exit),
            _ => unreachable!("every command is dispatched"),
        }
        Ok(Flow::Continue)
    }

    fn verdict(&self, r: &CheckResult, took: std::time::Duration) -> String {
        let word = match r.answer {
            Answer::Sat => self.style.sat("sat"),
            Answer::Unsat => self.style.unsat("unsat"),
            Answer::Unknown => self.style.unknown("unknown"),
        };
        let mut s = format!("{word}  {}", self.style.dim(&format!("({})", human(took))));
        if let Some(why) = &r.reason {
            s.push_str(&format!("  {}", self.style.unknown(why)));
        }
        if let Some(exp) = r.expected {
            if r.answer != Answer::Unknown && exp != r.answer {
                s.push_str(&format!(
                    "  {}",
                    self.style
                        .unsat(&format!("but the file's :status says {}", exp.as_str()))
                ));
            }
        }
        s
    }

    /// The error message, then `input` with a caret under the offending character.
    fn syntax_error(&self, input: &str, e: &ParseError, out: &mut dyn Write) -> io::Result<()> {
        let col = input[..e.at.min(input.len())].chars().count();
        writeln!(out, "{} {}", self.style.error("syntax error:"), e.message)?;
        writeln!(out, "  {input}")?;
        writeln!(out, "  {}{}", " ".repeat(col), self.style.error("^"))
    }

    fn fail(&self, msg: &str, out: &mut dyn Write) -> io::Result<()> {
        writeln!(out, "{} {msg}", self.style.error("error:"))
    }

    /// Parse a short-syntax formula, reporting a syntax error with a caret.
    fn parse(&self, input: &str, atoms: Atoms, out: &mut dyn Write) -> io::Result<Option<Formula>> {
        match formula::parse(input, atoms) {
            Ok(f) => Ok(Some(f)),
            Err(e) => {
                self.syntax_error(input, &e, out)?;
                Ok(None)
            }
        }
    }

    /// Load a translated formula into a fresh script and run `check-sat`.
    fn solve(&self, smt: &Smt) -> Result<(Script, CheckResult, std::time::Duration), String> {
        let mut script = self.fresh_script();
        for c in &smt.commands {
            script.exec(c)?;
        }
        let start = Instant::now();
        let r = match script.exec(&Sexp::List(vec![Sexp::Atom("check-sat".into())]))? {
            Some(Response::Check(r)) => r,
            _ => unreachable!("check-sat always answers"),
        };
        Ok((script, r, start.elapsed()))
    }

    fn read_file(&self, path: &str, out: &mut dyn Write) -> io::Result<Option<String>> {
        match std::fs::read_to_string(Path::new(path)) {
            Ok(s) => Ok(Some(s)),
            Err(e) => {
                self.fail(&format!("cannot read {path}: {e}"), out)?;
                Ok(None)
            }
        }
    }

    /// Run SMT-LIB commands on `script` and show their responses, stopping at the first error.
    fn show_smtlib(&self, script: &mut Script, src: &str, out: &mut dyn Write) -> io::Result<()> {
        let cmds = match parse_script(src) {
            Ok(c) => c,
            Err(e) => return self.fail(&e, out),
        };
        for cmd in &cmds {
            let start = Instant::now();
            match script.exec(cmd) {
                Ok(Some(Response::Check(r))) => {
                    writeln!(out, "{}", self.verdict(&r, start.elapsed()))?
                }
                Ok(Some(Response::Text(t))) => writeln!(out, "{t}")?,
                Ok(None) => {}
                Err(e) => {
                    let shown = cmd.to_string();
                    let shown = if shown.chars().count() > 60 {
                        format!("{}...", shown.chars().take(57).collect::<String>())
                    } else {
                        shown
                    };
                    return self.fail(&format!("{e}\n  in {shown}"), out);
                }
            }
            if script.exited() {
                break;
            }
        }
        Ok(())
    }

    fn smtlib_input(&mut self, src: &str, out: &mut dyn Write) -> io::Result<Flow> {
        let mut script = std::mem::take(&mut self.script);
        self.show_smtlib(&mut script, src, out)?;
        let exited = script.exited();
        self.script = script;
        Ok(if exited { Flow::Exit } else { Flow::Continue })
    }

    /// `smtlib <file>`, or `smtlib (...)` with the script inline; runs in a fresh script.
    fn smtlib_file(&mut self, path: &str, out: &mut dyn Write) -> io::Result<()> {
        let src = if path.starts_with('(') {
            path.to_string()
        } else {
            match self.read_file(path, out)? {
                Some(s) => s,
                None => return Ok(()),
            }
        };
        self.show_smtlib(&mut self.fresh_script(), &src, out)
    }

    fn dimacs(&mut self, path: &str, out: &mut dyn Write) -> io::Result<()> {
        let Some(src) = self.read_file(path, out)? else {
            return Ok(());
        };
        let cnf = match smtrex_sat::dimacs::parse(&src) {
            Ok(c) => c,
            Err(e) => return self.fail(&format!("{path}: {e}"), out),
        };
        let start = Instant::now();
        let result = solve_dimacs(&cnf, &self.stop, false);
        let took = self.style.dim(&format!("({})", human(start.elapsed())));
        let stats = self.style.dim(&format!(
            "{} variables, {} clauses",
            cnf.num_vars,
            cnf.clauses.len()
        ));
        match result {
            DimacsResult::Sat(model) => {
                writeln!(out, "{}  {took}  {stats}", self.style.sat("sat"))?;
                let items: Vec<(String, usize)> = model
                    .iter()
                    .enumerate()
                    .map(|(i, &b)| {
                        let text = format!("{}{}", if b { "" } else { "-" }, i + 1);
                        let n = text.len();
                        (
                            if b {
                                self.style.yes(&text)
                            } else {
                                self.style.no(&text)
                            },
                            n,
                        )
                    })
                    .collect();
                if !items.is_empty() {
                    writeln!(out, "{}", wrap(&items, "  ", WIDTH))?;
                }
            }
            DimacsResult::Unsat(_) => {
                writeln!(out, "{}  {took}  {stats}", self.style.unsat("unsat"))?
            }
            DimacsResult::Unknown(why) => writeln!(
                out,
                "{}  {took}  {}",
                self.style.unknown("unknown"),
                self.style.unknown(&why)
            )?,
        }
        Ok(())
    }

    fn read(&mut self, path: &str, out: &mut dyn Write) -> io::Result<Flow> {
        if self.read_depth >= 16 {
            self.fail(
                "read is nested more than 16 deep; does the file read itself?",
                out,
            )?;
            return Ok(Flow::Continue);
        }
        let Some(src) = self.read_file(path, out)? else {
            return Ok(Flow::Continue);
        };
        self.read_depth += 1;
        let mut flow = Flow::Continue;
        let mut pending = String::new();
        for line in src.lines() {
            pending.push_str(line);
            pending.push('\n');
            if pending.trim_start().starts_with('(') && !crate::repl::balanced(&pending) {
                continue;
            }
            let cmd = std::mem::take(&mut pending);
            if cmd.trim().is_empty() || cmd.trim_start().starts_with('#') {
                continue;
            }
            writeln!(
                out,
                "{} {}",
                self.style.dim(">"),
                self.style.dim(cmd.trim())
            )?;
            flow = self.run_line(&cmd, out)?;
            if flow == Flow::Exit {
                break;
            }
        }
        if !pending.trim().is_empty() && flow == Flow::Continue {
            self.fail("the file ends inside an unclosed '('", out)?;
        }
        self.read_depth -= 1;
        Ok(flow)
    }
}
