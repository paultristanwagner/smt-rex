//! The interactive prompt: line editing, history, tab completion of commands and logics, and
//! multi-line SMT-LIB input (a line that opens more parentheses than it closes continues).

use crate::session::{Flow, Session, COMMANDS};
use rustyline::completion::{Completer, Pair};
use rustyline::error::ReadlineError;
use rustyline::highlight::Highlighter;
use rustyline::hint::Hinter;
use rustyline::history::DefaultHistory;
use rustyline::validate::{ValidationContext, ValidationResult, Validator};
use rustyline::{Context, Editor, Helper};
use std::process::ExitCode;

const LOGICS: &[&str] = &["QF_EQ", "QF_EQUF", "QF_LRA"];

/// True if every `(` in `src` is closed, ignoring `;` comments, `|quoted|` symbols and
/// `"strings"`. An unterminated quote or string counts as unbalanced.
pub fn balanced(src: &str) -> bool {
    let b = src.as_bytes();
    let mut depth = 0i64;
    let mut i = 0;
    while i < b.len() {
        match b[i] {
            b';' => {
                while i < b.len() && b[i] != b'\n' {
                    i += 1;
                }
            }
            b'|' => {
                i += 1;
                while i < b.len() && b[i] != b'|' {
                    i += 1;
                }
                if i == b.len() {
                    return false;
                }
            }
            b'"' => {
                i += 1;
                loop {
                    if i >= b.len() {
                        return false;
                    }
                    if b[i] == b'"' {
                        if b.get(i + 1) == Some(&b'"') {
                            i += 1; // escaped quote
                        } else {
                            break;
                        }
                    }
                    i += 1;
                }
            }
            b'(' => depth += 1,
            b')' => depth -= 1,
            _ => {}
        }
        i += 1;
    }
    depth <= 0
}

struct RexHelper;

impl Helper for RexHelper {}
impl Highlighter for RexHelper {}

impl Hinter for RexHelper {
    type Hint = String;
}

impl Validator for RexHelper {
    fn validate(&self, ctx: &mut ValidationContext) -> rustyline::Result<ValidationResult> {
        let input = ctx.input();
        if input.trim_start().starts_with('(') && !balanced(input) {
            Ok(ValidationResult::Incomplete)
        } else {
            Ok(ValidationResult::Valid(None))
        }
    }
}

impl Completer for RexHelper {
    type Candidate = Pair;

    fn complete(
        &self,
        line: &str,
        pos: usize,
        _ctx: &Context<'_>,
    ) -> rustyline::Result<(usize, Vec<Pair>)> {
        let before = &line[..pos];
        let start = before.rfind(char::is_whitespace).map_or(0, |i| i + 1);
        let word = &before[start..];
        let words: Vec<&str> = before[..start].split_whitespace().collect();
        let pairs = |cands: Vec<&str>| {
            cands
                .into_iter()
                .filter(|c| c.starts_with(word))
                .map(|c| Pair {
                    display: c.to_string(),
                    replacement: format!("{c} "),
                })
                .collect::<Vec<_>>()
        };
        let cands = match words.as_slice() {
            [] => pairs(
                COMMANDS
                    .iter()
                    .flat_map(|c| std::iter::once(c.name).chain(c.aliases.iter().copied()))
                    .collect(),
            ),
            ["smt"] => pairs(LOGICS.to_vec()),
            ["help" | "?"] => pairs(COMMANDS.iter().map(|c| c.name).collect()),
            _ => Vec::new(),
        };
        Ok((start, cands))
    }
}

fn history_path() -> Option<std::path::PathBuf> {
    let base = std::env::var_os("XDG_STATE_HOME")
        .map(std::path::PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|h| std::path::PathBuf::from(h).join(".local/state"))
        })?;
    Some(base.join("smt-rex").join("history"))
}

pub fn run(mut session: Session) -> ExitCode {
    let mut rl: Editor<RexHelper, DefaultHistory> = match Editor::new() {
        Ok(rl) => rl,
        Err(e) => {
            eprintln!("smt-rex: cannot start the prompt: {e}");
            return ExitCode::FAILURE;
        }
    };
    rl.set_helper(Some(RexHelper));
    let history = history_path();
    if let Some(h) = &history {
        let _ = rl.load_history(h);
    }

    let style = session.style();
    println!(
        "{} {}  {}",
        style.bold("SMT-Rex"),
        env!("CARGO_PKG_VERSION"),
        style.dim("a SAT and SMT solver")
    );
    println!("{}", style.dim("Type help for commands, Ctrl-D to quit."));

    let mut stdout = std::io::stdout();
    loop {
        match rl.readline("smt-rex> ") {
            Ok(line) => {
                if !line.trim().is_empty() {
                    let _ = rl.add_history_entry(line.as_str());
                }
                match session.run_line(&line, &mut stdout) {
                    Ok(Flow::Continue) => {}
                    Ok(Flow::Exit) => break,
                    Err(e) => {
                        eprintln!("smt-rex: {e}");
                        break;
                    }
                }
            }
            // Ctrl-C at the prompt abandons the line; Ctrl-D quits.
            Err(ReadlineError::Interrupted) => continue,
            Err(ReadlineError::Eof) => break,
            Err(e) => {
                eprintln!("smt-rex: {e}");
                break;
            }
        }
    }

    if let Some(h) = &history {
        if let Some(dir) = h.parent() {
            let _ = std::fs::create_dir_all(dir);
        }
        let _ = rl.save_history(h);
    }
    ExitCode::SUCCESS
}

#[cfg(test)]
mod tests {
    use super::*;

    fn complete(line: &str) -> Vec<String> {
        let history = DefaultHistory::new();
        let (_, pairs) = RexHelper
            .complete(line, line.len(), &Context::new(&history))
            .unwrap();
        pairs.into_iter().map(|p| p.replacement).collect()
    }

    #[test]
    fn completion() {
        assert_eq!(complete("smt QF_L"), ["QF_LRA "]);
        assert_eq!(complete("smt QF_EQ"), ["QF_EQ ", "QF_EQUF "]);
        assert_eq!(complete("tse"), ["tseitin ", "tseytin "]);
    }

    #[test]
    fn balance() {
        assert!(balanced("(assert p)"));
        assert!(!balanced("(assert (and p"));
        assert!(balanced("(echo \"(\")"));
        assert!(balanced("(declare-fun |a(b| () Bool)"));
        assert!(balanced("(assert p) ; (unclosed comment"));
        assert!(!balanced("(echo \"unterminated"));
        assert!(balanced("(echo \"say \"\"(\"\" twice\")"));
    }
}
