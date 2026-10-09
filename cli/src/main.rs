//! `smt-rex`, the SMT-Rex command-line solver: the interactive prompt, `-e`, and the batch modes
//! for SMT-LIB and DIMACS input (see `USAGE`).

mod batch;
mod formula;
mod repl;
mod session;
mod style;

use session::{Flow, Session};
use std::io::{IsTerminal, Read};
use std::process::ExitCode;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;
use style::{ColorChoice, Style};

/// Stack for the solver thread. Encoding and evaluation recurse over the term structure, and
/// SMT-LIB files nest `let`s thousands deep.
const STACK_BYTES: usize = 1 << 30;

const USAGE: &str = "\
SMT-Rex, a SAT and SMT solver

Usage:
  smt-rex                    interactive prompt (or an SMT-LIB script piped on stdin)
  smt-rex <file.smt2>        run an SMT-LIB 2.6 script
  smt-rex <file.cnf>         solve a DIMACS CNF file
  smt-rex -e '<command>'     run one prompt command, e.g. smt-rex -e 'sat a & ~b'
  smt-rex -                  read an SMT-LIB script from stdin

Options:
  --timeout <seconds>        give up after this long and answer unknown
  --proof <file>             write a proof of unsatisfiability to <file>: LRAT for DIMACS,
                             Alethe for SMT-LIB (QF_UF, QF_LRA)
  --color <auto|always|never>
  -h, --help                 this help
  -V, --version              print the version

Exit codes: 0 done, 1 error; for DIMACS input 10 satisfiable, 20 unsatisfiable.";

fn main() -> ExitCode {
    std::thread::Builder::new()
        .name("smt-rex".into())
        .stack_size(STACK_BYTES)
        .spawn(real_main)
        .expect("spawn the solver thread")
        .join()
        .unwrap_or(ExitCode::FAILURE)
}

enum Input {
    Prompt,
    Stdin,
    File(String),
    Command(String),
}

struct Options {
    input: Input,
    timeout: Option<Duration>,
    color: ColorChoice,
    proof: Option<String>,
}

fn parse_args() -> Result<Options, String> {
    let mut args = std::env::args().skip(1);
    let mut opts = Options {
        input: Input::Prompt,
        timeout: None,
        color: ColorChoice::Auto,
        proof: None,
    };
    let mut input_set = false;
    let mut set_input = |opts: &mut Options, i: Input| {
        if std::mem::replace(&mut input_set, true) {
            return Err("give at most one input (a file, '-', or -e)".to_string());
        }
        opts.input = i;
        Ok(())
    };
    while let Some(a) = args.next() {
        match a.as_str() {
            "-h" | "--help" => {
                println!("{USAGE}");
                std::process::exit(0);
            }
            "-V" | "--version" => {
                println!("smt-rex {}", env!("CARGO_PKG_VERSION"));
                std::process::exit(0);
            }
            "-e" => {
                let cmd = args.next().ok_or("-e needs a command")?;
                set_input(&mut opts, Input::Command(cmd))?;
            }
            "--timeout" => {
                let s = args.next().ok_or("--timeout needs a number of seconds")?;
                let secs: f64 = s
                    .parse()
                    .ok()
                    .filter(|x: &f64| x.is_finite() && *x > 0.0)
                    .ok_or_else(|| format!("--timeout: '{s}' is not a positive number"))?;
                opts.timeout = Some(Duration::from_secs_f64(secs));
            }
            "--proof" => {
                opts.proof = Some(args.next().ok_or("--proof needs a file name")?);
            }
            "--color" | "--colour" => {
                opts.color = match args.next().as_deref() {
                    Some("auto") => ColorChoice::Auto,
                    Some("always") => ColorChoice::Always,
                    Some("never") => ColorChoice::Never,
                    _ => return Err("--color takes auto, always or never".into()),
                };
            }
            "-" => set_input(&mut opts, Input::Stdin)?,
            s if s.starts_with('-') => return Err(format!("unknown option '{s}' (see --help)")),
            path => set_input(&mut opts, Input::File(path.to_string()))?,
        }
    }
    Ok(opts)
}

fn real_main() -> ExitCode {
    let opts = match parse_args() {
        Ok(o) => o,
        Err(e) => {
            eprintln!("smt-rex: {e}");
            return ExitCode::FAILURE;
        }
    };

    // Ctrl-C raises the stop flag, which interrupts the running solve; a second Ctrl-C while
    // the flag is still up quits.
    let stop = Arc::new(AtomicBool::new(false));
    {
        let stop = stop.clone();
        let _ = ctrlc::set_handler(move || {
            if stop.swap(true, Ordering::Relaxed) {
                std::process::exit(130);
            }
        });
    }
    if let Some(t) = opts.timeout {
        let stop = stop.clone();
        std::thread::spawn(move || {
            std::thread::sleep(t);
            stop.store(true, Ordering::Relaxed);
        });
    }

    match opts.input {
        Input::Prompt if std::io::stdin().is_terminal() => {
            repl::run(Session::new(Style::new(opts.color), stop))
        }
        Input::Prompt | Input::Stdin => {
            let mut s = String::new();
            if let Err(e) = std::io::stdin().read_to_string(&mut s) {
                eprintln!("smt-rex: cannot read stdin: {e}");
                return ExitCode::FAILURE;
            }
            batch::smtlib(&s, stop)
        }
        Input::File(path) => {
            let src = match std::fs::read_to_string(&path) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("smt-rex: cannot read {path}: {e}");
                    return ExitCode::FAILURE;
                }
            };
            if looks_like_dimacs(&path, &src) {
                batch::dimacs(&src, &stop, opts.proof.as_deref())
            } else if let Some(proof_path) = &opts.proof {
                batch::alethe(&src, proof_path)
            } else {
                batch::smtlib(&src, stop)
            }
        }
        Input::Command(cmd) => {
            let mut session = Session::new(Style::new(opts.color), stop);
            match session.run_line(&cmd, &mut std::io::stdout()) {
                Ok(Flow::Continue | Flow::Exit) => ExitCode::SUCCESS,
                Err(e) => {
                    eprintln!("smt-rex: {e}");
                    ExitCode::FAILURE
                }
            }
        }
    }
}

/// By extension, else by the first line that is neither blank nor a `c` comment.
fn looks_like_dimacs(path: &str, src: &str) -> bool {
    if path.ends_with(".cnf") || path.ends_with(".dimacs") {
        return true;
    }
    if path.ends_with(".smt2") || path.ends_with(".smt") {
        return false;
    }
    src.lines()
        .map(str::trim)
        .find(|l| !l.is_empty() && !l.starts_with('c'))
        .is_some_and(|l| l.starts_with("p cnf"))
}
