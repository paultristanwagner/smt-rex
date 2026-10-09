//! The non-interactive modes: an SMT-LIB script, a DIMACS CNF, and an SMT-LIB script with an
//! Alethe proof.

use smtrex_sat::dimacs::Cnf;
use smtrex_sat::proof::Proof;
use smtrex_sat::{SolveResult, Solver};
use smtrex_smt::alethe;
use smtrex_smt::script::{Response, Script};
use smtrex_smt::sexp::parse_script;
use std::io::{BufWriter, Write};
use std::process::ExitCode;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

/// Run an SMT-LIB script command by command, printing each response as it comes. The first
/// error prints `(error "...")` and stops (`:error-behavior immediate-exit`): carrying on past a
/// rejected `assert` could turn into a wrong `sat`.
pub fn smtlib(input: &str, stop: Arc<AtomicBool>) -> ExitCode {
    let fail = |msg: &str| {
        println!("(error \"{}\")", msg.replace('"', "\"\""));
        ExitCode::FAILURE
    };
    let cmds = match parse_script(input) {
        Ok(c) => c,
        Err(e) => return fail(&e),
    };
    let mut script = Script::new();
    script.set_stop_flag(stop);
    for cmd in &cmds {
        match script.exec(cmd) {
            Ok(Some(Response::Check(r))) => {
                println!("{}", r.answer.as_str());
                if let Some(why) = &r.reason {
                    eprintln!("smt-rex: unknown: {why}");
                }
            }
            Ok(Some(Response::Text(t))) => println!("{t}"),
            Ok(None) => {}
            Err(e) => return fail(&e),
        }
        if script.exited() {
            break;
        }
    }
    ExitCode::SUCCESS
}

pub enum DimacsResult {
    Sat(Vec<bool>),
    /// With the solver's proof if one was requested.
    Unsat(Option<Proof>),
    Unknown(String),
}

/// Solve a CNF. A model is checked against every clause before it is reported.
pub fn solve_dimacs(cnf: &Cnf, stop: &Arc<AtomicBool>, with_proof: bool) -> DimacsResult {
    let mut s = Solver::new();
    if with_proof {
        s.enable_proof();
    }
    s.set_stop_flag(stop.clone());
    s.ensure_vars(cnf.num_vars);
    for c in &cnf.clauses {
        s.add_clause(c);
    }
    match s.solve() {
        SolveResult::Sat(model) => {
            let ok = cnf
                .clauses
                .iter()
                .all(|c| c.iter().any(|l| model[l.var().index()] != l.is_negated()));
            if ok {
                DimacsResult::Sat(model)
            } else {
                DimacsResult::Unknown("model self-check failed".into())
            }
        }
        SolveResult::Unsat => DimacsResult::Unsat(s.take_proof()),
        SolveResult::Interrupted => DimacsResult::Unknown("interrupted".into()),
    }
}

/// SAT-competition output (`s SATISFIABLE` and `v` lines) and exit codes 10 / 20. With
/// `proof_path`, an unsat answer also writes an LRAT proof there.
pub fn dimacs(src: &str, stop: &Arc<AtomicBool>, proof_path: Option<&str>) -> ExitCode {
    let cnf = match smtrex_sat::dimacs::parse(src) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("smt-rex: {e}");
            return ExitCode::FAILURE;
        }
    };
    match solve_dimacs(&cnf, stop, proof_path.is_some()) {
        DimacsResult::Sat(model) => {
            println!("s SATISFIABLE");
            let mut line = String::from("v");
            for (i, &b) in model.iter().enumerate() {
                let lit = format!(" {}{}", if b { "" } else { "-" }, i + 1);
                if line.len() + lit.len() > 78 {
                    println!("{line}");
                    line = String::from("v");
                }
                line.push_str(&lit);
            }
            println!("{line} 0");
            ExitCode::from(10)
        }
        DimacsResult::Unsat(proof) => {
            println!("s UNSATISFIABLE");
            if let (Some(path), Some(proof)) = (proof_path, &proof) {
                let written = std::fs::File::create(path).and_then(|f| {
                    let mut w = BufWriter::new(f);
                    proof.write_lrat(&mut w)?;
                    w.flush()
                });
                if let Err(e) = written {
                    eprintln!("smt-rex: cannot write the proof to {path}: {e}");
                    return ExitCode::FAILURE;
                }
            }
            ExitCode::from(20)
        }
        DimacsResult::Unknown(why) => {
            println!("s UNKNOWN");
            eprintln!("smt-rex: {why}");
            ExitCode::SUCCESS
        }
    }
}

/// Solve an SMT-LIB script in proof mode; on `unsat`, write its Alethe proof to `path`.
pub fn alethe(src: &str, path: &str) -> ExitCode {
    let open = || std::fs::File::create(path).map(BufWriter::new);
    match alethe::prove(src, open) {
        Ok(alethe::Outcome::Sat) => {
            println!("sat");
            ExitCode::SUCCESS
        }
        Ok(alethe::Outcome::Unsat) => {
            println!("unsat");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("smt-rex: {e}");
            ExitCode::FAILURE
        }
    }
}
