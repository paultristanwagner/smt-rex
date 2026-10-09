//! Proof log of a solver run, for certifying `unsat`.
//!
//! Clause ids follow LRAT: the clauses passed to [`crate::Solver::add_clause`] are `1, 2, …` in
//! that order, derived clauses get the following ids. A derived clause is justified by reverse
//! unit propagation over its hints, listed in propagation order (each hint is unit, or falsified
//! by the last one, after assuming the clause false). Theory lemmas are clauses the attached
//! theory asserts; the SMT layer justifies them.

use smtrex_core::Lit;
use std::io::{self, Write};

pub type ClauseId = u64;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Step {
    /// An input clause, as given (before any simplification).
    Input { id: ClauseId, lits: Vec<Lit> },
    /// A clause implied by reverse unit propagation over `hints`.
    Derived {
        id: ClauseId,
        lits: Vec<Lit>,
        hints: Vec<ClauseId>,
    },
    /// A clause asserted by the theory.
    Theory { id: ClauseId, lits: Vec<Lit> },
    /// The clause is no longer used.
    Delete { id: ClauseId },
}

#[derive(Default, Debug)]
pub struct Proof {
    pub steps: Vec<Step>,
    next_id: ClauseId,
}

impl Proof {
    pub fn new() -> Proof {
        Proof {
            steps: Vec::new(),
            next_id: 1,
        }
    }

    pub(crate) fn fresh_id(&mut self) -> ClauseId {
        let id = self.next_id;
        self.next_id += 1;
        id
    }

    /// Write the derivation in LRAT text format (the input clauses are the DIMACS file).
    /// Fails if the log contains theory lemmas, which LRAT cannot express.
    pub fn write_lrat(&self, out: &mut impl Write) -> io::Result<()> {
        let mut last = 0;
        for s in &self.steps {
            match s {
                Step::Input { id, .. } => last = *id,
                Step::Derived { id, lits, hints } => {
                    last = *id;
                    write!(out, "{id}")?;
                    for l in lits {
                        write!(out, " {}", l.to_dimacs())?;
                    }
                    write!(out, " 0")?;
                    for h in hints {
                        write!(out, " {h}")?;
                    }
                    writeln!(out, " 0")?;
                }
                Step::Delete { id } => writeln!(out, "{last} d {id} 0")?,
                Step::Theory { .. } => {
                    return Err(io::Error::other("theory lemmas have no LRAT form"));
                }
            }
        }
        Ok(())
    }
}
