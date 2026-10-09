//! Alethe proofs of `unsat` for QF_UF and QF_LRA, checked by Carcara:
//! `carcara check --expand-let-bindings --apply-function-defs --allow-int-real-subtyping`.
//!
//! The script is solved again by an encoder that keeps every SAT variable equal to one Alethe
//! term (expanded, nothing folded): every input clause is an assumption or a tautology rule
//! instance, the SAT core's LRAT log becomes resolution steps, and theory lemmas are re-derived
//! independently, EUF by a congruence closure of its own and arithmetic by a Farkas linear
//! program, so an unsound lemma is reported instead of certified.
//!
//! Not supported yet (reported as such): several `check-sat`s or `push`/`pop`, double negation,
//! Boolean function arguments, `ite` over uninterpreted sorts, n-ary `=`.

use crate::arith::{Cmp, Lin};
use crate::SmtBuilder;
use rustc_hash::FxHashMap;
use smtrex_core::{Lit, Var};
use smtrex_term::TermId;
use smtrex_theory::lra::AVar;
use std::io::{self, Write};

mod arith;
mod euf;
mod formula;
mod problem;
mod write;

use arith::real_text;
use euf::{node_text, Closure, LemmaWriter, Proved};
use problem::Problem;

pub enum Outcome {
    Sat,
    /// Unsatisfiable; the proof was written.
    Unsat,
}

/// Solve a QF_UF or QF_LRA script and, if it is unsatisfiable, write its proof to the writer `open`
/// returns (called only then). The proof is streamed: it can be much larger than the input.
pub fn prove<W: Write>(src: &str, open: impl FnOnce() -> io::Result<W>) -> Result<Outcome, String> {
    let problem = Problem::read(src)?;
    let mut enc = Encoder::new(&problem);
    for a in &problem.asserts {
        let l = enc.lit(a)?;
        let text = enc.render(l);
        enc.clause(vec![L(l)], How::Assume(text));
    }
    match enc.b.solve() {
        Some(true) => Ok(Outcome::Sat),
        Some(false) => {
            let proof = enc.b.take_proof().expect("proofs are enabled");
            let mut out = open().map_err(|e| format!("cannot write the proof: {e}"))?;
            enc.write(&proof.steps, &mut out)
                .map_err(|e| format!("cannot write the proof: {e}"))?;
            out.flush()
                .map_err(|e| format!("cannot write the proof: {e}"))?;
            Ok(Outcome::Unsat)
        }
        None => Err("interrupted".to_string()),
    }
}

/// A literal of a rule instance: `L(l)` is the literal `l`; `N(c)` is the negation of the
/// subformula `c`, written `(not c)` by the rule even when `c` is itself a negation (the clause
/// then contains the double negation, which [`Encoder::write`] removes with `not_not`).
#[derive(Clone, Copy)]
enum Part {
    L(Lit),
    N(Lit),
}
use Part::{L, N};

impl Part {
    fn lit(self) -> Lit {
        match self {
            L(l) => l,
            N(c) => !c,
        }
    }
}

/// The relation of a linear constraint `lin ⋈ 0`.
#[derive(Clone, Copy)]
enum Rel {
    Cmp(Cmp),
    Eq,
}

/// Why an input clause holds.
enum How {
    /// It is a linear-arithmetic tautology (`la_generic`; the Farkas coefficients are found
    /// when the proof is written).
    Lra,
    /// It is `(cl (= a b) (not (<= a b)) (not (<= b a)))` (`la_disequality`).
    Diseq,
    /// It is `(cl c (= T b))` (`then` false) or `(cl (not c) (= T a))` (`then` true) for the
    /// arithmetic term `T = (ite c a b)`, written `ite`; `u` is
    /// `(ite c (= T a) (= T b))`, which `ite_intro` provides.
    Ite { ite: String, u: String, then: bool },
    /// It is an assertion.
    Assume(String),
    /// It is an instance of this tautology rule, literals in the rule's order.
    Rule(&'static str),
    /// The same for rules that name one argument of the formula (0-based), like `and_pos`.
    RuleAt(&'static str, usize),
    /// It is `equiv1` (side 1) or `equiv2` (side 2) of the equivalence `base`, itself an
    /// instance of `rule`.
    Equiv {
        rule: &'static str,
        base: String,
        side: u8,
    },
}

struct Encoder<'a> {
    problem: &'a Problem,
    b: SmtBuilder,
    /// The Alethe term of each SAT variable and whether it is named (EUF transitivity atoms
    /// are looked up in the EUF).
    terms: Vec<Option<(String, bool)>>,
    /// The sort of every application node, for its definition in the proof.
    node_sorts: FxHashMap<TermId, String>,
    /// Real constants and their Simplex variables, and each variable's name.
    real_vars: FxHashMap<String, AVar>,
    real_names: FxHashMap<AVar, String>,
    /// The linear constraint of each arithmetic atom written as in the input (the Simplex's
    /// own atoms are read from the theory).
    meanings: FxHashMap<Var, (Lin, Rel)>,
    /// Encoded formulas by their text.
    memo: FxHashMap<String, Lit>,
    /// The justification of each input clause, in the order they were added.
    hows: Vec<(Vec<Part>, How)>,
    true_node: TermId,
}

impl<'a> Encoder<'a> {
    fn new(problem: &'a Problem) -> Encoder<'a> {
        let mut b = SmtBuilder::new();
        b.enable_proof();
        let true_node = b.euf().mk_const("true");
        Encoder {
            problem,
            b,
            terms: Vec::new(),
            node_sorts: FxHashMap::default(),
            real_vars: FxHashMap::default(),
            real_names: FxHashMap::default(),
            meanings: FxHashMap::default(),
            memo: FxHashMap::default(),
            hows: Vec::new(),
            true_node,
        }
    }

    /// Add a clause whose literals are given as the rule writes them (see [`Part`]).
    fn clause(&mut self, parts: Vec<Part>, how: How) {
        let lits: Vec<Lit> = parts.iter().map(|p| p.lit()).collect();
        self.hows.push((parts, how));
        self.b.add_clause(lits);
    }

    /// Record the Alethe term of `v`. A `named` term is defined once as `@v<index>` and
    /// referred to by that name, so terms are shared instead of repeated.
    fn set_term(&mut self, v: Var, term: String, named: bool) {
        if self.terms.len() <= v.index() {
            self.terms.resize(v.index() + 1, None);
        }
        self.terms[v.index()] = Some((term, named));
    }

    /// A variable for a compound formula, written `@v<index>` and defined in the proof.
    fn new_var(&mut self, body: String) -> Lit {
        let v = self.b.fresh_var();
        self.set_term(v, body, true);
        v.pos()
    }

    /// A variable for a short term written out in place (a symbol, an equality of names).
    fn new_leaf(&mut self, term: String) -> Lit {
        let v = self.b.fresh_var();
        self.set_term(v, term, false);
        v.pos()
    }

    /// `(head lit1 lit2 ...)` over the rendered literals.
    fn body(&self, head: &str, lits: &[Lit]) -> String {
        let args: Vec<String> = lits.iter().map(|&l| self.render(l)).collect();
        format!("({head} {})", args.join(" "))
    }

    fn render(&self, l: Lit) -> String {
        let v = l.var();
        let term = match self.terms.get(v.index()).and_then(Option::as_ref) {
            Some((_, true)) => format!("@v{}", v.index()),
            Some((t, false)) => t.clone(),
            None => {
                let (a, b) = self
                    .b
                    .euf_ref()
                    .atom(v)
                    .expect("every SAT variable has a term or is an EUF atom");
                format!("(= {} {})", self.text(a), self.text(b))
            }
        };
        if l.is_negated() {
            format!("(not {term})")
        } else {
            term
        }
    }

    fn render_clause(&self, lits: &[Lit]) -> String {
        let mut s = String::from("(cl");
        for &l in lits {
            s.push(' ');
            s.push_str(&self.render(l));
        }
        s.push(')');
        s
    }

    // ----- writing the proof -----
}
