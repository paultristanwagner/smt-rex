//! The prompt's short formula language and its translation to SMT-LIB.
//!
//! ```text
//!   formula ::= imp [ '<->' formula ]          (right-associative)
//!   imp     ::= or  [ '->' imp ]               (right-associative)
//!   or      ::= and { '|' and }
//!   and     ::= not { '&' not }
//!   not     ::= '~' not | primary
//!   primary ::= '(' formula ')' | atom
//!
//!   atom, propositional:   IDENT | 'true' | 'false'
//!   atom, QF_EQ:           IDENT ('=' | '!=') IDENT
//!   atom, QF_UF:           term  ('=' | '!=') term
//!   term                   IDENT [ '(' term { ',' term } ')' ]
//!
//!   atom, QF_LRA, QF_LIA:  'true' | 'false' | linear REL linear
//!   atom, QF_NRA:          'true' | 'false' | poly REL poly
//!   REL                    '<=' | '<' | '>=' | '>' | '=' | '!='
//!   linear, poly           summand { ('+' | '-') summand }
//!   summand                { '+' | '-' } [ COEF ] factor { ('*' | '/') factor }
//!   factor                 NUMBER | IDENT [ '^' INTEGER ]          ('^' only in QF_NRA)
//!   NUMBER                 42 | 0.8 | .5 | 1/2
//!   COEF                   a NUMBER directly followed by a letter: 2x, 0.8x, 1/2z
//! ```
//!
//! Alternative spellings: `!` for `~`, `&&`, `||`, `=>` for `->`, `<=>` for `<->`, `==` for `=`.
//!
//! `1/2z` is `(1/2)·z`: a fraction is two integers around a `/` with no spaces. Otherwise `/`
//! divides by a number (`z/2`). Implicit multiplication needs the number and the variable to
//! touch (`2x`). A linear summand has at most one variable; in QF_NRA a summand is a monomial.
//! In QF_LRA and QF_LIA, one `min(linear)` or `max(linear)` may appear as a top-level conjunct.

mod parse;
mod smtlib;
mod tseitin;

pub use parse::{parse, parse_constraints, ParseError};
pub use smtlib::{split_objective, to_smtlib, Smt};
pub use tseitin::{show_cnf, tseitin};

use smtrex_core::Rational;
use std::fmt;

/// Which atoms a formula may contain.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Atoms {
    /// Propositional variables (`sat`, `tseitin`).
    Prop,
    /// Equalities between constants (QF_EQ).
    Equality,
    /// Equalities between terms with uninterpreted functions (QF_EQUF).
    Functions,
    /// Linear constraints over real variables (QF_LRA).
    Arith,
    /// Linear constraints over integer variables (QF_LIA).
    Int,
    /// Polynomial constraints over real variables (QF_NRA).
    Poly,
}

impl Atoms {
    /// Whether atoms are arithmetic comparisons.
    pub fn arithmetic(self) -> bool {
        matches!(self, Atoms::Arith | Atoms::Int | Atoms::Poly)
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Formula {
    Const(bool),
    Var(String),
    /// `lhs = rhs`, or `lhs != rhs` when `!equal`.
    Eq {
        lhs: Term,
        rhs: Term,
        equal: bool,
    },
    /// A linear constraint `lhs rel rhs` (QF_LRA, QF_LIA).
    Cmp {
        lhs: Linear,
        rel: Rel,
        rhs: Linear,
    },
    /// A polynomial constraint `lhs rel rhs` (QF_NRA).
    PolyCmp {
        lhs: Poly,
        rel: Rel,
        rhs: Poly,
    },
    Not(Box<Formula>),
    And(Vec<Formula>),
    Or(Vec<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Iff(Box<Formula>, Box<Formula>),
    /// An objective `min(t)` / `max(t)` (QF_LRA); only valid as a top-level conjunct, see
    /// [`split_objective`].
    Objective {
        maximize: bool,
        term: Linear,
    },
}

/// A constant `c` (no arguments) or an application `f(t1, ..., tn)`.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Term {
    pub name: String,
    pub args: Vec<Term>,
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.name)?;
        if !self.args.is_empty() {
            f.write_str("(")?;
            for (i, a) in self.args.iter().enumerate() {
                if i > 0 {
                    f.write_str(", ")?;
                }
                write!(f, "{a}")?;
            }
            f.write_str(")")?;
        }
        Ok(())
    }
}

/// A linear expression `c1·x1 + ... + cn·xn + constant`. Each variable appears once, in
/// first-occurrence order; a zero coefficient (`x - x`) keeps the variable.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Linear {
    pub coeffs: Vec<(String, Rational)>,
    pub constant: Rational,
}

impl fmt::Display for Linear {
    /// The term in the short syntax, e.g. `2x - y/2 + 3x/4 + 3`.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        let mut part = |f: &mut fmt::Formatter<'_>, c: &Rational, x: Option<&str>| {
            let neg = c.is_negative();
            let a = c.abs();
            if first {
                if neg {
                    f.write_str("-")?;
                }
            } else {
                f.write_str(if neg { " - " } else { " + " })?;
            }
            first = false;
            match x {
                Some(x) if a == Rational::one() => write!(f, "{x}"),
                Some(x) if a.is_integer() => write!(f, "{a}{x}"),
                Some(x) => {
                    let (n, d) = (a.numer(), a.denom());
                    if n == 1.into() {
                        write!(f, "{x}/{d}")
                    } else {
                        write!(f, "{n}{x}/{d}")
                    }
                }
                None => write!(f, "{a}"),
            }
        };
        for (x, c) in &self.coeffs {
            part(f, c, Some(x))?;
        }
        if !self.constant.is_zero() || self.coeffs.is_empty() {
            part(f, &self.constant, None)?;
        }
        Ok(())
    }
}

impl Linear {
    fn add_var(&mut self, x: &str, c: &Rational) {
        match self.coeffs.iter_mut().find(|(y, _)| y == x) {
            Some((_, d)) => *d = &*d + c,
            None => self.coeffs.push((x.to_string(), c.clone())),
        }
    }
}

/// A monomial: variables with positive exponents, sorted by name; empty for the constant.
pub type Monomial = Vec<(String, u32)>;

/// A polynomial `c1·m1 + ... + cn·mn`: like monomials merged, in first-occurrence order.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Poly {
    pub terms: Vec<(Monomial, Rational)>,
}

impl Poly {
    fn add_term(&mut self, m: Monomial, c: &Rational) {
        match self.terms.iter_mut().find(|(n, _)| *n == m) {
            Some((_, d)) => *d = &*d + c,
            None => self.terms.push((m, c.clone())),
        }
    }

    fn vars(&self) -> impl Iterator<Item = &String> {
        self.terms
            .iter()
            .flat_map(|(m, _)| m.iter().map(|(x, _)| x))
    }
}

/// The comparison of a linear constraint.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Rel {
    Le,
    Lt,
    Ge,
    Gt,
    Eq,
    Ne,
}

impl Formula {
    /// Propositional variables, in first-occurrence order.
    pub fn vars(&self) -> Vec<String> {
        let mut out = Vec::new();
        self.walk(&mut |f| {
            if let Formula::Var(v) = f {
                if !out.contains(v) {
                    out.push(v.clone());
                }
            }
        });
        out
    }

    /// The numeric variables of an arithmetic formula, in first-occurrence order.
    pub fn numeric_vars(&self) -> Vec<String> {
        let mut out: Vec<String> = Vec::new();
        let mut add = |x: &String| {
            if !out.contains(x) {
                out.push(x.clone());
            }
        };
        self.walk(&mut |f| match f {
            Formula::Cmp { lhs, rhs, .. } => {
                lhs.coeffs
                    .iter()
                    .chain(&rhs.coeffs)
                    .for_each(|(x, _)| add(x));
            }
            Formula::PolyCmp { lhs, rhs, .. } => lhs.vars().chain(rhs.vars()).for_each(&mut add),
            Formula::Objective { term, .. } => term.coeffs.iter().for_each(|(x, _)| add(x)),
            _ => {}
        });
        out
    }

    /// Every term (constants and applications, including subterms), in first-occurrence order.
    pub fn terms(&self) -> Vec<Term> {
        fn add(t: &Term, out: &mut Vec<Term>) {
            for a in &t.args {
                add(a, out);
            }
            if !out.contains(t) {
                out.push(t.clone());
            }
        }
        let mut out = Vec::new();
        self.walk(&mut |f| {
            if let Formula::Eq { lhs, rhs, .. } = f {
                add(lhs, &mut out);
                add(rhs, &mut out);
            }
        });
        out
    }

    fn walk(&self, visit: &mut dyn FnMut(&Formula)) {
        visit(self);
        match self {
            Formula::Not(a) => a.walk(visit),
            Formula::And(xs) | Formula::Or(xs) => xs.iter().for_each(|x| x.walk(visit)),
            Formula::Implies(a, b) | Formula::Iff(a, b) => {
                a.walk(visit);
                b.walk(visit);
            }
            _ => {}
        }
    }
}
