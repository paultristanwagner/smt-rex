//! Encoding of sort-checked assertions into clauses for [`SmtBuilder`].
//!
//! - An equality between uninterpreted terms is an EUF atom; a `Bool` constant or predicate
//!   application `p` is the atom `p = |true` (with `|true ≠ |false`), so congruence covers
//!   predicates and Boolean arguments. Internal names start with U+0001.
//! - Connectives are Tseitin-encoded, constants folded.
//! - Linear arithmetic goes to the Simplex ([`crate::arith`]), QF_NRA arithmetic to the NRA
//!   theory as polynomials with a linear abstraction in the Simplex ([`crate::nlarith`]),
//!   bit-vectors are bit-blasted ([`crate::bv`]).
//! - `let`, `define-fun` and `:named` are resolved against already-encoded values ([`Bound`]),
//!   so shared subterms stay shared.

use crate::arith::Lin;
use crate::bv::{self, Bits, Blaster, Op};
use crate::nlarith::{PolyCmp, RPoly};
use crate::sexp::Sexp;
use crate::SmtBuilder;
use rustc_hash::FxHashMap;
use smtrex_core::Lit;
use smtrex_term::TermId;

use crate::script::{is_arith, negative_number, Def};

mod arith;
mod bits;
mod poly;
mod uf;

/// The value of a Boolean expression built only from `true`, `false`, `not`, `and`, `or` and
/// `ite`, if it is one.
pub(crate) fn const_bool(t: &Sexp) -> Option<bool> {
    match t {
        Sexp::Atom(a) if a == "true" => Some(true),
        Sexp::Atom(a) if a == "false" => Some(false),
        Sexp::Atom(_) => None,
        Sexp::List(l) => {
            let args = &l[1..];
            match l.first().and_then(Sexp::as_atom)? {
                "not" if args.len() == 1 => const_bool(&args[0]).map(|b| !b),
                "and" => args
                    .iter()
                    .map(const_bool)
                    .collect::<Option<Vec<_>>>()
                    .map(|v| v.iter().all(|b| *b)),
                "or" => args
                    .iter()
                    .map(const_bool)
                    .collect::<Option<Vec<_>>>()
                    .map(|v| v.iter().any(|b| *b)),
                "ite" if args.len() == 3 => {
                    if const_bool(&args[0])? {
                        const_bool(&args[1])
                    } else {
                        const_bool(&args[2])
                    }
                }
                _ => None,
            }
        }
    }
}

pub(crate) fn is_connective(head: &str) -> bool {
    matches!(
        head,
        "and" | "or" | "not" | "=>" | "xor" | "=" | "distinct" | "ite"
    ) || bv::is_predicate(head)
}

/// An already-encoded value bound to a name by `let`, a `define-fun` parameter or `:named`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Bound {
    Bool(Lit),
    /// A non-`Bool`, non-arithmetic term and its sort.
    Term(TermId, String),
    /// A `Real` value, as a linear expression over Simplex variables.
    Arith(Lin),
    /// A `Real` value in QF_NRA, as a polynomial over NRA variables.
    Poly(RPoly),
    /// A bit-vector, as its bits (least significant first).
    Bits(Bits),
}

impl Bound {
    fn sort(&self) -> std::borrow::Cow<'_, str> {
        match self {
            Bound::Bool(_) => "Bool".into(),
            Bound::Term(_, s) => s.into(),
            Bound::Arith(_) | Bound::Poly(_) => "Real".into(),
            Bound::Bits(b) => bv::sort_name(b.len() as u32).into(),
        }
    }
}

pub(crate) struct Encoder<'a> {
    pub(crate) builder: SmtBuilder,
    /// QF_NRA: arithmetic is encoded as polynomials for the NRA theory, not for the Simplex.
    pub(crate) nra: bool,
    /// Declared `Real` constants -> their NRA variables (QF_NRA; created on first use).
    pub(crate) poly_vars: FxHashMap<String, usize>,
    /// QF_NRA: variables eliminated by a top-level equation, and the polynomial standing for
    /// them (over variables that are not eliminated).
    pub(crate) poly_subst: FxHashMap<usize, RPoly>,
    /// QF_NRA: the LRA variable of each monomial in the linear abstraction.
    pub(crate) monomials: FxHashMap<smtrex_poly::mpoly::Monomial, smtrex_theory::lra::AVar>,
    /// QF_NRA: NRA atoms (SAT variables) already tied to their linear abstraction.
    pub(crate) abstracted: rustc_hash::FxHashSet<smtrex_core::Var>,
    /// QF_NRA: whether atoms get a linear abstraction (off with `SMTREX_NRA_NOLIN`, to measure).
    pub(crate) linear_abstraction: bool,
    /// Declared `Real` constants -> their Simplex variables (created on first use).
    pub(crate) real_vars: FxHashMap<String, smtrex_theory::lra::AVar>,
    /// Integer variables eliminated by a top-level equation, and the expression standing for
    /// them (over variables that are not eliminated).
    pub(crate) subst: FxHashMap<smtrex_theory::lra::AVar, Lin>,
    /// `(dividend, divisor)` -> the quotient and remainder variables of `div`/`mod`.
    pub(crate) divmods: FxHashMap<(Lin, smtrex_core::Rational), (Lin, Lin)>,
    /// Declared bit-vector constants -> their bits (created on first use).
    pub(crate) bv_vars: FxHashMap<String, Bits>,
    pub(crate) bv: Blaster,
    pub(crate) sigs: &'a FxHashMap<String, (Vec<String>, String)>,
    pub(crate) defs: &'a FxHashMap<String, Def>,
    /// Lexical scopes of `let` bindings / `define-fun` parameters, innermost last.
    pub(crate) scopes: Vec<FxHashMap<String, Bound>>,
    /// Names introduced by `(! t :named n)`; global, visible after their definition.
    pub(crate) named: FxHashMap<String, Bound>,
    /// Memoized `define-fun` applications, keyed by name and argument values.
    pub(crate) def_cache: FxHashMap<(String, Vec<Bound>), Bound>,
    /// EUF node standing for a `Bool` literal used as a term (see [`Self::node_for_lit`]).
    pub(crate) lit_nodes: FxHashMap<Lit, TermId>,
    /// `true` literal, forced true by a unit clause.
    pub(crate) true_lit: Lit,
    /// Reserved EUF constants used to encode `Bool`-sorted terms: a term's truth is `term=bool_true`
    /// and its falsity `term=bool_false`, with `bool_true != bool_false` asserted globally. The
    /// two-valued encoding is needed so that `Bool`-sorted *function arguments* get correct
    /// congruence (two `false` arguments must be provably equal).
    pub(crate) bool_true: TermId,
    pub(crate) bool_false: TermId,
    /// Bool-sorted term nodes already given the `(=true) | (=false)` linkage clause.
    pub(crate) linked: rustc_hash::FxHashSet<TermId>,
    pub(crate) bt_bf_distinct_added: bool,
    pub(crate) ite_counter: usize,
}

impl<'a> Encoder<'a> {
    pub(crate) fn new(
        sigs: &'a FxHashMap<String, (Vec<String>, String)>,
        defs: &'a FxHashMap<String, Def>,
        nra: bool,
    ) -> Encoder<'a> {
        let mut builder = SmtBuilder::new();
        let true_var = builder.fresh_var();
        let true_lit = true_var.pos();
        builder.add_clause(vec![true_lit]);
        let bool_true = builder.euf().mk_const("\u{1}true");
        let bool_false = builder.euf().mk_const("\u{1}false");
        Encoder {
            builder,
            nra,
            poly_vars: FxHashMap::default(),
            poly_subst: FxHashMap::default(),
            monomials: FxHashMap::default(),
            abstracted: rustc_hash::FxHashSet::default(),
            linear_abstraction: std::env::var_os("SMTREX_NRA_NOLIN").is_none(),
            real_vars: FxHashMap::default(),
            divmods: FxHashMap::default(),
            subst: FxHashMap::default(),
            bv_vars: FxHashMap::default(),
            bv: Blaster::new(true_lit),
            sigs,
            defs,
            scopes: Vec::new(),
            named: FxHashMap::default(),
            def_cache: FxHashMap::default(),
            lit_nodes: FxHashMap::default(),
            true_lit,
            bool_true,
            bool_false,
            linked: rustc_hash::FxHashSet::default(),
            bt_bf_distinct_added: false,
            ite_counter: 0,
        }
    }

    /// Encode `t` as a [`Bound`], dispatching on its sort.
    pub(crate) fn value(&mut self, t: &Sexp) -> Result<Bound, String> {
        // Binding forms first: they carry their sort, and resolving them directly keeps deeply
        // nested `let`s linear (computing `sort_of` first would rescan the nest at every level).
        if let Some(b) = self.resolve(t)? {
            return Ok(b);
        }
        let sort = self.sort_of(t)?;
        if sort == "Bool" {
            Ok(Bound::Bool(self.bool(t)?))
        } else if is_arith(&sort) && self.nra {
            Ok(Bound::Poly(self.rpoly(t)?))
        } else if is_arith(&sort) {
            Ok(Bound::Arith(self.lin(t)?))
        } else if bv::width(&sort).is_some() {
            Ok(Bound::Bits(self.bits(t)?))
        } else {
            Ok(Bound::Term(self.term(t)?, sort))
        }
    }

    pub(crate) fn lookup(&self, name: &str) -> Option<&Bound> {
        self.scopes
            .iter()
            .rev()
            .find_map(|s| s.get(name))
            .or_else(|| self.named.get(name))
    }

    /// Resolve the forms that bind or name values — `let`, `!`, a bound name, and `define-fun`
    /// applications — to an encoded value. `None` means `t` is an ordinary term or formula.
    pub(crate) fn resolve(&mut self, t: &Sexp) -> Result<Option<Bound>, String> {
        let (head, args) = match t {
            Sexp::Atom(a) => {
                if let Some(b) = self.lookup(a) {
                    return Ok(Some(b.clone()));
                }
                (a.as_str(), &[][..])
            }
            Sexp::List(l) => match l.first().and_then(Sexp::as_atom) {
                Some(h) => (h, &l[1..]),
                None => return Ok(None),
            },
        };
        match (head, t) {
            ("let", Sexp::List(_)) => {
                let [bindings, body] = args else {
                    return Err("let expects bindings and a body".to_string());
                };
                // Parallel binding: every right-hand side is evaluated in the outer scope.
                let mut scope = FxHashMap::default();
                for b in bindings.as_list().ok_or("let bindings must be a list")? {
                    let Some([Sexp::Atom(name), expr]) = b.as_list() else {
                        return Err("malformed let binding".to_string());
                    };
                    let v = self.value(expr)?;
                    scope.insert(name.clone(), v);
                }
                self.scopes.push(scope);
                let v = self.value(body);
                self.scopes.pop();
                Ok(Some(v?))
            }
            ("!", Sexp::List(_)) => {
                let (inner, attrs) = args.split_first().ok_or("! expects a term")?;
                let v = self.value(inner)?;
                for w in attrs.windows(2) {
                    if let [Sexp::Atom(k), Sexp::Atom(n)] = w {
                        if k == ":named" {
                            self.named.insert(n.clone(), v.clone());
                        }
                    }
                }
                Ok(Some(v))
            }
            _ => {
                let Some(def) = self.defs.get(head) else {
                    return Ok(None);
                };
                if def.params.len() != args.len() {
                    return Err(format!(
                        "'{head}' expects {} arguments, got {}",
                        def.params.len(),
                        args.len()
                    ));
                }
                let vals = args
                    .iter()
                    .map(|a| self.value(a))
                    .collect::<Result<Vec<_>, _>>()?;
                let key = (head.to_string(), vals);
                if let Some(v) = self.def_cache.get(&key) {
                    return Ok(Some(v.clone()));
                }
                // The body sees only its parameters (plus global declarations), not the caller's lets.
                let scope = def
                    .params
                    .iter()
                    .map(|(n, _)| n.clone())
                    .zip(key.1.iter().cloned())
                    .collect();
                let saved = std::mem::replace(&mut self.scopes, vec![scope]);
                let v = self.value(&def.body);
                self.scopes = saved;
                let v = v?;
                let sort = v.sort();
                if sort != def.ret && !(is_arith(&sort) && is_arith(&def.ret)) {
                    return Err(format!("'{head}' returned {sort}, not {}", def.ret));
                }
                self.def_cache.insert(key, v.clone());
                Ok(Some(v))
            }
        }
    }

    /// The sort of a term (only `"Bool"` vs everything-else matters for dispatch).
    pub(crate) fn sort_of(&self, t: &Sexp) -> Result<String, String> {
        self.sort_in(t, &mut Vec::new())
    }

    /// [`Self::sort_of`] with `local`: sorts of `let` names being looked through (not yet encoded).
    pub(crate) fn sort_in(
        &self,
        t: &Sexp,
        local: &mut Vec<(String, String)>,
    ) -> Result<String, String> {
        match t {
            Sexp::Atom(a) => match a.as_str() {
                "true" | "false" => Ok("Bool".to_string()),
                sym => {
                    if let Some((_, s)) = local.iter().rev().find(|(n, _)| n == sym) {
                        return Ok(s.clone());
                    }
                    if let Some(b) = self.lookup(sym) {
                        return Ok(b.sort().to_string());
                    }
                    if let Some((_, w)) = bv::literal(t)? {
                        return Ok(bv::sort_name(w));
                    }
                    if sym.starts_with(|c: char| c.is_ascii_digit()) {
                        return Ok("Real".to_string());
                    }
                    if !self.sigs.contains_key(sym)
                        && !self.defs.contains_key(sym)
                        && negative_number(sym).is_some()
                    {
                        return Ok("Real".to_string());
                    }
                    if let Some(d) = self.defs.get(sym) {
                        return Ok(d.ret.clone());
                    }
                    self.sigs
                        .get(sym)
                        .map(|(_, ret)| ret.clone())
                        .ok_or_else(|| format!("undeclared symbol '{sym}'"))
                }
            },
            Sexp::List(l) => {
                if let Some((_, w)) = bv::literal(t)? {
                    return Ok(bv::sort_name(w));
                }
                if let Some(op) = l.first().map(Op::parse).transpose()?.flatten() {
                    let ret = op.ret(l.len() - 1, |i| {
                        let s = self.sort_in(&l[i + 1], local)?;
                        bv::width(&s).ok_or_else(|| format!("expected a bit-vector, got {s}"))
                    })?;
                    return Ok(ret.sort_name());
                }
                let head = l
                    .first()
                    .and_then(Sexp::as_atom)
                    .ok_or("empty application")?;
                match head {
                    "and" | "or" | "not" | "=>" | "xor" | "=" | "distinct" | "<=" | "<" | ">="
                    | ">" => Ok("Bool".to_string()),
                    "+" | "-" | "*" | "/" => Ok("Real".to_string()),
                    "div" | "mod" | "abs" => Ok("Int".to_string()),
                    "ite" => self.sort_in(l.get(2).ok_or("ite expects 3 args")?, local), // then-branch
                    "!" => self.sort_in(l.get(1).ok_or("! expects a term")?, local),
                    "let" => {
                        let (Some(bindings), Some(body)) =
                            (l.get(1).and_then(Sexp::as_list), l.get(2))
                        else {
                            return Err("malformed let".to_string());
                        };
                        let mut sorts = Vec::with_capacity(bindings.len());
                        for b in bindings {
                            let Some([Sexp::Atom(n), e]) = b.as_list() else {
                                return Err("malformed let binding".to_string());
                            };
                            sorts.push((n.clone(), self.sort_in(e, local)?));
                        }
                        let depth = local.len();
                        local.extend(sorts);
                        let s = self.sort_in(body, local);
                        local.truncate(depth);
                        s
                    }
                    f => match self.defs.get(f) {
                        Some(d) => Ok(d.ret.clone()),
                        None => self
                            .sigs
                            .get(f)
                            .map(|(_, ret)| ret.clone())
                            .ok_or_else(|| format!("undeclared function '{f}'")),
                    },
                }
            }
        }
    }

    /// Encode a `Bool`-sorted formula into a literal, emitting Tseitin clauses as needed.
    pub(crate) fn bool(&mut self, t: &Sexp) -> Result<Lit, String> {
        if let Some(b) = self.resolve(t)? {
            return self.lit_of(b);
        }
        match t {
            Sexp::Atom(a) => match a.as_str() {
                "true" => Ok(self.true_lit),
                "false" => Ok(!self.true_lit),
                sym => {
                    // a Bool-sorted constant: encode as (sym = |true)
                    let term = self.builder.euf().mk_const(sym);
                    Ok(self.builder.eq_atom(term, self.bool_true))
                }
            },
            Sexp::List(l) => {
                let head = l
                    .first()
                    .and_then(Sexp::as_atom)
                    .ok_or("empty application")?;
                let args = &l[1..];
                match head {
                    "not" => Ok(!self.bool(&args[0])?),
                    "and" => {
                        let lits = self.bool_all(args)?;
                        Ok(self.tseitin_and(lits))
                    }
                    "or" => {
                        let lits = self.bool_all(args)?;
                        Ok(self.tseitin_or(lits))
                    }
                    "=>" => {
                        // (=> a b ... z) == (or !a !b ... z_last)
                        let mut lits = self.bool_all(args)?;
                        let last = lits.pop().ok_or("=> needs args")?;
                        let mut clause: Vec<Lit> = lits.into_iter().map(|l| !l).collect();
                        clause.push(last);
                        Ok(self.tseitin_or(clause))
                    }
                    "xor" => {
                        let lits = self.bool_all(args)?;
                        let mut acc = lits[0];
                        for &l in &lits[1..] {
                            acc = self.mk_xor(acc, l);
                        }
                        Ok(acc)
                    }
                    "ite" => {
                        let c = self.bool(&args[0])?;
                        let th = self.bool(&args[1])?;
                        let el = self.bool(&args[2])?;
                        Ok(self.tseitin_ite(c, th, el))
                    }
                    "=" => self.eq(args),
                    "distinct" => self.distinct(args),
                    "<=" | "<" | ">=" | ">" => self.compare(head, args),
                    h if bv::is_predicate(h) => {
                        let op = Op::parse(&l[0])?.expect("a bit-vector predicate");
                        let [x, y] = args else {
                            return Err(format!("'{h}' expects 2 arguments"));
                        };
                        let (x, y) = (self.bits(x)?, self.bits(y)?);
                        Ok(self.bv.predicate(&mut self.builder, op, &x, &y))
                    }
                    _ => {
                        // predicate application: encode as ((P args) = |true)
                        let term = self.term(t)?;
                        Ok(self.builder.eq_atom(term, self.bool_true))
                    }
                }
            }
        }
    }

    pub(crate) fn bool_all(&mut self, ts: &[Sexp]) -> Result<Vec<Lit>, String> {
        ts.iter().map(|t| self.bool(t)).collect()
    }

    /// `(= a b ...)`: iff-chain over Bool args, equality-atom chain over `U` args.
    pub(crate) fn eq(&mut self, args: &[Sexp]) -> Result<Lit, String> {
        if args.len() < 2 {
            return Ok(self.true_lit);
        }
        let sort = self.sort_of(&args[0])?;
        if is_arith(&sort) && self.nra {
            let ps = args
                .iter()
                .map(|a| self.rpoly(a))
                .collect::<Result<Vec<_>, _>>()?;
            let mut conj = Vec::new();
            for w in ps.windows(2) {
                conj.push(self.poly_cmp(&w[0].sub(&w[1]), PolyCmp::Eq));
            }
            return Ok(self.tseitin_and(conj));
        }
        if is_arith(&sort) {
            let lins = args
                .iter()
                .map(|a| self.lin(a))
                .collect::<Result<Vec<_>, _>>()?;
            let mut conj = Vec::new();
            for w in lins.windows(2) {
                conj.push(self.arith_eq(&w[0].sub(&w[1])));
            }
            return Ok(self.tseitin_and(conj));
        }
        if bv::width(&sort).is_some() {
            let vs = self.bits_all(args)?;
            let mut conj = Vec::new();
            for w in vs.windows(2) {
                conj.push(self.bv.eq(&mut self.builder, &w[0], &w[1]));
            }
            return Ok(self.tseitin_and(conj));
        }
        if sort == "Bool" {
            let lits = self.bool_all(args)?;
            let mut conj = Vec::new();
            for w in lits.windows(2) {
                conj.push(self.mk_iff(w[0], w[1]));
            }
            Ok(self.tseitin_and(conj))
        } else {
            let mut terms = Vec::with_capacity(args.len());
            for a in args {
                terms.push(self.term(a)?);
            }
            let mut conj = Vec::new();
            for w in terms.windows(2) {
                conj.push(self.builder.eq_atom(w[0], w[1]));
            }
            Ok(self.tseitin_and(conj))
        }
    }

    /// `(distinct a b ...)`: pairwise `!=`.
    pub(crate) fn distinct(&mut self, args: &[Sexp]) -> Result<Lit, String> {
        if is_arith(&self.sort_of(&args[0])?) && self.nra {
            let ps = args
                .iter()
                .map(|a| self.rpoly(a))
                .collect::<Result<Vec<_>, _>>()?;
            let mut conj = Vec::new();
            for i in 0..ps.len() {
                for j in (i + 1)..ps.len() {
                    let eq = self.poly_cmp(&ps[i].sub(&ps[j]), PolyCmp::Eq);
                    conj.push(!eq);
                }
            }
            return Ok(self.tseitin_and(conj));
        }
        if is_arith(&self.sort_of(&args[0])?) {
            let lins = args
                .iter()
                .map(|a| self.lin(a))
                .collect::<Result<Vec<_>, _>>()?;
            let mut conj = Vec::new();
            for i in 0..lins.len() {
                for j in (i + 1)..lins.len() {
                    let eq = self.arith_eq(&lins[i].sub(&lins[j]));
                    conj.push(!eq);
                }
            }
            return Ok(self.tseitin_and(conj));
        }
        if bv::width(&self.sort_of(&args[0])?).is_some() {
            let vs = self.bits_all(args)?;
            let mut conj = Vec::new();
            for i in 0..vs.len() {
                for j in (i + 1)..vs.len() {
                    conj.push(!self.bv.eq(&mut self.builder, &vs[i], &vs[j]));
                }
            }
            return Ok(self.tseitin_and(conj));
        }
        let is_bool = self.sort_of(&args[0])? == "Bool";
        let mut conj = Vec::new();
        if is_bool {
            let lits = self.bool_all(args)?;
            for i in 0..lits.len() {
                for j in (i + 1)..lits.len() {
                    // distinct bools: lits[i] xor lits[j]
                    let x = self.mk_xor(lits[i], lits[j]);
                    conj.push(x);
                }
            }
        } else {
            let mut terms = Vec::with_capacity(args.len());
            for a in args {
                terms.push(self.term(a)?);
            }
            for i in 0..terms.len() {
                for j in (i + 1)..terms.len() {
                    let e = self.builder.eq_atom(terms[i], terms[j]);
                    conj.push(!e);
                }
            }
        }
        Ok(self.tseitin_and(conj))
    }

    // ----- bit-vectors -----

    pub(crate) fn tseitin_and(&mut self, lits: Vec<Lit>) -> Lit {
        // Fold constants and duplicates: true drops out, false (or l ∧ ¬l) decides it.
        let mut kept: Vec<Lit> = Vec::with_capacity(lits.len());
        for l in lits {
            if l == self.true_lit || kept.contains(&l) {
                continue;
            }
            if l == !self.true_lit || kept.contains(&!l) {
                return !self.true_lit;
            }
            kept.push(l);
        }
        let lits = kept;
        if lits.is_empty() {
            return self.true_lit;
        }
        if lits.len() == 1 {
            return lits[0];
        }
        let r = self.builder.fresh_var().pos();
        for &l in &lits {
            self.builder.add_clause(vec![!r, l]); // r -> l
        }
        let mut big = Vec::with_capacity(lits.len() + 1);
        big.push(r);
        for &l in &lits {
            big.push(!l); // (all l) -> r
        }
        self.builder.add_clause(big);
        r
    }

    pub(crate) fn tseitin_or(&mut self, lits: Vec<Lit>) -> Lit {
        // ¬(¬a ∧ ¬b ...), so the same folding applies.
        let mut kept: Vec<Lit> = Vec::with_capacity(lits.len());
        for l in lits {
            if l == !self.true_lit || kept.contains(&l) {
                continue;
            }
            if l == self.true_lit || kept.contains(&!l) {
                return self.true_lit;
            }
            kept.push(l);
        }
        let lits = kept;
        if lits.is_empty() {
            return !self.true_lit;
        }
        if lits.len() == 1 {
            return lits[0];
        }
        let r = self.builder.fresh_var().pos();
        for &l in &lits {
            self.builder.add_clause(vec![!l, r]); // l -> r
        }
        let mut big = Vec::with_capacity(lits.len() + 1);
        big.push(!r);
        for &l in &lits {
            big.push(l); // r -> (some l)
        }
        self.builder.add_clause(big);
        r
    }

    pub(crate) fn tseitin_ite(&mut self, c: Lit, t: Lit, e: Lit) -> Lit {
        if c == self.true_lit || t == e {
            return t;
        }
        if c == !self.true_lit {
            return e;
        }
        let r = self.builder.fresh_var().pos();
        self.builder.add_clause(vec![!c, !r, t]);
        self.builder.add_clause(vec![!c, r, !t]);
        self.builder.add_clause(vec![c, !r, e]);
        self.builder.add_clause(vec![c, r, !e]);
        r
    }

    pub(crate) fn mk_xor(&mut self, a: Lit, b: Lit) -> Lit {
        for (x, y) in [(a, b), (b, a)] {
            if x == self.true_lit {
                return !y;
            }
            if x == !self.true_lit {
                return y;
            }
        }
        if a == b {
            return !self.true_lit;
        }
        if a == !b {
            return self.true_lit;
        }
        let r = self.builder.fresh_var().pos();
        self.builder.add_clause(vec![!a, !b, !r]);
        self.builder.add_clause(vec![a, b, !r]);
        self.builder.add_clause(vec![a, !b, r]);
        self.builder.add_clause(vec![!a, b, r]);
        r
    }

    pub(crate) fn mk_iff(&mut self, a: Lit, b: Lit) -> Lit {
        !self.mk_xor(a, b)
    }
}
