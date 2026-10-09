//! Uninterpreted terms and Boolean-sorted terms used as terms.

use crate::sexp::Sexp;
use smtrex_core::Lit;
use smtrex_term::TermId;

use super::*;

impl Encoder<'_> {
    /// Give a `Bool`-sorted term node `n` the two-valued linkage `(n=true) | (n=false)` (once),
    /// and ensure the global `bool_true != bool_false` constraint exists.
    pub(crate) fn link_bool(&mut self, n: TermId) {
        if n == self.bool_true || n == self.bool_false || !self.linked.insert(n) {
            return;
        }
        let et = self.builder.eq_atom(n, self.bool_true);
        let ef = self.builder.eq_atom(n, self.bool_false);
        self.builder.add_clause(vec![et, ef]);
        if !self.bt_bf_distinct_added {
            self.bt_bf_distinct_added = true;
            let e = self.builder.eq_atom(self.bool_true, self.bool_false);
            self.builder.add_clause(vec![!e]);
        }
    }

    /// Build the EUF node for a `Bool`-sorted term used *as a term* (e.g. a function argument),
    /// wiring its propositional truth literal to `node = bool_true`.
    pub(crate) fn bool_arg(&mut self, t: &Sexp) -> Result<TermId, String> {
        if let Some(b) = self.resolve(t)? {
            return self.term_of(b);
        }
        let node = match t {
            Sexp::Atom(a) => match a.as_str() {
                "true" => self.bool_true,
                "false" => self.bool_false,
                sym => self.builder.euf().mk_const(sym),
            },
            Sexp::List(l) => {
                let head = l
                    .first()
                    .and_then(Sexp::as_atom)
                    .ok_or("empty application")?;
                if is_connective(head) {
                    // A compound formula used as a term: a fresh node bound to its truth value.
                    let val = self.bool(t)?;
                    return Ok(self.node_for_lit(val));
                } else {
                    // A predicate application: build the application node directly.
                    let mut args = Vec::with_capacity(l.len() - 1);
                    for a in &l[1..] {
                        args.push(self.term(a)?);
                    }
                    self.builder.euf().mk_app(head, args)
                }
            }
        };
        self.link_bool(node);
        Ok(node)
    }

    /// A fresh `Bool`-sorted EUF node whose truth (`node = bool_true`) is tied to `lit`, so a
    /// formula can be passed where a term is expected. Memoized per literal.
    pub(crate) fn node_for_lit(&mut self, lit: Lit) -> TermId {
        if let Some(&n) = self.lit_nodes.get(&lit) {
            return n;
        }
        self.ite_counter += 1;
        let n = self
            .builder
            .euf()
            .mk_const(&format!("\u{1}b{}", self.ite_counter));
        let et = self.builder.eq_atom(n, self.bool_true);
        self.builder.add_clause(vec![!lit, et]);
        self.builder.add_clause(vec![lit, !et]);
        self.link_bool(n);
        self.lit_nodes.insert(lit, n);
        n
    }

    pub(crate) fn lit_of(&mut self, b: Bound) -> Result<Lit, String> {
        match b {
            Bound::Bool(l) => Ok(l),
            other => Err(format!(
                "expected a Bool, got a value of sort {}",
                other.sort()
            )),
        }
    }

    pub(crate) fn term_of(&mut self, b: Bound) -> Result<TermId, String> {
        match b {
            Bound::Bool(l) => Ok(self.node_for_lit(l)),
            Bound::Term(t, _) => Ok(t),
            Bound::Arith(_) | Bound::Poly(_) => {
                Err("a Real value cannot be a function argument here".to_string())
            }
            Bound::Bits(_) => {
                Err("a bit-vector value cannot be a function argument here".to_string())
            }
        }
    }

    /// Build a term in the EUF term DAG. `Bool`-sorted terms are routed through [`Self::bool_arg`]
    /// so their truth is wired to `bool_true`/`bool_false`.
    pub(crate) fn term(&mut self, t: &Sexp) -> Result<TermId, String> {
        if let Some(b) = self.resolve(t)? {
            return self.term_of(b);
        }
        if self.sort_of(t)? == "Bool" {
            return self.bool_arg(t);
        }
        match t {
            Sexp::Atom(name) => Ok(self.builder.euf().mk_const(name)),
            Sexp::List(l) => {
                let head = l
                    .first()
                    .and_then(Sexp::as_atom)
                    .ok_or("empty application")?;
                if head == "ite" {
                    // term-level ITE: fresh constant lifted with c -> t=a, !c -> t=b
                    let cond = self.bool(&l[1])?;
                    let then_t = self.term(&l[2])?;
                    let else_t = self.term(&l[3])?;
                    self.ite_counter += 1;
                    let fresh = self
                        .builder
                        .euf()
                        .mk_const(&format!("\u{1}ite{}", self.ite_counter));
                    let eq_then = self.builder.eq_atom(fresh, then_t);
                    let eq_else = self.builder.eq_atom(fresh, else_t);
                    self.builder.add_clause(vec![!cond, eq_then]);
                    self.builder.add_clause(vec![cond, eq_else]);
                    Ok(fresh)
                } else {
                    let mut args = Vec::with_capacity(l.len() - 1);
                    for a in &l[1..] {
                        args.push(self.term(a)?);
                    }
                    Ok(self.builder.euf().mk_app(head, args))
                }
            }
        }
    }
}
