//! Formulas and uninterpreted terms: each SAT variable is one Alethe term.

use crate::arith::Cmp;
use crate::sexp::Sexp;
use smtrex_core::Lit;
use smtrex_term::TermId;

use super::*;

impl Encoder<'_> {
    /// The EUF node of an uninterpreted-sort term.
    pub(super) fn node(&mut self, t: &Sexp) -> Result<TermId, String> {
        match t {
            Sexp::Atom(a) => Ok(self.b.euf().mk_const(a)),
            Sexp::List(l) => {
                let f = l.first().and_then(Sexp::as_atom).ok_or("malformed term")?;
                if f == "ite" {
                    return Err("term-level ite is not supported with proofs yet".to_string());
                }
                let mut args = Vec::with_capacity(l.len() - 1);
                for a in &l[1..] {
                    if self.problem.sort_of(a)? == "Bool" {
                        return Err(
                            "Boolean function arguments are not supported with proofs yet"
                                .to_string(),
                        );
                    }
                    args.push(self.node(a)?);
                }
                let id = self.b.euf().mk_app(f, args);
                let sort = self.problem.sort_of(t)?;
                self.node_sorts.insert(id, sort);
                Ok(id)
            }
        }
    }

    /// The equality atom between two EUF nodes; its term is `(= a b)` in the order the builder
    /// keys it by.
    pub(super) fn eq_atom(&mut self, a: TermId, b: TermId) -> Lit {
        let l = self.b.eq_atom(a, b);
        if self
            .terms
            .get(l.var().index())
            .and_then(Option::as_ref)
            .is_none()
        {
            let (x, y) = if a <= b { (a, b) } else { (b, a) };
            let text = format!("(= {} {})", self.text(x), self.text(y));
            self.set_term(l.var(), text, false);
        }
        l
    }

    pub(super) fn text(&self, t: TermId) -> String {
        node_text(self.b.euf_ref().arena(), t)
    }

    /// Tie a fresh variable for the term `key` to `canon` through `base`, an equivalence
    /// `(= L R)` that `rule` proves; `key_is_left` says which side `key` is.
    pub(super) fn alias(
        &mut self,
        key: String,
        canon: Lit,
        rule: &'static str,
        key_is_left: bool,
    ) -> Lit {
        let r = self.new_leaf(key.clone());
        let canon_text = self.render(canon);
        let (base, l, rr) = if key_is_left {
            (format!("(= {key} {canon_text})"), r, canon)
        } else {
            (format!("(= {canon_text} {key})"), canon, r)
        };
        self.clause(
            vec![N(l), L(rr)],
            How::Equiv {
                rule,
                base: base.clone(),
                side: 1,
            },
        );
        self.clause(
            vec![L(l), N(rr)],
            How::Equiv {
                rule,
                base,
                side: 2,
            },
        );
        r
    }

    pub(super) fn lit(&mut self, t: &Sexp) -> Result<Lit, String> {
        let key = t.to_string();
        if let Some(&l) = self.memo.get(&key) {
            return Ok(l);
        }
        let l = self.encode(t, &key)?;
        self.memo.insert(key, l);
        Ok(l)
    }

    pub(super) fn encode(&mut self, t: &Sexp, key: &str) -> Result<Lit, String> {
        let l = match t {
            Sexp::Atom(a) => match a.as_str() {
                "true" => {
                    let v = self.new_leaf("true".to_string());
                    self.clause(vec![L(v)], How::Rule("true"));
                    v
                }
                "false" => {
                    let v = self.new_leaf("false".to_string());
                    self.clause(vec![N(v)], How::Rule("false"));
                    v
                }
                _ => {
                    if self.problem.sort_of(t)? != "Bool" {
                        return Err(format!("'{a}' is not a formula"));
                    }
                    self.new_leaf(key.to_string())
                }
            },
            Sexp::List(items) => {
                let head = items
                    .first()
                    .and_then(Sexp::as_atom)
                    .ok_or("malformed term")?;
                let args = &items[1..];
                match (head, args.len()) {
                    ("not", 1) => {
                        if matches!(&args[0], Sexp::List(l) if l.first().and_then(Sexp::as_atom) == Some("not"))
                        {
                            return Err("double negation is not supported with proofs yet".into());
                        }
                        return Ok(!self.lit(&args[0])?);
                    }
                    ("and", _) | ("or", _) => {
                        let ls = args
                            .iter()
                            .map(|a| self.lit(a))
                            .collect::<Result<Vec<_>, _>>()?;
                        let r = self.new_var(self.body(head, &ls));
                        if head == "and" {
                            for (i, &x) in ls.iter().enumerate() {
                                self.clause(vec![N(r), L(x)], How::RuleAt("and_pos", i));
                            }
                            let mut parts = vec![L(r)];
                            parts.extend(ls.iter().map(|&x| N(x)));
                            self.clause(parts, How::Rule("and_neg"));
                        } else {
                            let mut parts = vec![N(r)];
                            parts.extend(ls.iter().map(|&x| L(x)));
                            self.clause(parts, How::Rule("or_pos"));
                            for (i, &x) in ls.iter().enumerate() {
                                self.clause(vec![L(r), N(x)], How::RuleAt("or_neg", i));
                            }
                        }
                        r
                    }
                    ("=>", 2) => {
                        let (a, b) = (self.lit(&args[0])?, self.lit(&args[1])?);
                        let r = self.new_var(self.body("=>", &[a, b]));
                        self.clause(vec![N(r), N(a), L(b)], How::Rule("implies_pos"));
                        self.clause(vec![L(r), L(a)], How::Rule("implies_neg1"));
                        self.clause(vec![L(r), N(b)], How::Rule("implies_neg2"));
                        r
                    }
                    ("xor", 2) => {
                        let (a, b) = (self.lit(&args[0])?, self.lit(&args[1])?);
                        let r = self.new_var(self.body("xor", &[a, b]));
                        self.clause(vec![N(r), L(a), L(b)], How::Rule("xor_pos1"));
                        self.clause(vec![N(r), N(a), N(b)], How::Rule("xor_pos2"));
                        self.clause(vec![L(r), L(a), N(b)], How::Rule("xor_neg1"));
                        self.clause(vec![L(r), N(a), L(b)], How::Rule("xor_neg2"));
                        r
                    }
                    ("ite", 3) => {
                        let c = self.lit(&args[0])?;
                        let (a, b) = (self.lit(&args[1])?, self.lit(&args[2])?);
                        let r = self.new_var(self.body("ite", &[c, a, b]));
                        self.clause(vec![N(r), L(c), L(b)], How::Rule("ite_pos1"));
                        self.clause(vec![N(r), N(c), L(a)], How::Rule("ite_pos2"));
                        self.clause(vec![L(r), L(c), N(b)], How::Rule("ite_neg1"));
                        self.clause(vec![L(r), N(c), N(a)], How::Rule("ite_neg2"));
                        r
                    }
                    ("<=" | "<" | ">=" | ">", 2) => {
                        let cmp = match head {
                            "<=" => Cmp::Le,
                            "<" => Cmp::Lt,
                            ">=" => Cmp::Ge,
                            _ => Cmp::Gt,
                        };
                        let e = self.lin(&args[0])?.sub(&self.lin(&args[1])?);
                        self.arith_atom(&real_text(t), e, cmp)
                    }
                    ("=", 2) if self.problem.sort_of(&args[0])? == "Real" => {
                        self.arith_eq(&real_text(t), &args[0], &args[1])?
                    }
                    ("=", 2) if self.problem.sort_of(&args[0])? == "Bool" => {
                        let (a, b) = (self.lit(&args[0])?, self.lit(&args[1])?);
                        let r = self.new_var(self.body("=", &[a, b]));
                        self.clause(vec![N(r), L(a), N(b)], How::Rule("equiv_pos1"));
                        self.clause(vec![N(r), N(a), L(b)], How::Rule("equiv_pos2"));
                        self.clause(vec![L(r), N(a), N(b)], How::Rule("equiv_neg1"));
                        self.clause(vec![L(r), L(a), L(b)], How::Rule("equiv_neg2"));
                        r
                    }
                    ("=", 2) => {
                        let (a, b) = (self.node(&args[0])?, self.node(&args[1])?);
                        let c = self.eq_atom(a, b);
                        let written = format!("(= {} {})", self.text(a), self.text(b));
                        if self.render(c) == written {
                            c
                        } else {
                            self.alias(written, c, "eq_symmetric", true)
                        }
                    }
                    ("=", _) => return Err("n-ary = is not supported with proofs yet".into()),
                    ("distinct", n) if n >= 2 => {
                        // (distinct x1 .. xn) is the conjunction of the pairwise disequalities.
                        let mut pairs = Vec::new();
                        for i in 0..n {
                            for j in i + 1..n {
                                let eq = Sexp::List(vec![
                                    Sexp::Atom("=".into()),
                                    args[i].clone(),
                                    args[j].clone(),
                                ]);
                                pairs.push(Sexp::List(vec![Sexp::Atom("not".into()), eq]));
                            }
                        }
                        let e = if pairs.len() == 1 {
                            pairs.pop().unwrap()
                        } else {
                            Sexp::List([vec![Sexp::Atom("and".into())], pairs].concat())
                        };
                        let el = self.lit(&e)?;
                        let mut nodes = Vec::with_capacity(n);
                        for a in args {
                            if self.problem.sort_of(a)? == "Real" {
                                nodes.push(real_text(a));
                            } else {
                                let id = self.node(a)?;
                                nodes.push(self.text(id));
                            }
                        }
                        let r = self.new_var(format!("(distinct {})", nodes.join(" ")));
                        let base = format!("(= {} {})", self.render(r), self.render(el));
                        self.clause(
                            vec![N(r), L(el)],
                            How::Equiv {
                                rule: "distinct_elim",
                                base: base.clone(),
                                side: 1,
                            },
                        );
                        self.clause(
                            vec![L(r), N(el)],
                            How::Equiv {
                                rule: "distinct_elim",
                                base,
                                side: 2,
                            },
                        );
                        r
                    }
                    (f, _) if self.problem.sigs.get(f).is_some_and(|(_, s)| s == "Bool") => {
                        // A predicate application: the EUF atom (= app true), aliased to app.
                        let app = self.node(t)?;
                        let c = self.eq_atom(app, self.true_node);
                        let written = self.text(app);
                        self.alias(written, c, "equiv_simplify", false)
                    }
                    _ => return Err(format!("'{head}' is not supported with proofs yet")),
                }
            }
        };
        Ok(l)
    }
}
