//! Models for satisfiable scripts: construction, SMT-LIB printing, and the evaluator that
//! self-checks every `sat`.
//!
//! The EUF classes give the model: one domain element per class of an uninterpreted sort, a
//! `Bool` term true iff it is in the class of the reserved `true`, and each function the table
//! of its applications. [`Evaluator`] interprets the original assertions under the model and
//! shares no code with the encoder: bit-vectors are evaluated on integers ([`bv_apply`]), and
//! real algebraic values (QF_NRA, printed as `root-obj`) exactly, one operation at a time
//! ([`RealAlgebraic::add`], [`RealAlgebraic::mul`]), never with floating point.

use crate::arith::real_literal;
use crate::bv::{self, Op};
use crate::script::Def;
use crate::sexp::{quote_symbol, Sexp};
use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, Signed, Zero};
use rustc_hash::FxHashMap;
use smtrex_core::Rational;
use smtrex_poly::RealAlgebraic;
use smtrex_term::TermId;
use smtrex_theory::Euf;

/// A value in a model: a Boolean, element `index` of the uninterpreted sort `sort` (an index
/// into `Model::sorts`), an exact real number, or a bit-vector of `width` bits whose unsigned
/// value is `value` (always below `2^width`).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    Bool(bool),
    Elem {
        sort: u32,
        index: u32,
    },
    Real(Rational),
    /// An irrational real algebraic number (a rational is always [`Value::Real`]).
    Algebraic(Box<RealAlgebraic>),
    /// An integer (always integral).
    Int(Rational),
    BitVec {
        width: u32,
        value: BigUint,
    },
}

impl Value {
    /// The number, for `Int` and `Real` values.
    fn num(&self) -> Option<&Rational> {
        match self {
            Value::Real(q) | Value::Int(q) => Some(q),
            _ => None,
        }
    }

    /// Equality that compares numbers by value, so the numeral `3` equals an `Int` or `Real` 3.
    fn same(&self, other: &Value) -> bool {
        match (self.num(), other.num()) {
            (Some(a), Some(b)) => a == b,
            _ => match (self.real(), other.real()) {
                (Some(a), Some(b)) => a == b,
                _ => self == other,
            },
        }
    }

    /// A real number as a real algebraic number.
    fn real(&self) -> Option<RealAlgebraic> {
        match self {
            Value::Real(q) | Value::Int(q) => Some(RealAlgebraic::from_rational(q.to_big())),
            Value::Algebraic(a) => Some((**a).clone()),
            _ => None,
        }
    }

    /// The value of a real algebraic number: [`Value::Real`] if rational.
    pub fn from_algebraic(a: RealAlgebraic) -> Value {
        match a.as_rational() {
            Some(q) => Value::Real(Rational::from_big(q.clone())),
            None => Value::Algebraic(Box::new(a)),
        }
    }
}

/// One row of a function table: argument values and the result.
type Entry = (Vec<Value>, Value);

/// A function table under construction: entries in first-seen order, and the same as a map.
type Table = (Vec<Entry>, FxHashMap<Vec<Value>, Value>);

/// The interpretation of one declared symbol.
#[derive(Debug, Clone)]
pub enum Interp {
    Const(Value),
    Func {
        arg_sorts: Vec<String>,
        ret_sort: String,
        /// Explicit entries in first-seen order (each argument tuple once).
        entries: Vec<Entry>,
        table: FxHashMap<Vec<Value>, Value>,
        /// The value for argument tuples not in `table`.
        default: Value,
    },
}

#[derive(Debug, Clone, Default)]
pub struct Model {
    /// Uninterpreted sorts with their cardinality in this model, in first-seen order.
    sorts: Vec<(String, u32)>,
    /// Declared symbols in declaration order.
    decls: Vec<(String, Interp)>,
    index: FxHashMap<String, usize>,
}

impl Model {
    /// Build the model of the current (satisfiable) EUF state. `sigs` gives every declared
    /// symbol's (argument sorts, return sort), `decl_order` the declaration order for printing,
    /// and `bool_true` the reserved constant whose class is "true". Terms whose names start with
    /// U+0001 are encoder-internal and contribute no symbol of their own.
    pub fn from_euf(
        euf: &Euf,
        bool_true: TermId,
        sigs: &FxHashMap<String, (Vec<String>, String)>,
        decl_order: &[String],
    ) -> Result<Model, String> {
        let mut b = Builder {
            euf,
            true_class: euf.class_of(bool_true),
            model: Model::default(),
            elems: FxHashMap::default(),
        };
        let arena = euf.arena();
        let mut consts: FxHashMap<&str, Value> = FxHashMap::default();
        let mut funcs: FxHashMap<&str, Table> = FxHashMap::default();
        for i in 0..arena.num_terms() {
            let id = TermId::from_index(i);
            let name = arena.name_of(id);
            if name.starts_with('\u{1}') {
                continue;
            }
            let Some((arg_sorts, ret)) = sigs.get(name) else {
                continue;
            };
            let args = arena.args_of(id);
            if args.len() != arg_sorts.len() {
                return Err(format!(
                    "internal error: '{name}' built with the wrong arity"
                ));
            }
            let value = b.value(id, ret);
            if args.is_empty() {
                consts.insert(name, value);
                continue;
            }
            let key: Vec<Value> = args
                .iter()
                .zip(arg_sorts)
                .map(|(&a, s)| b.value(a, s))
                .collect();
            let (entries, table) = funcs.entry(name).or_default();
            match table.get(&key) {
                Some(old) if *old != value => {
                    return Err(format!(
                        "internal error: congruence violated for '{name}' in the model"
                    ));
                }
                Some(_) => {}
                None => {
                    table.insert(key.clone(), value.clone());
                    entries.push((key, value));
                }
            }
        }

        for name in decl_order {
            let Some((arg_sorts, ret)) = sigs.get(name) else {
                continue;
            };
            let interp = if arg_sorts.is_empty() {
                let v = match consts.get(name.as_str()) {
                    Some(v) => v.clone(),
                    None => b.default_of(ret),
                };
                Interp::Const(v)
            } else {
                let (entries, table) = funcs.remove(name.as_str()).unwrap_or_default();
                // The most frequent result is the default, so the printed table stays short.
                let mut counts: Vec<(Value, usize)> = Vec::new();
                for (_, v) in &entries {
                    match counts.iter_mut().find(|(c, _)| c == v) {
                        Some((_, n)) => *n += 1,
                        None => counts.push((v.clone(), 1)),
                    }
                }
                let default = match counts.iter().max_by_key(|(_, n)| *n) {
                    Some((v, _)) => v.clone(),
                    None => b.default_of(ret),
                };
                Interp::Func {
                    arg_sorts: arg_sorts.clone(),
                    ret_sort: ret.clone(),
                    entries,
                    table,
                    default,
                }
            };
            b.model.index.insert(name.clone(), b.model.decls.len());
            b.model.decls.push((name.clone(), interp));
        }
        Ok(b.model)
    }

    /// Override the value of a declared constant (used for arithmetic variables, whose values
    /// come from the Simplex rather than the e-graph).
    pub fn set_const(&mut self, name: &str, v: Value) {
        if let Some(&i) = self.index.get(name) {
            self.decls[i].1 = Interp::Const(v);
        }
    }

    pub fn get(&self, name: &str) -> Option<&Interp> {
        self.index.get(name).map(|&i| &self.decls[i].1)
    }

    /// Apply a declared function (or read a constant) under the model.
    pub fn apply(&self, name: &str, args: &[Value]) -> Option<Value> {
        match self.get(name)? {
            Interp::Const(v) if args.is_empty() => Some(v.clone()),
            Interp::Func {
                arg_sorts,
                table,
                default,
                ..
            } if arg_sorts.len() == args.len() => Some(table.get(args).unwrap_or(default).clone()),
            _ => None,
        }
    }

    /// The value in SMT-LIB syntax: `true`, `false`, `(as @U_0 U)`, a real literal, or a
    /// bit-vector literal `#b…`.
    pub fn show(&self, v: &Value) -> String {
        match v {
            Value::Bool(b) => b.to_string(),
            Value::Real(q) => real_literal(q),
            Value::Algebraic(a) => root_obj(a),
            Value::Int(q) if q.is_negative() => format!("(- {})", q.abs()),
            Value::Int(q) => q.to_string(),
            Value::BitVec { width, value } => {
                let digits = value.to_str_radix(2);
                format!("#b{digits:0>w$}", w = *width as usize)
            }
            Value::Elem { sort, index } => {
                let s = &self.sorts[*sort as usize].0;
                format!(
                    "(as {} {})",
                    quote_symbol(&format!("@{s}_{index}")),
                    quote_symbol(s)
                )
            }
        }
    }

    /// The model in SMT-LIB `get-model` syntax (the layout cvc5 uses).
    pub fn to_smtlib(&self) -> String {
        let mut out = String::from("(\n");
        for (s, n) in &self.sorts {
            out.push_str(&format!("; cardinality of {} is {n}\n", quote_symbol(s)));
        }
        for (name, interp) in &self.decls {
            let name = quote_symbol(name);
            match interp {
                Interp::Const(v) => {
                    let sort = self.sort_name(v);
                    out.push_str(&format!("(define-fun {name} () {sort} {})\n", self.show(v)));
                }
                Interp::Func {
                    arg_sorts,
                    ret_sort,
                    entries,
                    default,
                    ..
                } => {
                    let params: Vec<String> = arg_sorts
                        .iter()
                        .enumerate()
                        .map(|(i, s)| format!("(_arg_{} {})", i + 1, quote_symbol(s)))
                        .collect();
                    let mut body = self.show(default);
                    for (key, v) in entries.iter().rev() {
                        if v == default {
                            continue;
                        }
                        let conds: Vec<String> = key
                            .iter()
                            .enumerate()
                            .map(|(i, a)| format!("(= _arg_{} {})", i + 1, self.show(a)))
                            .collect();
                        let cond = if conds.len() == 1 {
                            conds[0].clone()
                        } else {
                            format!("(and {})", conds.join(" "))
                        };
                        body = format!("(ite {cond} {} {body})", self.show(v));
                    }
                    out.push_str(&format!(
                        "(define-fun {name} ({}) {} {body})\n",
                        params.join(" "),
                        quote_symbol(ret_sort)
                    ));
                }
            }
        }
        out.push(')');
        out
    }

    fn sort_name(&self, v: &Value) -> std::borrow::Cow<'_, str> {
        match v {
            Value::Bool(_) => "Bool".into(),
            Value::Real(_) | Value::Algebraic(_) => "Real".into(),
            Value::Int(_) => "Int".into(),
            Value::BitVec { width, .. } => bv::sort_name(*width).into(),
            Value::Elem { sort, .. } => quote_symbol(&self.sorts[*sort as usize].0),
        }
    }
}

struct Builder<'a> {
    euf: &'a Euf,
    true_class: TermId,
    model: Model,
    /// e-graph class -> its domain element.
    elems: FxHashMap<TermId, Value>,
}

impl Builder<'_> {
    fn sort_id(&mut self, sort: &str) -> u32 {
        match self.model.sorts.iter().position(|(s, _)| s == sort) {
            Some(i) => i as u32,
            None => {
                self.model.sorts.push((sort.to_string(), 0));
                (self.model.sorts.len() - 1) as u32
            }
        }
    }

    fn value(&mut self, t: TermId, sort: &str) -> Value {
        let class = self.euf.class_of(t);
        if sort == "Bool" {
            return Value::Bool(class == self.true_class);
        }
        if let Some(v) = self.elems.get(&class) {
            return v.clone();
        }
        let sid = self.sort_id(sort);
        let card = &mut self.model.sorts[sid as usize].1;
        let v = Value::Elem {
            sort: sid,
            index: *card,
        };
        *card += 1;
        self.elems.insert(class, v.clone());
        v
    }

    /// A value of `sort` for a symbol the solver never constrained (domains are non-empty).
    fn default_of(&mut self, sort: &str) -> Value {
        if sort == "Bool" {
            return Value::Bool(false);
        }
        if sort == "Real" {
            return Value::Real(Rational::zero());
        }
        if sort == "Int" {
            return Value::Int(Rational::zero());
        }
        if let Some(width) = bv::width(sort) {
            return Value::BitVec {
                width,
                value: BigUint::zero(),
            };
        }
        let sid = self.sort_id(sort);
        let card = &mut self.model.sorts[sid as usize].1;
        *card = (*card).max(1);
        Value::Elem {
            sort: sid,
            index: 0,
        }
    }
}

/// Rational numeric values and whether all are integers; `t` is for error messages.
fn rationals(vals: Vec<Value>, t: &Sexp) -> Result<(Vec<Rational>, bool), String> {
    let mut all_int = true;
    let mut out = Vec::with_capacity(vals.len());
    for v in vals {
        match v {
            Value::Int(q) => out.push(q),
            Value::Real(q) => {
                all_int = false;
                out.push(q)
            }
            _ => return Err(format!("expected rational numbers in {t}")),
        }
    }
    Ok((out, all_int))
}

/// Numeric values as real algebraic numbers; `t` is for error messages.
fn algebraics(vals: Vec<Value>, t: &Sexp) -> Result<Vec<RealAlgebraic>, String> {
    vals.into_iter()
        .map(|v| v.real().ok_or_else(|| format!("expected numbers in {t}")))
        .collect()
}

/// z3's syntax for an irrational real algebraic number: `(root-obj p k)` with `p` its minimal
/// polynomial in `x` and `k` its 1-based index among the real roots of `p`, ascending; e.g.
/// `(root-obj (+ (^ x 2) (- 2)) 2)` for √2.
pub fn root_obj(a: &RealAlgebraic) -> String {
    let p = a.minimal_polynomial();
    let int = |c: &BigInt| {
        if c.is_negative() {
            format!("(- {})", -c)
        } else {
            c.to_string()
        }
    };
    let mut terms = Vec::new();
    for (k, c) in p.coeffs().iter().enumerate().rev() {
        if c.is_zero() {
            continue;
        }
        let mono = match k {
            0 => None,
            1 => Some("x".to_string()),
            _ => Some(format!("(^ x {k})")),
        };
        terms.push(match mono {
            None => int(c),
            Some(m) if c.is_one() => m,
            Some(m) => format!("(* {} {m})", int(c)),
        });
    }
    let poly = if terms.len() == 1 {
        terms.pop().unwrap()
    } else {
        format!("(+ {})", terms.join(" "))
    };
    format!("(root-obj {poly} {})", a.root_index() + 1)
}

/// Evaluates SMT-LIB terms under a [`Model`], independently of the encoder.
pub struct Evaluator<'a> {
    model: &'a Model,
    defs: &'a FxHashMap<String, Def>,
    scopes: Vec<FxHashMap<String, Value>>,
    /// Values of `(! t :named n)` terms seen so far.
    named: FxHashMap<String, Value>,
    def_cache: FxHashMap<(String, Vec<Value>), Value>,
}

impl<'a> Evaluator<'a> {
    pub fn new(model: &'a Model, defs: &'a FxHashMap<String, Def>) -> Evaluator<'a> {
        Evaluator {
            model,
            defs,
            scopes: Vec::new(),
            named: FxHashMap::default(),
            def_cache: FxHashMap::default(),
        }
    }

    fn bool(&mut self, t: &Sexp) -> Result<bool, String> {
        match self.eval(t)? {
            Value::Bool(b) => Ok(b),
            _ => Err(format!("expected a Bool: {t}")),
        }
    }

    /// Evaluate numeric arguments: their values, and whether all of them are integers.
    fn numbers(&mut self, ts: &[Sexp]) -> Result<(Vec<Rational>, bool), String> {
        let vals = self.eval_all(ts)?;
        rationals(vals, &Sexp::List(ts.to_vec()))
    }

    pub fn eval(&mut self, t: &Sexp) -> Result<Value, String> {
        let list = match t {
            Sexp::Atom(a) => return self.atom(a),
            Sexp::List(l) => l,
        };
        if let Some((value, width)) = bv::literal(t)? {
            return Ok(Value::BitVec { width, value });
        }
        if let Some(op) = list.first().map(Op::parse).transpose()?.flatten() {
            let mut args = Vec::with_capacity(list.len() - 1);
            for a in &list[1..] {
                match self.eval(a)? {
                    Value::BitVec { width, value } => args.push((width, value)),
                    _ => return Err(format!("expected a bit-vector: {a}")),
                }
            }
            return bv_apply(op, &args);
        }
        let head = list
            .first()
            .and_then(Sexp::as_atom)
            .ok_or_else(|| format!("cannot evaluate {t}"))?;
        let args = &list[1..];
        let arity = |n: usize| {
            if args.len() == n {
                Ok(())
            } else {
                Err(format!("'{head}' expects {n} arguments: {t}"))
            }
        };
        let v = match head {
            "not" => {
                arity(1)?;
                !self.bool(&args[0])?
            }
            "and" => {
                let mut all = true;
                for a in args {
                    all &= self.bool(a)?;
                }
                all
            }
            "or" => {
                let mut any = false;
                for a in args {
                    any |= self.bool(a)?;
                }
                any
            }
            "=>" => {
                // right-associative: a => (b => c)
                let (last, init) = args.split_last().ok_or("=> needs arguments")?;
                let mut acc = self.bool(last)?;
                for a in init.iter().rev() {
                    acc = !self.bool(a)? || acc;
                }
                acc
            }
            "xor" => {
                let mut acc = false;
                for a in args {
                    acc ^= self.bool(a)?;
                }
                acc
            }
            "=" => {
                let vals = self.eval_all(args)?;
                vals.windows(2).all(|w| w[0].same(&w[1]))
            }
            "<=" | "<" | ">=" | ">" => {
                let vals = self.eval_all(args)?;
                if vals.iter().any(|v| matches!(v, Value::Algebraic(_))) {
                    let xs = algebraics(vals, t)?;
                    xs.windows(2).all(|w| match head {
                        "<=" => w[0] <= w[1],
                        "<" => w[0] < w[1],
                        ">=" => w[0] >= w[1],
                        _ => w[0] > w[1],
                    })
                } else {
                    let xs = rationals(vals, t)?.0;
                    xs.windows(2).all(|w| match head {
                        "<=" => w[0] <= w[1],
                        "<" => w[0] < w[1],
                        ">=" => w[0] >= w[1],
                        _ => w[0] > w[1],
                    })
                }
            }
            "+" | "*" | "-" | "/" => {
                let vals = self.eval_all(args)?;
                if vals.iter().any(|v| matches!(v, Value::Algebraic(_))) {
                    let xs = algebraics(vals, t)?;
                    let (first, rest) = xs.split_first().ok_or("arithmetic needs arguments")?;
                    let r = match head {
                        "+" => rest.iter().fold(first.clone(), |a, x| a.add(x)),
                        "*" => rest.iter().fold(first.clone(), |a, x| a.mul(x)),
                        "-" if rest.is_empty() => first.neg(),
                        "-" => rest.iter().fold(first.clone(), |a, x| a.sub(x)),
                        _ => {
                            let mut acc = first.clone();
                            for x in rest {
                                let Some(q) = x.as_rational() else {
                                    return Err(format!("division by an irrational number in {t}"));
                                };
                                if q.is_zero() {
                                    return Err("division by zero".to_string());
                                }
                                acc = acc.mul(&RealAlgebraic::from_rational(q.recip()));
                            }
                            acc
                        }
                    };
                    return Ok(Value::from_algebraic(r));
                }
                let (xs, all_int) = rationals(vals, t)?;
                let (first, rest) = xs.split_first().ok_or("arithmetic needs arguments")?;
                if head == "/" {
                    let mut acc = first.clone();
                    for x in rest {
                        if x.is_zero() {
                            return Err("division by zero".to_string());
                        }
                        acc = &acc / x;
                    }
                    return Ok(Value::Real(acc));
                }
                let r = match head {
                    "+" => rest.iter().fold(first.clone(), |a, x| &a + x),
                    "*" => rest.iter().fold(first.clone(), |a, x| &a * x),
                    _ if rest.is_empty() => -first,
                    _ => rest.iter().fold(first.clone(), |a, x| &a - x),
                };
                return Ok(if all_int {
                    Value::Int(r)
                } else {
                    Value::Real(r)
                });
            }
            "div" | "mod" => {
                arity(2)?;
                let (xs, _) = self.numbers(args)?;
                let (a, k) = (&xs[0], &xs[1]);
                if k.is_zero() {
                    return Err(format!("'{head}' by zero"));
                }
                // Euclidean: a = k·q + r with 0 ≤ r < |k|.
                let q = if k.is_positive() {
                    (a / k).floor()
                } else {
                    (a / k).ceil()
                };
                let r = a - &(k * &q);
                return Ok(Value::Int(if head == "div" { q } else { r }));
            }
            "abs" => {
                arity(1)?;
                let (xs, _) = self.numbers(args)?;
                return Ok(Value::Int(xs[0].abs()));
            }
            "distinct" => {
                let vals = self.eval_all(args)?;
                (0..vals.len()).all(|i| (i + 1..vals.len()).all(|j| !vals[i].same(&vals[j])))
            }
            "ite" => {
                arity(3)?;
                return if self.bool(&args[0])? {
                    self.eval(&args[1])
                } else {
                    self.eval(&args[2])
                };
            }
            "let" => {
                arity(2)?;
                let mut scope = FxHashMap::default();
                for b in args[0].as_list().ok_or("let bindings must be a list")? {
                    let Some([Sexp::Atom(name), expr]) = b.as_list() else {
                        return Err("malformed let binding".to_string());
                    };
                    let v = self.eval(expr)?;
                    scope.insert(name.clone(), v);
                }
                self.scopes.push(scope);
                let v = self.eval(&args[1]);
                self.scopes.pop();
                return v;
            }
            "!" => {
                let (inner, attrs) = args.split_first().ok_or("! expects a term")?;
                let v = self.eval(inner)?;
                for w in attrs.windows(2) {
                    if let [Sexp::Atom(k), Sexp::Atom(n)] = w {
                        if k == ":named" {
                            self.named.insert(n.clone(), v.clone());
                        }
                    }
                }
                return Ok(v);
            }
            f => {
                let vals = self.eval_all(args)?;
                return self.call(f, vals);
            }
        };
        Ok(Value::Bool(v))
    }

    fn eval_all(&mut self, ts: &[Sexp]) -> Result<Vec<Value>, String> {
        ts.iter().map(|t| self.eval(t)).collect()
    }

    fn atom(&mut self, a: &str) -> Result<Value, String> {
        match a {
            "true" => return Ok(Value::Bool(true)),
            "false" => return Ok(Value::Bool(false)),
            _ => {}
        }
        if let Some(v) = self.scopes.iter().rev().find_map(|s| s.get(a)) {
            return Ok(v.clone());
        }
        if let Some(v) = self.named.get(a) {
            return Ok(v.clone());
        }
        if let Some((value, width)) = bv::literal(&Sexp::Atom(a.to_string()))? {
            return Ok(Value::BitVec { width, value });
        }
        if a.starts_with(|c: char| c.is_ascii_digit()) {
            let q = Rational::parse_decimal(a).ok_or_else(|| format!("bad number '{a}'"))?;
            return Ok(if a.contains('.') {
                Value::Real(q)
            } else {
                Value::Int(q)
            });
        }
        if !self.defs.contains_key(a) && self.model.get(a).is_none() {
            if let Some(q) = crate::script::negative_number(a) {
                return Ok(if a.contains('.') {
                    Value::Real(q)
                } else {
                    Value::Int(q)
                });
            }
        }
        self.call(a, Vec::new())
    }

    fn call(&mut self, f: &str, vals: Vec<Value>) -> Result<Value, String> {
        if let Some(def) = self.defs.get(f) {
            if def.params.len() != vals.len() {
                return Err(format!("'{f}' expects {} arguments", def.params.len()));
            }
            let key = (f.to_string(), vals);
            if let Some(v) = self.def_cache.get(&key) {
                return Ok(v.clone());
            }
            let scope = def
                .params
                .iter()
                .map(|(n, _)| n.clone())
                .zip(key.1.iter().cloned())
                .collect();
            let saved = std::mem::replace(&mut self.scopes, vec![scope]);
            let v = self.eval(&def.body);
            self.scopes = saved;
            let v = v?;
            self.def_cache.insert(key, v.clone());
            return Ok(v);
        }
        self.model
            .apply(f, &vals)
            .ok_or_else(|| format!("'{f}' has no interpretation in the model"))
    }
}

/// The two's-complement value of the `w`-bit vector `v`.
fn signed(w: u32, v: &BigUint) -> BigInt {
    if v.bit(u64::from(w) - 1) {
        BigInt::from(v.clone()) - (BigInt::one() << w)
    } else {
        BigInt::from(v.clone())
    }
}

/// `v` modulo `2^w`, as a `w`-bit vector.
fn wrap(w: u32, v: BigInt) -> BigUint {
    let m = BigInt::one() << w;
    let r = ((v % &m) + &m) % &m;
    r.to_biguint().expect("non-negative after reduction")
}

/// Apply a bit-vector operator to `(width, value)` arguments, by the SMT-LIB 2.6 definitions
/// on integers. Arguments are assumed well-sorted (the script sort-checks every assertion).
pub fn bv_apply(op: Op, args: &[(u32, BigUint)]) -> Result<Value, String> {
    let bits = |width: u32, value: BigUint| Ok(Value::BitVec { width, value });
    let boolean = |b: bool| Ok(Value::Bool(b));
    let Some((w, x)) = args.first().cloned() else {
        return Err(format!("{op:?} needs arguments"));
    };
    let m = bv::mask(w);
    // Left-associative operators: fold the rest one at a time.
    if args.len() > 2
        && matches!(
            op,
            Op::Concat | Op::And | Op::Or | Op::Xor | Op::Add | Op::Mul
        )
    {
        let mut acc = (w, x);
        for a in &args[1..] {
            match bv_apply(op, &[acc, a.clone()])? {
                Value::BitVec { width, value } => acc = (width, value),
                _ => unreachable!("bit-vector operators return bit-vectors"),
            }
        }
        return bits(acc.0, acc.1);
    }
    let y = || -> Result<BigUint, String> {
        args.get(1)
            .map(|a| a.1.clone())
            .ok_or_else(|| format!("{op:?} needs two arguments"))
    };
    let shift_amount = |s: &BigUint| -> Option<u32> { u32::try_from(s).ok().filter(|&k| k < w) };
    use Op::*;
    match op {
        Concat => {
            let (wy, vy) = args.get(1).cloned().ok_or("concat needs two arguments")?;
            bits(w + wy, (x << wy) | vy)
        }
        Extract(i, j) => bits(i - j + 1, (x >> j) & bv::mask(i - j + 1)),
        ZeroExtend(k) => bits(w + k, x),
        SignExtend(k) => {
            let v = wrap(w + k, signed(w, &x));
            bits(w + k, v)
        }
        Repeat(k) => {
            let mut v = BigUint::zero();
            for _ in 0..k {
                v = (v << w) | &x;
            }
            bits(w * k, v)
        }
        RotateLeft(k) => {
            let k = k % w;
            bits(w, ((&x << k) | (&x >> (w - k))) & m)
        }
        RotateRight(k) => {
            let k = k % w;
            bits(w, ((&x >> k) | (&x << (w - k))) & m)
        }
        Not => bits(w, &m ^ x),
        And => bits(w, x & y()?),
        Or => bits(w, x | y()?),
        Xor => bits(w, x ^ y()?),
        Nand => bits(w, &m ^ (x & y()?)),
        Nor => bits(w, &m ^ (x | y()?)),
        Xnor => bits(w, &m ^ (x ^ y()?)),
        Comp => bits(1, BigUint::from(u8::from(x == y()?))),
        Neg => bits(w, wrap(w, -BigInt::from(x))),
        Add => bits(w, (x + y()?) & m),
        Sub => bits(w, wrap(w, BigInt::from(x) - BigInt::from(y()?))),
        Mul => bits(w, (x * y()?) & m),
        Udiv => {
            let d = y()?;
            bits(w, if d.is_zero() { m } else { x / d })
        }
        Urem => {
            let d = y()?;
            bits(w, if d.is_zero() { x } else { x % d })
        }
        Sdiv | Srem | Smod => {
            let (s, t) = (signed(w, &x), signed(w, &y()?));
            let r = if t.is_zero() {
                match op {
                    // s / 0 is "all ones" on |s|, then the sign fix-up: -1 or 1.
                    Sdiv if s.is_negative() => BigInt::one(),
                    Sdiv => -BigInt::one(),
                    _ => s,
                }
            } else {
                match op {
                    // Truncating division; the remainder takes the dividend's sign.
                    Sdiv => &s / &t,
                    Srem => &s % &t,
                    // Floored remainder: takes the divisor's sign.
                    _ => {
                        let r = &s % &t;
                        if !r.is_zero() && (r.sign() == Sign::Minus) != (t.sign() == Sign::Minus) {
                            r + t
                        } else {
                            r
                        }
                    }
                }
            };
            bits(w, wrap(w, r))
        }
        Shl => bits(
            w,
            match shift_amount(&y()?) {
                Some(k) => (x << k) & m,
                None => BigUint::zero(),
            },
        ),
        Lshr => bits(
            w,
            match shift_amount(&y()?) {
                Some(k) => x >> k,
                None => BigUint::zero(),
            },
        ),
        Ashr => {
            let s = signed(w, &x);
            let k = shift_amount(&y()?).unwrap_or(w);
            // Arithmetic shift is floor division by 2^k (num-bigint's >> rounds toward -inf).
            bits(w, wrap(w, s >> k))
        }
        Ult => boolean(x < y()?),
        Ule => boolean(x <= y()?),
        Ugt => boolean(x > y()?),
        Uge => boolean(x >= y()?),
        Slt | Sle | Sgt | Sge => {
            let (s, t) = (signed(w, &x), signed(w, &y()?));
            boolean(match op {
                Slt => s < t,
                Sle => s <= t,
                Sgt => s > t,
                _ => s >= t,
            })
        }
    }
}
