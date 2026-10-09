//! SMT-LIB scripts: commands, sort checking, solving and models.
//!
//! Assertions are sort-checked when asserted and encoded at each `check-sat`; every `sat` is
//! self-checked by evaluating the assertions under the model ([`crate::model::Evaluator`]), and
//! a failed check is reported as `unknown`.

use crate::bv;
use crate::model::{Evaluator, Model, Value};
use crate::sexp::Sexp;
use rustc_hash::FxHashMap;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

mod solve;
mod sorts;
#[cfg(test)]
mod tests;

use sorts::unify;
pub(crate) use sorts::{is_arith, negative_number};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Answer {
    Sat,
    Unsat,
    Unknown,
}

impl Answer {
    pub fn as_str(self) -> &'static str {
        match self {
            Answer::Sat => "sat",
            Answer::Unsat => "unsat",
            Answer::Unknown => "unknown",
        }
    }
}

#[derive(Debug, Clone)]
pub struct CheckResult {
    pub answer: Answer,
    /// The `:status` annotation in scope at this `check-sat`, if any.
    pub expected: Option<Answer>,
    /// Why the answer is `unknown` (e.g. a failed model self-check).
    pub reason: Option<String>,
    /// The optimum, when an objective (`maximize`/`minimize`) is in scope and the answer is sat.
    pub objective: Option<ObjectiveResult>,
}

/// An objective set with `(maximize t)` or `(minimize t)`.
#[derive(Debug, Clone)]
struct Objective {
    term: Sexp,
    maximize: bool,
    /// The assertion level it was set at; popping that level removes it.
    depth: usize,
}

#[derive(Debug, Clone)]
pub struct ObjectiveResult {
    pub term: Sexp,
    pub maximize: bool,
    pub value: OptValue,
}

/// The optimum of an objective.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OptValue {
    /// Attained: some model reaches it.
    Exact(Value),
    /// The supremum (maximize) or infimum (minimize), approached but not reached, e.g. the
    /// maximum of `x` under `x < 3`.
    NotAttained(Value),
    Unbounded,
}

impl ObjectiveResult {
    /// The value in the syntax of z3's `get-objectives`: a number, `oo`, `(- oo)`, or
    /// `(- c epsilon)` / `(+ c epsilon)` for a bound that is not attained.
    pub fn show(&self, model: Option<&Model>) -> String {
        let num = |v: &Value| match model {
            Some(m) => m.show(v),
            None => format!("{v:?}"),
        };
        match &self.value {
            OptValue::Exact(v) => num(v),
            OptValue::NotAttained(v) if self.maximize => format!("(- {} epsilon)", num(v)),
            OptValue::NotAttained(v) => format!("(+ {} epsilon)", num(v)),
            OptValue::Unbounded if self.maximize => "oo".to_string(),
            OptValue::Unbounded => "(- oo)".to_string(),
        }
    }
}

/// What a command printed, if anything.
#[derive(Debug, Clone)]
pub enum Response {
    Check(CheckResult),
    /// Text output (`get-model`, `get-value`, `echo`, `get-info`, ...), in SMT-LIB syntax.
    Text(String),
}

/// A `define-fun` macro: parameters (name, sort), return sort, body.
#[derive(Debug, Clone)]
pub struct Def {
    pub params: Vec<(String, String)>,
    pub ret: String,
    pub body: Sexp,
}

/// One assertion level (`push`/`pop`): what to undo when it is popped.
#[derive(Default)]
struct Frame {
    assert_len: usize,
    /// Functions, constants and definitions declared at this level, in order.
    decls: Vec<String>,
    /// Sorts declared or defined at this level.
    sorts: Vec<String>,
    /// Names introduced by `(! t :named n)` in assertions at this level.
    named: Vec<String>,
}

/// Function symbols that are part of the Core theory and cannot be declared.
const RESERVED: &[&str] = &[
    "true", "false", "not", "and", "or", "=>", "xor", "=", "distinct", "ite", "let", "!", "Bool",
    "_", "as", "forall", "exists", "match", "par",
];

/// Logics this front-end decides.
const LOGICS: &[&str] = &[
    "QF_UF", "QF_EQ", "QF_SAT", "QF_LRA", "QF_RDL", "QF_LIA", "QF_IDL", "QF_BV", "QF_NRA", "ALL",
];

/// A processed SMT-LIB script. Each `(check-sat)` produces one [`CheckResult`].
pub struct Script {
    /// Declared sort or `define-sort` alias -> the declared sort it stands for.
    sorts: FxHashMap<String, String>,
    /// symbol -> (argument sorts, return sort)
    sigs: FxHashMap<String, (Vec<String>, String)>,
    defs: FxHashMap<String, Def>,
    /// `:named` term -> its sort.
    named: FxHashMap<String, String>,
    asserts: Vec<Sexp>,
    frames: Vec<Frame>,
    expected: Option<Answer>,
    logic: Option<String>,
    /// The model of the last `check-sat`, while it is still current (cleared by any change to the
    /// assertion stack).
    model: Option<Model>,
    reason_unknown: Option<String>,
    objective: Option<Objective>,
    /// The optimum found by the last `check-sat`, for `get-objectives`.
    last_objective: Option<ObjectiveResult>,
    exited: bool,
    /// Raised from outside to interrupt a running `check-sat` (it then answers `unknown`).
    stop: Option<Arc<AtomicBool>>,
    pub results: Vec<CheckResult>,
}

impl Default for Script {
    fn default() -> Self {
        Script::new()
    }
}

impl Script {
    pub fn new() -> Script {
        Script {
            sorts: FxHashMap::default(),
            sigs: FxHashMap::default(),
            defs: FxHashMap::default(),
            named: FxHashMap::default(),
            asserts: Vec::new(),
            frames: vec![Frame::default()],
            expected: None,
            logic: None,
            model: None,
            reason_unknown: None,
            objective: None,
            last_objective: None,
            exited: false,
            stop: None,
            results: Vec::new(),
        }
    }

    /// Interrupt running and future `check-sat`s while `flag` is raised: they answer `unknown`
    /// with reason "interrupted". The caller lowers the flag again before the next command.
    pub fn set_stop_flag(&mut self, flag: Arc<AtomicBool>) {
        self.stop = Some(flag);
    }

    /// Parse and run a whole script, stopping at `(exit)` or at the first error.
    pub fn run(input: &str) -> Result<Script, String> {
        let cmds = crate::sexp::parse_script(input)?;
        let mut script = Script::new();
        for cmd in &cmds {
            script.exec(cmd)?;
            if script.exited {
                break;
            }
        }
        Ok(script)
    }

    /// Run a single command and return what it printed, if anything.
    pub fn exec(&mut self, cmd: &Sexp) -> Result<Option<Response>, String> {
        self.command(cmd)
    }

    /// The logic set via `(set-logic …)`, if any (for the REPL prompt).
    pub fn logic(&self) -> Option<&str> {
        self.logic.as_deref()
    }

    /// True once `(exit)` has run.
    pub fn exited(&self) -> bool {
        self.exited
    }

    /// The model of the last `check-sat`, if it was `sat` and nothing changed since.
    pub fn model(&self) -> Option<&Model> {
        self.model.as_ref()
    }

    fn command(&mut self, cmd: &Sexp) -> Result<Option<Response>, String> {
        let list = cmd.as_list().ok_or("expected a command in parentheses")?;
        let head = list
            .first()
            .and_then(Sexp::as_atom)
            .ok_or("empty command")?;
        let args = &list[1..];
        match head {
            "declare-sort" => self.declare_sort(args)?,
            "define-sort" => self.define_sort(args)?,
            "declare-fun" => self.declare_fun(args)?,
            "declare-const" => self.declare_const(args)?,
            "define-fun" => self.define_fun(args)?,
            "assert" => {
                let [a] = args else {
                    return Err("assert expects one formula".to_string());
                };
                // A rejected assertion must not leave its `:named` labels behind.
                let named_before = self.frame().named.len();
                let checked = match self.check_term(a, &mut Vec::new(), true) {
                    Ok(s) if s == "Bool" => Ok(()),
                    Ok(s) => Err(format!("assert expects a Bool, got a term of sort {s}")),
                    Err(e) => Err(e),
                };
                if let Err(e) = checked {
                    let added: Vec<String> = self.frame().named.drain(named_before..).collect();
                    for n in added {
                        self.named.remove(&n);
                    }
                    return Err(e);
                }
                self.asserts.push(a.clone());
                self.model = None;
            }
            "check-sat" => {
                if !args.is_empty() {
                    return Err("check-sat takes no arguments".to_string());
                }
                return self.check_sat(&[]).map(Some);
            }
            "check-sat-assuming" => {
                let assumptions = match args {
                    [Sexp::List(l)] => l,
                    _ => return Err("check-sat-assuming expects a list of literals".to_string()),
                };
                for a in assumptions {
                    if self.check_term(a, &mut Vec::new(), false)? != "Bool" {
                        return Err(format!("assumption {a} is not a Bool"));
                    }
                }
                return self.check_sat(assumptions).map(Some);
            }
            "maximize" | "minimize" => {
                // (maximize t [:attributes]) — z3's optimization extension.
                let Some(t) = args.first() else {
                    return Err(format!("{head} expects a term"));
                };
                let sort = self.check_term(t, &mut Vec::new(), false)?;
                if !is_arith(&sort) {
                    return Err(format!("{head} expects an Int or Real term, got {sort}"));
                }
                if self.objective.is_some() {
                    return Err("only one objective at a time is supported".to_string());
                }
                self.objective = Some(Objective {
                    term: t.clone(),
                    maximize: head == "maximize",
                    depth: self.frames.len() - 1,
                });
                self.model = None;
            }
            "get-objectives" => {
                let Some(r) = self.last_objective.as_ref() else {
                    if self.objective.is_some() {
                        // The last check-sat was not sat: there is no optimum to report.
                        return Ok(Some(Response::Text("(objectives\n)".to_string())));
                    }
                    return Err(
                        "no objectives: set one with maximize/minimize, then check-sat".to_string(),
                    );
                };
                let shown = r.show(self.model.as_ref());
                return Ok(Some(Response::Text(format!(
                    "(objectives\n ({} {shown})\n)",
                    r.term
                ))));
            }
            "get-model" => {
                let m = self.model.as_ref().ok_or(
                    "no model available: the last check-sat was not sat, or assertions changed since",
                )?;
                return Ok(Some(Response::Text(m.to_smtlib())));
            }
            "get-value" => return self.get_value(args).map(Some),
            "get-assertions" => {
                let all: Vec<String> = self.asserts.iter().map(|a| a.to_string()).collect();
                return Ok(Some(Response::Text(format!("({})", all.join("\n ")))));
            }
            "get-info" => return self.get_info(args).map(Some),
            "echo" => {
                let [Sexp::Atom(s)] = args else {
                    return Err("echo expects a string".to_string());
                };
                return Ok(Some(Response::Text(s.clone())));
            }
            "push" => self.push(args)?,
            "pop" => self.pop(args)?,
            "reset" => {
                let stop = self.stop.take();
                *self = Script::new();
                self.stop = stop;
            }
            "set-info" => self.set_info(args),
            "set-logic" => {
                let [Sexp::Atom(l)] = args else {
                    return Err("set-logic expects a logic name".to_string());
                };
                if !LOGICS.contains(&l.as_str()) {
                    return Err(format!(
                        "logic {l} is not supported yet (SMT-Rex decides {})",
                        LOGICS.join(", ")
                    ));
                }
                self.logic = Some(l.clone());
            }
            "set-option" => {}
            "exit" => self.exited = true,
            "get-unsat-core"
            | "get-proof"
            | "get-assignment"
            | "get-unsat-assumptions"
            | "reset-assertions"
            | "define-fun-rec"
            | "define-funs-rec"
            | "declare-datatype"
            | "declare-datatypes"
            | "get-option" => {
                return Err(format!("'{head}' is not supported yet"));
            }
            other => return Err(format!("unknown command '{other}'")),
        }
        Ok(None)
    }

    fn frame(&mut self) -> &mut Frame {
        self.frames
            .last_mut()
            .expect("the base frame is never popped")
    }

    fn fresh_symbol(&self, name: &str) -> Result<(), String> {
        if RESERVED.contains(&name) || bv::OP_NAMES.contains(&name) {
            return Err(format!("'{name}' is reserved"));
        }
        if self.sigs.contains_key(name)
            || self.defs.contains_key(name)
            || self.named.contains_key(name)
        {
            return Err(format!("'{name}' is already declared"));
        }
        Ok(())
    }

    /// Resolve a sort expression to `Bool` or a declared sort (following `define-sort` aliases).
    fn resolve_sort(&self, s: &Sexp) -> Result<String, String> {
        match s {
            Sexp::Atom(a) if a == "Bool" => Ok("Bool".to_string()),
            Sexp::Atom(a) if a == "Real" || a == "Int" => Ok(a.clone()),
            Sexp::Atom(a) => match self.sorts.get(a) {
                Some(target) => Ok(target.clone()),
                None => Err(format!("unknown sort '{a}'")),
            },
            Sexp::List(l) => match bv::parse_sort(l) {
                Some(bv) => bv,
                None => Err(format!("parametric sort {s} is not supported")),
            },
        }
    }

    fn declare_sort(&mut self, args: &[Sexp]) -> Result<(), String> {
        // (declare-sort name arity)
        let (name, arity) = match args {
            [Sexp::Atom(n)] => (n, "0"),
            [Sexp::Atom(n), Sexp::Atom(a)] => (n, a.as_str()),
            _ => return Err("declare-sort expects a name and an arity".to_string()),
        };
        if arity != "0" {
            return Err(format!(
                "sort {name} has arity {arity}; only arity 0 is supported"
            ));
        }
        if name == "Bool" || self.sorts.contains_key(name) {
            return Err(format!("sort '{name}' is already declared"));
        }
        self.sorts.insert(name.clone(), name.clone());
        let name = name.clone();
        self.frame().sorts.push(name);
        Ok(())
    }

    fn define_sort(&mut self, args: &[Sexp]) -> Result<(), String> {
        // (define-sort name () sort)
        let [Sexp::Atom(name), Sexp::List(params), target] = args else {
            return Err("define-sort expects a name, parameters and a sort".to_string());
        };
        if !params.is_empty() {
            return Err(format!("parametric define-sort {name} is not supported"));
        }
        if name == "Bool" || self.sorts.contains_key(name) {
            return Err(format!("sort '{name}' is already declared"));
        }
        let target = self.resolve_sort(target)?;
        if target == "Bool" {
            return Err("aliases of Bool are not supported".to_string());
        }
        self.sorts.insert(name.clone(), target);
        let name = name.clone();
        self.frame().sorts.push(name);
        Ok(())
    }

    fn declare_fun(&mut self, args: &[Sexp]) -> Result<(), String> {
        // (declare-fun name (argSorts...) retSort)
        let [Sexp::Atom(name), Sexp::List(arg_sorts), ret] = args else {
            return Err("declare-fun expects a name, argument sorts and a return sort".to_string());
        };
        self.fresh_symbol(name)?;
        let arg_sorts = arg_sorts
            .iter()
            .map(|s| self.resolve_sort(s))
            .collect::<Result<Vec<_>, _>>()?;
        let ret = self.resolve_sort(ret)?;
        if !arg_sorts.is_empty() && (is_arith(&ret) || arg_sorts.iter().any(|s| is_arith(s))) {
            return Err(format!(
                "'{name}': functions over numbers need QF_UFLRA/QF_UFLIA, which SMT-Rex does not \
                 support yet"
            ));
        }
        if !arg_sorts.is_empty()
            && (bv::width(&ret).is_some() || arg_sorts.iter().any(|s| bv::width(s).is_some()))
        {
            return Err(format!(
                "'{name}': functions over bit-vectors need QF_UFBV, which SMT-Rex does not support yet"
            ));
        }
        self.model = None;
        self.sigs.insert(name.clone(), (arg_sorts, ret));
        let name = name.clone();
        self.frame().decls.push(name);
        Ok(())
    }

    fn declare_const(&mut self, args: &[Sexp]) -> Result<(), String> {
        // (declare-const name sort)
        let [name, sort] = args else {
            return Err("declare-const expects a name and a sort".to_string());
        };
        self.declare_fun(&[name.clone(), Sexp::List(Vec::new()), sort.clone()])
    }

    fn define_fun(&mut self, args: &[Sexp]) -> Result<(), String> {
        // (define-fun name ((param Sort)...) retSort body)
        let [Sexp::Atom(name), Sexp::List(params), ret, body] = args else {
            return Err(
                "define-fun expects a name, parameters, a return sort and a body".to_string(),
            );
        };
        self.fresh_symbol(name)?;
        let params = params
            .iter()
            .map(|p| match p.as_list() {
                Some([Sexp::Atom(n), sort]) => Ok((n.clone(), self.resolve_sort(sort)?)),
                _ => Err(format!("malformed define-fun parameter {p}")),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let ret = self.resolve_sort(ret)?;
        let mut local = params.clone();
        let body_sort = self.check_term(body, &mut local, false)?;
        if unify(&body_sort, &ret).as_deref() != Some(ret.as_str()) {
            return Err(format!(
                "define-fun {name}: the body has sort {body_sort}, but {ret} was declared"
            ));
        }
        self.model = None;
        self.defs.insert(
            name.clone(),
            Def {
                params,
                ret,
                body: body.clone(),
            },
        );
        let name = name.clone();
        self.frame().decls.push(name);
        Ok(())
    }

    fn push(&mut self, args: &[Sexp]) -> Result<(), String> {
        let n = count_arg(args)?;
        for _ in 0..n {
            self.frames.push(Frame {
                assert_len: self.asserts.len(),
                ..Frame::default()
            });
        }
        self.model = None;
        Ok(())
    }

    fn pop(&mut self, args: &[Sexp]) -> Result<(), String> {
        let n = count_arg(args)?;
        if n >= self.frames.len() {
            return Err(format!(
                "cannot pop {n} levels: only {} pushed",
                self.frames.len() - 1
            ));
        }
        let remaining = self.frames.len() - n;
        if self
            .objective
            .as_ref()
            .is_some_and(|o| o.depth >= remaining)
        {
            self.objective = None;
        }
        for _ in 0..n {
            let f = self.frames.pop().expect("checked above");
            for d in &f.decls {
                self.sigs.remove(d);
                self.defs.remove(d);
            }
            for s in &f.sorts {
                self.sorts.remove(s);
            }
            for n in &f.named {
                self.named.remove(n);
            }
            self.asserts.truncate(f.assert_len);
        }
        self.model = None;
        Ok(())
    }

    fn set_info(&mut self, args: &[Sexp]) {
        // (set-info :status sat|unsat|unknown)
        if let [Sexp::Atom(key), Sexp::Atom(val)] = args {
            if key == ":status" {
                self.expected = match val.as_str() {
                    "sat" => Some(Answer::Sat),
                    "unsat" => Some(Answer::Unsat),
                    _ => None,
                };
            }
        }
    }

    fn get_info(&self, args: &[Sexp]) -> Result<Response, String> {
        let [Sexp::Atom(key)] = args else {
            return Err("get-info expects a keyword".to_string());
        };
        let value = match key.as_str() {
            ":name" => "\"SMT-Rex\"".to_string(),
            ":version" => format!("\"{}\"", env!("CARGO_PKG_VERSION")),
            ":authors" => "\"Paul Tristan Wagner\"".to_string(),
            ":error-behavior" => "immediate-exit".to_string(),
            ":reason-unknown" => match &self.reason_unknown {
                Some(r) => format!("\"{}\"", r.replace('"', "\"\"")),
                None => return Err("no check-sat returned unknown".to_string()),
            },
            _ => return Ok(Response::Text("unsupported".to_string())),
        };
        Ok(Response::Text(format!("({key} {value})")))
    }

    fn get_value(&mut self, args: &[Sexp]) -> Result<Response, String> {
        let [Sexp::List(terms)] = args else {
            return Err("get-value expects a list of terms".to_string());
        };
        if terms.is_empty() {
            return Err("get-value expects at least one term".to_string());
        }
        let values = self.values(terms)?;
        let model = self
            .model
            .as_ref()
            .expect("values() succeeded, so there is a model");
        let pairs: Vec<String> = terms
            .iter()
            .zip(values)
            .map(|(t, v)| format!("({t} {})", model.show(&v)))
            .collect();
        Ok(Response::Text(format!("({})", pairs.join("\n "))))
    }

    /// The values of `terms` in the current model (the programmatic form of `get-value`).
    pub fn values(&mut self, terms: &[Sexp]) -> Result<Vec<Value>, String> {
        for t in terms {
            self.check_term(t, &mut Vec::new(), false)?;
        }
        let model = self.model.as_ref().ok_or(
            "no model available: the last check-sat was not sat, or assertions changed since",
        )?;
        let mut ev = Evaluator::new(model, &self.defs);
        // Re-evaluate the assertions so `:named` terms have their values.
        for a in &self.asserts {
            ev.eval(a)?;
        }
        terms.iter().map(|t| ev.eval(t)).collect()
    }
}

fn count_arg(args: &[Sexp]) -> Result<usize, String> {
    match args {
        [] => Ok(1),
        [Sexp::Atom(s)] => s
            .parse::<usize>()
            .map_err(|_| format!("bad push/pop count '{s}'")),
        _ => Err("push/pop expects one numeral".to_string()),
    }
}
