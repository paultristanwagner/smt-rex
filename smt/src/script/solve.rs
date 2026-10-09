//! `check-sat`: encoding, solving, optimisation and the model self-check.

use crate::bv::{self};
use crate::model::{Evaluator, Model, Value};
use crate::sexp::Sexp;
use smtrex_theory::lra::{BoundKind, Optimum};
use std::sync::atomic::Ordering;

use super::*;
use crate::encode::Encoder;
use smtrex_poly::stats;

/// A `check-sat` result.
struct Outcome {
    answer: Answer,
    /// The model, if `sat`.
    model: Option<Model>,
    /// Why, if `unknown`.
    reason: Option<String>,
    objective: Option<ObjectiveResult>,
}

impl Outcome {
    fn sat(model: Model, objective: Option<ObjectiveResult>) -> Outcome {
        Outcome {
            answer: Answer::Sat,
            model: Some(model),
            reason: None,
            objective,
        }
    }

    fn unsat() -> Outcome {
        Outcome {
            answer: Answer::Unsat,
            model: None,
            reason: None,
            objective: None,
        }
    }

    fn unknown(why: &str) -> Outcome {
        Outcome {
            answer: Answer::Unknown,
            model: None,
            reason: Some(why.to_string()),
            objective: None,
        }
    }
}

impl Script {
    /// `check-sat`. Input the solver cannot handle (e.g. a non-linear term) is an error; an
    /// interrupted solve or a failed model self-check answers `unknown` with a reason.
    pub(super) fn check_sat(&mut self, assumptions: &[Sexp]) -> Result<Response, String> {
        let outcome = self.solve(assumptions);
        if outcome.is_err() {
            self.model = None;
        }
        let Outcome {
            answer,
            model,
            reason,
            objective,
        } = outcome?;
        self.model = model;
        self.reason_unknown = reason.clone();
        self.last_objective = objective.clone();
        let r = CheckResult {
            answer,
            expected: self.expected,
            reason,
            objective,
        };
        self.results.push(r.clone());
        Ok(Response::Check(r))
    }

    /// Build a fresh solver instance, encode all in-scope assertions plus the `check-sat-assuming`
    /// assumptions (as unit clauses), and solve. A `sat` answer comes with its model, which has
    /// been checked against every assertion. `Err` is input the solver cannot encode; an answer
    /// that cannot be trusted is `unknown` with the reason. With an objective in scope, the
    /// answer also carries the optimum (see [`Self::optimize`]).
    fn solve(&self, assumptions: &[Sexp]) -> Result<Outcome, String> {
        let interrupted = || {
            self.stop
                .as_ref()
                .is_some_and(|f| f.load(Ordering::Relaxed))
        };
        let nra = self.logic.as_deref() == Some("QF_NRA");
        if nra && self.objective.is_some() {
            return Err("maximize/minimize is not supported in QF_NRA".to_string());
        }
        // NRA profiling (SMTREX_NRA_STATS), reported with the answer.
        let report = |answer: &str| {
            if nra {
                stats::report(answer);
            }
        };
        if nra {
            stats::start();
        }
        let encode_phase = stats::outer(stats::Outer::Encode);
        let mut enc = Encoder::new(&self.sigs, &self.defs, nra);
        if let Some(flag) = &self.stop {
            enc.builder.set_stop_flag(flag.clone());
        }
        for a in &self.asserts {
            if nra {
                enc.eliminate_real(a)?;
            } else {
                enc.eliminate(a)?;
            }
        }
        for a in self.asserts.iter().chain(assumptions) {
            if interrupted() {
                return Ok(Outcome::unknown("interrupted"));
            }
            let lit = enc.bool(a)?;
            enc.builder.add_clause(vec![lit]);
        }
        drop(encode_phase);
        if let Some(obj) = &self.objective {
            return self.optimize(&mut enc, obj, assumptions);
        }
        match enc.builder.solve() {
            Some(true) => {}
            Some(false) => {
                report("unsat");
                return Ok(Outcome::unsat());
            }
            None => return Ok(Outcome::unknown("interrupted")),
        }
        let checked = {
            let _o = stats::outer(stats::Outer::SelfCheck);
            self.checked_model(&enc, assumptions)
        };
        report("sat");
        Ok(match checked {
            Ok(model) => Outcome::sat(model, None),
            Err(why) => Outcome::unknown(&why),
        })
    }

    /// Optimisation by linear search, as in OptiMathSAT and z3: solve, maximise the objective
    /// over that solution's bounds with the primal Simplex, demand a strictly better value, and
    /// repeat until unsatisfiable. Over integers "strictly better" is `+1`, and an unbounded
    /// relaxation at an integer point means the integer problem is unbounded (Meyer 1974).
    fn optimize(
        &self,
        enc: &mut Encoder,
        obj: &Objective,
        assumptions: &[Sexp],
    ) -> Result<Outcome, String> {
        let lin = enc.lin(&obj.term)?;
        // Always maximise: minimising t is maximising -t.
        let lin = if obj.maximize {
            lin
        } else {
            lin.scale(&-smtrex_core::Rational::one())
        };
        let sign = |q: smtrex_core::Rational| if obj.maximize { q } else { -q };
        let is_int = enc.lin_is_int(&lin);
        let wrap = |q: smtrex_core::Rational| {
            if is_int {
                Value::Int(q)
            } else {
                Value::Real(q)
            }
        };
        let result = |value: OptValue| ObjectiveResult {
            term: obj.term.clone(),
            maximize: obj.maximize,
            value,
        };
        let o = (!lin.terms.is_empty()).then(|| enc.builder.lra().term_var(&lin.terms));
        let mut best: Option<(Model, OptValue)> = None;
        loop {
            match enc.builder.solve() {
                Some(true) => {}
                Some(false) => break,
                None => return Ok(Outcome::unknown("interrupted")),
            }
            let Some(o) = o else {
                // A constant objective: any model is optimal.
                let model = match self.checked_model(enc, assumptions) {
                    Ok(m) => m,
                    Err(why) => return Ok(Outcome::unknown(&why)),
                };
                let v = OptValue::Exact(wrap(sign(lin.constant.clone())));
                return Ok(Outcome::sat(model, Some(result(v))));
            };
            // Over the integers, the model must be read before the Simplex moves the assignment
            // (the relaxation's optimum need not be integral).
            let model_first = if is_int {
                match self.checked_model(enc, assumptions) {
                    Ok(m) => Some(m),
                    Err(why) => return Ok(Outcome::unknown(&why)),
                }
            } else {
                None
            };
            let current = enc.builder.lra_ref().model()[o as usize].clone();
            let opt = enc.builder.lra().maximize(o);
            let model = match model_first {
                Some(m) => m,
                None => match self.checked_model(enc, assumptions) {
                    Ok(m) => m,
                    Err(why) => return Ok(Outcome::unknown(&why)),
                },
            };
            let m = match opt {
                Optimum::Unbounded => {
                    return Ok(Outcome::sat(model, Some(result(OptValue::Unbounded))));
                }
                Optimum::Max(m) => m,
            };
            // Record this solution and demand a strictly better one.
            let (value, better) = if is_int {
                let v = OptValue::Exact(wrap(sign(&current + &lin.constant)));
                let next = &current + &smtrex_core::Rational::one();
                (v, enc.builder.bound_atom(o, BoundKind::Ge, next))
            } else if m.delta.is_negative() {
                // Supremum c not attained: better means o >= c.
                let v = OptValue::NotAttained(wrap(sign(&m.value + &lin.constant)));
                (v, enc.builder.bound_atom(o, BoundKind::Ge, m.value.clone()))
            } else {
                // Attained (or approached from above): better means o > c.
                let v = OptValue::Exact(wrap(sign(&m.value + &lin.constant)));
                (
                    v,
                    !enc.builder.bound_atom(o, BoundKind::Le, m.value.clone()),
                )
            };
            best = Some((model, value));
            enc.builder.add_clause(vec![better]);
        }
        Ok(match best {
            Some((model, value)) => Outcome::sat(model, Some(result(value))),
            None => Outcome::unsat(),
        })
    }

    /// The model of the current satisfiable state, checked against every assertion by the
    /// independent evaluator. `Err` is the reason it cannot be trusted.
    fn checked_model(&self, enc: &Encoder, assumptions: &[Sexp]) -> Result<Model, String> {
        let decl_order: Vec<String> = self.frames.iter().flat_map(|f| f.decls.clone()).collect();
        let mut model = Model::from_euf(
            enc.builder.euf_ref(),
            enc.bool_true,
            &self.sigs,
            &decl_order,
        )
        .map_err(|e| format!("model construction failed: {e}"))?;
        // Arithmetic variables take their values from the Simplex.
        let reals = enc.builder.lra_ref().model();
        for (name, x) in &enc.real_vars {
            let q = enc
                .eliminated_value(*x, &reals)
                .unwrap_or_else(|| reals[*x as usize].clone());
            let is_int = self.sigs.get(name).is_some_and(|(_, s)| s == "Int");
            if is_int && !q.is_integer() {
                return Err(format!(
                    "model self-check failed: {name} = {q} is not an integer"
                ));
            }
            model.set_const(
                name,
                if is_int {
                    Value::Int(q)
                } else {
                    Value::Real(q)
                },
            );
        }
        // Polynomial-arithmetic variables take their values from the NRA theory's model.
        if !enc.poly_vars.is_empty() {
            let values = enc.builder.nra_ref().model();
            for (name, &v) in &enc.poly_vars {
                let value = match enc.poly_subst.get(&v) {
                    Some(e) => e.eval(&values),
                    None => values[v].clone(),
                };
                model.set_const(name, Value::from_algebraic(value));
            }
        }
        // Bit-vector constants take their values from the SAT assignment of their bits.
        for (name, bits) in &enc.bv_vars {
            let value = bv::read_bits(bits, |l| enc.builder.lit_value(l));
            let width = bits.len() as u32;
            model.set_const(name, Value::BitVec { width, value });
        }
        let mut ev = Evaluator::new(&model, &self.defs);
        for a in self.asserts.iter().chain(assumptions) {
            match ev.eval(a) {
                Ok(Value::Bool(true)) => {}
                Ok(_) => return Err(format!("model self-check failed: {a} is false")),
                Err(e) => return Err(format!("model self-check failed: {e}")),
            }
        }
        Ok(model)
    }
}
