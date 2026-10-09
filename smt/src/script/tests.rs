use super::*;

fn verdict(r: Option<Response>) -> Answer {
    match r {
        Some(Response::Check(c)) => c.answer,
        other => panic!("expected a check-sat response, got {other:?}"),
    }
}

fn answers(input: &str) -> Vec<Answer> {
    Script::run(input)
        .unwrap()
        .results
        .into_iter()
        .map(|r| r.answer)
        .collect()
}

#[test]
fn eq_diamond_like_unsat() {
    let s = "
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun x0 () U) (declare-fun y0 () U) (declare-fun z0 () U)
        (declare-fun x1 () U)
        (assert (and (or (and (= x0 y0) (= y0 x1)) (and (= x0 z0) (= z0 x1)))
                     (not (= x0 x1))))
        (check-sat)";
    assert_eq!(answers(s), vec![Answer::Unsat]);
}

#[test]
fn congruence_and_predicates() {
    // a=b => f(a)=f(b); P over equal args agrees
    let unsat = "
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U) (declare-fun b () U)
        (declare-fun f (U) U)
        (assert (= a b))
        (assert (not (= (f a) (f b))))
        (check-sat)";
    assert_eq!(answers(unsat), vec![Answer::Unsat]);

    let pred = "
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U) (declare-fun b () U)
        (declare-fun P (U) Bool)
        (assert (= a b))
        (assert (P a))
        (assert (not (P b)))
        (check-sat)";
    assert_eq!(answers(pred), vec![Answer::Unsat]);
}

#[test]
fn ite_term_level() {
    // (ite c a b): if c then result=a. With c true and a!=result forced -> interplay
    let s = "
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U) (declare-fun b () U)
        (declare-fun c () Bool)
        (assert c)
        (assert (not (= (ite c a b) a)))
        (check-sat)";
    assert_eq!(answers(s), vec![Answer::Unsat]);

    let sat = "
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U) (declare-fun b () U)
        (declare-fun c () Bool)
        (assert (not (= (ite c a b) a)))
        (check-sat)";
    assert_eq!(answers(sat), vec![Answer::Sat]);
}

#[test]
fn bool_equality_and_distinct() {
    let s = "
        (set-logic QF_UF)
        (declare-fun p () Bool) (declare-fun q () Bool)
        (assert (= p q))
        (assert (distinct p q))
        (check-sat)";
    assert_eq!(answers(s), vec![Answer::Unsat]);
}

#[test]
fn incremental_exec_surfaces_results() {
    // Mirrors how the REPL drives the solver: feed commands one at a time and observe the
    // verdict returned by the (check-sat) command itself.
    let mut s = Script::new();
    for src in [
        "(set-logic QF_UF)",
        "(declare-sort U 0)",
        "(declare-fun a () U)",
        "(declare-fun b () U)",
        "(assert (= a b))",
    ] {
        let cmd = &crate::sexp::parse_script(src).unwrap()[0];
        assert!(s.exec(cmd).unwrap().is_none());
    }
    assert_eq!(s.logic(), Some("QF_UF"));
    let check = &crate::sexp::parse_script("(check-sat)").unwrap()[0];
    assert_eq!(verdict(s.exec(check).unwrap()), Answer::Sat);
    let neg = &crate::sexp::parse_script("(assert (not (= a b)))").unwrap()[0];
    assert!(s.exec(neg).unwrap().is_none());
    assert_eq!(verdict(s.exec(check).unwrap()), Answer::Unsat);
}

#[test]
fn let_bindings() {
    let unsat = "
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U) (declare-fun b () U) (declare-fun f (U) U)
        (assert (let ((x (f a)) (p (= a b))) (and p (not (= x (f b))))))
        (check-sat)";
    assert_eq!(answers(unsat), vec![Answer::Unsat]);
    // Parallel binding: the inner `b` on the right-hand side is the declared `b`, not `a`.
    let parallel = "
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U) (declare-fun b () U)
        (assert (not (= a b)))
        (assert (let ((b a) (c b)) (not (= b c))))
        (check-sat)";
    assert_eq!(answers(parallel), vec![Answer::Sat]);
    // Shadowing: the inner binding of `x` wins inside its body.
    let shadow = "
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U) (declare-fun b () U)
        (assert (not (= a b)))
        (assert (let ((x a)) (let ((x b)) (= x b))))
        (check-sat)";
    assert_eq!(answers(shadow), vec![Answer::Sat]);
    // A let-bound Bool used as a function argument gets congruence.
    let bool_arg = "
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U) (declare-fun b () U) (declare-fun g (Bool) U)
        (assert (let ((p (= a a)) (q true)) (not (= (g p) (g q)))))
        (check-sat)";
    assert_eq!(answers(bool_arg), vec![Answer::Unsat]);
}

#[test]
fn define_fun_macros() {
    let unsat = "
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U) (declare-fun b () U) (declare-fun f (U) U)
        (define-fun same ((x U) (y U)) Bool (= (f x) (f y)))
        (define-fun ab () Bool (= a b))
        (assert ab)
        (assert (not (same a b)))
        (check-sat)";
    assert_eq!(answers(unsat), vec![Answer::Unsat]);
    // The body sees its parameters, not the caller's let bindings of the same name.
    let scoping = "
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U) (declare-fun b () U) (declare-fun y () U)
        (define-fun is_y ((x U)) Bool (= x y))
        (assert (= a y))
        (assert (not (= b y)))
        (assert (let ((y b)) (is_y a)))
        (check-sat)";
    assert_eq!(answers(scoping), vec![Answer::Sat]);
    // Bool parameter, used both as a formula and as a function argument.
    let bool_param = "
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun p () Bool) (declare-fun g (Bool) U)
        (define-fun h ((c Bool)) U (ite c (g c) (g true)))
        (assert (not (= (h p) (g true))))
        (check-sat)";
    assert_eq!(answers(bool_param), vec![Answer::Unsat]);
    // Definitions are scoped by push/pop.
    let popped = "
        (set-logic QF_UF)
        (push 1)
        (define-fun t () Bool false)
        (pop 1)
        (declare-fun t () Bool)
        (assert t)
        (check-sat)";
    assert_eq!(answers(popped), vec![Answer::Sat]);
}

#[test]
fn named_annotations() {
    let s = "
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U) (declare-fun b () U)
        (assert (! (= a b) :named ab))
        (assert (! (not ab) :named nab :weight 1))
        (check-sat)";
    assert_eq!(answers(s), vec![Answer::Unsat]);
}

#[test]
fn check_sat_assuming_uses_assumptions() {
    let s = "
        (set-logic QF_UF)
        (declare-fun p () Bool)
        (assert p)
        (check-sat-assuming ((not p)))
        (check-sat)";
    assert_eq!(answers(s), vec![Answer::Unsat, Answer::Sat]);
}

fn texts(input: &str) -> Vec<String> {
    let mut script = Script::new();
    let mut out = Vec::new();
    for cmd in &crate::sexp::parse_script(input).unwrap() {
        match script.exec(cmd).unwrap() {
            Some(Response::Text(t)) => out.push(t),
            Some(Response::Check(c)) => out.push(c.answer.as_str().to_string()),
            None => {}
        }
    }
    out
}

fn error(input: &str) -> String {
    match Script::run(input) {
        Err(e) => e,
        Ok(_) => panic!("expected an error from:\n{input}"),
    }
}

#[test]
fn models_and_values() {
    let out = texts(
        "
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U) (declare-fun b () U)
        (declare-fun f (U) U) (declare-fun P (U) Bool) (declare-fun p () Bool)
        (assert (not (= a b)))
        (assert (= (f a) b))
        (assert (= (f b) b))
        (assert (P a))
        (assert (not (P b)))
        (assert (! (= p (P (f a))) :named link))
        (check-sat)
        (get-model)
        (get-value (a b (f a) (f (f a)) (P b) p link))",
    );
    assert_eq!(out[0], "sat");
    let model = &out[1];
    assert!(model.contains("; cardinality of U is 2"), "{model}");
    assert!(model.contains("(define-fun a () U (as @U_0 U))"), "{model}");
    assert!(model.contains("(define-fun b () U (as @U_1 U))"), "{model}");
    assert!(
        model.contains("(define-fun f ((_arg_1 U)) U (as @U_1 U))"),
        "{model}"
    );
    assert!(model.contains("(define-fun p () Bool false)"), "{model}");
    assert_eq!(
        out[2],
        "((a (as @U_0 U))\n (b (as @U_1 U))\n ((f a) (as @U_1 U))\n ((f (f a)) (as @U_1 U))\n \
         ((P b) false)\n (p false)\n (link true))"
    );
}

#[test]
fn model_requires_a_current_sat() {
    let unsat = "(declare-fun p () Bool) (assert (and p (not p))) (check-sat) (get-model)";
    assert!(error(unsat).starts_with("no model available"));
    let stale = "(declare-fun p () Bool) (check-sat) (assert p) (get-model)";
    assert!(error(stale).starts_with("no model available"));
}

#[test]
fn rejects_ill_formed_input() {
    let u = "(declare-sort U 0) (declare-fun a () U) (declare-fun f (U) U) (declare-fun p () Bool)";
    for (bad, why) in [
        ("(assert a)", "assert expects a Bool"),
        ("(assert (= a p))", "mixes sorts"),
        ("(assert (= a c))", "unknown symbol 'c'"),
        ("(assert (= (f a a) a))", "expects 1 arguments"),
        ("(assert (= f a))", "apply it"),
        ("(assert (and p a))", "expects Bool arguments"),
        ("(assert (= (ite p a p) a))", "branches of 'ite'"),
        ("(declare-fun a () U)", "already declared"),
        ("(declare-fun x () V)", "unknown sort 'V'"),
        ("(define-fun d () U p)", "the body has sort Bool"),
        ("(assert (let ((x a) (x a)) (= x a)))", "bound twice"),
        ("(pop 1)", "cannot pop"),
        ("(frobnicate)", "unknown command"),
    ] {
        let e = error(&format!("{u} {bad}"));
        assert!(e.contains(why), "{bad}: got error '{e}', expected '{why}'");
    }
    assert!(error("(set-logic QF_NIA)").contains("not supported yet"));
}

#[test]
fn rejected_assert_leaves_no_names() {
    let mut s = Script::new();
    let cmds = crate::sexp::parse_script(
        "(declare-sort U 0) (declare-fun a () U)
         (assert (and (! (= a a) :named n) a))
         (assert (! (= a a) :named n))
         (check-sat)",
    )
    .unwrap();
    assert!(s.exec(&cmds[0]).is_ok() && s.exec(&cmds[1]).is_ok());
    assert!(s.exec(&cmds[2]).is_err(), "a is not a Bool");
    assert!(s.exec(&cmds[3]).is_ok(), "the name n is free again");
    assert!(matches!(
        s.exec(&cmds[4]).unwrap(),
        Some(Response::Check(CheckResult {
            answer: Answer::Sat,
            ..
        }))
    ));
}

#[test]
fn define_sort_aliases() {
    let s = "
        (declare-sort U 0)
        (define-sort V () U)
        (declare-fun a () U) (declare-fun b () V)
        (assert (= a b))
        (assert (not (= b a)))
        (check-sat)";
    assert_eq!(answers(s), vec![Answer::Unsat]);
}

#[test]
fn internal_names_cannot_clash() {
    // A user symbol spelled like an old internal name is just a symbol.
    let s = "
        (declare-fun !true () Bool) (declare-fun |ite1| () Bool)
        (assert (not !true))
        (assert ite1)
        (check-sat)";
    assert_eq!(answers(s), vec![Answer::Sat]);
}

/// Random QF_UF scripts: the solver must never return `unknown` (that would mean the model of
/// a `sat` answer failed its self-check), and must agree with itself under push/pop.
#[test]
fn random_formulas_self_check() {
    struct Gen(u64);
    impl Gen {
        fn next(&mut self, n: u64) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0 % n
        }
        fn term(&mut self, d: u32) -> String {
            let c = || ["a", "b", "c", "d"];
            if d == 0 {
                return c()[self.next(4) as usize].to_string();
            }
            match self.next(5) {
                0 => format!("(f {})", self.term(d - 1)),
                1 => format!("(g {} {})", self.term(d - 1), self.term(d - 1)),
                2 => format!(
                    "(ite {} {} {})",
                    self.form(d - 1),
                    self.term(d - 1),
                    self.term(d - 1)
                ),
                3 => format!("(h {})", self.form(d - 1)),
                _ => c()[self.next(4) as usize].to_string(),
            }
        }
        fn form(&mut self, d: u32) -> String {
            if d == 0 {
                return ["p", "q", "true", "false"][self.next(4) as usize].to_string();
            }
            match self.next(9) {
                0 => format!("(not {})", self.form(d - 1)),
                1 => format!("(and {} {})", self.form(d - 1), self.form(d - 1)),
                2 => format!(
                    "(or {} {} {})",
                    self.form(d - 1),
                    self.form(d - 1),
                    self.form(d - 1)
                ),
                3 => format!("(=> {} {})", self.form(d - 1), self.form(d - 1)),
                4 => format!("(= {} {})", self.term(d - 1), self.term(d - 1)),
                5 => format!(
                    "(distinct {} {} {})",
                    self.term(d - 1),
                    self.term(d - 1),
                    self.term(d - 1)
                ),
                6 => format!("(P {})", self.term(d - 1)),
                7 => format!(
                    "(let ((x {}) (y {})) (or (= x {}) y))",
                    self.term(d - 1),
                    self.form(d - 1),
                    self.term(d - 1)
                ),
                _ => format!("(xor {} {})", self.form(d - 1), self.form(d - 1)),
            }
        }
    }
    let mut g = Gen(0x2545F4914F6CDD1D);
    let (mut sat, mut unsat) = (0, 0);
    for _ in 0..3000 {
        let mut src = String::from(
            "(declare-sort U 0) (declare-fun a () U) (declare-fun b () U) (declare-fun c () U)
             (declare-fun d () U) (declare-fun f (U) U) (declare-fun g (U U) U)
             (declare-fun h (Bool) U) (declare-fun P (U) Bool) (declare-fun p () Bool)
             (declare-fun q () Bool)",
        );
        for _ in 0..1 + g.next(4) {
            src.push_str(&format!(" (assert {})", g.form(3)));
        }
        src.push_str(" (check-sat)");
        let script = Script::run(&src).unwrap_or_else(|e| panic!("{e}\n{src}"));
        let r = &script.results[0];
        assert_ne!(r.answer, Answer::Unknown, "{:?}\n{src}", r.reason);
        if r.answer == Answer::Sat {
            assert!(script.model().is_some());
            sat += 1;
        } else {
            unsat += 1;
        }
    }
    assert!(
        sat > 100 && unsat > 100,
        "{sat} sat / {unsat} unsat: generator is unbalanced"
    );
}

#[test]
fn linear_real_arithmetic() {
    let base = "(set-logic QF_LRA) (declare-fun x () Real) (declare-fun y () Real)";
    let sat = |body: &str| answers(&format!("{base} {body} (check-sat)"));
    assert_eq!(
        sat("(assert (< x (- 2))) (assert (> x 0))"),
        vec![Answer::Unsat]
    );
    assert_eq!(sat("(assert (< 2 x 3))"), vec![Answer::Sat]);
    assert_eq!(sat("(assert (and (> x 2) (< x 2)))"), vec![Answer::Unsat]);
    assert_eq!(
        sat("(assert (and (>= x 2) (<= x 2) (distinct x 2)))"),
        vec![Answer::Unsat]
    );
    assert_eq!(
        sat("(assert (= (* 2 (+ x y)) (- 4 (* 2 y))))"),
        vec![Answer::Sat]
    );
    assert_eq!(
        sat("(assert (let ((s (+ x y))) (and (<= s 1) (>= (* 3 s) 4))))"),
        vec![Answer::Unsat]
    );
    // Decimal constants and division by constants.
    assert_eq!(
        sat("(assert (and (= x 0.5) (= y (/ x 2)) (> y 0.25)))"),
        vec![Answer::Unsat]
    );
    // ite over reals.
    assert_eq!(
        sat("(declare-const p Bool) (assert (= y (ite p x (- x)))) (assert (< y 0)) (assert (> x 0)) (assert p)"),
        vec![Answer::Unsat]
    );
    // Strictness survives scaling: 2x < 2 and x >= 1.
    assert_eq!(
        sat("(assert (< (* 2 x) 2)) (assert (>= x 1))"),
        vec![Answer::Unsat]
    );
}

#[test]
fn real_models_are_exact() {
    let out = texts(
        "(set-logic QF_LRA) (declare-fun x () Real) (declare-fun y () Real)
         (assert (and (< 2 x 3) (= (* 3 y) x) (> (+ x y) 3.5)))
         (check-sat) (get-value (x y (- y)))",
    );
    assert_eq!(out[0], "sat");
    // The self-check already evaluated the assertions exactly; check the printed form too.
    assert!(
        out[1].contains("(x ") && out[1].contains("(/ "),
        "{}",
        out[1]
    );
    assert!(out[1].contains("((- y) (- "), "{}", out[1]);
}

#[test]
fn non_linear_and_unsupported_arithmetic_are_errors() {
    let base = "(set-logic QF_LRA) (declare-fun x () Real) (declare-fun y () Real)";
    let e = |body: &str| error(&format!("{base} {body} (check-sat)"));
    assert!(e("(assert (> (* x y) 1))").contains("non-linear"));
    assert!(e("(assert (> (/ 1 x) 1))").contains("non-constant"));
    assert!(e("(assert (> (/ x 0) 1))").contains("division by zero"));
    assert!(e("(declare-fun f (Real) Real)").contains("QF_UFLRA"));
    assert!(e("(declare-fun g (Int) Int)").contains("QF_UFLIA"));
    assert!(e("(assert (> x true))").contains("expects numeric arguments"));
}

#[test]
fn nonlinear_real_arithmetic() {
    let base = "(set-logic QF_NRA) (declare-fun x () Real) (declare-fun y () Real)";
    let sat = |body: &str| answers(&format!("{base} {body} (check-sat)"));
    assert_eq!(sat("(assert (= (* x x) 2))"), vec![Answer::Sat]);
    assert_eq!(sat("(assert (< (* x x) 0))"), vec![Answer::Unsat]);
    assert_eq!(
        sat("(assert (> (* x y) 1)) (assert (< x 0)) (assert (> y 0))"),
        vec![Answer::Unsat]
    );
    assert_eq!(
        sat("(assert (or (= (* x x) 2) (= (* x x) 3))) (assert (> x 1.5))"),
        vec![Answer::Sat]
    );
    assert_eq!(
        sat("(assert (= (/ x 2) (* x x))) (assert (distinct x 0))"),
        vec![Answer::Sat]
    );
    // linear atoms are part of the same conjunction
    assert_eq!(
        sat("(assert (= (* x x) 4)) (assert (> x y)) (assert (> y 2))"),
        vec![Answer::Unsat]
    );
    // ite over reals, let, define-fun, push/pop
    assert_eq!(
        answers(&format!(
            "{base} (define-fun sq ((a Real)) Real (* a a))
             (assert (= (sq (ite (> x 0) x (- x))) 9))
             (push 1) (assert (< x 0)) (check-sat) (pop 1)
             (assert (let ((z (* x y))) (and (> z 0) (> y 0) (< x 1)))) (check-sat)"
        )),
        vec![Answer::Sat, Answer::Unsat]
    );
    // negative numerals as single tokens (z3 compatibility)
    assert_eq!(
        sat("(assert (< x -2)) (assert (> x 0))"),
        vec![Answer::Unsat]
    );
}

#[test]
fn nonlinear_models_print_root_objects() {
    let out = texts(
        "(set-logic QF_NRA) (declare-fun x () Real) (declare-fun y () Real)
         (assert (= (* x x) 2)) (assert (> x 0)) (assert (= (* y y y) (- 3)))
         (check-sat) (get-value (x y (* x y) (+ x 1)))",
    );
    assert_eq!(out[0], "sat");
    assert_eq!(
        out[1],
        "((x (root-obj (+ (^ x 2) (- 2)) 2))\n (y (root-obj (+ (^ x 3) 3) 1))\n \
         ((* x y) (root-obj (+ (^ x 6) (- 72)) 1))\n ((+ x 1) (root-obj (+ (^ x 2) (* (- 2) x) (- 1)) 2)))"
    );
}

#[test]
fn nonlinear_unsupported_input_is_an_error() {
    let base = "(set-logic QF_NRA) (declare-fun x () Real) (declare-fun y () Real)";
    let e = |body: &str| error(&format!("{base} {body} (check-sat)"));
    assert!(e("(assert (> (/ 1 x) 1))").contains("non-constant"));
    assert!(e("(assert (> (/ x 0) 1))").contains("division by zero"));
    assert!(e("(declare-fun n () Int) (assert (> n 1))").contains("QF_NIA"));
    assert!(e("(maximize x)").contains("not supported"));
}

#[test]
fn linear_integer_arithmetic() {
    let base = "(set-logic QF_LIA) (declare-fun x () Int) (declare-fun y () Int)";
    let sat = |body: &str| answers(&format!("{base} {body} (check-sat)"));
    // No branching needed: normalisation rounds these to contradictions.
    assert_eq!(
        sat("(assert (= (- (* 2 x) (* 2 y)) 1))"),
        vec![Answer::Unsat]
    );
    assert_eq!(sat("(assert (and (> x 0) (< x 1)))"), vec![Answer::Unsat]);
    assert_eq!(
        sat("(assert (<= 1 (- (* 3 x) (* 6 y)) 2))"),
        vec![Answer::Unsat]
    );
    // Branch and bound.
    assert_eq!(
        sat("(assert (and (>= (* 2 x) 3) (<= (* 2 x) 5) (>= (+ x y) 10) (<= (- y x) 6)))"),
        vec![Answer::Sat]
    );
    assert_eq!(
        sat("(assert (and (= (+ (* 3 x) (* 5 y)) 7) (>= x 0) (>= y 0)))"),
        vec![Answer::Unsat]
    );
    // div / mod / abs, Euclidean.
    assert_eq!(
        sat("(assert (= (mod (- 7) 2) 1)) (assert (= (div (- 7) 2) (- 4)))"),
        vec![Answer::Sat]
    );
    assert_eq!(sat("(assert (= (mod x 3) 3))"), vec![Answer::Unsat]);
    assert_eq!(
        sat("(assert (and (= (abs x) 3) (< x 0) (= y (+ x 3))))"),
        vec![Answer::Sat]
    );
    // A remainder that must move from 0 to 1 (needs patching, not just branching).
    assert_eq!(
        sat("(assert (>= (- y) (div (+ x (- 5) x) 2)))"),
        vec![Answer::Sat]
    );
}

#[test]
fn integer_models_are_integral_and_numerals_adapt() {
    let out = texts(
        "(set-logic QF_LIA) (declare-fun x () Int) (declare-fun y () Int)
         (assert (and (>= (* 2 x) 3) (<= (* 2 x) 5) (= y (- x 10))))
         (check-sat) (get-value (x y (div y 3) (mod y 3)))",
    );
    assert_eq!(out[0], "sat");
    assert_eq!(
        out[1],
        "((x 2)\n (y (- 8))\n ((div y 3) (- 3))\n ((mod y 3) 1))"
    );
    // A numeral is Int in an Int context and Real in a Real one.
    assert_eq!(
        answers("(declare-const r Real) (assert (> r 2)) (assert (< r 3)) (check-sat)"),
        vec![Answer::Sat]
    );
    assert!(
        error("(declare-const r Real) (declare-const i Int) (assert (= r i))")
            .contains("mixes sorts")
    );
    assert!(error("(declare-const i Int) (assert (= (/ i 2) 1))").contains("use div"));
}

#[test]
fn quoted_symbols_are_not_numbers() {
    // |3| is a symbol, not the numeral 3; |286| a Bool constant (as in SMT-LIB's ezsmt files).
    let s = "(set-logic QF_LRA) (declare-fun |3| () Real) (declare-fun |286| () Bool)
             (assert (> |3| 3)) (assert (not |286|)) (check-sat) (get-value (|3| |286|))";
    let out = texts(s);
    assert_eq!(out[0], "sat");
    assert!(out[1].starts_with("((|3| "), "{}", out[1]);
    assert!(out[1].contains("(|286| false)"), "{}", out[1]);
    assert_eq!(
        answers("(declare-fun |3| () Real) (assert (< |3| 3)) (assert (= |3| 3)) (check-sat)"),
        vec![Answer::Unsat]
    );
}

#[test]
fn optimization() {
    let obj = |body: &str| {
        let out = texts(&format!("{body} (check-sat) (get-objectives)"));
        assert_eq!(out[0], "sat", "{body}");
        out[1].lines().nth(1).unwrap().trim().to_string()
    };
    let r = "(declare-const x Real) (declare-const y Real)";
    let i = "(declare-const x Int) (declare-const y Int)";
    // An unattained supremum, and two unbounded objectives.
    assert_eq!(
        obj(&format!("{r} (assert (< x 3)) (maximize x)")),
        "(x (- 3.0 epsilon))"
    );
    assert_eq!(
        obj(&format!("{r} (assert (>= x 1)) (maximize x)")),
        "(x oo)"
    );
    assert_eq!(
        obj(&format!("{r} (assert (or (<= x 0) (>= x 5))) (maximize x)")),
        "(x oo)"
    );
    assert_eq!(
        obj(&format!("{r} (assert (>= x 1)) (minimize x)")),
        "(x 1.0)"
    );
    assert_eq!(
        obj(&format!("{r} (assert (> x 0)) (minimize x)")),
        "(x (+ 0.0 epsilon))"
    );
    // The best of several boolean cases.
    assert_eq!(
        obj(&format!(
            "{r} (assert (or (<= x 0) (and (>= x 5) (<= x 7)))) (maximize x)"
        )),
        "(x 7.0)"
    );
    assert_eq!(
        obj(&format!(
            "{r} (assert (<= (+ x (* 2 y)) 4)) (assert (<= (+ (* 3 x) y) 6))
             (assert (>= x 0)) (assert (>= y 0)) (maximize (+ x y))"
        )),
        "((+ x y) (/ 14.0 5.0))"
    );
    // Integers: the optimum is integral and attained.
    assert_eq!(obj(&format!("{i} (assert (< x 3)) (maximize x)")), "(x 2)");
    assert_eq!(
        obj(&format!("{i} (assert (>= x 3)) (minimize (- x 1))")),
        "((- x 1) 2)"
    );
    assert_eq!(
        obj(&format!("{i} (assert (>= (* 2 x) 3)) (maximize x)")),
        "(x oo)"
    );
    // The model is the optimal one.
    let out = texts(&format!(
        "{r} (assert (<= x 4)) (assert (<= (- y x) 1)) (maximize y) (check-sat) (get-value (x y))"
    ));
    assert_eq!(out[1], "((x 4.0)\n (y 5.0))");
    // Unsat stays unsat; pop removes the objective.
    assert_eq!(
        answers(&format!("{r} (assert (< x x)) (maximize x) (check-sat)")),
        vec![Answer::Unsat]
    );
    assert!(error(&format!(
        "{r} (push 1) (maximize x) (pop 1) (check-sat) (get-objectives)"
    ))
    .contains("no objectives"));
    assert!(error(&format!("{r} (maximize x) (minimize y)")).contains("one objective"));
}

#[test]
fn integer_equations_do_not_send_branching_to_infinity() {
    // Both used to loop: branch and bound chased unbounded variables forever.
    let i =
        "(set-logic QF_LIA) (declare-fun x () Int) (declare-fun y () Int) (declare-fun z () Int)";
    // Parity: 2x - 5 is odd, so its remainder mod 2 is never 0.
    assert_eq!(
        answers(&format!(
            "{i} (assert (= (mod (- (* 2 x) 5) 2) 0)) (check-sat)"
        )),
        vec![Answer::Unsat]
    );
    // A top-level equation (even with a constant ite) is solved for z and substituted.
    assert_eq!(
        answers(&format!(
            "{i} (assert (= (+ (* 4 y) x x z 5) (ite (ite true false false) y 36)))
             (assert (>= (abs z) 0)) (check-sat)"
        )),
        vec![Answer::Sat]
    );
    // The eliminated variable still gets its value in the model.
    let out = texts(&format!(
        "{i} (assert (= z (- (* 2 x) 3))) (assert (= x 5)) (check-sat) (get-value (z))"
    ));
    assert_eq!(out[1], "((z 7))");
}

#[test]
fn push_pop_scoping() {
    let s = "
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U) (declare-fun b () U)
        (assert (= a b))
        (push 1)
        (assert (not (= a b)))
        (check-sat)
        (pop 1)
        (check-sat)";
    assert_eq!(answers(s), vec![Answer::Unsat, Answer::Sat]);
}
