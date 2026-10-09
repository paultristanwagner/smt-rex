use super::*;
use crate::formula::{self, Atoms, Formula, Rel};
use crate::style::natural_key;
use smtrex_core::Rational;

fn run(lines: &[&str]) -> String {
    let mut s = Session::new(Style::plain(), Arc::new(AtomicBool::new(false)));
    let mut out = Vec::new();
    for l in lines {
        s.run_line(l, &mut out).unwrap();
    }
    // Timings vary; blank them out.
    let text = String::from_utf8(out).unwrap();
    let mut clean = String::new();
    let is_time = |s: &str| {
        let num = s
            .trim_end_matches(" µs")
            .trim_end_matches(" ms")
            .trim_end_matches(" s");
        num != s && !num.is_empty() && num.chars().all(|c| c.is_ascii_digit() || c == '.')
    };
    for line in text.lines() {
        let line = match (line.find("  ("), line.find(')')) {
            (Some(a), Some(b)) if b > a && is_time(&line[a + 3..b]) => {
                format!("{}{}", &line[..a], &line[b + 1..])
            }
            _ => line.to_string(),
        };
        clean.push_str(line.trim_end());
        clean.push('\n');
    }
    clean
}

#[test]
fn sat_shows_a_model() {
    assert_eq!(
        run(&["sat (a | b) & (~a | c) & ~c"]),
        "sat\n  a=0  b=1  c=0\n"
    );
    assert_eq!(run(&["sat a & ~a"]), "unsat\n");
    assert_eq!(run(&["sat x10 & x2 & ~x1"]), "sat\n  x1=0  x2=1  x10=1\n");
    assert_eq!(run(&["sat true"]), "sat\n  (no variables)\n");
    // Reserved SMT-LIB words are fine as variable names.
    assert_eq!(run(&["sat and & ~not"]), "sat\n  and=1  not=0\n");
}

#[test]
fn syntax_errors_have_a_caret() {
    assert_eq!(
        run(&["sat (a | b"]),
        "syntax error: expected ')', got the end of the input\n  (a | b\n        ^\n"
    );
}

#[test]
fn allsat_counts_models() {
    let out = run(&["allsat a | b"]);
    assert!(out.ends_with("3 models\n"), "{out}");
    assert_eq!(out.lines().count(), 4);
    let out = run(&["allsat -n 2 a | b | c"]);
    assert!(out.contains("2 models shown"), "{out}");
    assert_eq!(run(&["allsat a & ~a"]), "unsat: no models\n");
    assert_eq!(
        run(&["allsat -n x a"]),
        "usage: -n needs a positive number\n"
    );
}

#[test]
fn smt_groups_terms_by_value() {
    let out = run(&["smt QF_EQUF (x1 = x2) & (x2 = x3) & (x4 = x5) & (f(x1) != f(x5))"]);
    assert_eq!(
        out,
        "sat\n  e0  x1 = x2 = x3\n  e1  x4 = x5\n  e2  f(x1)\n  e3  f(x5)\n"
    );
    assert_eq!(run(&["smt QF_EQ (a=b) & (b=c) & (a!=c)"]), "unsat\n");
    assert_eq!(
        run(&["smt QF_EQUF (f(f(y)) != x) & (x = f(y)) & (y = u) & (x = y)"]),
        "unsat\n"
    );
    assert_eq!(
        run(&["smt QF_UF (f(a) = b) & (f(b) != b) & (a = b)"]),
        "unsat\n"
    );
    assert!(run(&["smt QF_BV a=b"]).contains("QF_BV has no short syntax"));
    assert!(run(&["smt QF_FOO a=b"]).contains("unknown logic"));
    assert!(run(&["smt QF_EQUF f(a) = f(a, b)"]).contains("used with 1 and with 2"));
}

/// `x + 2y <= 3` etc. evaluated exactly under `model`.
fn holds(f: &Formula, model: &[(String, Rational)]) -> bool {
    let value = |l: &formula::Linear| {
        l.coeffs.iter().fold(l.constant.clone(), |acc, (x, c)| {
            let (_, v) = model
                .iter()
                .find(|(y, _)| y == x)
                .unwrap_or_else(|| panic!("the model has no value for {x}"));
            &acc + &(c * v)
        })
    };
    match f {
        Formula::Const(b) => *b,
        Formula::Cmp { lhs, rel, rhs } => {
            let (a, b) = (value(lhs), value(rhs));
            match rel {
                Rel::Le => a <= b,
                Rel::Lt => a < b,
                Rel::Ge => a >= b,
                Rel::Gt => a > b,
                Rel::Eq => a == b,
                Rel::Ne => a != b,
            }
        }
        Formula::Not(x) => !holds(x, model),
        Formula::And(xs) => xs.iter().all(|x| holds(x, model)),
        Formula::Or(xs) => xs.iter().any(|x| holds(x, model)),
        Formula::Implies(x, y) => !holds(x, model) || holds(y, model),
        Formula::Iff(x, y) => holds(x, model) == holds(y, model),
        // An objective constrains nothing; the optimum is checked separately.
        Formula::Objective { .. } => true,
        Formula::Var(_) | Formula::Eq { .. } | Formula::PolyCmp { .. } => {
            unreachable!("not a QF_LRA formula")
        }
    }
}

/// `x=7  y=-9/4` back into exact values.
fn parse_model(lines: &str) -> Vec<(String, Rational)> {
    lines
        .split_whitespace()
        .map(|item| {
            let (x, v) = item.split_once('=').expect("name=value");
            let (neg, v) = v.strip_prefix('-').map_or((false, v), |v| (true, v));
            let (n, d) = v.split_once('/').unwrap_or((v, "1"));
            let q = &Rational::parse_decimal(n).unwrap() / &Rational::parse_decimal(d).unwrap();
            (x.to_string(), if neg { -q } else { q })
        })
        .collect()
}

/// Run `command`, expect `sat`, and check the shown model against `f` exactly: every
/// variable has a value and `f` holds. Returns the model.
fn checked_model(command: &str, f: &Formula) -> Vec<(String, Rational)> {
    let out = run(&[command]);
    let lines = out
        .strip_prefix("sat\n")
        .unwrap_or_else(|| panic!("{command}: {out}"));
    let model = parse_model(lines);
    let names: Vec<&String> = model.iter().map(|(x, _)| x).collect();
    let mut want = f.numeric_vars();
    want.sort_by_key(|v| natural_key(v));
    assert_eq!(names, want.iter().collect::<Vec<_>>(), "{command}: {out}");
    assert!(holds(f, &model), "{command}: the model {out} is wrong");
    model
}

fn lra_model(formula: &str) -> Vec<(String, Rational)> {
    let f = formula::parse(formula, Atoms::Arith).unwrap();
    checked_model(&format!("smt QF_LRA {formula}"), &f)
}

fn value(model: &[(String, Rational)], x: &str) -> Rational {
    model.iter().find(|(y, _)| y == x).unwrap().1.clone()
}

#[test]
fn lra_examples() {
    let m = lra_model("(x<=-3 | x>=3) & (y=5) & (x+y>=12)");
    assert_eq!(value(&m, "y"), Rational::from_int(5));
    assert_eq!(
        run(&["smt QF_LRA (x<=-3 | x>=3) & (y=5) & (x+y>=12)"]),
        "sat\n  x=7  y=5\n"
    );
    assert_eq!(
        run(&["smt QF_LRA (x<=0 | x>=5) & (x+y=5/2) & (y=1)"]),
        "unsat\n"
    );
    lra_model("(y+0.8x<=4) & (y-0.25x>=0)");
    assert_eq!(
        run(&["smt qf_lra (y-x<=0) & (y+x<=1) & (y>=0.6)"]),
        "unsat\n"
    );
}

#[test]
fn lra_models_are_exact() {
    assert_eq!(
        run(&["smt QF_LRA 0.8x + 1/2y = 1 & x - y = 1/4"]),
        "sat\n  x=45/52  y=8/13\n"
    );
    assert_eq!(run(&["smt QF_LRA 2x = -1"]), "sat\n  x=-1/2\n");
    assert_eq!(
        run(&["smt QF_LRA x10 = 1 & x2 = 2 & x1 = 3"]),
        "sat\n  x1=3  x2=2  x10=1\n"
    );
    // Reserved SMT-LIB words are fine as variable names.
    assert_eq!(
        run(&["smt QF_LRA and + Real = 3 & and = 1"]),
        "sat\n  Real=2  and=1\n"
    );
    assert_eq!(run(&["smt QF_LRA true"]), "sat\n  (no variables)\n");
    assert_eq!(run(&["smt QF_LRA 1 > 2"]), "unsat\n");
    lra_model("x + 2y - 1/2z + 0.8x <= 1 & z > 4y & x - x = 0");
}

#[test]
fn lra_strict_inequalities_and_disequalities() {
    let m = lra_model("(x < 3) & (x > 2)");
    let x = value(&m, "x");
    assert!(
        Rational::from_int(2) < x && x < Rational::from_int(3),
        "{x}"
    );
    assert_eq!(run(&["smt QF_LRA (x < 3) & (x >= 3)"]), "unsat\n");
    assert_eq!(run(&["smt QF_LRA (2x < 2) & (x >= 1)"]), "unsat\n");
    lra_model("(x < 3) & (x > 2) & (x != 5/2)");
    lra_model("x != 2");
    lra_model("~(x = 2) & x >= 2 & x <= 3 & x != 3");
    assert_eq!(run(&["smt QF_LRA x >= 2 & x <= 2 & x != 2"]), "unsat\n");
    assert_eq!(
        run(&["smt QF_LRA x - y < 0 & y - z < 0 & z <= x"]),
        "unsat\n"
    );
    lra_model("x - y < 0 & y - z < 0 & z <= x + 1/1000");
    lra_model("(x > y -> y > 1) & (x = y <-> x = 7) & x >= 3");
}

#[test]
fn lra_optimization() {
    assert_eq!(
        run(&["smt QF_LRA (x<=-3 | x>=3) & (y=5) & (x+y>=12) & (min(x))"]),
        "sat\n  min x = 7\n  x=7  y=5\n"
    );
    // Unattained and unbounded optima.
    assert_eq!(
        run(&["smt QF_LRA (x < 3) & (max(x))"])
            .lines()
            .nth(1)
            .unwrap(),
        "  max x: no maximum (supremum 3, never reached)"
    );
    assert!(run(&["smt QF_LRA (x >= 1) & (max(x))"]).contains("max x: unbounded above"));
    assert!(run(&["smt QF_LRA (x <= 0 | x >= 5) & (max(x))"]).contains("unbounded above"));
    assert!(run(&["smt QF_LRA (x <= 3) & (max(2x - 1))"]).contains("max 2x - 1 = 5"));
}

#[test]
fn lra_errors() {
    assert!(run(&["smt QF_LRA (max(x) | x <= 1)"]).contains("top level"));
    assert!(run(&["smt QF_LRA (max(x)) & (min(x)) & x <= 1"]).contains("only one"));
    assert_eq!(
        run(&["smt QF_LRA x + <= 3"]),
        "syntax error: expected a number or a variable, got '<='\n  x + <= 3\n      ^\n"
    );
    assert!(run(&["smt QF_LRA x*y <= 3"]).starts_with("syntax error:"));
    assert_eq!(run(&["smt QF_LRA"]), "usage: smt QF_LRA <formula>\n");
    assert!(run(&["smt QF_FOO x <= 3"]).contains("QF_UF, QF_LRA, QF_LIA, QF_NRA"));
}

/// Random QF_LRA formulas: every `sat` model shown must satisfy the formula exactly.
#[test]
fn lra_random_models_check_out() {
    let mut seed = 0x2545F4914F6CDD1Du64;
    let mut rnd = move |n: u64| {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed % n
    };
    let mut sat = 0;
    for _ in 0..150 {
        let mut atoms = Vec::new();
        for _ in 0..1 + rnd(5) {
            let mut lhs = String::new();
            for x in ["x", "y", "z"] {
                if rnd(3) > 0 {
                    let c = rnd(7) as i64 - 3;
                    let d = 1 + rnd(3);
                    lhs.push_str(&format!(" + {c}/{d}{x}"));
                }
            }
            if lhs.is_empty() {
                lhs.push('0');
            }
            let rel = ["<=", "<", ">=", ">", "=", "!="][rnd(6) as usize];
            let rhs = rnd(9) as i64 - 4;
            let neg = if rnd(4) == 0 { "~" } else { "" };
            atoms.push(format!("{neg}({lhs} {rel} {rhs})"));
        }
        let mut text = atoms[0].clone();
        for a in &atoms[1..] {
            text = format!("({text}) {} {a}", ["&", "|", "->"][rnd(3) as usize]);
        }
        let f = formula::parse(&text, Atoms::Arith).unwrap_or_else(|e| panic!("{text}: {e:?}"));
        let command = format!("smt QF_LRA {text}");
        let out = run(&[&command]);
        if out.starts_with("sat\n") {
            sat += 1;
            checked_model(&command, &f);
        } else {
            assert_eq!(out, "unsat\n", "{command}");
        }
    }
    assert!(sat >= 50, "only {sat} random formulas were sat");
}

fn simplex_model(constraints: &str) -> Vec<(String, Rational)> {
    let f = Formula::And(formula::parse_constraints(constraints).unwrap());
    checked_model(&format!("simplex {constraints}"), &f)
}

#[test]
fn simplex_examples() {
    let m = simplex_model("a+3b+5c=30 a>=5 a<=10 b>=2 c>=1");
    assert_eq!(m.len(), 3);
    assert_eq!(run(&["simplex x+y=3 y=1 x<=1"]), "unsat\n");
    simplex_model("x+y>=10 x-y<=5 1/2x-y<=0");
    // The objective examples, without their objectives.
    simplex_model("3x+2y+z<=10 2x+5y+3z<=15 x>=0 y>=0 z>=0");
    // Feasible, though unbounded under max(x).
    let m = simplex_model("x>=-1 x>=-1/2");
    assert!(value(&m, "x") >= Rational::new(-1, 2));
}

#[test]
fn simplex_constraints() {
    // Spaces inside constraints; a sign opening a word starts the next one.
    let m = simplex_model("x + y >= 10 x>=1 -y<=5 x <= 2");
    assert!(value(&m, "y") >= Rational::from_int(8));
    let m = simplex_model("x<3 x>2");
    let x = value(&m, "x");
    assert!(
        Rational::from_int(2) < x && x < Rational::from_int(3),
        "{x}"
    );
    simplex_model("x>=2 x<=3 x!=2 x!=3");
    assert_eq!(run(&["simplex x>=2 x<=2 x!=2"]), "unsat\n");
    assert_eq!(run(&["simplex x<3 x>=3"]), "unsat\n");
    assert_eq!(
        run(&["simplex 0.8x+1/2y=1 x-y=1/4"]),
        "sat\n  x=45/52  y=8/13\n"
    );
}

#[test]
fn simplex_errors() {
    let out = run(&["simplex max(x+y) x+2y<=4 3x+y<=6 x>=0 y>=0"]);
    assert_eq!(out, "sat\n  max x + y = 14/5\n  x=8/5  y=6/5\n");
    let out = run(&["simplex min(x) x+y>=10 x-y<=5 1/2x-y<=0"]);
    assert!(out.starts_with("sat\n  min x: unbounded below"), "{out}");
    assert!(run(&["simplex max(x) x>=-1 x>=-1/2"]).contains("unbounded above"));
    assert_eq!(
        run(&["simplex x>=1 & y<=2"]),
        "syntax error: expected a number or a variable, got '&'\n  x>=1 & y<=2\n       ^\n"
    );
    assert_eq!(run(&["simplex"]), "usage: simplex <constraint> ...\n");
    assert!(run(&["help simplex"]).contains("simplex x+y>=10 x-y<=5 1/2x-y<=0"));
    assert!(run(&["help"]).contains("simplex <constraint> ..."));
}

#[test]
fn tseitin_output_is_valid_sat_input() {
    let out = run(&["tseitin a -> b"]);
    let cnf = out.lines().next().unwrap();
    assert_eq!(cnf, "(~h0 | ~a | b) & (a | h0) & (~b | h0) & (h0)");
    assert!(out.contains("4 clauses, 1 helper variable"));
    assert!(run(&[&format!("sat {cnf}")]).starts_with("sat"));
}

#[test]
fn smtlib_lines_keep_state() {
    let out = run(&[
        "(declare-const p Bool)",
        "(assert p)",
        "(check-sat)",
        "(get-value (p))",
        "(assert (not p))",
        "(check-sat)",
        "(get-model)",
    ]);
    assert!(
        out.starts_with("sat\n((p true))\nunsat\nerror: no model available"),
        "{out}"
    );
}

#[test]
fn smtlib_inline_and_status_mismatch() {
    assert_eq!(
        run(&["smtlib (declare-const p Bool)(assert (and p (not p)))(check-sat)"]),
        "unsat\n"
    );
    let out = run(&[
        "smtlib (set-info :status sat)(declare-const p Bool)(assert (and p (not p)))(check-sat)",
    ]);
    assert!(out.contains("but the file's :status says sat"), "{out}");
    assert!(run(&["smtlib /no/such/file.smt2"]).starts_with("error: cannot read"));
}

#[test]
fn unknown_commands_and_usage() {
    assert_eq!(
        run(&["frob"]),
        "error: unknown command 'frob'. Type help for the list.\n"
    );
    assert_eq!(run(&["sat"]), "usage: sat <formula>\n");
    assert!(run(&["help"]).contains("allsat [-n <limit>] <formula>"));
    assert!(run(&["help smt"]).contains("smt QF_UF (f(f(y)) != x)"));
    assert!(run(&["? tseytin"]).starts_with("tseitin <formula>"));
}

#[test]
fn exit_ends_the_session() {
    let mut s = Session::new(Style::plain(), Arc::new(AtomicBool::new(false)));
    let mut out = Vec::new();
    assert_eq!(s.run_line("exit", &mut out).unwrap(), Flow::Exit);
    assert_eq!(s.run_line("(exit)", &mut out).unwrap(), Flow::Exit);
}

#[test]
fn integer_arithmetic() {
    assert_eq!(
        run(&["smt QF_LIA (y + 0.8x <= 4) & (y - x/4 >= 0) & (max(x))"]),
        "sat\n  max x = 3\n  x=3  y=1\n"
    );
    // Satisfiable over the reals, not over the integers.
    assert_eq!(run(&["smt QF_LIA (2x = 1)"]), "unsat\n");
    assert_eq!(
        run(&["smt QF_LIA (y - x <= 0) & (y + x <= 1) & (y >= 0.1)"]),
        "unsat\n"
    );
    // The objective is scaled to integer coefficients; the optimum is shown unscaled.
    assert_eq!(
        run(&["smt QF_LIA (x <= 7/2) & (max(x/2))"]),
        "sat\n  max x/2 = 3/2\n  x=3\n"
    );
}

#[test]
fn polynomial_arithmetic() {
    assert_eq!(
        run(&["smt QF_NRA (x^2 = 2) & (x > 0)"]),
        "sat\n  x≈1.414214 (root 2 of x^2 - 2)\n"
    );
    assert_eq!(
        run(&["smt QF_NRA (x*y > 0) & (y*z > 0) & (x*z > 0) & (x + y + z = 0)"]),
        "unsat\n"
    );
    assert_eq!(run(&["smt QF_NRA (x^2 + y^2 < 0)"]), "unsat\n");
    let out = run(&["smt QF_NRA (x*y = 6) & (x + y = 5) & (x < y)"]);
    assert_eq!(out, "sat\n  x=2  y=3\n");
    assert!(run(&["smt QF_NRA (x^2 <= 1) & (max(x))"]).contains("need QF_LRA or QF_LIA"));
    assert!(run(&["smt QF_LRA x*y <= 1"]).contains("QF_NRA allows x*y"));
}

#[test]
fn help_after_a_command() {
    let help = run(&["help smt"]);
    assert!(help.starts_with("smt <logic> <formula>"), "{help}");
    for line in ["smt help", "smt --help", "smt -h"] {
        assert_eq!(run(&[line]), help, "{line}");
    }
    assert_eq!(run(&["sat --help"]), run(&["help sat"]));
}
