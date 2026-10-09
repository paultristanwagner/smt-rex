use super::{Atoms, Formula, Linear, Rel, Term};
use smtrex_core::Rational;

/// A syntax error at byte offset `at` of the input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
    pub at: usize,
}

/// Parse `input` as a formula whose atoms are of kind `atoms`.
pub fn parse(input: &str, atoms: Atoms) -> Result<Formula, ParseError> {
    let mut p = Parser::new(input, atoms, "a formula")?;
    let f = p.formula()?;
    p.finish()?;
    Ok(f)
}

/// Parse the `simplex` input: linear constraints side by side, `x+y>=10 x-y<=5`. Spaces
/// inside a constraint are fine (`x + y >= 10`); a sign that opens a word (`x>=1 -y<=5`)
/// starts the next constraint.
pub fn parse_constraints(input: &str) -> Result<Vec<Formula>, ParseError> {
    let mut p = Parser::new(input, Atoms::Arith, "a linear constraint")?;
    p.list = true;
    let mut out = Vec::new();
    while p.pos < p.toks.len() {
        out.push(p.objective_or_comparison()?);
    }
    Ok(out)
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Tok {
    Ident(String),
    LParen,
    RParen,
    Comma,
    Not,
    And,
    Or,
    Implies,
    Iff,
    Eq,
    Neq,
    // Arithmetic only (QF_LRA). Numbers keep their source text for error messages.
    Num(Rational, String),
    /// A number directly followed by a variable, as in `2x`: implicit multiplication.
    Coef(Rational, String),
    Plus,
    Minus,
    Star,
    Le,
    Lt,
    Ge,
    Gt,
}

impl Tok {
    fn describe(&self) -> String {
        match self {
            Tok::Ident(s) => format!("'{s}'"),
            Tok::LParen => "'('".into(),
            Tok::RParen => "')'".into(),
            Tok::Comma => "','".into(),
            Tok::Not => "'~'".into(),
            Tok::And => "'&'".into(),
            Tok::Or => "'|'".into(),
            Tok::Implies => "'->'".into(),
            Tok::Iff => "'<->'".into(),
            Tok::Eq => "'='".into(),
            Tok::Neq => "'!='".into(),
            Tok::Num(_, s) | Tok::Coef(_, s) => format!("'{s}'"),
            Tok::Plus => "'+'".into(),
            Tok::Minus => "'-'".into(),
            Tok::Star => "'*'".into(),
            Tok::Le => "'<='".into(),
            Tok::Lt => "'<'".into(),
            Tok::Ge => "'>='".into(),
            Tok::Gt => "'>'".into(),
        }
    }
}

fn is_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '\'' || c == '.'
}

/// In arithmetic, identifiers start with a letter or `_` and cannot contain `.`, so that `2x`
/// and `0.8x` split into a number and a variable.
fn is_arith_ident_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '\''
}

/// The number at the start of `rest` (`42`, `0.8`, `.5`, `5.`, `1/2`) and its length in bytes,
/// or `None` if `rest` does not start with one.
fn lex_number(rest: &str) -> Option<Result<(Rational, usize), String>> {
    let b = rest.as_bytes();
    let digits = |from: usize| from + b[from..].iter().take_while(|c| c.is_ascii_digit()).count();
    let int_end = digits(0);
    let mut end = int_end;
    if b.get(end) == Some(&b'.') {
        end = digits(end + 1);
    }
    if end == 0 || &rest[..end] == "." {
        return None;
    }
    let (int, frac) = rest[..end].split_once('.').unwrap_or((&rest[..end], ""));
    let int = if int.is_empty() { "0" } else { int };
    let text = if frac.is_empty() {
        int.to_string()
    } else {
        format!("{int}.{frac}")
    };
    let q = Rational::parse_decimal(&text).expect("digits are a decimal");
    // A fraction: integer '/' integer, with no spaces.
    if end == int_end && b.get(end) == Some(&b'/') && b.get(end + 1).is_some_and(u8::is_ascii_digit)
    {
        let den_end = digits(end + 1);
        let den = Rational::parse_decimal(&rest[end + 1..den_end]).expect("digits");
        if den.is_zero() {
            return Some(Err(format!("division by zero in '{}'", &rest[..den_end])));
        }
        return Some(Ok((&q / &den, den_end)));
    }
    Some(Ok((q, end)))
}

fn lex(input: &str, atoms: Atoms) -> Result<Vec<(Tok, usize)>, ParseError> {
    let arith = atoms == Atoms::Arith;
    let mut out = Vec::new();
    let mut it = input.char_indices().peekable();
    while let Some(&(i, c)) = it.peek() {
        let rest = &input[i..];
        let number = if arith { lex_number(rest) } else { None };
        let (tok, len) = if c.is_whitespace() {
            it.next();
            continue;
        } else if let Some(n) = number {
            let (q, len) = n.map_err(|message| ParseError { message, at: i })?;
            let text = rest[..len].to_string();
            let touching = rest[len..]
                .chars()
                .next()
                .is_some_and(|ch| ch.is_ascii_alphabetic() || ch == '_');
            if touching {
                (Tok::Coef(q, text), len)
            } else {
                (Tok::Num(q, text), len)
            }
        } else if arith && is_arith_ident_char(c) {
            let end = rest
                .find(|ch: char| !is_arith_ident_char(ch))
                .unwrap_or(rest.len());
            (Tok::Ident(rest[..end].to_string()), end)
        } else if arith && c == '/' {
            return Err(ParseError {
                message: "'/' only writes a fraction of two integers, as in 1/2x".into(),
                at: i,
            });
        } else if !arith && is_ident_char(c) {
            let end = rest
                .find(|ch: char| !is_ident_char(ch))
                .unwrap_or(rest.len());
            (Tok::Ident(rest[..end].to_string()), end)
        } else if let Some((t, l)) = [
            // (spelling, token, arithmetic only); longer spellings first.
            ("<->", Tok::Iff, false),
            ("<=>", Tok::Iff, false),
            ("->", Tok::Implies, false),
            ("=>", Tok::Implies, false),
            ("!=", Tok::Neq, false),
            ("==", Tok::Eq, false),
            ("&&", Tok::And, false),
            ("||", Tok::Or, false),
            ("<=", Tok::Le, true),
            (">=", Tok::Ge, true),
            ("(", Tok::LParen, false),
            (")", Tok::RParen, false),
            (",", Tok::Comma, false),
            ("~", Tok::Not, false),
            ("!", Tok::Not, false),
            ("&", Tok::And, false),
            ("|", Tok::Or, false),
            ("=", Tok::Eq, false),
            ("<", Tok::Lt, true),
            (">", Tok::Gt, true),
            ("+", Tok::Plus, true),
            ("-", Tok::Minus, true),
            ("*", Tok::Star, true),
        ]
        .into_iter()
        .find(|(s, _, arith_only)| (arith || !arith_only) && rest.starts_with(s))
        .map(|(s, t, _)| (t, s.len()))
        {
            (t, l)
        } else {
            return Err(ParseError {
                message: format!("unexpected character '{c}'"),
                at: i,
            });
        };
        out.push((tok, i));
        while it.peek().is_some_and(|&(j, _)| j < i + len) {
            it.next();
        }
    }
    Ok(out)
}

struct Parser {
    toks: Vec<(Tok, usize)>,
    pos: usize,
    end: usize,
    atoms: Atoms,
    /// For `simplex` lists: whether token `i` opens a word, i.e. has a space before it and none
    /// after it. A sign that opens a word (`10 -y`, not `10 - y`) starts the next constraint.
    opens_word: Vec<bool>,
    list: bool,
}

impl Parser {
    fn new(input: &str, atoms: Atoms, what: &str) -> Result<Parser, ParseError> {
        let toks = lex(input, atoms)?;
        if toks.is_empty() {
            return Err(ParseError {
                message: format!("expected {what}"),
                at: input.len(),
            });
        }
        let opens_word = toks
            .iter()
            .map(|(_, at)| {
                let before = input[..*at].chars().next_back();
                let after = input[at + 1..].chars().next();
                before.is_none_or(char::is_whitespace) && after.is_some_and(|c| !c.is_whitespace())
            })
            .collect();
        Ok(Parser {
            toks,
            pos: 0,
            end: input.trim_end().len(),
            atoms,
            opens_word,
            list: false,
        })
    }

    /// Fail unless every token was consumed.
    fn finish(&self) -> Result<(), ParseError> {
        if let Some((t, at)) = self.toks.get(self.pos) {
            let hint = if *t == Tok::RParen {
                "unmatched ')'".to_string()
            } else {
                format!("expected an operator, got {}", t.describe())
            };
            return Err(ParseError {
                message: hint,
                at: *at,
            });
        }
        Ok(())
    }

    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos).map(|(t, _)| t)
    }

    fn here(&self) -> usize {
        self.toks.get(self.pos).map_or(self.end, |(_, at)| *at)
    }

    fn eat(&mut self, t: &Tok) -> bool {
        if self.peek() == Some(t) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn error<T>(&self, expected: &str) -> Result<T, ParseError> {
        let got = match self.peek() {
            Some(t) => format!(", got {}", t.describe()),
            None => ", got the end of the input".to_string(),
        };
        Err(ParseError {
            message: format!("expected {expected}{got}"),
            at: self.here(),
        })
    }

    fn expect(&mut self, t: &Tok) -> Result<(), ParseError> {
        if self.eat(t) {
            Ok(())
        } else {
            self.error(&t.describe())
        }
    }

    fn formula(&mut self) -> Result<Formula, ParseError> {
        let lhs = self.implication()?;
        if self.eat(&Tok::Iff) {
            let rhs = self.formula()?;
            return Ok(Formula::Iff(Box::new(lhs), Box::new(rhs)));
        }
        Ok(lhs)
    }

    fn implication(&mut self) -> Result<Formula, ParseError> {
        let lhs = self.disjunction()?;
        if self.eat(&Tok::Implies) {
            let rhs = self.implication()?;
            return Ok(Formula::Implies(Box::new(lhs), Box::new(rhs)));
        }
        Ok(lhs)
    }

    fn disjunction(&mut self) -> Result<Formula, ParseError> {
        let mut parts = vec![self.conjunction()?];
        while self.eat(&Tok::Or) {
            parts.push(self.conjunction()?);
        }
        Ok(if parts.len() == 1 {
            parts.pop().unwrap()
        } else {
            Formula::Or(parts)
        })
    }

    fn conjunction(&mut self) -> Result<Formula, ParseError> {
        let mut parts = vec![self.negation()?];
        while self.eat(&Tok::And) {
            parts.push(self.negation()?);
        }
        Ok(if parts.len() == 1 {
            parts.pop().unwrap()
        } else {
            Formula::And(parts)
        })
    }

    fn negation(&mut self) -> Result<Formula, ParseError> {
        if self.eat(&Tok::Not) {
            return Ok(Formula::Not(Box::new(self.negation()?)));
        }
        self.primary()
    }

    fn primary(&mut self) -> Result<Formula, ParseError> {
        if self.eat(&Tok::LParen) {
            let f = self.formula()?;
            self.expect(&Tok::RParen)?;
            return Ok(f);
        }
        match self.atoms {
            Atoms::Prop => match self.peek().cloned() {
                Some(Tok::Ident(name)) => {
                    self.pos += 1;
                    Ok(match name.as_str() {
                        "true" => Formula::Const(true),
                        "false" => Formula::Const(false),
                        _ => Formula::Var(name),
                    })
                }
                _ => self.error("a variable or '('"),
            },
            Atoms::Equality | Atoms::Functions => {
                let lhs = self.term()?;
                let equal = match self.peek() {
                    Some(Tok::Eq) => true,
                    Some(Tok::Neq) => false,
                    _ => return self.error("'=' or '!='"),
                };
                self.pos += 1;
                let rhs = self.term()?;
                Ok(Formula::Eq { lhs, rhs, equal })
            }
            Atoms::Arith => match self.peek() {
                Some(Tok::Ident(n)) if n == "true" || n == "false" => {
                    let b = n == "true";
                    self.pos += 1;
                    Ok(Formula::Const(b))
                }
                _ => self.objective_or_comparison(),
            },
        }
    }

    /// `min(linear)`, `max(linear)`, or a comparison.
    fn objective_or_comparison(&mut self) -> Result<Formula, ParseError> {
        let is_objective = matches!(
            (self.peek(), self.toks.get(self.pos + 1).map(|(t, _)| t)),
            (Some(Tok::Ident(n)), Some(Tok::LParen))
                if matches!(n.to_ascii_lowercase().as_str(), "min" | "max")
        );
        if !is_objective {
            return self.comparison();
        }
        let maximize = matches!(self.peek(), Some(Tok::Ident(n)) if n.eq_ignore_ascii_case("max"));
        self.pos += 2;
        let list = std::mem::replace(&mut self.list, false);
        let term = self.linear();
        self.list = list;
        let term = term?;
        self.expect(&Tok::RParen)?;
        Ok(Formula::Objective { maximize, term })
    }

    /// `linear REL linear`.
    fn comparison(&mut self) -> Result<Formula, ParseError> {
        let lhs = self.linear()?;
        let rel = match self.peek() {
            Some(Tok::Le) => Rel::Le,
            Some(Tok::Lt) => Rel::Lt,
            Some(Tok::Ge) => Rel::Ge,
            Some(Tok::Gt) => Rel::Gt,
            Some(Tok::Eq) => Rel::Eq,
            Some(Tok::Neq) => Rel::Ne,
            _ => return self.error("'+', '-' or a comparison (<=, <, >=, >, =, !=)"),
        };
        self.pos += 1;
        let rhs = self.linear()?;
        Ok(Formula::Cmp { lhs, rel, rhs })
    }

    fn linear(&mut self) -> Result<Linear, ParseError> {
        let mut lin = Linear::default();
        self.summand(&mut lin, Rational::one())?;
        loop {
            let sign = match self.peek() {
                Some(Tok::Plus) => Rational::one(),
                Some(Tok::Minus) => -Rational::one(),
                _ => break,
            };
            if self.list && self.opens_word[self.pos] {
                break;
            }
            self.pos += 1;
            self.summand(&mut lin, sign)?;
        }
        Ok(lin)
    }

    /// One summand of a linear expression, with any leading signs, added to `lin` times `sign`.
    fn summand(&mut self, lin: &mut Linear, sign: Rational) -> Result<(), ParseError> {
        let mut sign = sign;
        while let Some(t @ (Tok::Plus | Tok::Minus)) = self.peek() {
            if *t == Tok::Minus {
                sign = -sign;
            }
            self.pos += 1;
        }
        match self.peek().cloned() {
            Some(Tok::Coef(q, _)) => {
                self.pos += 1;
                let x = self.variable()?;
                lin.add_var(&x, &(&sign * &q));
            }
            Some(Tok::Num(q, _)) => {
                self.pos += 1;
                if self.eat(&Tok::Star) {
                    let x = self.variable()?;
                    lin.add_var(&x, &(&sign * &q));
                } else {
                    lin.constant = &lin.constant + &(&sign * &q);
                }
            }
            Some(Tok::Ident(_)) => {
                let x = self.variable()?;
                let c = if self.eat(&Tok::Star) {
                    match self.peek().cloned() {
                        Some(Tok::Num(q, _)) => {
                            self.pos += 1;
                            q
                        }
                        _ => return self.error("a number (the product must stay linear)"),
                    }
                } else {
                    Rational::one()
                };
                lin.add_var(&x, &(&sign * &c));
            }
            _ => return self.error("a number or a variable"),
        }
        Ok(())
    }

    fn variable(&mut self) -> Result<String, ParseError> {
        match self.peek().cloned() {
            Some(Tok::Ident(n)) if n != "true" && n != "false" => {
                self.pos += 1;
                Ok(n)
            }
            _ => self.error("a variable"),
        }
    }

    fn term(&mut self) -> Result<Term, ParseError> {
        let name = match self.peek().cloned() {
            Some(Tok::Ident(n)) => n,
            _ => {
                return self.error(if self.atoms == Atoms::Functions {
                    "a term"
                } else {
                    "a constant"
                })
            }
        };
        self.pos += 1;
        let mut args = Vec::new();
        if self.peek() == Some(&Tok::LParen) {
            if self.atoms == Atoms::Equality {
                return Err(ParseError {
                    message: format!("QF_EQ has no functions; use QF_EQUF for '{name}(...)'"),
                    at: self.here(),
                });
            }
            self.pos += 1;
            loop {
                args.push(self.term()?);
                if self.eat(&Tok::RParen) {
                    break;
                }
                if !self.eat(&Tok::Comma) {
                    return self.error("',' or ')'");
                }
            }
        }
        Ok(Term { name, args })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn p(s: &str) -> Formula {
        parse(s, Atoms::Prop).unwrap_or_else(|e| panic!("{s}: {e:?}"))
    }

    fn var(s: &str) -> Formula {
        Formula::Var(s.into())
    }

    #[test]
    fn precedence_and_associativity() {
        // ~ binds tighter than &, & than |, | than ->, -> than <->; -> and <-> are right-assoc.
        assert_eq!(
            p("~a & b | c -> d <-> e"),
            Formula::Iff(
                Box::new(Formula::Implies(
                    Box::new(Formula::Or(vec![
                        Formula::And(vec![Formula::Not(Box::new(var("a"))), var("b")]),
                        var("c"),
                    ])),
                    Box::new(var("d")),
                )),
                Box::new(var("e")),
            )
        );
        assert_eq!(
            p("a -> b -> c"),
            Formula::Implies(
                Box::new(var("a")),
                Box::new(Formula::Implies(Box::new(var("b")), Box::new(var("c"))))
            )
        );
        assert_eq!(p("!!a"), p("~~a"));
        assert_eq!(p("a && b || c => d <=> e"), p("a & b | c -> d <-> e"));
    }

    #[test]
    fn examples_parse() {
        for s in [
            "(a | b) & (~a | c) & ~c",
            "(~a | b) & (a)",
            "(a | b) & (~a | b) & (a | ~b) & (~a | ~b)",
            "a -> b -> c",
            "~(a <-> b | c)",
        ] {
            p(s);
        }
        parse("(a=b) & (b=c) & (a!=c | c!=d)", Atoms::Equality).unwrap();
        parse("(x=y) & (f(x) = y) & (f(f(x)) = y)", Atoms::Functions).unwrap();
        parse(
            "(x1 = x2) & (x2 = x3) & (x4 = x5) & (f(x1) != f(x5))",
            Atoms::Functions,
        )
        .unwrap();
    }

    #[test]
    fn errors_point_at_the_problem() {
        let e = parse("(a | b", Atoms::Prop).unwrap_err();
        assert_eq!(
            (e.message.as_str(), e.at),
            ("expected ')', got the end of the input", 6)
        );
        let e = parse("a & | b", Atoms::Prop).unwrap_err();
        assert_eq!(e.at, 4);
        let e = parse("a b", Atoms::Prop).unwrap_err();
        assert_eq!(
            (e.message.as_str(), e.at),
            ("expected an operator, got 'b'", 2)
        );
        let e = parse("a = f(b)", Atoms::Equality).unwrap_err();
        assert!(e.message.contains("use QF_EQUF"), "{}", e.message);
        let e = parse("a # b", Atoms::Prop).unwrap_err();
        assert_eq!((e.message.as_str(), e.at), ("unexpected character '#'", 2));
        let e = parse("f(a,) = b", Atoms::Functions).unwrap_err();
        assert_eq!(e.at, 4);
        let e = parse("", Atoms::Prop).unwrap_err();
        assert_eq!(e.message, "expected a formula");
    }

    fn lra(s: &str) -> Formula {
        parse(s, Atoms::Arith).unwrap_or_else(|e| panic!("{s}: {e:?}"))
    }

    fn q(n: i64, d: i64) -> Rational {
        Rational::new(n, d)
    }

    fn lin(coeffs: &[(&str, Rational)], constant: Rational) -> Linear {
        Linear {
            coeffs: coeffs
                .iter()
                .map(|(x, c)| (x.to_string(), c.clone()))
                .collect(),
            constant,
        }
    }

    fn cmp(lhs: Linear, rel: Rel, rhs: Linear) -> Formula {
        Formula::Cmp { lhs, rel, rhs }
    }

    #[test]
    fn linear_terms() {
        // Implicit multiplication, fractions and decimals; like variables are merged.
        assert_eq!(
            lra("x + 2y - 1/2z + 0.8x <= 1"),
            cmp(
                lin(&[("x", q(9, 5)), ("y", q(2, 1)), ("z", q(-1, 2))], q(0, 1)),
                Rel::Le,
                lin(&[], q(1, 1))
            )
        );
        // Explicit '*' on either side, repeated signs, constants on both sides, .5 and 5.
        assert_eq!(
            lra("-2*x + y*3 - -4 >= .5 - --x + 5."),
            cmp(
                lin(&[("x", q(-2, 1)), ("y", q(3, 1))], q(4, 1)),
                Rel::Ge,
                lin(&[("x", q(-1, 1))], q(11, 2))
            )
        );
        // x2 is a variable, 2x is 2·x; a zero coefficient keeps its variable.
        assert_eq!(
            lra("x2 - 2x2 + x - x = 0"),
            cmp(
                lin(&[("x2", q(-1, 1)), ("x", q(0, 1))], q(0, 1)),
                Rel::Eq,
                lin(&[], q(0, 1))
            )
        );
        let rels = ["<=", "<", ">=", ">", "=", "!=", "=="];
        let want = [
            Rel::Le,
            Rel::Lt,
            Rel::Ge,
            Rel::Gt,
            Rel::Eq,
            Rel::Ne,
            Rel::Eq,
        ];
        for (r, w) in rels.iter().zip(want) {
            match lra(&format!("x {r} 1")) {
                Formula::Cmp { rel, .. } => assert_eq!(rel, w, "{r}"),
                f => panic!("{f:?}"),
            }
        }
    }

    #[test]
    fn arithmetic_precedence() {
        let a = || cmp(lin(&[("x", q(1, 1))], q(0, 1)), Rel::Le, lin(&[], q(-3, 1)));
        let b = || cmp(lin(&[("x", q(1, 1))], q(0, 1)), Rel::Ge, lin(&[], q(3, 1)));
        let c = || cmp(lin(&[("y", q(1, 1))], q(0, 1)), Rel::Eq, lin(&[], q(5, 1)));
        assert_eq!(
            lra("x<=-3 | x>=3 & y=5"),
            Formula::Or(vec![a(), Formula::And(vec![b(), c()])])
        );
        assert_eq!(
            lra("(x<=-3 | x>=3) & (y=5)"),
            Formula::And(vec![Formula::Or(vec![a(), b()]), c()])
        );
        // '<->' and '->' are not '<' or '-' followed by something.
        assert_eq!(
            lra("~x<=-3 -> y=5 <-> true"),
            Formula::Iff(
                Box::new(Formula::Implies(
                    Box::new(Formula::Not(Box::new(a()))),
                    Box::new(c())
                )),
                Box::new(Formula::Const(true))
            )
        );
    }

    #[test]
    fn arithmetic_errors_point_at_the_problem() {
        let err = |s: &str| {
            let e = parse(s, Atoms::Arith).unwrap_err();
            (e.message, e.at)
        };
        let (m, at) = err("x + <= 3");
        assert_eq!(
            (m.as_str(), at),
            ("expected a number or a variable, got '<='", 4)
        );
        // A space breaks implicit multiplication.
        let (m, at) = err("2 x <= 1");
        assert_eq!(
            (m.as_str(), at),
            (
                "expected '+', '-' or a comparison (<=, <, >=, >, =, !=), got 'x'",
                2
            )
        );
        assert_eq!(err("x/2 <= 1").1, 1);
        assert!(err("x/2 <= 1").0.contains("fraction"));
        assert_eq!(
            err("x <= 1/0"),
            ("division by zero in '1/0'".to_string(), 5)
        );
        let (m, at) = err("x*y <= 1");
        assert_eq!(at, 2);
        assert!(m.contains("linear"), "{m}");
        assert_eq!(
            err("x"),
            (
                "expected '+', '-' or a comparison (<=, <, >=, >, =, !=), got the end of the input"
                    .to_string(),
                1
            )
        );
        assert_eq!(err("(x <= 3").1, 7);
        assert_eq!(err("x <= true").1, 5);
        assert_eq!(err("x # 1"), ("unexpected character '#'".to_string(), 2));
        assert_eq!(err("x <= ."), ("unexpected character '.'".to_string(), 5));
    }

    #[test]
    fn constraint_lists_and_objectives() {
        assert_eq!(
            parse_constraints("x+y>=10 x-y<=5 1/2x-y<=0").unwrap().len(),
            3
        );
        assert_eq!(
            parse_constraints("x + y >= 10   x - y <= 5").unwrap().len(),
            2
        );
        // A sign opening a word starts a new constraint; a spaced-out sign does not.
        let cs = parse_constraints("x>=1 -y<=5").unwrap();
        assert_eq!(cs.len(), 2);
        assert_eq!(
            cs[1],
            cmp(lin(&[("y", q(-1, 1))], q(0, 1)), Rel::Le, lin(&[], q(5, 1)))
        );
        assert_eq!(parse_constraints("x >= 1 - y").unwrap().len(), 1);
        assert_eq!(parse_constraints("x>=1 & y<=2").unwrap_err().at, 5);
        assert_eq!(
            parse_constraints(" ").unwrap_err().message,
            "expected a linear constraint"
        );
    }
}
