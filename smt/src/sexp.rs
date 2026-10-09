//! A minimal SMT-LIB 2.6 s-expression reader.
//!
//! Handles the lexical syntax we need for QF_UF/QF_EQ scripts: `;` line comments,
//! `|quoted symbols|` (which may span lines, as in `:source |...|`), `"string literals"`,
//! `:keywords`, and ordinary symbols/numerals. Produces a flat list of top-level s-expressions.

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sexp {
    Atom(String),
    List(Vec<Sexp>),
}

impl Sexp {
    pub fn as_atom(&self) -> Option<&str> {
        match self {
            Sexp::Atom(s) => Some(s),
            Sexp::List(_) => None,
        }
    }

    pub fn as_list(&self) -> Option<&[Sexp]> {
        match self {
            Sexp::List(v) => Some(v),
            Sexp::Atom(_) => None,
        }
    }
}

impl std::fmt::Display for Sexp {
    /// SMT-LIB concrete syntax. Symbols that are not valid simple symbols are re-quoted as
    /// `|...|` (the reader strips the bars); string literals and keywords print as read.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Sexp::Atom(a) => f.write_str(&quote_symbol(a)),
            Sexp::List(items) => {
                f.write_str("(")?;
                for (i, item) in items.iter().enumerate() {
                    if i > 0 {
                        f.write_str(" ")?;
                    }
                    write!(f, "{item}")?;
                }
                f.write_str(")")
            }
        }
    }
}

/// `s` as SMT-LIB source: unchanged if it is a simple symbol, numeral, keyword or string literal,
/// otherwise wrapped in `|...|`.
pub fn quote_symbol(s: &str) -> std::borrow::Cow<'_, str> {
    let simple = |c: char| c.is_ascii_alphanumeric() || "~!@$%^&*_-+=<>.?/".contains(c);
    let is_numeral = !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit());
    let is_decimal = s.split_once('.').is_some_and(|(i, f)| {
        !i.is_empty()
            && !f.is_empty()
            && i.bytes().all(|b| b.is_ascii_digit())
            && f.bytes().all(|b| b.is_ascii_digit())
    });
    let is_simple = is_simple_symbol(s);
    // Already quoted by the reader (see `tokenize`).
    let is_quoted = s.len() >= 2 && s.starts_with('|') && s.ends_with('|');
    let is_keyword = s.len() > 1 && s.starts_with(':') && s[1..].chars().all(simple);
    let is_string = s.len() >= 2 && s.starts_with('"') && s.ends_with('"');
    let is_bv_literal = match (s.strip_prefix("#b"), s.strip_prefix("#x")) {
        (Some(d), _) => !d.is_empty() && d.bytes().all(|b| b == b'0' || b == b'1'),
        (_, Some(d)) => !d.is_empty() && d.bytes().all(|b| b.is_ascii_hexdigit()),
        _ => false,
    };
    if is_simple
        || is_numeral
        || is_decimal
        || is_keyword
        || is_string
        || is_bv_literal
        || is_quoted
    {
        std::borrow::Cow::Borrowed(s)
    } else {
        std::borrow::Cow::Owned(format!("|{s}|"))
    }
}

/// A simple SMT-LIB symbol: non-empty, letters, digits and `~!@$%^&*_-+=<>.?/`, not starting
/// with a digit.
pub fn is_simple_symbol(s: &str) -> bool {
    !s.is_empty()
        && !s.starts_with(|c: char| c.is_ascii_digit())
        && s.chars()
            .all(|c| c.is_ascii_alphanumeric() || "~!@$%^&*_-+=<>.?/".contains(c))
}

enum Token {
    LParen,
    RParen,
    Atom(String),
}

fn tokenize(input: &str) -> Result<Vec<Token>, String> {
    let bytes = input.as_bytes();
    let mut i = 0;
    let mut tokens = Vec::new();
    while i < bytes.len() {
        let c = bytes[i];
        match c {
            b' ' | b'\t' | b'\r' | b'\n' => i += 1,
            b';' => {
                // line comment to end of line
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'(' => {
                tokens.push(Token::LParen);
                i += 1;
            }
            b')' => {
                tokens.push(Token::RParen);
                i += 1;
            }
            b'|' => {
                // quoted symbol: everything up to the next '|'
                let start = i + 1;
                i += 1;
                while i < bytes.len() && bytes[i] != b'|' {
                    i += 1;
                }
                if i >= bytes.len() {
                    return Err("unterminated |quoted symbol|".to_string());
                }
                let s = std::str::from_utf8(&bytes[start..i]).map_err(|e| e.to_string())?;
                // `|x|` and `x` are the same symbol, so the bars go when the content is a simple
                // symbol. Otherwise they stay: `|286|` is a symbol, never the numeral 286, and
                // `|:k|` never the keyword `:k`.
                tokens.push(Token::Atom(if is_simple_symbol(s) {
                    s.to_string()
                } else {
                    format!("|{s}|")
                }));
                i += 1; // closing '|'
            }
            b'"' => {
                // string literal: "" is an escaped quote
                let start = i;
                i += 1;
                loop {
                    if i >= bytes.len() {
                        return Err("unterminated string literal".to_string());
                    }
                    if bytes[i] == b'"' {
                        if i + 1 < bytes.len() && bytes[i + 1] == b'"' {
                            i += 2; // escaped quote
                            continue;
                        }
                        i += 1; // closing quote
                        break;
                    }
                    i += 1;
                }
                let s = std::str::from_utf8(&bytes[start..i]).map_err(|e| e.to_string())?;
                tokens.push(Token::Atom(s.to_string()));
            }
            _ => {
                let start = i;
                while i < bytes.len() {
                    let d = bytes[i];
                    if matches!(
                        d,
                        b' ' | b'\t' | b'\r' | b'\n' | b'(' | b')' | b';' | b'|' | b'"'
                    ) {
                        break;
                    }
                    i += 1;
                }
                let s = std::str::from_utf8(&bytes[start..i]).map_err(|e| e.to_string())?;
                tokens.push(Token::Atom(s.to_string()));
            }
        }
    }
    Ok(tokens)
}

/// Parse a whole script into its sequence of top-level s-expressions (commands).
pub fn parse_script(input: &str) -> Result<Vec<Sexp>, String> {
    let tokens = tokenize(input)?;
    let mut pos = 0;
    let mut out = Vec::new();
    while pos < tokens.len() {
        let s = parse_one(&tokens, &mut pos)?;
        out.push(s);
    }
    Ok(out)
}

fn parse_one(tokens: &[Token], pos: &mut usize) -> Result<Sexp, String> {
    match tokens.get(*pos) {
        None => Err("unexpected end of input".to_string()),
        Some(Token::RParen) => Err("unexpected ')'".to_string()),
        Some(Token::Atom(s)) => {
            let s = s.clone();
            *pos += 1;
            Ok(Sexp::Atom(s))
        }
        Some(Token::LParen) => {
            *pos += 1;
            let mut items = Vec::new();
            loop {
                match tokens.get(*pos) {
                    None => return Err("unterminated list".to_string()),
                    Some(Token::RParen) => {
                        *pos += 1;
                        return Ok(Sexp::List(items));
                    }
                    _ => items.push(parse_one(tokens, pos)?),
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_basic_script() {
        let s = "(set-logic QF_UF) ; comment\n(assert (= a b))\n(check-sat)";
        let cmds = parse_script(s).unwrap();
        assert_eq!(cmds.len(), 3);
        assert_eq!(cmds[0].as_list().unwrap()[0].as_atom(), Some("set-logic"));
        assert_eq!(cmds[2].as_list().unwrap()[0].as_atom(), Some("check-sat"));
    }

    #[test]
    fn prints_round_trip() {
        let src = "(assert (! (= |a b| x) :named n1))";
        let cmds = parse_script(src).unwrap();
        assert_eq!(cmds[0].to_string(), src);
        assert_eq!(quote_symbol("x!1"), "x!1");
        assert_eq!(quote_symbol("1x"), "|1x|");
        assert_eq!(quote_symbol("42"), "42");
        assert_eq!(quote_symbol(""), "||");
    }

    #[test]
    fn handles_quoted_and_strings() {
        let s = "(set-info :source |multi\nline|)(set-info :category \"crafted\")";
        let cmds = parse_script(s).unwrap();
        assert_eq!(cmds.len(), 2);
        assert_eq!(
            cmds[0].as_list().unwrap()[2].as_atom(),
            Some("|multi\nline|")
        );
        // `|x|` is `x`; `|286|` is a symbol, not the numeral 286.
        let cmds = parse_script("(f |x| |286| 286 |:k|)").unwrap();
        let atoms: Vec<&str> = cmds[0]
            .as_list()
            .unwrap()
            .iter()
            .filter_map(Sexp::as_atom)
            .collect();
        assert_eq!(atoms, ["f", "x", "|286|", "286", "|:k|"]);
        assert_eq!(cmds[0].to_string(), "(f x |286| 286 |:k|)");
    }
}
