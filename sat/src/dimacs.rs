//! Lenient DIMACS CNF reader: skips comments and blank lines, accepts clauses spanning lines,
//! stops at a `%` end marker, and ignores the declared clause count.

use smtrex_core::Lit;

#[derive(Clone, Debug)]
pub struct Cnf {
    pub num_vars: usize,
    pub clauses: Vec<Vec<Lit>>,
}

/// Parse DIMACS CNF text. Literals beyond the declared variable count grow `num_vars`.
pub fn parse(input: &str) -> Result<Cnf, String> {
    let mut num_vars = 0usize;
    let mut clauses: Vec<Vec<Lit>> = Vec::new();
    let mut cur: Vec<Lit> = Vec::new();
    let mut seen_header = false;

    for line in input.lines() {
        let t = line.trim();
        if t.is_empty() || t.starts_with('c') {
            continue;
        }
        if t.starts_with('%') {
            break;
        }
        if t.starts_with('p') {
            let mut it = t.split_whitespace();
            it.next(); // "p"
            if it.next() != Some("cnf") {
                return Err(format!("expected 'p cnf ...' header, got: {t}"));
            }
            num_vars = it
                .next()
                .ok_or("missing variable count in header")?
                .parse()
                .map_err(|_| "bad variable count in header")?;
            seen_header = true;
            continue;
        }
        if !seen_header {
            return Err("clause data before 'p cnf' header".into());
        }
        for tok in t.split_whitespace() {
            let n: i64 = tok
                .parse()
                .map_err(|_| format!("non-integer token: {tok}"))?;
            if n == 0 {
                clauses.push(std::mem::take(&mut cur));
            } else {
                let v = n.unsigned_abs() as usize;
                num_vars = num_vars.max(v);
                cur.push(Lit::from_dimacs(n as i32));
            }
        }
    }
    if !seen_header {
        return Err("missing 'p cnf' header".into());
    }
    if !cur.is_empty() {
        clauses.push(cur); // tolerate a final clause without a trailing 0
    }
    Ok(Cnf { num_vars, clauses })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_comments_and_multiline() {
        let c = parse("c hi\nc yo\np cnf 3 2\n1 -3 0\n2\n3 -1 0\n").unwrap();
        assert_eq!(c.num_vars, 3);
        assert_eq!(c.clauses.len(), 2);
        assert_eq!(c.clauses[1].len(), 3);
    }

    #[test]
    fn missing_header_errors() {
        assert!(parse("1 2 0").is_err());
    }
}
