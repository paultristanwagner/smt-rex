//! Terminal colours, off unless stdout is a terminal (and `NO_COLOR` is unset), plus the small
//! formatting helpers the commands share.

use std::io::IsTerminal;
use std::time::Duration;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ColorChoice {
    Auto,
    Always,
    Never,
}

#[derive(Clone, Copy, Debug)]
pub struct Style {
    color: bool,
}

impl Style {
    pub fn new(choice: ColorChoice) -> Style {
        let color = match choice {
            ColorChoice::Always => true,
            ColorChoice::Never => false,
            ColorChoice::Auto => {
                std::io::stdout().is_terminal()
                    && std::env::var_os("NO_COLOR").is_none_or(|v| v.is_empty())
                    && std::env::var("TERM").map_or(true, |t| t != "dumb")
            }
        };
        Style { color }
    }

    #[cfg(test)]
    pub fn plain() -> Style {
        Style { color: false }
    }

    fn paint(&self, code: &str, s: &str) -> String {
        if self.color {
            format!("\x1b[{code}m{s}\x1b[0m")
        } else {
            s.to_string()
        }
    }

    pub fn sat(&self, s: &str) -> String {
        self.paint("1;32", s)
    }
    pub fn unsat(&self, s: &str) -> String {
        self.paint("1;31", s)
    }
    pub fn unknown(&self, s: &str) -> String {
        self.paint("1;33", s)
    }
    pub fn error(&self, s: &str) -> String {
        self.paint("31", s)
    }
    pub fn dim(&self, s: &str) -> String {
        self.paint("90", s)
    }
    pub fn bold(&self, s: &str) -> String {
        self.paint("1", s)
    }
    pub fn accent(&self, s: &str) -> String {
        self.paint("36", s)
    }
    pub fn yes(&self, s: &str) -> String {
        self.paint("32", s)
    }
    pub fn no(&self, s: &str) -> String {
        self.paint("31", s)
    }
}

/// A duration for people: `850 µs`, `12.3 ms`, `4.56 s`.
pub fn human(d: Duration) -> String {
    let us = d.as_secs_f64() * 1e6;
    if us < 1000.0 {
        format!("{us:.0} µs")
    } else if us < 100_000.0 {
        format!("{:.1} ms", us / 1000.0)
    } else if us < 1e6 {
        format!("{:.0} ms", us / 1000.0)
    } else {
        format!("{:.2} s", us / 1e6)
    }
}

/// Join `items` with two spaces, breaking lines before `width` columns; each line is indented
/// by `indent`. Widths are measured on the uncoloured text (`visible`).
pub fn wrap(items: &[(String, usize)], indent: &str, width: usize) -> String {
    let mut out = String::new();
    let mut col = 0;
    for (text, visible) in items {
        if col > 0 && col + 2 + visible > width {
            out.push('\n');
            col = 0;
        }
        if col == 0 {
            out.push_str(indent);
            col = indent.len();
        } else {
            out.push_str("  ");
            col += 2;
        }
        out.push_str(text);
        col += visible;
    }
    out
}

/// Sort key that orders `x2` before `x10`.
pub fn natural_key(s: &str) -> Vec<(bool, u64, String)> {
    let mut key = Vec::new();
    let mut chars = s.chars().peekable();
    while let Some(&c) = chars.peek() {
        if c.is_ascii_digit() {
            let mut n = String::new();
            while let Some(&d) = chars.peek().filter(|d| d.is_ascii_digit()) {
                n.push(d);
                chars.next();
            }
            key.push((true, n.parse().unwrap_or(u64::MAX), n));
        } else {
            let mut t = String::new();
            while let Some(&d) = chars.peek().filter(|d| !d.is_ascii_digit()) {
                t.push(d);
                chars.next();
            }
            key.push((false, 0, t));
        }
    }
    key
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn durations() {
        assert_eq!(human(Duration::from_micros(850)), "850 µs");
        assert_eq!(human(Duration::from_micros(12_340)), "12.3 ms");
        assert_eq!(human(Duration::from_millis(250)), "250 ms");
        assert_eq!(human(Duration::from_millis(4_560)), "4.56 s");
    }

    #[test]
    fn natural_order() {
        let mut v = vec!["x10", "x2", "y", "x1"];
        v.sort_by_key(|s| natural_key(s));
        assert_eq!(v, ["x1", "x2", "x10", "y"]);
    }

    #[test]
    fn wrapping() {
        let items: Vec<(String, usize)> = ["aaaa", "bbbb", "cccc"]
            .iter()
            .map(|s| (s.to_string(), 4))
            .collect();
        assert_eq!(wrap(&items, "  ", 13), "  aaaa  bbbb\n  cccc");
    }
}
