//! Run every benchmark in `tests/corpus` and check the verdict against its SMT-LIB `:status`
//! annotation, which z3 agrees with.

use smtrex_smt::script::{Answer, Script};

/// Extract the `(set-info :status sat|unsat|unknown)` value, if present.
fn status(src: &str) -> Option<Answer> {
    let i = src.find(":status")? + ":status".len();
    let rest = src[i..].trim_start();
    if rest.starts_with("sat") {
        Some(Answer::Sat)
    } else if rest.starts_with("unsat") {
        Some(Answer::Unsat)
    } else {
        None // unknown / absent
    }
}

#[test]
fn corpus_matches_status() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/corpus");
    let mut checked = 0;
    for entry in std::fs::read_dir(dir).expect("read corpus dir") {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("smt2") {
            continue;
        }
        let src = std::fs::read_to_string(&path).unwrap();
        let expected = match status(&src) {
            Some(a) => a,
            None => continue,
        };
        let script = Script::run(&src)
            .unwrap_or_else(|e| panic!("{}: parse/run error: {e}", path.display()));
        assert_eq!(
            script.results.len(),
            1,
            "{}: expected exactly one (check-sat)",
            path.display()
        );
        assert_eq!(
            script.results[0].answer,
            expected,
            "{}: verdict disagrees with :status",
            path.display()
        );
        checked += 1;
    }
    assert!(
        checked >= 8,
        "expected to check the committed corpus, got {checked}"
    );
}
