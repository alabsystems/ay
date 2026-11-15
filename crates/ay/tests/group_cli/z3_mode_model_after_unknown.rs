// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `(get-model)` after `unknown`. z3 answers it with the candidate its search
//! stopped at, and Verus's AIR reads that candidate to name the assertion that
//! failed. `--z3-mode` prints ay's candidate, marked as unvalidated, where z3
//! would print one; every other mode keeps answering `model is not
//! available`, because a model after `unknown` has not been checked and must
//! never pass for a counterexample.

use ntest::timeout;
use std::io::Write;
use std::process::{Command, Stdio};

/// Satisfiable, but ay answers `unknown`: the ground search does not see that
/// the injective `I` forces `Poly` to be infinite, and ay's own check rejects
/// the model it stops at. Every model sets `L0` true; nothing needs `L1` true.
/// `(pop 2)` removes all of it.
const UNKNOWN_QUERY: &str = r#"
(push)
(declare-sort Poly 0)
(declare-fun I (Int) Poly)
(declare-fun %I (Poly) Int)
(assert (forall ((x Int)) (! (= x (%I (I x))) :pattern ((I x)))))
(push)
(declare-const a Int)
(declare-const L0 Bool)
(declare-const L1 Bool)
(assert (<= (%I (I a)) 0))
(assert (not (and (=> L1 (< (%I (I a)) 1)) (=> L0 (> (%I (I a)) 0)))))
(check-sat)
"#;

const MARKER: &str = ";; candidate model after unknown: not validated";

fn run_stdin(args: &[&str], input: &str) -> String {
    let mut child = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(args)
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ay -in");
    child
        .stdin
        .as_mut()
        .expect("child stdin")
        .write_all(input.as_bytes())
        .expect("write SMT-LIB input");
    let output = child.wait_with_output().expect("wait for ay -in");
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn assert_unknown(stdout: &str) {
    let first = stdout.lines().map(str::trim).find(|line| !line.is_empty());
    assert_eq!(
        first,
        Some("unknown"),
        "the fixture must answer unknown, or these tests prove nothing; stdout: {stdout}"
    );
}

#[test]
#[timeout(120_000)]
fn outside_z3_mode_get_model_after_unknown_is_still_an_error() {
    for args in [&["-q"][..], &[][..]] {
        let stdout = run_stdin(args, &format!("{UNKNOWN_QUERY}(get-model)\n"));
        assert_unknown(&stdout);
        assert!(
            stdout.contains("model is not available"),
            "args {args:?}: get-model after unknown must fail; stdout: {stdout}"
        );
        assert!(
            !stdout.contains("define-fun") && !stdout.contains(MARKER),
            "args {args:?}: no model may follow unknown; stdout: {stdout}"
        );
    }
}

#[test]
#[timeout(120_000)]
fn z3_mode_prints_the_candidate_marked_unvalidated() {
    let stdout = run_stdin(
        &["-q", "--z3-mode"],
        &format!("{UNKNOWN_QUERY}(get-model)\n"),
    );
    assert_unknown(&stdout);
    assert!(stdout.contains(MARKER), "stdout: {stdout}");
    assert!(
        stdout.contains("(define-fun L0 () Bool true)"),
        "stdout: {stdout}"
    );
    assert!(
        stdout.contains("(define-fun L1 () Bool false)"),
        "nothing needs L1 true, so the candidate leaves it false; stdout: {stdout}"
    );
    assert!(
        !stdout.contains("model is not available"),
        "stdout: {stdout}"
    );
}

/// z3 keeps no model after `unknown` from a plain `check-sat` in a session
/// that never pushed (it runs a tactic there), and AIR reports such queries
/// differently; `--z3-mode` does the same.
#[test]
#[timeout(120_000)]
fn z3_mode_keeps_no_model_where_z3_runs_its_tactic() {
    let input = format!("{}(get-model)\n", UNKNOWN_QUERY.replace("(push)", ""));
    let stdout = run_stdin(&["-q", "--z3-mode"], &input);
    assert_unknown(&stdout);
    assert!(
        stdout.contains("model is not available"),
        "stdout: {stdout}"
    );
    assert!(!stdout.contains(MARKER), "stdout: {stdout}");
}

#[test]
#[timeout(120_000)]
fn z3_mode_keeps_get_value_and_later_commands_honest() {
    let input = format!(
        "{UNKNOWN_QUERY}(get-value (L0))\n(assert true)\n(get-model)\n(pop 2)\n\
         (declare-const x Int)\n(assert (> x 3))\n(check-sat)\n(get-model)\n"
    );
    let stdout = run_stdin(&["-q", "--z3-mode"], &input);
    assert_unknown(&stdout);
    assert_eq!(
        stdout.matches("model is not available").count(),
        2,
        "get-value after unknown, and get-model once the assertions changed, fail; stdout: {stdout}"
    );
    let after_sat = stdout
        .split_once("\nsat\n")
        .map(|(_, rest)| rest)
        .expect("the last query answers sat");
    assert!(
        after_sat.contains("(define-fun x () Int"),
        "stdout: {stdout}"
    );
    assert!(
        !after_sat.contains(MARKER),
        "a model after sat is the validated one; stdout: {stdout}"
    );
}
