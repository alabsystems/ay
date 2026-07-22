// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for false UNSAT from str.at reduction lemma interaction.
//!
//! When multiple str.at terms target the same string variable, each generates
//! an independent skolem decomposition (s = sk_pre ++ skt ++ sk_suf). These
//! competing decompositions create conflicting NFs that the solver cannot
//! reconcile, producing false UNSAT.
//!
//! Found by Prover P5 differential testing (AY vs Z3).
//! Related: #4025 (strings wrong answers tracking)

use ay_dpll::Executor;
use ay_frontend::parse;

fn solve(smt: &str) -> String {
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .map(|lines| lines.join("\n"))
        .unwrap_or_else(|e| format!("error: {e}"))
}

/// Two str.at on same variable with length constraint (length > coverage).
/// str.at(x,0)="a" AND str.at(x,1)="b" AND len(x)=3
/// SAT model: x = "abc" (any 3-char string starting with "ab")
#[test]
fn two_str_at_with_excess_length_not_false_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.at x 0) "a"))
(assert (= (str.at x 1) "b"))
(assert (= (str.len x) 3))
(check-sat)
"#;
    let result = solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_ne!(
        ay,
        Some("unsat"),
        "str.at(x,0)=\"a\" + str.at(x,1)=\"b\" + len(x)=3 is SAT (e.g. x=\"abc\"); must not return unsat"
    );
}

/// Two non-adjacent str.at positions with length constraint.
/// str.at(x,0)="a" AND str.at(x,2)="c" AND len(x)=3
/// SAT model: x = "abc" (any 3-char string with 'a' at 0 and 'c' at 2)
#[test]
fn two_str_at_nonadjacent_with_length_not_false_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.at x 0) "a"))
(assert (= (str.at x 2) "c"))
(assert (= (str.len x) 3))
(check-sat)
"#;
    let result = solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_ne!(
        ay,
        Some("unsat"),
        "str.at(x,0)=\"a\" + str.at(x,2)=\"c\" + len(x)=3 is SAT (e.g. x=\"abc\"); must not return unsat"
    );
}

/// Two str.at at distant positions on a 5-character string.
/// str.at(x,0)="h" AND str.at(x,4)="o" AND len(x)=5
/// SAT model: x = "hello"
#[test]
fn two_str_at_distant_positions_not_false_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.at x 0) "h"))
(assert (= (str.at x 4) "o"))
(assert (= (str.len x) 5))
(check-sat)
"#;
    let result = solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_ne!(
        ay,
        Some("unsat"),
        "str.at(x,0)=\"h\" + str.at(x,4)=\"o\" + len(x)=5 is SAT (e.g. x=\"hello\"); must not return unsat"
    );
}

/// Two str.at that exactly cover the string length (baseline — should pass).
/// str.at(x,0)="a" AND str.at(x,1)="b" AND len(x)=2
/// SAT model: x = "ab"
#[test]
fn two_str_at_exact_coverage_is_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.at x 0) "a"))
(assert (= (str.at x 1) "b"))
(assert (= (str.len x) 2))
(check-sat)
"#;
    let result = solve(smt);
    let ay = crate::common::sat_result(&result);
    assert_eq!(
        ay,
        Some("sat"),
        "str.at(x,0)=\"a\" + str.at(x,1)=\"b\" + len(x)=2 is SAT (x=\"ab\")"
    );
}

/// Single str.at with length (baseline — should pass).
/// str.at(x,0)="h" AND len(x)=5
/// SAT model: x = "hxxxx"
#[test]
fn single_str_at_with_length_is_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(assert (= (str.at x 0) "h"))
(assert (= (str.len x) 5))
(check-sat)
"#;
    let result = solve(smt);
    let ay = crate::common::sat_result(&result);
    assert!(
        matches!(ay, Some("sat") | Some("unknown")),
        "str.at(x,0)=\"h\" + len(x)=5 must not be unsat; got {ay:?}"
    );
}
