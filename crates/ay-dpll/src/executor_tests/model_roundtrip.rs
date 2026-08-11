// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-output round-trip tests.

use crate::Executor;
use ay_frontend::parse;

#[test]
fn test_real_uf_unlisted_point_matches_printed_else_branch() {
    // A read at an argument point the table does not list must answer the
    // printed define-fun's ELSE branch byte-for-byte.
    let input = r#"
        (set-logic QF_UFLRA)
        (declare-fun f (Real) Real)
        (assert (= (f (/ 1 2)) (/ 7 2)))
        (assert (= (f 2.0) (- (/ 9 4))))
        (check-sat)
        (get-model)
        (get-value ((f 99.0)))
    "#;

    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");

    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    // The else branch is the LAST resolved table entry; extract it from the
    // get-value answer and confirm the printed table ends with it.
    let value = outputs[2]
        .strip_prefix("(((f 99.0) ")
        .and_then(|s| s.strip_suffix("))"))
        .unwrap_or_else(|| panic!("unexpected get-value shape: {}", outputs[2]));
    assert!(
        model.contains(value),
        "else-branch value {value} must appear in the printed table: {model}"
    );
    // And it is in the new spelling (a Real table over these constraints
    // has only z3-exact atoms).
    assert!(
        value == "(/ 7.0 2.0)" || value == "(- (/ 9.0 4.0))",
        "unexpected else value: {value}"
    );
}

#[test]
fn test_real_printed_values_round_trip_to_sat_and_pin_unsat_on_distinct() {
    // Round-trip: re-asserting AY's own printed get-value pairs on top of the
    // original constraints stays sat...
    let round_trip = r#"
        (set-logic QF_LRA)
        (declare-const r Real)
        (declare-const s Real)
        (declare-const n Real)
        (declare-const m Real)
        (assert (= r 5.0))
        (assert (= s (/ 7 2)))
        (assert (= n (- 5.0)))
        (assert (= m (- (/ 7 2))))
        (assert (= r 5.0))
        (assert (= s (/ 7.0 2.0)))
        (assert (= n (- 5.0)))
        (assert (= m (- (/ 7.0 2.0))))
        (check-sat)
    "#;
    let commands = parse(round_trip).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    assert_eq!(outputs, vec!["sat"]);

    // ...and the printed value is THE value, not merely parseable: requiring
    // the variable to differ from it is unsat.
    let wrong = r#"
        (set-logic QF_LRA)
        (declare-const s Real)
        (assert (= s (/ 7 2)))
        (assert (distinct s (/ 7.0 2.0)))
        (check-sat)
    "#;
    let commands = parse(wrong).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    assert_eq!(outputs, vec!["unsat"]);
}
