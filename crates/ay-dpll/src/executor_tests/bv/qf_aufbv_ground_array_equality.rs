// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A QF_AUFBV model evaluates ground array (dis)equalities exactly
//! (#aufbv-const-array-equality, `model/eval_array/ground_equality.rs`).
//!
//! Before, the BV-lane guard made every normalized mismatch Unknown, so the
//! solver's own `distinct_const_array` axiom failed model validation (the w37
//! fuzz file f035) and `get-value` refused these terms. A full write coverage
//! of a finite index sort makes the defaults irrelevant: z3's solver agrees
//! (`unsat` for the covered disequality below), although z3 5.1.0's
//! `get-value` prints `false` for it.

use super::*;

fn run(input: &str) -> Vec<String> {
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("invariant: execute succeeds")
}

const MODEL: &str = r#"
    (set-logic QF_AUFBV)
    (set-option :produce-models true)
    (declare-const x (_ BitVec 8))
    (declare-const a (Array (_ BitVec 8) Bool))
    (assert (select a x))
    (assert (= x #x05))
    (check-sat)
"#;

/// The single `get-value` answer for `term`, which must be a value.
fn value_of(term: &str) -> String {
    let out = run(&format!("{MODEL} (get-value ({term}))"));
    assert_eq!(out.len(), 2, "{out:?}");
    assert_eq!(out[0], "sat");
    let answer = out[1].trim();
    assert!(!answer.starts_with("(error"), "{answer}");
    if answer.ends_with(" true))") {
        "true".to_string()
    } else if answer.ends_with(" false))") {
        "false".to_string()
    } else {
        panic!("not a Bool value: {answer}")
    }
}

#[test]
fn test_const_arrays_with_distinct_defaults_differ() {
    let term = "(= ((as const (Array (_ BitVec 32) Bool)) true) \
                ((as const (Array (_ BitVec 32) Bool)) false))";
    assert_eq!(value_of(term), "false");
}

#[test]
fn test_writes_covering_a_bv1_index_sort_equal_the_const_array() {
    let covered =
        "(= (store (store ((as const (Array (_ BitVec 1) Bool)) false) #b0 true) #b1 true) \
                   ((as const (Array (_ BitVec 1) Bool)) true))";
    let half = "(= (store ((as const (Array (_ BitVec 1) Bool)) false) #b0 true) \
                ((as const (Array (_ BitVec 1) Bool)) true))";
    assert_eq!(value_of(covered), "true");
    assert_eq!(value_of(half), "false");
}

#[test]
fn test_a_store_at_a_scalar_index_reads_the_model_value() {
    let same = "(= (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) x #x01) \
                (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) #x05 #x01))";
    let other = "(= (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) x #x01) \
                 (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x00) #x06 #x01))";
    assert_eq!(value_of(same), "true");
    assert_eq!(value_of(other), "false");
}

#[test]
fn test_the_covered_disequality_is_unsat() {
    let input = r#"
        (set-logic QF_AUFBV)
        (assert (not (= (store (store ((as const (Array (_ BitVec 1) Bool)) false) #b0 true) #b1 true)
                        ((as const (Array (_ BitVec 1) Bool)) true))))
        (check-sat)
    "#;
    assert_eq!(run(input), vec!["unsat"]);
}
