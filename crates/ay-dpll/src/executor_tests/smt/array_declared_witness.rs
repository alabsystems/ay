// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Declared-array witness availability (#array-decl-default-witness).
//!
//! A consumer that declares an array-sorted constant must be able to read its
//! value out of `(get-model)` whenever `check-sat` answered `sat` — including
//! when the query never actually constrains a single cell.  The deductive-checks
//! zero-length-array counterexample regressed exactly here: ground
//! instantiation schemas (`(=> (= len k) (= r (select a k)))` for every k)
//! keep `select` terms in the assertion tree even when the model falsifies
//! every guard, and treating those dead reads as required observations left
//! the declared array permanently partial — `(get-model)` then answered
//! `(error "model value for array a is not available")` for a genuinely SAT,
//! genuinely unconstrained array.

use super::*;

fn run_sat_model(input: &str) -> Vec<String> {
    let commands = parse(input).expect("parse declared-array witness script");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execute declared-array witness script");
    assert_eq!(outputs[0], "sat", "expected sat, got {outputs:?}");
    outputs
}

fn assert_model_defines(outputs: &[String], arrays: &[&str]) {
    assert_eq!(outputs.len(), 2, "expected [sat, model], got {outputs:?}");
    let model = &outputs[1];
    assert!(
        !model.contains("(error"),
        "every declared array value must be available in the model, got: {model}"
    );
    for name in arrays {
        assert!(
            model.contains(&format!("define-fun {name} ")),
            "expected `{name}` in model output, got: {model}"
        );
    }
}

/// deductive-checks `array_to_slice_view_wrong_len_counterexample` reduction
/// (the development design notes): guarded per-index
/// equalities between two declared arrays, all guards live for len == 3.
/// Both arrays must render as total witnesses.
#[test]
fn arr_repro_all_declared_arrays_available() {
    let input = r#"
        (set-logic ALL)
        (set-option :produce-models true)
        (declare-const ar (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-const sl (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-const len_ar Int)
        (declare-const len_sl Int)
        (declare-const seed_ar (_ BitVec 8))
        (declare-const seed_sl (_ BitVec 8))
        (assert (<= 0 len_ar))
        (assert (= len_ar 3))
        (assert (<= 0 len_sl))
        (assert (and (= len_ar len_sl)
          (or (= (select sl #x0000000000000000) (select ar #x0000000000000000)) (not (< 0 len_sl)))
          (or (= (select sl #x0000000000000001) (select ar #x0000000000000001)) (not (< 1 len_sl)))
          (or (= (select sl #x0000000000000002) (select ar #x0000000000000002)) (not (< 2 len_sl)))
          (or (= (select sl #x0000000000000003) (select ar #x0000000000000003)) (not (< 3 len_sl)))
          (or (= (select sl #x0000000000000004) (select ar #x0000000000000004)) (not (< 4 len_sl)))
          (or (= (select sl #x0000000000000005) (select ar #x0000000000000005)) (not (< 5 len_sl)))
          (or (= (select sl #x0000000000000006) (select ar #x0000000000000006)) (not (< 6 len_sl)))
          (or (= (select sl #x0000000000000007) (select ar #x0000000000000007)) (not (< 7 len_sl)))))
        (assert (= (select ar #x0000000000000000) seed_ar))
        (assert (= (select sl #x0000000000000000) seed_sl))
        (assert (not (= len_sl 4)))
        (check-sat)
        (get-model)
    "#;
    let outputs = run_sat_model(input);
    assert_model_defines(&outputs, &["ar", "sl"]);
}

/// deductive-checks `zero_length_native_array_last_fails_closed` reduction: a
/// declared `[u8; 0]` array whose only reads sit under per-length guards the
/// model falsifies (`len == 0`).  Zero active observations means the
/// canonical default is a genuine witness; the declared array must still
/// render.
#[test]
fn zero_length_guarded_reads_array_available() {
    let input = r#"
        (set-logic ALL)
        (set-option :produce-models true)
        (declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-const len Int)
        (declare-const result (_ BitVec 8))
        (assert (= len 0))
        (assert (=> (= len 1) (= result (select a #x0000000000000000))))
        (assert (=> (= len 2) (= result (select a #x0000000000000001))))
        (assert (=> (= len 3) (= result (select a #x0000000000000002))))
        (assert (=> (= len 4) (= result (select a #x0000000000000003))))
        (assert (=> (= len 5) (= result (select a #x0000000000000004))))
        (assert (=> (= len 6) (= result (select a #x0000000000000005))))
        (assert (=> (= len 7) (= result (select a #x0000000000000006))))
        (assert (=> (= len 8) (= result (select a #x0000000000000007))))
        (assert (not (<= 1 len)))
        (check-sat)
        (get-model)
    "#;
    let outputs = run_sat_model(input);
    assert_model_defines(&outputs, &["a"]);
}

/// Zero-length shape twin: declare an array, never store/select it at all,
/// assert something unrelated.  `sat` + `(get-model)` must still render the
/// array (canonical default, no stores).
#[test]
fn declared_untouched_array_available() {
    let input = r#"
        (set-logic ALL)
        (set-option :produce-models true)
        (declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-const len Int)
        (assert (= len 0))
        (assert (<= 0 len))
        (check-sat)
        (get-model)
    "#;
    let outputs = run_sat_model(input);
    assert_model_defines(&outputs, &["a"]);
}

/// EUF-alias twin: an aliased pair `(= a b)` where the only reads are dead
/// guarded reads of `a`.  The alias component must stay consistent — both
/// arrays render, and through the same completion component (no divergent
/// defaults).
#[test]
fn declared_alias_with_dead_reads_consistent() {
    let input = r#"
        (set-logic ALL)
        (set-option :produce-models true)
        (declare-const a (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-const b (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-const len Int)
        (declare-const result (_ BitVec 8))
        (assert (= a b))
        (assert (= len 0))
        (assert (=> (= len 1) (= result (select a #x0000000000000000))))
        (assert (not (<= 1 len)))
        (check-sat)
        (get-value ((= a b)))
        (get-model)
    "#;
    let commands = parse(input).expect("parse alias witness script");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execute alias witness script");
    assert_eq!(outputs[0], "sat", "expected sat, got {outputs:?}");
    assert_eq!(
        outputs.len(),
        3,
        "expected [sat, value, model], got {outputs:?}"
    );
    assert!(
        outputs[1].contains("true"),
        "aliased arrays must agree under get-value, got: {}",
        outputs[1]
    );
    let model = &outputs[2];
    assert!(
        !model.contains("(error"),
        "aliased declared arrays must both be available, got: {model}"
    );
    for name in ["a", "b"] {
        assert!(
            model.contains(&format!("define-fun {name} ")),
            "expected `{name}` in model output, got: {model}"
        );
    }
}
