// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #no-fabricated-model-values: a value that is GENUINELY missing at print
//! time is an explicit `(error ...)` — never a fabricated sort default. The
//! removed `format_value` fabricator printed `""`/`0`/all-zeros/... for ANY
//! sort whose evaluation came back Unknown, directly into user-visible
//! `(get-model)` / `(get-value)` output — a lie that could contradict the
//! asserted formula.

use super::*;
use ay_frontend::parse;

/// Solve a string constraint, then synthetically strip every string value and
/// the completion slot from the model. The printer must surface an explicit
/// error for the missing value — the pre-fix fabricator printed `s ""` here,
/// contradicting the asserted `(= s "abc")`.
#[test]
fn missing_model_value_is_an_explicit_error_not_a_default() {
    let commands = parse(
        r#"
        (set-option :produce-models true)
        (set-logic QF_S)
        (declare-const s String)
        (assert (= s "abc"))
        (check-sat)
    "#,
    )
    .expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute succeeds");
    assert_eq!(outputs[0], "sat");

    // Corrupt the witness: remove every string value AND the completion slot.
    let model = exec.last_model.as_mut().expect("model exists");
    if let Some(sm) = model.string_model.as_mut() {
        sm.values.clear();
    }
    model.completed_values.clear();
    eval_memo_clear();

    let printed = exec.model();
    assert!(
        printed.starts_with("(error"),
        "a missing value must surface as an error, got: {printed}"
    );
    assert!(
        !printed.contains("\"\""),
        "the empty-string fabrication must be gone: {printed}"
    );
}

/// A deliberately-partial array interpretation cannot be turned into a total
/// const array by the printer.  In particular, `read_conflicted` remains
/// poison even if a stale default was present before the conflicting cell was
/// dropped.
#[test]
fn read_conflicted_array_output_is_an_explicit_error_not_a_const_default() {
    let commands = parse(
        r#"
        (set-option :produce-models true)
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (assert (= (select a 0) 1))
        (check-sat)
    "#,
    )
    .expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute succeeds");
    assert_eq!(outputs[0], "sat");

    let a = exec
        .ctx
        .terms
        .mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let model = exec.last_model.as_mut().expect("model exists");
    let arrays = model.array_model.get_or_insert_with(Default::default);
    let interp = arrays.array_values.entry(a).or_default();
    interp.default = Some("0".to_string());
    interp.index_sort = Some(Sort::Int);
    interp.element_sort = Some(Sort::Int);
    arrays.read_conflicted.insert(a);
    eval_memo_clear();

    let printed = exec.model();
    assert!(
        printed.starts_with("(error"),
        "a read-conflicted array must fail closed, got: {printed}"
    );
    assert!(
        !printed.contains("((as const (Array Int Int)) 0)"),
        "the stale default must not total the conflicted array: {printed}"
    );
}
