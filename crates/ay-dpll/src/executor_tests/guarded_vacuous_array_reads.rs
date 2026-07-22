// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the guarded-VACUOUS-read array model gap
//! (#guarded-vacuous-array-read, deductive-checks cluster "model value for array X is
//! not available").
//!
//! Shape: a `(select ar i)` read occurs ONLY under an implication/disjunct the
//! SAT assignment satisfies vacuously (guard false), so the read literal never
//! reaches the array/BV theory and evaluates to Unknown in the extracted
//! model. The audit-hardened completion (0bd4fda960) deliberately refused to
//! default such an array (the read is an ACTIVE observation), which made the
//! ENTIRE `(get-model)` / `(get-value)` answer collapse to
//! `(error "model value for array ar is not available")` even though check-sat
//! answered `sat` and the validation gates confirmed the model — demoting
//! every downstream counterexample (deductive-checks) to Unknown.
//!
//! The fix is a SECOND, GATE-VERIFIED completion pass
//! (`complete_array_models_for_validation`): candidates skip the
//! Unknown-VALUED active reads (an Unknown INDEX still fails closed), are
//! committed, and are accepted only if the strict oracles + independent gate
//! re-confirm the completed model; any refutation retracts to the fail-closed
//! partial model. So these tests must see a full, valid witness — and the
//! constrained-read test below must still see the solver-pinned value, never a
//! skipped/defaulted one.

use crate::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn run(input: &str) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute succeeds");
    (exec, outputs)
}

/// The minimal deductive-checks regression shape: BV-element array with one guarded
/// read whose guard is falsified by the model. `(get-model)` must print a
/// full model containing `ar` — not the whole-model error.
#[test]
#[timeout(60000)]
fn bv_array_guarded_vacuous_read_prints_full_model() {
    let (_exec, outputs) = run(r#"
        (set-option :produce-models true)
        (set-logic ALL)
        (declare-const ar (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-const x (_ BitVec 8))
        (assert (=> (= x (_ bv0 8)) (= (select ar (_ bv0 64)) (_ bv5 8))))
        (assert (= x (_ bv1 8)))
        (check-sat)
        (get-model)
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    assert!(
        !model.contains("error"),
        "guarded vacuous read must not poison the model: {model}"
    );
    assert!(
        model.contains("(define-fun ar () (Array (_ BitVec 64) (_ BitVec 8))"),
        "model must contain the array witness: {model}"
    );
    assert!(
        model.contains("(define-fun x () (_ BitVec 8) #x01)"),
        "model must contain the scalar witness: {model}"
    );
}

/// Same shape through `(get-value)`: both the whole array and the vacuous
/// `select` cell must answer from the committed, gate-verified witness.
#[test]
#[timeout(60000)]
fn bv_array_guarded_vacuous_read_answers_get_value() {
    let (_exec, outputs) = run(r#"
        (set-option :produce-models true)
        (set-logic ALL)
        (declare-const ar (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-const x (_ BitVec 8))
        (assert (=> (= x (_ bv0 8)) (= (select ar (_ bv0 64)) (_ bv5 8))))
        (assert (= x (_ bv1 8)))
        (check-sat)
        (get-value (ar))
        (get-value ((select ar (_ bv0 64))))
    "#);
    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].starts_with("((ar ") && !outputs[1].contains("error"),
        "whole-array get-value must answer: {}",
        outputs[1]
    );
    assert!(
        !outputs[2].contains("error"),
        "vacuous cell get-value must answer from the committed default: {}",
        outputs[2]
    );
}

/// Nested (Array BV64 (Array BV64 BV64)) variant — the deductive-checks nested
/// fixed-array encoding. Both `(get-model)` and `(get-value)` must produce the
/// nested witness.
#[test]
#[timeout(60000)]
fn nested_bv_array_guarded_vacuous_read_prints_full_model() {
    let (_exec, outputs) = run(r#"
        (set-option :produce-models true)
        (set-logic ALL)
        (declare-const m (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))))
        (declare-const x (_ BitVec 8))
        (assert (=> (= x (_ bv0 8))
                    (= (select (select m (_ bv1 64)) (_ bv0 64)) (_ bv5 64))))
        (assert (= x (_ bv1 8)))
        (check-sat)
        (get-model)
        (get-value (m))
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    assert!(
        !model.contains("error"),
        "nested guarded vacuous read must not poison the model: {model}"
    );
    assert!(
        model
            .contains("(define-fun m () (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))"),
        "model must contain the nested array witness: {model}"
    );
    assert!(
        outputs[2].starts_with("((m ") && !outputs[2].contains("error"),
        "nested whole-array get-value must answer: {}",
        outputs[2]
    );
}

/// Control: an ACTIVE (guard-true) constrained read must keep the
/// solver-pinned cell value in the printed witness — the skip semantics are
/// candidate-building only and must never drop a real constraint.
#[test]
#[timeout(60000)]
fn bv_array_active_constrained_read_keeps_pinned_value() {
    let (_exec, outputs) = run(r#"
        (set-option :produce-models true)
        (set-logic ALL)
        (declare-const ar (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-const x (_ BitVec 8))
        (assert (=> (= x (_ bv1 8)) (= (select ar (_ bv0 64)) (_ bv5 8))))
        (assert (= x (_ bv1 8)))
        (check-sat)
        (get-model)
        (get-value ((select ar (_ bv0 64))))
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    assert!(!model.contains("error"), "{model}");
    assert!(
        model.contains("#x05"),
        "the constrained cell value must appear in the witness: {model}"
    );
    assert_eq!(outputs[2], "(((select ar (_ bv0 64)) #x05))");
}

/// Int-element control (never regressed): the arithmetic model assigns the
/// vacuous read, and the completed model still prints.
#[test]
#[timeout(60000)]
fn int_array_guarded_vacuous_read_prints_full_model() {
    let (_exec, outputs) = run(r#"
        (set-option :produce-models true)
        (set-logic ALL)
        (declare-const ar (Array Int Int))
        (declare-const x Int)
        (assert (=> (= x 0) (= (select ar 0) 5)))
        (assert (= x 1))
        (check-sat)
        (get-model)
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    assert!(!model.contains("error"), "{model}");
    assert!(
        model.contains("(define-fun ar () (Array Int Int)"),
        "{model}"
    );
}

/// The deductive-checks ground-seed shape: a flat array constant DEFINED by an
/// array-valued `select` cell of a nested array (`(= (select m 0) seed)`).
/// The first-pass definition fixpoint cannot interpret the select RHS, so the
/// gate-verified pass must resolve the definition with the skip-mode candidate
/// builder — both `m` and `seed` must print, consistently.
#[test]
#[timeout(60000)]
fn array_valued_select_defined_seed_constant_prints() {
    let (_exec, outputs) = run(r#"
        (set-option :produce-models true)
        (set-logic ALL)
        (declare-const seed (Array (_ BitVec 64) (_ BitVec 64)))
        (declare-const m (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64))))
        (declare-const len Int)
        (assert (= len 0))
        (assert (= (select m #x0000000000000000) seed))
        (assert (= 1 (+ len 1)))
        (check-sat)
        (get-model)
    "#);
    assert_eq!(outputs[0], "sat");
    let model = &outputs[1];
    assert!(
        !model.contains("error"),
        "select-defined seed constant must not poison the model: {model}"
    );
    assert!(
        model.contains("(define-fun seed () (Array (_ BitVec 64) (_ BitVec 64))"),
        "model must contain the seed witness: {model}"
    );
    assert!(
        model
            .contains("(define-fun m () (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 64)))"),
        "model must contain the nested array witness: {model}"
    );
}
