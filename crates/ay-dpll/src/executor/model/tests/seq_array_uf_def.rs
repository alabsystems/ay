// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #seq-array-uf-def: an equality between an array constructor and an OPAQUE
//! array-valued UF application, asserted as a `check-sat-assuming` assumption,
//! must validate as a genuine `sat` — not degrade to `unknown`.
//!
//! ROOT CAUSE — verification-consumer's Seq encoding carries a Seq-sorted value's backing
//! array through a plain UF `seq_array : Seq -> (Array Int Int)`, and its
//! base-consistency check passes premises like
//! `(= (const-array 0) (seq_array v))` as assumptions. The model evaluator had
//! no value for the opaque application (the array solver materializes no entry
//! when no select constrains it), so the equality evaluated to `Unknown`; the
//! `SmtAssumption` validation boundary has no array-theory delegation
//! carve-out (deliberately — assumptions must validate independently), so a
//! genuine `sat` degraded to `unknown` on verification-consumer index_range / Seq-heavy
//! base checks (rank-15 #3).
//!
//! FIX — `normalize_array_with_definitions` resolves an opaque array-valued
//! UF application through its asserted/assumed definitional equality, exactly
//! like a bare array variable (with the same visited-set cycle guard), plus a
//! CONGRUENCE guard: if another definitional equality binds the same function
//! symbol at argument values the model cannot distinguish to a DIFFERENT
//! concrete array, resolution refuses and validation stays degraded
//! (fail-closed). The validation gate remains the sole acceptance judge.

use super::*;
use ay_frontend::parse;

fn solve_all(input: &str) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute succeeds");
    (exec, outputs)
}

fn solve(input: &str) -> (Executor, String) {
    let (exec, outputs) = solve_all(input);
    let verdict = outputs.into_iter().next().expect("a check-sat verdict");
    (exec, verdict)
}

const SEQ_HEADER: &str = r#"
(set-logic ALL)
(declare-sort Seq 0)
(declare-fun v () Seq)
(declare-fun seq_array (Seq) (Array Int Int))
"#;

/// The pinned verification-consumer shape: the assumption
/// `(= (const-array 0) (seq_array v))` alone is trivially satisfiable and must
/// answer `sat` (was `unknown`: the assumption evaluated to Unknown and the
/// SmtAssumption boundary fail-closed).
#[test]
fn seq_array_const_array_assumption_is_sat() {
    let input = format!(
        "{SEQ_HEADER}\
         (check-sat-assuming ((= ((as const (Array Int Int)) 0) (seq_array v))))"
    );
    let (_exec, verdict) = solve(&input);
    assert_eq!(
        verdict, "sat",
        "a definitional const-array assumption over an opaque array UF app is \
         trivially satisfiable"
    );
}

/// The same shape with surrounding array-store context (mirrors the live
/// verification-consumer base-consistency VC more closely).
#[test]
fn seq_array_assumption_with_store_context_is_sat() {
    let input = format!(
        "{SEQ_HEADER}\
         (declare-fun a () (Array Int Int))\
         (assert (= a (store (seq_array v) 0 5)))\
         (check-sat-assuming ((= ((as const (Array Int Int)) 0) (seq_array v))))"
    );
    let (_exec, verdict) = solve(&input);
    assert_eq!(verdict, "sat");
}

/// SOUNDNESS: two CONFLICTING definitions of the same opaque app must never
/// validate as `sat` (the set is UNSAT: const-array 0 != const-array 1).
#[test]
fn seq_array_conflicting_definitions_never_sat() {
    let input = format!(
        "{SEQ_HEADER}\
         (check-sat-assuming (\
            (= ((as const (Array Int Int)) 0) (seq_array v)) \
            (= ((as const (Array Int Int)) 1) (seq_array v))))"
    );
    let (_exec, verdict) = solve(&input);
    assert_ne!(verdict, "sat", "conflicting definitions are jointly UNSAT");
}

/// SOUNDNESS (congruence): `v = w` forces `seq_array(v) = seq_array(w)`, so
/// binding them to DIFFERENT const-arrays is jointly UNSAT and must never
/// validate as `sat`. This is the exact hazard the congruence guard in
/// `opaque_app_congruent_definitions_agree` fail-closes if the solver ever
/// wrongly reported Sat.
#[test]
fn seq_array_congruent_apps_with_different_definitions_never_sat() {
    let input = format!(
        "{SEQ_HEADER}\
         (declare-fun w () Seq)\
         (assert (= v w))\
         (check-sat-assuming (\
            (= ((as const (Array Int Int)) 0) (seq_array v)) \
            (= ((as const (Array Int Int)) 1) (seq_array w))))"
    );
    let (_exec, verdict) = solve(&input);
    assert_ne!(
        verdict, "sat",
        "congruence makes the definitions jointly UNSAT"
    );
}

/// SOUNDNESS (point-fact conflict): an asserted select fact that contradicts
/// the definitional const-array must never validate as `sat`
/// (`select(const-array 0, 3) = 0 != 7`).
#[test]
fn seq_array_definition_conflicting_point_fact_never_sat() {
    let input = format!(
        "{SEQ_HEADER}\
         (assert (= (select (seq_array v) 3) 7))\
         (check-sat-assuming ((= ((as const (Array Int Int)) 0) (seq_array v))))"
    );
    let (_exec, verdict) = solve(&input);
    assert_ne!(verdict, "sat", "the point fact contradicts the definition");
}

/// Direct evaluator pin: with the definitional assumption active, the
/// equality itself must evaluate to Bool(true) under the emitted model — the
/// resolution is genuine evaluation evidence, not a delegation/skip.
#[test]
fn seq_array_definition_equality_evaluates_true_under_model() {
    let input = format!(
        "{SEQ_HEADER}\
         (check-sat-assuming ((= ((as const (Array Int Int)) 0) (seq_array v))))"
    );
    let (exec, verdict) = solve(&input);
    assert_eq!(verdict, "sat");
    let model = exec.last_model.as_ref().expect("sat retains its model");
    let assumption = exec
        .last_assumptions
        .as_ref()
        .and_then(|a| a.first().copied())
        .expect("the assumption is recorded");
    eval_memo_clear();
    assert!(
        matches!(exec.evaluate_term(model, assumption), EvalValue::Bool(true)),
        "the definitional equality must ground-evaluate to true under the model"
    );
}
