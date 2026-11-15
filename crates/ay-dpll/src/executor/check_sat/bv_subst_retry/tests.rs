// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #abv-subst-model-retry arming. Each `sat` query below was `unknown` before
//! the arm read every gate rejection, and today only the preprocessing-free
//! re-solve answers it. The first model of the Bool-UF queries is rejected as
//! `incomplete`, not refuted: a substituted Bool proxy, or a substituted Bool
//! variable whose right-hand side, a Bool uninterpreted application, the solve
//! never assigned. The first model of the cannot-confirm query is withheld by
//! the independent gate, so no validation-pipeline counter moves.
//!
//! The tests named after the arming pin the re-solve stat. The Bool-UF tests
//! pin only the verdict, so closing the purification gap at its source, which
//! would answer them without a second solve, keeps them green.
//!
//! The `unsat` checks are soundness sanity checks of the same shapes. The
//! first solve already decides them, so they never reach the re-solve.
//! Over-arming is pinned by the predicate tests at the end: lane scoping,
//! timeout, deadline, latch and evaluation stops.

use crate::executor_types::{SolveResult, UnknownOrigin, UnknownReason};
use crate::Executor;
use ay_frontend::parse;

const RETRY_STAT: &str = "model_validation.bv.subst_retry";

/// Run `input`, returning the outputs and whether the re-solve ran.
fn run(input: &str) -> (Vec<String>, Option<u64>) {
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let out = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    (out, exec.statistics().get_int(RETRY_STAT))
}

/// fzN1 q8811_118. The base model was refuted by the arrays oracle, which armed
/// the retry, and the retry answered `sat`. With the store-chain model the
/// first rejection is `(h boolarg_13) evaluates to Unknown`, which did not arm
/// it.
const Q8811_118: &str = r#"
    (set-logic QF_AUFBV)
    (declare-const a (Array (_ BitVec 4) Bool))
    (declare-const b (Array (_ BitVec 4) Bool))
    (declare-const c (Array (_ BitVec 4) Bool))
    (declare-const d (Array (_ BitVec 4) Bool))
    (declare-const e (Array (_ BitVec 4) Bool))
    (declare-const u (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const w (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const z (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const p Bool)
    (declare-const q Bool)
    (declare-const x (_ BitVec 4))
    (declare-const y (_ BitVec 4))
    (declare-const v (_ BitVec 3))
    (declare-fun f ((_ BitVec 4)) Bool)
    (declare-fun g ((_ BitVec 4)) (_ BitVec 3))
    (declare-fun h (Bool) Bool)
    (declare-fun k ((_ BitVec 3)) (_ BitVec 4))
    (assert (and (not (select c (_ bv8 4)))
                 (h (= (store ((as const (Array (_ BitVec 4) (_ BitVec 3))) (_ bv1 3)) (_ bv14 4) v) w))))
    (assert (and (not (= v (_ bv3 3))) (select e (bvadd x (_ bv1 4)))
                 (=> (not (select a (_ bv3 4)))
                     (= w ((as const (Array (_ BitVec 4) (_ BitVec 3))) (g (ite p x y)))))))
    (assert (not (= w u)))
    (assert (not p))
    (assert (= c e))
"#;

#[test]
fn incomplete_rejection_of_store_chain_model_arms_the_retry() {
    let (out, retry) = run(&format!(
        "{Q8811_118} (check-sat) (get-value ((select e (bvadd x (_ bv1 4)))))"
    ));
    assert_eq!(out[0], "sat", "{out:?}");
    assert_eq!(out[1], "(((select e (bvadd x (_ bv1 4))) true))", "{out:?}");
    assert_eq!(retry, Some(1), "{out:?}");
}

#[test]
fn store_chain_query_with_contradicted_proxy_argument_is_unsat() {
    let (out, _) = run(&format!(
        "{Q8811_118} (assert (not (h true))) (assert (not (h false))) (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

/// The independent gate cannot confirm the substitution-lane model (`model does
/// not pin this leaf: w`). Only the gate-downgrade funnel arms this retry: no
/// validation-pipeline counter moves (fzG1 g060; also fzN1 q8811_050, fzG1
/// g196, fzC q7303_035 and q7303_207).
const CANNOT_CONFIRM: &str = r#"
    (set-logic QF_AUFBV)
    (declare-const w (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const x (_ BitVec 4))
    (declare-fun g ((_ BitVec 4)) (_ BitVec 3))
    (assert (= w (store ((as const (Array (_ BitVec 4) (_ BitVec 3))) (g x)) x (_ bv0 3))))
"#;

#[test]
fn cannot_confirm_of_substitution_lane_model_arms_the_retry() {
    let (out, retry) = run(&format!(
        "{CANNOT_CONFIRM} (check-sat) (get-value ((select w x)))"
    ));
    assert_eq!(out[0], "sat", "{out:?}");
    assert_eq!(out[1], "(((select w x) #b000))", "{out:?}");
    assert_eq!(retry, Some(1), "{out:?}");
}

#[test]
fn cannot_confirm_query_with_contradicted_store_is_unsat() {
    let (out, _) = run(&format!(
        "{CANNOT_CONFIRM} (assert (not (= (select w x) (_ bv0 3)))) (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

/// `b := (f x)` empties the formula, so the solve never assigns `(f x)`.
const DEFINITION_ONLY: &str = r#"
    (set-logic QF_UFBV)
    (declare-fun f ((_ BitVec 8)) Bool)
    (declare-const x (_ BitVec 8))
    (declare-const b Bool)
    (assert (= b (f x)))
"#;

#[test]
fn bool_application_eliminated_by_substitution_is_sat() {
    let (out, _) = run(&format!(
        "{DEFINITION_ONLY} (check-sat) (get-value ((= b (f x))))"
    ));
    assert_eq!(out[0], "sat", "{out:?}");
    assert_eq!(out[1], "(((= b (f x)) true))", "{out:?}");
}

#[test]
fn bool_application_eliminated_by_substitution_contradiction_is_unsat() {
    let (out, _) = run(&format!(
        "{DEFINITION_ONLY} (assert b) (assert (not (f x))) (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

/// The purified proxy of `(g (f x))` is substituted back, so `(f x)` is only
/// an argument (`u4` of the store-chain final).
const PROXY_ARGUMENT: &str = r#"
    (set-logic QF_UFBV)
    (declare-fun f ((_ BitVec 8)) Bool)
    (declare-fun g (Bool) Bool)
    (declare-const x (_ BitVec 8))
    (declare-const p Bool)
    (assert (and p (g (f x))))
"#;

#[test]
fn bool_argument_of_bool_application_is_sat() {
    let (out, _) = run(&format!(
        "{PROXY_ARGUMENT} (check-sat) (get-value ((g (f x))))"
    ));
    assert_eq!(out[0], "sat", "{out:?}");
    assert_eq!(out[1], "(((g (f x)) true))", "{out:?}");
}

#[test]
fn bool_argument_of_bool_application_contradiction_is_unsat() {
    let (out, _) = run(&format!(
        "{PROXY_ARGUMENT} (assert (not (g true))) (assert (not (g false))) (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

/// The constant array's element is the purified `(f x)`; `c` and the proxy are
/// both substituted away (`u1` of the store-chain final).
const CONST_ARRAY_ELEMENT: &str = r#"
    (set-logic QF_AUFBV)
    (declare-fun f ((_ BitVec 8)) Bool)
    (declare-const x (_ BitVec 8))
    (declare-const c (Array (_ BitVec 32) Bool))
    (assert (= c ((as const (Array (_ BitVec 32) Bool)) (f x))))
"#;

#[test]
fn bool_application_as_constant_array_element_is_sat() {
    let (out, _) = run(&format!(
        "{CONST_ARRAY_ELEMENT} (assert (= (select c #x00000003) (f x))) (check-sat)"
    ));
    assert_eq!(out, vec!["sat"]);
}

#[test]
fn bool_application_as_constant_array_element_contradiction_is_unsat() {
    let (out, _) = run(&format!(
        "{CONST_ARRAY_ELEMENT} (assert (not (= (select c #x00000003) (f x)))) (check-sat)"
    ));
    assert_eq!(out, vec!["unsat"]);
}

/// Performance pin: a substitution-lane model the gates accept the first time
/// never pays for the re-solve. It cannot catch over-arming, since the arm
/// needs an `unknown` first answer; the predicate tests below do.
#[test]
fn accepted_substitution_lane_model_does_not_retry() {
    let (out, retry) = run(&format!("{DEFINITION_ONLY} (assert b) (check-sat)"));
    assert_eq!(out, vec!["sat"]);
    assert_eq!(retry, None);
}

/// The arming predicate on its own: a validation failure arms the re-solve
/// only for a substitution-lane solve, and never after a timeout, the latch
/// or the deadline.
#[test]
fn validation_failure_arms_only_the_substitution_lane() {
    let mut exec = Executor::new();
    exec.last_statistics.model_validation_failures = 1;
    exec.last_unknown_reason = Some(UnknownReason::Incomplete);
    assert!(!exec.bv_subst_retry_armed(&SolveResult::Unknown));
    exec.bv_subst_lane = true;
    assert!(exec.bv_subst_retry_armed(&SolveResult::Unknown));
    assert!(!exec.bv_subst_retry_armed(&SolveResult::Sat));
    exec.last_unknown_reason = Some(UnknownReason::Timeout);
    assert!(!exec.bv_subst_retry_armed(&SolveResult::Unknown));
    exec.last_unknown_reason = Some(UnknownReason::Incomplete);
    exec.bv_subst_retry_done = true;
    assert!(!exec.bv_subst_retry_armed(&SolveResult::Unknown));
    exec.bv_subst_retry_done = false;
    assert!(exec.bv_subst_retry_armed(&SolveResult::Unknown));
    exec.solve_deadline.set(Some(ay_core::time::Instant::now()));
    assert!(!exec.bv_subst_retry_armed(&SolveResult::Unknown));
}

/// Every gate downgrade of a substitution-lane model arms the re-solve, and a
/// downgrade on any other lane does not.
#[test]
fn gate_downgrade_arms_only_the_substitution_lane() {
    let mut exec = Executor::new();
    exec.downgrade_sat_after_gate("cannot confirm");
    assert!(!exec.bv_subst_model_rejected);
    exec.bv_subst_lane = true;
    exec.downgrade_sat_after_gate("cannot confirm");
    assert!(exec.bv_subst_model_rejected);
    assert!(exec.bv_subst_retry_armed(&SolveResult::Unknown));
}

/// A downgrade that publishes an evaluation stop (memory, interrupt) is not a
/// rejection of the model, so it never arms the re-solve.
#[test]
fn gate_downgrade_after_evaluation_stop_does_not_arm() {
    let mut exec = Executor::new();
    exec.bv_subst_lane = true;
    let _read = exec.begin_external_evaluation_read();
    exec.record_evaluation_stop(UnknownOrigin::MemoryBudget);
    exec.downgrade_sat_after_gate("cannot confirm");
    assert!(!exec.bv_subst_model_rejected);
}
