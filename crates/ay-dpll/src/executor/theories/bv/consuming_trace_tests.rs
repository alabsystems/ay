// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The actual fresh BV search route; SAT replay is not SMT source authority.

use super::*;
use ay_frontend::parse;

fn fixture(extra: &str) -> Executor {
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    let source = format!(
        "(set-logic QF_BV)
         (declare-const x (_ BitVec 2))
         (declare-const y (_ BitVec 2))
         (assert (bvult x y))
         (assert (bvult y x)) {extra}"
    );
    executor.execute_all(&parse(&source).unwrap()).unwrap();
    // solve_bv_core is an internal search route. Use the normal authored
    // proof-query lifecycle before asking its assembled proof to be public.
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    executor
}

fn inspect_primary_trace(trace: &ay_sat::ClauseTrace) {
    assert!(!trace.proof_work_exhausted() && !trace.is_truncated());
    assert!(trace.original_clauses().count() > 0);
    ay_sat::validate_clause_trace_resolution(
        trace,
        trace
            .solver_num_vars()
            .expect("original native variable namespace"),
        &ay_sat::ResolutionValidationLimits::default(),
    )
    .expect("the actual primary SAT rows require independent positive-RUP replay");
}

#[test]
fn default_eager_bv_route_retains_original_rows_and_native_resolution() {
    let mut executor = fixture("");
    let assertions = executor.ctx.assertions.clone();
    let attempt = executor.evaluation_attempt();
    let (result, transfers) =
        consuming_trace::observation::observe_trace(&attempt, inspect_primary_trace, || {
            executor.solve_bv_core(BvSolveConfig::qf_bv(), &[]).unwrap()
        });
    assert!(
        result.is_unsat(),
        "expected primary BV UNSAT, independently checked below: {result:?}"
    );
    assert_eq!(
        transfers, 1,
        "the original primary solver must complete its consuming handoff; legacy capture or a fresh fallback is not this route"
    );
    assert_eq!(executor.ctx.assertions, assertions);
    // The real primary trace was inspected at handoff. Proof reconstruction
    // may consume it; requiring a retained copy afterward tests the wrong
    // lifecycle and would defeat the consuming path's purpose.
    let proof = executor.last_proof().expect("actual SMT proof assembly");
    let quality = executor
        .check_proof_strict_with_datatypes(proof)
        .expect("independent strict replay of the actual assembled SMT proof");
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);
    assert_eq!(quality.hole_count, 0);
    ay_proof::validate_reachable_assumes_in_problem_scope(proof, &assertions)
        .expect("SAT rows cannot become authority beyond the unchanged original SMT roots");
}

#[test]
fn explicit_empty_input_keeps_ordinary_default_unsat_behavior() {
    let mut executor = fixture("(assert false)");
    assert!(executor
        .solve_bv_core(BvSolveConfig::qf_bv(), &[])
        .unwrap()
        .is_unsat());
}

#[test]
fn original_cancelled_owner_cannot_publish_a_copied_fallback_trace() {
    let mut executor = fixture("");
    let _stop = ay_core::resource::enter_check_stop(std::sync::Arc::new(|| true));
    let (result, transfers) = consuming_trace::observation::observe_trace(
        &executor.evaluation_attempt(),
        |_| panic!("an already cancelled original owner cannot inspect a transfer"),
        || executor.solve_bv_core(BvSolveConfig::qf_bv(), &[]).unwrap(),
    );
    assert_eq!(result, SolveResult::Unknown);
    assert_eq!(transfers, 0);
    assert!(executor.last_clause_trace.is_none());
    assert!(executor.last_model.is_none());
    assert!(!executor.last_model_validated);
    assert!(executor.retained_internal_proof_for_test().is_none());
    assert!(executor.last_lrat_certificate.is_none());
}

fn nonroot_conflict_fixture() -> Executor {
    // All eight three-literal clauses on three independent BV1 atoms.
    // No atom is a unit and every total assignment falsifies one clause:
    // neither root propagation nor a lucky SAT assignment can settle it.
    // The first nonroot conflict meets the real decision-budget checkpoint.
    let mut source = String::from(
        "(set-logic QF_BV)
         (declare-const x (_ BitVec 1))
         (declare-const y (_ BitVec 1))
         (declare-const z (_ BitVec 1))",
    );
    for mask in 0..8 {
        let literals: Vec<_> = ["x", "y", "z"]
            .iter()
            .enumerate()
            .map(|(bit, name)| {
                let atom = format!("(= {name} #b1)");
                if mask & (1 << bit) == 0 {
                    atom
                } else {
                    format!("(not {atom})")
                }
            })
            .collect();
        source.push_str(&format!("(assert (or {}))", literals.join(" ")));
    }
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    executor.execute_all(&parse(&source).unwrap()).unwrap();
    assert_eq!(executor.ctx.assertions.len(), 8);
    executor.set_decision_limit(Some(0));
    executor
}

fn cleanup_fixture(expected: &SolveResult) -> Executor {
    if matches!(expected, SolveResult::Unknown) {
        let mut executor = nonroot_conflict_fixture();
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        return executor;
    }
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    executor
        .execute_all(
            &parse(
                "(set-logic QF_BV)
                 (declare-const x (_ BitVec 8))
                 (declare-const y (_ BitVec 8))
                 (assert (bvult x y))",
            )
            .unwrap(),
        )
        .unwrap();
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    executor
}

fn run_cleanup_control(
    expected: SolveResult,
    refusal: Option<usize>,
) -> (usize, Option<crate::executor_types::UnknownOrigin>) {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;
    let mut executor = cleanup_fixture(&expected);
    executor.set_random_seed(1);
    let assertions = executor.ctx.assertions.clone();
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = calls.clone();
    let _stop = ay_core::resource::enter_check_stop(Arc::new(move || {
        let call = observed.fetch_add(1, Ordering::AcqRel) + 1;
        refusal == Some(call)
    }));
    crate::executor::theories::slow_host::delay_each_poll(std::time::Duration::ZERO);
    let (result, transfers) = consuming_trace::observation::observe_trace(
        &executor.evaluation_attempt(),
        |_| panic!("SAT/Unknown cleanup cannot publish or inspect an UNSAT transfer"),
        || executor.solve_bv_core(BvSolveConfig::qf_bv(), &[]).unwrap(),
    );
    assert_eq!(transfers, 0);
    assert!(
        crate::executor::theories::slow_host::polls() > 0,
        "the control must enter the actual fresh SAT solve, not stop in bitblasting"
    );
    assert_eq!(executor.ctx.assertions, assertions);
    assert!(executor.last_clause_trace.is_none());
    if let Some(refusal) = refusal {
        assert!(calls.load(Ordering::Acquire) >= refusal);
        assert_eq!(result, SolveResult::Unknown);
        assert!(executor.last_model.is_none());
        assert!(!executor.last_model_validated);
    } else {
        assert_eq!(result, expected);
        if matches!(expected, SolveResult::Unknown) {
            assert_eq!(
                executor.get_reason_unknown(),
                Some(UnknownReason::ResourceLimit)
            );
            assert!(executor.statistics().decisions > 0);
            assert!(executor.statistics().conflicts > 0);
        }
    }
    if matches!(result, SolveResult::Unknown) {
        assert!(executor.last_model.is_none());
        assert!(!executor.last_model_validated);
        assert!(executor.retained_internal_proof_for_test().is_none());
        assert!(executor.last_lrat_certificate.is_none());
    }
    let origin = executor.evaluation_attempt().stop_origin();
    drop(_stop);
    let _replacement = ay_core::resource::enter_check_stop(Arc::new(|| false));
    if origin.is_some() {
        let retry = consuming_trace::TraceCaller::capture(&executor);
        assert!(
            retry.stopped(),
            "a healthy callback cannot revive the attempt"
        );
        assert_eq!(executor.evaluation_attempt().stop_origin(), origin);
    }
    (calls.load(Ordering::Acquire), origin)
}

#[test]
fn actual_sat_route_cleanup_cannot_publish_after_a_one_shot_stop() {
    let (calls, _) = run_cleanup_control(SolveResult::Sat, None);
    assert!(calls > 2);
    // Counted trajectory, not a timing assumption: exercise both final owner
    // observations after the actual SAT result and its solver cleanup.
    let (_, origin) = run_cleanup_control(SolveResult::Sat, Some(calls - 1));
    assert!(
        origin.is_some(),
        "retained bridge stop reaches the same attempt"
    );
    let _ = run_cleanup_control(SolveResult::Sat, Some(calls));
}

#[test]
fn actual_unknown_route_cleanup_keeps_stopped_state_and_no_artifacts() {
    let (calls, _) = run_cleanup_control(SolveResult::Unknown, None);
    assert!(calls > 2);
    let (_, origin) = run_cleanup_control(SolveResult::Unknown, Some(calls - 1));
    assert!(
        origin.is_some(),
        "Unknown cleanup retains the original refusal"
    );
    let _ = run_cleanup_control(SolveResult::Unknown, Some(calls));
}
