// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::executor_types::{SolveResult, UnknownReason};

use super::proof_checkpoint::{
    bulk_clone_fits_allowances, executor_memory_available, observed_memory_for_test,
    plan_checkpoint_allowance, process_memory_available,
};
use super::Executor;

#[test]
fn exhausted_checkpoint_budget_declines_before_running_window() {
    let mut executor = Executor::new();
    executor.proof_checkpoint_budget.set_remaining(0);
    let assertions_before = executor.ctx.assertions.clone();
    let mut closure_ran = false;

    let result = executor
        .with_isolated_incremental_state(None, |_executor| {
            closure_ran = true;
            Ok(SolveResult::Sat)
        })
        .expect("checkpoint exhaustion is a solver decline, not an executor error");

    assert_eq!(result, SolveResult::Unknown);
    assert!(!closure_ran, "the speculative closure must not run");
    assert_eq!(executor.ctx.assertions, assertions_before);
    assert!(executor.incr_theory_state.is_none());
    assert!(executor.incr_bv_state.is_none());
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::ResourceLimit)
    );
}

#[test]
fn memory_preflight_declines_with_memory_origin_before_running_window() {
    let mut executor = Executor::new();
    executor.set_memory_limit(Some(1));
    let mut closure_ran = false;

    let result = executor
        .with_isolated_incremental_state(None, |_executor| {
            closure_ran = true;
            Ok(SolveResult::Sat)
        })
        .expect("memory exhaustion is a solver decline, not an executor error");

    assert_eq!(result, SolveResult::Unknown);
    assert!(!closure_ran, "the speculative closure must not run");
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::MemoryLimit)
    );
}

#[test]
fn public_solve_does_not_rearm_but_external_query_does() {
    let mut executor = Executor::new();
    executor.proof_checkpoint_budget.set_remaining(0);

    executor.begin_public_solve(false);
    assert_eq!(executor.proof_checkpoint_budget.remaining(), 0);

    executor.begin_external_decision_query(false);

    assert!(executor.proof_checkpoint_budget.remaining() > 0);
}

#[test]
fn tracker_replacement_does_not_replenish_query_budget() {
    let mut executor = Executor::new();
    executor.proof_checkpoint_budget.set_remaining(0);
    executor.proof_tracker = crate::proof_tracker::ProofTracker::new();

    assert!(executor.bounded_proof_rollback_checkpoint().is_err());
    assert_eq!(executor.proof_checkpoint_budget.remaining(), 0);
}

#[test]
fn checkpoint_budget_is_cumulative_at_exact_accounted_boundaries() {
    let mut executor = Executor::new();
    let charge = executor
        .proof_tracker
        .checkpoint_clone_charge_for_test()
        .expect("empty tracker has a conservative footprint");
    executor.proof_checkpoint_budget.set_remaining(charge * 2);

    let first = executor
        .bounded_proof_rollback_checkpoint()
        .expect("first exact charge fits");
    assert_eq!(executor.proof_checkpoint_budget.remaining(), charge);
    executor.proof_tracker.restore_checkpoint_metadata(first);
    let second = executor
        .bounded_proof_rollback_checkpoint()
        .expect("second exact charge fits");
    assert_eq!(executor.proof_checkpoint_budget.remaining(), 0);
    executor.proof_tracker.restore_checkpoint_metadata(second);
    assert!(executor.bounded_proof_rollback_checkpoint().is_err());

    executor.begin_external_decision_query(false);
    executor.proof_checkpoint_budget.set_remaining(charge);
    executor.proof_tracker = crate::proof_tracker::ProofTracker::new();
    let auxiliary = executor
        .bounded_proof_rollback_checkpoint()
        .expect("a replacement tracker consumes the same executor meter");
    executor
        .proof_tracker
        .restore_checkpoint_metadata(auxiliary);
    assert_eq!(executor.proof_checkpoint_budget.remaining(), 0);
}

#[test]
fn checkpoint_memory_headroom_arithmetic_is_exact_and_fail_closed() {
    assert_eq!(process_memory_available(17, 0), usize::MAX);
    assert_eq!(process_memory_available(0, 1), 0);
    assert_eq!(executor_memory_available(0, Some(0)), 0);
    let max_target = (usize::MAX as u128 * 95 / 100) as usize;
    assert_eq!(process_memory_available(0, usize::MAX), max_target);
    assert_eq!(process_memory_available(max_target - 3, usize::MAX), 3);

    let allowance = plan_checkpoint_allowance(7, Some(13), 0, Some(10))
        .expect("three bytes of live headroom remain");
    assert_eq!(allowance.scan_limit, 3);
    assert_eq!(allowance.memory_available, 3);
    assert!(plan_checkpoint_allowance(7, Some(10), 0, Some(10)).is_err());
    assert!(plan_checkpoint_allowance(7, Some(20), 0, Some(0)).is_err());
    assert_eq!(observed_memory_for_test(5, 7, 99), 7);
    assert_eq!(observed_memory_for_test(11, 7, 99), 11);
    assert_eq!(observed_memory_for_test(5, 0, 99), 99);
    assert_eq!(observed_memory_for_test(0, 0, 99), 99);

    let tie = plan_checkpoint_allowance(3, Some(13), 0, Some(10))
        .expect("equal query and memory headroom is representable");
    assert_eq!(tie.scan_limit, 3);
    assert_eq!(tie.memory_available, 3);

    let mut budget = super::proof_checkpoint::ProofCheckpointBudget::default();
    budget.set_remaining(7);
    assert_eq!(
        budget.reject_limit_exceeded(3, 7),
        crate::UnknownOrigin::MemoryBudget
    );
    assert_eq!(
        budget.remaining(),
        7,
        "memory rejection preserves query quota"
    );
    assert_eq!(
        budget.reject_limit_exceeded(7, 7),
        crate::UnknownOrigin::DeterministicResourceBudget
    );
    assert_eq!(budget.remaining(), 0, "a tie is query-bound and latches");
}

#[test]
fn bulk_clone_admission_checks_the_exact_doubling_boundary() {
    assert!(bulk_clone_fits_allowances(10, Some(20), 0));
    assert!(!bulk_clone_fits_allowances(11, Some(20), 0));
    assert!(!bulk_clone_fits_allowances(0, Some(20), 0));

    // The process envelope reserves its normal 5% cleanup margin: 20 bytes
    // yields a target of 19, so duplicating 9 fits and duplicating 10 does not.
    assert!(bulk_clone_fits_allowances(9, None, 20));
    assert!(!bulk_clone_fits_allowances(10, None, 20));
}
