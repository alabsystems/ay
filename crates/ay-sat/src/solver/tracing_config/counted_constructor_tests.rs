// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, FiniteAdmissionGrant};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;

fn owner(work: u64, storage: usize) -> CountedAdmission {
    CountedAdmission::new(
        FiniteAdmissionGrant::new(work, storage),
        None,
        Arc::new(|| false),
    )
    .unwrap()
}

fn attach(solver: &mut Solver, original: &CountedAdmission) {
    assert!(solver.attach_counted_admission(original.clone()).is_ok());
}

#[test]
fn failed_bootstrap_preserves_existing_checker_and_blocks_trivial_verdicts() {
    for unsat in [false, true] {
        let mut solver = Solver::new(0);
        solver.enable_forward_checker_sampled(7);
        if unsat {
            assert!(!solver.add_clause(Vec::new()));
        }
        let original = owner(0, 1_000_000);
        attach(&mut solver, &original);
        solver.enable_forward_checker();
        assert_eq!(
            solver
                .cold
                .forward_checker
                .as_ref()
                .unwrap()
                .sample_period(),
            7
        );
        solver.enable_forward_checker_sampled(19);
        assert_eq!(
            solver
                .cold
                .forward_checker
                .as_ref()
                .unwrap()
                .sample_period(),
            7
        );
        assert_eq!(original.check(), Err(CountedAdmissionError::WorkExhausted));
        assert!(matches!(solver.solve().into_inner(), SatResult::Unknown));
        assert_eq!(
            solver.last_unknown_reason(),
            Some(SatUnknownReason::ResourceBudget)
        );
    }
}

#[test]
fn successful_replacement_keeps_requested_sampling_and_original_ledger() {
    let mut solver = Solver::new(0);
    solver.enable_forward_checker_sampled(7);
    let original = owner(1_000_000, 1_000_000);
    attach(&mut solver, &original);
    solver.enable_forward_checker_sampled(11);
    assert_eq!(
        solver
            .cold
            .forward_checker
            .as_ref()
            .unwrap()
            .sample_period(),
        11
    );
    let used = original.usage().unwrap();
    assert!(used.work_admitted > 0);
    assert!(used.storage_admitted > 0);
    solver.enable_forward_checker();
    assert_eq!(
        solver
            .cold
            .forward_checker
            .as_ref()
            .unwrap()
            .sample_period(),
        0
    );
    let twice = original.usage().unwrap();
    assert_eq!(twice.work_admitted, used.work_admitted * 2);
    assert_eq!(twice.storage_admitted, used.storage_admitted * 2);
    assert!(matches!(solver.solve().into_inner(), SatResult::Sat(_)));
}

#[test]
fn first_storage_refusal_does_not_install_a_silently_unchecked_solver() {
    let mut solver = Solver::new(0);
    let original = owner(1_000_000, 0);
    attach(&mut solver, &original);
    solver.enable_forward_checker();
    assert!(solver.cold.forward_checker.is_none());
    assert_eq!(
        original.check(),
        Err(CountedAdmissionError::StorageExhausted)
    );
    assert!(matches!(solver.solve().into_inner(), SatResult::Unknown));
}

#[test]
fn one_shot_cancellation_during_replacement_preserves_checker_on_retry() {
    let mut solver = Solver::new(3);
    solver.enable_forward_checker_sampled(5);
    let armed = Arc::new(AtomicBool::new(true));
    let observed = Arc::clone(&armed);
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1_000_000),
        None,
        Arc::new(move || observed.swap(false, Ordering::SeqCst)),
    )
    .unwrap();
    attach(&mut solver, &original);
    solver.enable_forward_checker_sampled(9);
    assert!(!armed.load(Ordering::SeqCst));
    assert_eq!(
        solver
            .cold
            .forward_checker
            .as_ref()
            .unwrap()
            .sample_period(),
        5
    );
    solver.enable_forward_checker();
    assert_eq!(
        solver
            .cold
            .forward_checker
            .as_ref()
            .unwrap()
            .sample_period(),
        5
    );
    assert!(matches!(solver.solve().into_inner(), SatResult::Unknown));
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::Interrupted)
    );
}

#[test]
fn post_commit_cleanup_fence_can_stop_without_authorizing_a_verdict() {
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let baseline = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1_000_000),
        None,
        Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst);
            false
        }),
    )
    .unwrap();
    let mut solver = Solver::new(0);
    solver.enable_forward_checker_sampled(5);
    attach(&mut solver, &baseline);
    solver.enable_forward_checker_sampled(9);
    let last = calls.load(Ordering::SeqCst) - 1;
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let original = CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1_000_000),
        None,
        Arc::new(move || observed.fetch_add(1, Ordering::SeqCst) == last),
    )
    .unwrap();
    let mut solver = Solver::new(0);
    solver.enable_forward_checker_sampled(5);
    attach(&mut solver, &original);
    solver.enable_forward_checker_sampled(9);
    assert_eq!(
        solver
            .cold
            .forward_checker
            .as_ref()
            .unwrap()
            .sample_period(),
        9
    );
    assert!(original.usage().unwrap().refusal.is_some());
    assert!(matches!(solver.solve().into_inner(), SatResult::Unknown));
}
