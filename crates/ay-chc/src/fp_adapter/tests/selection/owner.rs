// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn original_raw_callback_and_expired_end_refusals_remain_sticky() {
    let mut terms = TermStore::new();
    let root = selection_constant(&mut terms);
    let namespace = ChcProblem::new();
    let raw = Arc::new(AtomicBool::new(true));
    let original = Arc::clone(&raw);
    let mut stop = || {
        if original.load(Ordering::Relaxed) {
            ControlFlow::Break(StopReason::Cancelled)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(10_000_000_000, &mut stop);
    assert!(matches!(
        lower_fp_clause(&terms, &[root], &[], &namespace, &mut budget),
        Err(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Cancelled
        )))
    ));
    raw.store(false, Ordering::Relaxed);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
    let end = Instant::now()
        .checked_sub(Duration::from_secs(1))
        .expect("fixture instant supports a one-second offset");
    let mut deadline = || {
        if Instant::now() >= end {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(10_000_000_000, &mut deadline);
    assert!(matches!(
        lower_fp_clause(&terms, &[root], &[], &namespace, &mut budget),
        Err(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Deadline
        )))
    ));
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Deadline))
    );
}

pub(super) fn native_branch_progress_and_final_admission_refuse_on_same_owner() {
    let mut terms = TermStore::new();
    let root = selection_constant(&mut terms);
    let namespace = ChcProblem::new();
    let calls = Cell::new(0usize);
    let mut count = || {
        calls.set(calls.get() + 1);
        ControlFlow::Continue(())
    };
    let final_call = {
        let mut budget = WorkBudget::new(10_000_000_000, &mut count);
        assert!(lower_fp_clause(&terms, &[root], &[], &namespace, &mut budget).is_ok());
        calls.get()
    };
    let calls = Cell::new(0usize);
    let mut final_stop = || {
        calls.set(calls.get() + 1);
        if calls.get() == final_call {
            ControlFlow::Break(StopReason::Deadline)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(10_000_000_000, &mut final_stop);
    assert!(matches!(
        lower_fp_clause(&terms, &[root], &[], &namespace, &mut budget),
        Err(FpAdapterError::Owner(QueryError::Interrupted(
            StopReason::Deadline
        )))
    ));
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Deadline))
    );
    let raw = Cell::new(false);
    let mut poll = || {
        if raw.get() {
            ControlFlow::Break(StopReason::Cancelled)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut budget = WorkBudget::new(10_000_000_000, &mut poll);
    let plan = source::plan(&terms, &[root], &[], &mut budget).unwrap();
    plan.prepay(&mut budget).unwrap();
    let mut stop = |progress: ay_fp::FpBuildProgress| {
        if progress.variables > 0 {
            raw.set(true);
        }
        budget.charge(0).is_err()
    };
    let mut attempt = ay_fp::FpConstruction::new(ay_fp::FpSolver::new(&terms), &mut stop).unwrap();
    assert!(matches!(
        attempt.try_encode_bool_condition(root),
        Err(ay_fp::FpBuildError::Interrupted)
    ));
    raw.set(false);
    assert!(matches!(
        attempt.finish(),
        Err(ay_fp::FpBuildError::Interrupted)
    ));
    drop(stop);
    assert_eq!(
        budget.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
}
