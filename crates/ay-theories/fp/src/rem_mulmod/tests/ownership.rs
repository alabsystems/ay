// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::{FpBuildError, FpBuildProgress, FpBuildStage, FpConstruction, FpPrecision, FpSolver};
use ay_core::TermStore;
use std::cell::{Cell, RefCell};
use std::time::{Duration, Instant};

fn stop_rows(stage: FpBuildStage) {
    let end = Instant::now() + Duration::from_secs(20);
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    // Only the retained large-exponent route has multiplication rows. The
    // direct Float16 route still exercises real restoring-divider refusal.
    let precision = if stage == FpBuildStage::MultiplyRow {
        FpPrecision::Float64
    } else {
        FpPrecision::Float16
    };
    let x = solver.fresh_decomposed(precision);
    let y = solver.fresh_decomposed(precision);
    let enabled = Cell::new(true);
    let advanced = Cell::new(0);
    let previous = Cell::new(None::<(u32, usize)>);
    let trace = RefCell::new(Vec::new());
    let mut stop = |progress: FpBuildProgress| {
        trace.borrow_mut().push(progress);
        if progress.stage == stage {
            if let Some((variables, clauses)) = previous.get() {
                if progress.variables > variables && progress.clauses > clauses {
                    advanced.set(advanced.get() + 1);
                }
            }
            previous.set(Some((progress.variables, progress.clauses)));
        }
        Instant::now() >= end || (enabled.get() && advanced.get() >= 2)
    };
    let mut attempt = FpConstruction::new(solver, &mut stop).unwrap();
    assert!(matches!(
        attempt.try_make_rem(&x, &y),
        Err(FpBuildError::Interrupted)
    ));
    assert_eq!(advanced.get(), 2);
    assert_eq!(trace.borrow().last().unwrap().stage, stage);
    let calls = trace.borrow().len();
    enabled.set(false);
    assert!(matches!(
        attempt.try_make_rem(&x, &y),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
    assert_eq!(trace.borrow().len(), calls);
    drop(trace);
    assert!(Instant::now() < end);
}

#[test]
fn native_rem_multiply_row_refusal_is_sticky_after_external_reset() {
    stop_rows(FpBuildStage::MultiplyRow);
}

#[test]
fn native_rem_narrow_divide_row_refusal_is_sticky_after_external_reset() {
    stop_rows(FpBuildStage::DivideRow);
}

#[test]
fn fresh_complete_native_rem_owner_remains_healthy_after_a_separate_refusal() {
    let end = Instant::now() + Duration::from_secs(20);
    let terms = TermStore::new();
    let mut refused = |_: FpBuildProgress| true;
    assert!(matches!(
        FpConstruction::new(FpSolver::new(&terms), &mut refused),
        Err(FpBuildError::Interrupted)
    ));
    let mut solver = FpSolver::new(&terms);
    let x = solver.fresh_decomposed(FpPrecision::Custom { eb: 2, sb: 3 });
    let y = solver.fresh_decomposed(FpPrecision::Custom { eb: 2, sb: 3 });
    let final_polls = Cell::new(0);
    let mut stop = |progress: FpBuildProgress| {
        if progress.stage == FpBuildStage::Finalize {
            final_polls.set(final_polls.get() + 1);
        }
        Instant::now() >= end
    };
    let mut attempt = FpConstruction::new(solver, &mut stop).unwrap();
    let result = attempt.try_make_rem(&x, &y).unwrap();
    assert_eq!(result.precision, x.precision);
    let built = attempt.finish().unwrap();
    assert!(!built.has_encoding_gap);
    assert!(!built.clauses.is_empty());
    assert_eq!(final_polls.get(), 2);
    drop((built, result, x, y));
    assert!(Instant::now() < end);
}

#[test]
fn completed_native_rem_still_refuses_both_final_publication_boundaries() {
    let end = Instant::now() + Duration::from_secs(20);
    let terms = TermStore::new();
    for stop_at in [1, 2] {
        let mut solver = FpSolver::new(&terms);
        let x = solver.fresh_decomposed(FpPrecision::Custom { eb: 2, sb: 3 });
        let y = solver.fresh_decomposed(FpPrecision::Custom { eb: 2, sb: 3 });
        let final_polls = Cell::new(0);
        let mut stop = |progress: FpBuildProgress| {
            if progress.stage == FpBuildStage::Finalize {
                final_polls.set(final_polls.get() + 1);
            }
            Instant::now() >= end || final_polls.get() == stop_at
        };
        let mut attempt = FpConstruction::new(solver, &mut stop).unwrap();
        attempt.try_make_rem(&x, &y).unwrap();
        assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
        assert_eq!(final_polls.get(), stop_at);
        drop((x, y));
        assert!(Instant::now() < end);
    }
}
