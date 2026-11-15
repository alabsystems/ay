// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use std::cell::Cell;

mod meter;
mod reconstruction;

fn fixture() -> BoundedRawReasonFixture {
    let mut fixture = bounded_reserved_level0_raw_reason_fixture();
    // The tests control cancellation deterministically, not by wall-clock races.
    fixture.limits.deadline = None;
    fixture
}

fn assert_same_result(
    actual: Result<BoundedBackwardProofResult, BackwardProofFailure>,
    expected: Result<BoundedBackwardProofResult, BackwardProofFailure>,
) {
    match (actual, expected) {
        (Ok(actual), Ok(expected)) => {
            assert_eq!(actual.steps, expected.steps);
            assert_eq!(actual.empty_hints, expected.empty_hints);
            assert_eq!(actual.complete, expected.complete);
        }
        (Err(actual), Err(expected)) => assert_eq!(actual, expected),
        (actual, expected) => panic!("result mismatch: {actual:?} != {expected:?}"),
    }
}

fn every_reconstruction_poll(solver: &Solver, limits: &BackwardProofLimits) -> usize {
    let calls = Cell::new(0);
    let completed = solver.reconstruct_lrat_backward_bounded_with_cancellation(limits, &|| {
        calls.set(calls.get() + 1);
        true
    });
    assert!(completed.is_ok());
    let count = calls.get();
    assert!((2..2_048).contains(&count), "bounded fixture: {count}");
    for refused_at in 1..=count {
        calls.set(0);
        let refused = solver.reconstruct_lrat_backward_bounded_with_cancellation(limits, &|| {
            calls.set(calls.get() + 1);
            calls.get() != refused_at
        });
        assert!(matches!(refused, Err(BackwardProofFailure::Cancelled)));
        assert_eq!(calls.get(), refused_at, "refusal cannot resume");
        assert_same_result(
            solver.reconstruct_lrat_backward_bounded_with_cancellation(limits, &|| true),
            solver.reconstruct_lrat_backward_bounded(limits),
        );
    }
    count
}
