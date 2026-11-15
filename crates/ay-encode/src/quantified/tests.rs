// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use std::cell::Cell;

mod fixtures;
mod integration;
mod membership;
mod obligation;
mod scheduling;
mod tree_rows;
mod unsafe_rows;

use fixtures::*;

#[test]
fn classified_panics_are_errors_but_programmer_panics_propagate() {
    let error = runner::caught::<()>(|| panic!("sort mismatch: injected AY failure"));
    assert!(matches!(error, Err(crate::EncodeError::SolverPanicked(_))));
    let programmer = std::panic::catch_unwind(|| {
        runner::caught::<()>(|| panic!("injected unrelated programmer failure"))
    });
    assert!(programmer.is_err());
}

#[test]
fn public_precancel_zero_and_overflow_budgets_cannot_publish_a_batch() {
    let problem = source();
    let token = CancellationToken::new();
    token.cancel();
    assert!(matches!(
        solve_quantified_query_obligations_with_cancellation(
            &problem,
            Duration::from_secs(1),
            Some(1024),
            &token,
        ),
        Err(crate::EncodeError::Cancelled)
    ));
    token.reset();
    for budget in [Duration::ZERO, Duration::MAX] {
        assert!(solve_quantified_query_obligations_with_cancellation(
            &problem,
            budget,
            Some(1024),
            &token,
        )
        .is_err());
    }
}
