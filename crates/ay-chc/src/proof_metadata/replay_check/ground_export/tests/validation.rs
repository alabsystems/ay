// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ground validation shares the original sticky allowance with export.

#![cfg(test)]

use super::*;
use ay_core::time::Instant;
use std::time::Duration;

#[test]
fn validation_precancellation_precedes_malformed_bytes_for_both_formats() {
    let calls = Cell::new(0);
    let mut callback = || {
        calls.set(calls.get() + 1);
        calls.get() != 1
    };
    let mut progress = ReplayProgress::new(&mut callback);
    for format in [Format::GroundDerivationV1, Format::GroundDerivationV2] {
        assert_interrupted(validate_ground(
            &ChcProblem::new(),
            format,
            b"{",
            &mut progress,
        ));
        assert_eq!(
            calls.get(),
            1,
            "the second format cannot revive refused progress"
        );
    }
}

#[test]
fn every_validation_boundary_preserves_refusal_over_malformed_diagnostics() {
    for format in [Format::GroundDerivationV1, Format::GroundDerivationV2] {
        let total = Cell::new(0);
        let mut callback = || {
            total.set(total.get() + 1);
            true
        };
        let mut progress = ReplayProgress::new(&mut callback);
        let error = validate_ground(&ChcProblem::new(), format, b"{", &mut progress)
            .expect_err("live malformed bytes remain invalid");
        assert!(error.to_string().contains("malformed_envelope"));
        assert!(error.to_string().contains(format.as_str()));
        assert!(
            total.get() > 2,
            "must reach the validator and post-work admission"
        );
        for stop_at in 1..=total.get() {
            let calls = Cell::new(0);
            let mut callback = || {
                calls.set(calls.get() + 1);
                calls.get() != stop_at
            };
            let mut progress = ReplayProgress::new(&mut callback);
            assert_interrupted(validate_ground(
                &ChcProblem::new(),
                format,
                b"{",
                &mut progress,
            ));
            assert_interrupted(progress.check());
            assert_eq!(calls.get(), stop_at);
        }
    }
}

#[test]
fn export_and_validation_do_not_receive_independent_allowances() {
    let allowance = Cell::new(true);
    let calls = Cell::new(0);
    let mut callback = || {
        calls.set(calls.get() + 1);
        allowance.get()
    };
    let mut progress = ReplayProgress::new(&mut callback);
    let plan = select_plan(
        Some(Format::GroundDerivationV1),
        |_, _| Ok(Some(b"{".to_vec())),
        || panic!("ground export success cannot invoke fallback"),
        &mut progress,
    )
    .expect("live exporter result may be selected before fresh validation");
    assert_ground(plan, Format::GroundDerivationV1, b"{");
    allowance.set(false);
    assert_interrupted(validate_ground(
        &ChcProblem::new(),
        Format::GroundDerivationV1,
        b"{",
        &mut progress,
    ));
    let stopped_at = calls.get();
    allowance.set(true);
    assert_interrupted(validate_ground(
        &ChcProblem::new(),
        Format::GroundDerivationV2,
        b"{",
        &mut progress,
    ));
    assert_eq!(calls.get(), stopped_at);
}

#[test]
fn absolute_budget_is_not_reset_by_export_or_validation_entry() {
    let now = Instant::now();
    let earlier = now
        .checked_sub(Duration::from_secs(5))
        .expect("test clock represents a past start");
    for (start, budget) in [(now, Duration::ZERO), (earlier, Duration::from_secs(1))] {
        let mut callback = || within_budget(&start, budget);
        let mut progress = ReplayProgress::new(&mut callback);
        assert_interrupted(select_plan(
            Some(Format::SmtlibV1),
            |_, _| panic!("expired absolute budget must prevent export"),
            || panic!("expired absolute budget must prevent fallback"),
            &mut progress,
        ));
        for format in [Format::GroundDerivationV1, Format::GroundDerivationV2] {
            assert_interrupted(validate_ground(
                &ChcProblem::new(),
                format,
                b"{",
                &mut progress,
            ));
        }
    }
}

#[test]
fn ground_validation_refuses_smt_format_without_trying_an_artifact_parser() {
    let calls = Cell::new(0);
    let mut callback = || {
        calls.set(calls.get() + 1);
        true
    };
    let mut progress = ReplayProgress::new(&mut callback);
    let error = validate_ground(&ChcProblem::new(), Format::SmtlibV1, b"{", &mut progress)
        .expect_err("a ground plan cannot relabel its evidence as SMT-LIB");
    assert!(error.to_string().contains("labels evidence as SMT-LIB"));
    assert_eq!(calls.get(), 1, "only the entry allowance is checked");
}
