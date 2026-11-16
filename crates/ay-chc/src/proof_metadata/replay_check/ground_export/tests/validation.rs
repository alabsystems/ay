// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ground validation shares the original sticky allowance with export.

#![cfg(test)]

use super::*;

#[test]
fn validation_precancellation_precedes_malformed_bytes_for_both_formats() {
    let allowed = Cell::new(true);
    let calls = Cell::new(0);
    let mut callback = || {
        calls.set(calls.get() + 1);
        allowed.get()
    };
    let mut progress = live_progress(&mut callback);
    allowed.set(false);
    for format in [Format::GroundDerivationV1, Format::GroundDerivationV2] {
        assert_interrupted(validate_ground(
            &ChcProblem::new(),
            format,
            b"{",
            &mut progress,
        ));
        let stopped_at = calls.get();
        assert!(!progress.poll());
        assert_eq!(calls.get(), stopped_at);
    }
}

#[test]
fn every_validation_boundary_preserves_refusal_over_malformed_diagnostics() {
    for format in [Format::GroundDerivationV1, Format::GroundDerivationV2] {
        let armed = Cell::new(false);
        let total = Cell::new(0);
        let mut callback = || {
            if !armed.get() {
                return true;
            }
            total.set(total.get() + 1);
            true
        };
        let mut progress = live_progress(&mut callback);
        armed.set(true);
        let error = validate_ground(&ChcProblem::new(), format, b"{", &mut progress)
            .expect_err("live malformed bytes remain invalid");
        assert!(error.to_string().contains("malformed_envelope"));
        assert!(error.to_string().contains(format.as_str()));
        assert!(
            total.get() > 2,
            "must reach the validator and post-work admission"
        );
        for stop_at in 1..=total.get() {
            let armed = Cell::new(false);
            let calls = Cell::new(0);
            let mut callback = || {
                if !armed.get() {
                    return true;
                }
                calls.set(calls.get() + 1);
                calls.get() != stop_at
            };
            let mut progress = live_progress(&mut callback);
            armed.set(true);
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
    let mut progress = live_progress(&mut callback);
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
fn ground_validation_refuses_smt_format_without_trying_an_artifact_parser() {
    let mut callback = || true;
    let mut progress = live_progress(&mut callback);
    let error = validate_ground(&ChcProblem::new(), Format::SmtlibV1, b"{", &mut progress)
        .expect_err("a ground plan cannot relabel its evidence as SMT-LIB");
    assert!(error.to_string().contains("labels evidence as SMT-LIB"));
}
