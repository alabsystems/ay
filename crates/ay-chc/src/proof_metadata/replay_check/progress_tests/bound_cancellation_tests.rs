// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::CancellationToken;

#[test]
fn typed_bound_replay_preserves_exact_v1_and_v2_artifacts() {
    let run = truth_run();
    let parent = CancellationToken::new();
    let token = parent.child();
    for format in [Format::GroundDerivationV1, Format::GroundDerivationV2] {
        let expected = Mode::Bound(format).legacy(&run).unwrap();
        let supplied = binding(&run, format);
        let actual = run
            .run_checked_replay_with_binding_and_cancellation(
                supplied.options,
                supplied.solver,
                supplied.obligation_id,
                supplied.base_evidence,
                BUDGET,
                &token,
            )
            .unwrap();
        assert_same(&actual, &expected);
        assert_eq!(actual.summary().obligations[0].payload_format, format);
    }
    assert!(!parent.is_cancelled());
    assert!(!token.is_cancelled());
}

#[test]
fn inherited_precancel_prevents_supplied_id_conversion() {
    let run = truth_run();
    let original = run.metadata().to_json_value();
    let parent = CancellationToken::new();
    let token = parent.child().child();
    let conversions = Cell::new(0);
    parent.cancel();
    assert_interrupted(run.run_checked_replay_with_binding_and_cancellation(
        ChcProofEvidenceOptions::pdr_strict(&crate::PdrConfig::default()),
        ChcProofSolverIdentity::new("bound-pre-cancel"),
        ObservedId {
            conversions: &conversions,
        },
        None,
        BUDGET,
        &token,
    ));
    assert_eq!(conversions.get(), 0);
    assert_eq!(run.metadata().to_json_value(), original);
    assert!(parent.is_cancelled());
}

#[test]
fn zero_and_overflow_precede_cancellation_and_id_conversion() {
    let run = truth_run();
    let token = CancellationToken::new();
    let conversions = Cell::new(0);
    token.cancel();
    for budget in [Duration::ZERO, Duration::MAX] {
        let expected = run.run_checked_replay(budget).unwrap_err().to_string();
        let error = run
            .run_checked_replay_with_binding_and_cancellation(
                ChcProofEvidenceOptions::pdr_strict(&crate::PdrConfig::default()),
                ChcProofSolverIdentity::new("bound-budget"),
                ObservedId {
                    conversions: &conversions,
                },
                None,
                budget,
                &token,
            )
            .unwrap_err();
        assert_eq!(error.to_string(), expected);
    }
    assert_eq!(conversions.get(), 0);
}

struct CancellingId<'a> {
    parent: &'a CancellationToken,
    conversions: &'a Cell<usize>,
}

impl From<CancellingId<'_>> for String {
    fn from(value: CancellingId<'_>) -> Self {
        value.conversions.set(value.conversions.get() + 1);
        value.parent.cancel();
        "cancel-during-id-conversion".to_owned()
    }
}

#[test]
fn cancellation_during_id_conversion_cannot_reach_evidence_publication() {
    let run = truth_run();
    let original = run.metadata().to_json_value();
    let parent = CancellationToken::new();
    let token = parent.child();
    let conversions = Cell::new(0);
    assert_interrupted(run.run_checked_replay_with_binding_and_cancellation(
        ChcProofEvidenceOptions::pdr_strict(&crate::PdrConfig::default()),
        ChcProofSolverIdentity::new("bound-conversion"),
        CancellingId {
            parent: &parent,
            conversions: &conversions,
        },
        None,
        BUDGET,
        &token,
    ));
    assert_eq!(conversions.get(), 1);
    assert_eq!(run.metadata().to_json_value(), original);
}

#[test]
fn every_bound_token_boundary_is_terminal_including_final_admission() {
    let run = truth_run();
    for format in [Format::GroundDerivationV1, Format::GroundDerivationV2] {
        let token = CancellationToken::new();
        let mut total = 0;
        let expected = run
            .run_checked_replay_with_binding_factory(
                Instant::now(),
                BUDGET,
                &mut || {
                    total += 1;
                    true
                },
                Some(&token),
                || binding(&run, format),
            )
            .unwrap();
        assert!(total > 10);
        assert_same(&expected, &Mode::Bound(format).legacy(&run).unwrap());
        for cancelled_at in 1..=total {
            let parent = CancellationToken::new();
            let token = parent.child();
            let mut calls = 0;
            assert_interrupted(run.run_checked_replay_with_binding_factory(
                Instant::now(),
                BUDGET,
                &mut || {
                    calls += 1;
                    if calls == cancelled_at {
                        parent.cancel();
                    }
                    true
                },
                Some(&token),
                || binding(&run, format),
            ));
            assert_eq!(
                calls, cancelled_at,
                "no later phase or alternate format may resume"
            );
        }
    }
}

#[test]
fn live_token_does_not_relax_caller_payload_binding() {
    let run = truth_run();
    let token = CancellationToken::new();
    for format in [Format::GroundDerivationV1, Format::GroundDerivationV2] {
        let mut supplied = binding(&run, format);
        supplied.base_evidence.as_mut().unwrap().replay_obligations[0]
            .query
            .sha256 = "0".repeat(64);
        let error = run
            .run_checked_replay_with_binding_and_cancellation(
                supplied.options,
                supplied.solver,
                supplied.obligation_id,
                supplied.base_evidence,
                BUDGET,
                &token,
            )
            .unwrap_err();
        assert!(error
            .to_string()
            .contains("do not match the supplied replay evidence"));
    }
    assert!(!token.is_cancelled());
}

#[test]
fn original_wall_is_checked_before_the_binding_factory_runs() {
    let run = truth_run();
    let token = CancellationToken::new();
    let started = Instant::now().checked_sub(Duration::from_secs(5)).unwrap();
    assert_interrupted(run.run_checked_replay_with_binding_factory(
        started,
        Duration::from_secs(1),
        &mut || panic!("expired callback"),
        Some(&token),
        || panic!("expired binding factory"),
    ));
    assert!(!token.is_cancelled());
}
