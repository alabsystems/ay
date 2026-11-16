// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

mod cancellation_tests;

use super::*;
use crate::ground_derivation::{
    validate_ground_derivation, GroundDerivation, GroundDerivationStep,
};

const REPLAY_BUDGET: Duration = Duration::from_secs(60);

fn run() -> ChcPdrProofRun {
    let mut problem = ChcProblem::new();
    problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        true,
    ))));
    let derivation = GroundDerivation {
        steps: vec![GroundDerivationStep {
            clause_index: 0,
            env: Default::default(),
            premises: Vec::new(),
        }],
        query_step: 0,
    };
    validate_ground_derivation(&problem, &derivation).unwrap();
    let counterexample = Counterexample::new(Vec::new()).with_ground_derivation(derivation);
    ChcPdrProofRun::new(
        problem,
        VerifiedChcResult::Unsafe(VerifiedCounterexample::from_validated(counterexample)),
        "engine-attachment-progress-test",
    )
}

#[test]
fn engine_attachment_matches_direct_replay_and_exact_source() {
    let original = run();
    let expected = original
        .run_checked_replay(REPLAY_BUDGET)
        .unwrap()
        .into_proof_run();
    let retained = original.clone();
    let attached = attach_checked_replay_with_progress(original, REPLAY_BUDGET, &mut || true);
    assert_eq!(
        attached.metadata().to_json_value(),
        expected.metadata().to_json_value()
    );
    assert!(attached.metadata().trust_full_verifier_admissible());
    assert!(attached.result().is_unsafe());
    assert!(std::ptr::eq(retained.problem(), attached.problem()));
}

#[test]
fn every_engine_attachment_poll_refusal_preserves_metadata_and_stays_terminal() {
    let original = run();
    let metadata = original.metadata().to_json_value();
    let mut total = 0;
    let checked = attach_checked_replay_with_progress(original.clone(), REPLAY_BUDGET, &mut || {
        total += 1;
        true
    });
    assert!(checked.metadata().trust_full_verifier_admissible());
    assert!(total > 2);
    for stop_at in 1..=total {
        let mut calls = 0;
        let stopped =
            attach_checked_replay_with_progress(original.clone(), REPLAY_BUDGET, &mut || {
                calls += 1;
                calls != stop_at
            });
        assert_eq!(calls, stop_at);
        assert_eq!(stopped.metadata().to_json_value(), metadata);
        assert!(stopped.result().is_unsafe());
        assert!(std::ptr::eq(original.problem(), stopped.problem()));
    }
}

#[test]
fn retained_config_tokens_cancel_attachment_without_changing_verified_result() {
    let parent = CancellationToken::new();
    let base = PdrConfig::default();
    let pdr = PdrConfig {
        cancellation_token: Some(parent.child()),
        ..base
    };
    let bmc = BmcConfig::default().with_cancellation(parent.child());
    let tokens = [
        pdr.cancellation_token.clone(),
        bmc.base.cancellation_token.clone(),
    ];
    drop((pdr, bmc));
    parent.cancel();
    for cancellation in tokens {
        let original = run();
        let metadata = original.metadata().to_json_value();
        let mut calls = 0;
        let stopped = attach_checked_replay_with_progress(original, REPLAY_BUDGET, &mut || {
            calls += 1;
            !cancellation
                .as_ref()
                .is_some_and(CancellationToken::is_cancelled)
        });
        assert_eq!(calls, 1);
        assert_eq!(stopped.metadata().to_json_value(), metadata);
        assert!(stopped.result().is_unsafe());
    }
}

#[test]
fn already_upgraded_metadata_is_not_downgraded_by_failed_reattachment() {
    let checked = attach_checked_replay_with_progress(run(), REPLAY_BUDGET, &mut || true);
    let metadata = checked.metadata().to_json_value();
    assert!(checked.metadata().trust_full_verifier_admissible());
    let stopped = attach_checked_replay_with_progress(checked, Duration::ZERO, &mut || false);
    assert_eq!(stopped.metadata().to_json_value(), metadata);
}

#[test]
fn engine_attachment_classified_panic_does_not_publish_an_upgrade() {
    let original = run();
    let metadata = original.metadata().to_json_value();
    let mut total = 0;
    let checked = attach_checked_replay_with_progress(original.clone(), REPLAY_BUDGET, &mut || {
        total += 1;
        true
    });
    assert!(checked.metadata().trust_full_verifier_admissible());
    let mut calls = 0;
    let stopped = attach_checked_replay_with_progress(original, REPLAY_BUDGET, &mut || {
        calls += 1;
        assert_ne!(calls, total, "BUG: synthetic attachment callback panic");
        true
    });
    assert_eq!(calls, total);
    assert_eq!(stopped.metadata().to_json_value(), metadata);
}

#[test]
fn ineligible_engine_result_does_not_attempt_replay() {
    let original = ChcPdrProofRun::new(
        ChcProblem::new(),
        VerifiedChcResult::from_validated(
            ChcEngineResult::Unknown,
            ValidationEvidence::FullVerification,
        ),
        "engine-attachment-unknown",
    );
    let metadata = original.metadata().to_json_value();
    let unchanged = attach_checked_replay_with_progress(original, REPLAY_BUDGET, &mut || {
        panic!("Unknown must not start replay")
    });
    assert_eq!(unchanged.metadata().to_json_value(), metadata);
}
