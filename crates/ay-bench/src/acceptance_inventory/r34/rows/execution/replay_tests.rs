// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use ay_chc::{ChcError, ChcParser};
use ay_core::resource::ResourceGuard;
use std::cell::Cell;
use std::time::Duration;

const TEST_BUDGET: Duration = Duration::from_secs(60);

fn config() -> PdrConfig {
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(TEST_BUDGET);
    config
}

fn safe_run() -> ChcPdrProofRun {
    // Actual proof-grade producer, not a fabricated verified-result capability.
    let problem = ChcParser::parse(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#,
    )
    .unwrap();
    let run = ay_chc::engines::solve_pdr_proof(problem, config()).unwrap();
    assert!(matches!(run.result(), VerifiedChcResult::Safe(_)));
    assert!(run.accepted_as_proof());
    assert!(!run.metadata().trust_full_verifier_admissible());
    run
}

#[test]
fn exact_zero_budget_replay_error_is_not_demoted_to_metadata_only() {
    let run = safe_run();
    let original = run.metadata().to_json_value();
    let token = CancellationToken::new();
    let error = strict_replay(&run, Instant::now(), &token).unwrap_err();
    assert!(matches!(&error, ChcError::Verification(message)
        if message == "checked replay budget is zero; staying metadata-only"));
    assert_eq!(run.metadata().to_json_value(), original);
    assert!(!token.is_cancelled());
}

#[test]
fn inherited_cancellation_preserves_the_lower_strict_replay_error() {
    let run = safe_run();
    let original = run.metadata().to_json_value();
    let parent = CancellationToken::new();
    let token = parent.child();
    parent.cancel();
    let expected = run
        .run_checked_replay_with_cancellation(TEST_BUDGET, &token)
        .unwrap_err()
        .to_string();
    let actual = strict_replay(&run, Instant::now() + TEST_BUDGET, &token)
        .unwrap_err()
        .to_string();
    assert_eq!(actual, expected);
    assert_eq!(run.metadata().to_json_value(), original);
    assert!(parent.is_cancelled());
    assert!(token.is_cancelled());
}

#[test]
fn checked_success_uses_the_same_original_owner_and_strict_artifact_rules() {
    let run = safe_run();
    let original_metadata = run.metadata().to_json_value();
    let mut original = ResourceGuard::new();
    let deadline = Instant::now() + TEST_BUDGET;
    original.set_deadline(Some(deadline));
    let token = CancellationToken::new();
    let owner = ExternalInvariantValidationOwner::capture(
        &original,
        &config().with_cancellation_token(Some(token.clone())),
    );
    assert_eq!(owner.deadline(), deadline);
    let before_ticks = original.ticks();
    owner
        .with_resources(|| {
            let VerifiedChcResult::Safe(invariant) = run.result() else {
                panic!("actual producer did not retain a Safe invariant");
            };
            let mut validation = config();
            validation.solve_timeout =
                Some(owner.deadline().saturating_duration_since(Instant::now()));
            assert_eq!(
                validate_external_invariant_model_typed(
                    run.problem(),
                    invariant.model(),
                    &validation,
                )?,
                Kind::Valid
            );
            let checked = strict_replay(&run, owner.deadline(), &token)?;
            assert!(checked
                .proof_run()
                .metadata()
                .trust_full_verifier_admissible());
            assert_eq!(
                checked.proof_run().problem().normalized_input_sha256(),
                run.problem().normalized_input_sha256()
            );
            assert!(!checked.summary().obligations.is_empty());
            for payload in checked.obligation_payloads() {
                assert!(payload.smt_query_bytes().is_some());
                assert!(payload.strict_bundle_bytes().is_some());
            }
            // Only the sealed checked run gains authority; the producer is intact.
            assert_eq!(run.metadata().to_json_value(), original_metadata);
            drop(checked);
            Ok(())
        })
        .unwrap()
        .unwrap();
    assert_eq!(owner.check(), None);
    assert_eq!(owner.deadline(), deadline);
    assert!(original.ticks() > before_ticks);
    assert!(!token.is_cancelled());
}

#[test]
fn exhausted_original_owner_never_enters_a_fresh_replay_allowance() {
    let run = safe_run();
    let mut original = ResourceGuard::new();
    original.set_deadline(Some(Instant::now() + TEST_BUDGET));
    original.set_rlimit(Some(0));
    let token = CancellationToken::new();
    let owner = ExternalInvariantValidationOwner::capture(&original, &config());
    let entries = Cell::new(0);
    let ticks = original.ticks();
    let result = owner
        .with_resources(|| {
            entries.set(entries.get() + 1);
            strict_replay(&run, owner.deadline(), &token).map(|checked| drop(checked))
        })
        .unwrap();
    assert_eq!(result, Err(Kind::WorkLimit));
    assert_eq!(entries.get(), 0);
    assert_eq!(original.ticks(), ticks);
    assert!(!run.metadata().trust_full_verifier_admissible());
}
