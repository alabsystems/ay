// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use std::time::Duration;

use super::*;

fn fixture() -> ChcProblem {
    ChcParser::parse(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x 0)) false)))
(check-sat)
"#,
    )
    .expect("over-approximation reason fixture should parse")
}

#[test]
fn strict_proof_boundary_rejects_overapproximated_refutation() {
    let mut problem = fixture();
    let exact = engines::solve_pdr_proof(problem.clone(), PdrConfig::default())
        .expect("exact strict proof solve should not fail");
    assert!(exact.result().is_unsafe() && exact.accepted_as_proof());

    problem.mark_stripped_body_forall();
    let run = engines::solve_pdr_proof(problem, PdrConfig::default())
        .expect("over-approximated strict proof solve should not fail");
    assert_non_admissible_overapproximated_refutation(&run);
}

#[test]
fn bmc_proof_and_checked_replay_reject_overapproximated_refutation() {
    let config = BmcConfig::default()
        .with_max_depth(4)
        .with_time_budget(Duration::from_secs(10));
    let mut problem = fixture();
    let exact = engines::solve_bmc_proof(problem.clone(), config.clone())
        .expect("exact BMC proof solve should not fail");
    assert!(exact.result().is_unsafe() && exact.accepted_as_proof());

    problem.mark_stripped_body_forall();
    let run =
        engines::solve_bmc_proof_with_checked_replay(problem, config, Duration::from_secs(10))
            .expect("over-approximated checked BMC solve should not fail");
    assert_non_admissible_overapproximated_refutation(&run);
}

fn assert_non_admissible_overapproximated_refutation(run: &ChcPdrProofRun) {
    assert!(run.result().is_unknown());
    assert!(!run.accepted_as_proof());
    assert!(!run.metadata().accepted_as_proof());
    assert!(!run.metadata().trust_full_verifier_admissible());
    assert!(run.metadata().checked_summary_identity_sha256().is_none());
    assert_eq!(
        run.result().unknown_reason(),
        Some(VerifiedUnknownReason::OverApproximatedRefutation)
    );
}

#[test]
fn overapproximation_guard_leaves_every_other_verdict_and_reason_unchanged() {
    let problem = fixture();
    let unsafe_without_flag = engines::downgrade_unsafe_if_overapproximated(
        VerifiedChcResult::Unsafe(VerifiedCounterexample::from_validated(
            engine_result::skeleton_counterexample(&problem, 0),
        )),
        false,
    );
    assert!(unsafe_without_flag.is_unsafe());

    let safe_with_flag = engines::downgrade_unsafe_if_overapproximated(
        VerifiedChcResult::Safe(VerifiedInvariant::from_validated(InvariantModel::new())),
        true,
    );
    assert!(safe_with_flag.is_safe());

    for original in [
        VerifiedChcResult::from_validated(
            engine_result::ChcEngineResult::Unknown,
            engine_result::ValidationEvidence::FullVerification,
        ),
        VerifiedChcResult::from_validated(
            engine_result::ChcEngineResult::NotApplicable,
            engine_result::ValidationEvidence::FullVerification,
        ),
        VerifiedChcResult::unknown_candidate_not_admitted(),
    ] {
        let reason = original.unknown_reason();
        let guarded = engines::downgrade_unsafe_if_overapproximated(original, true);
        assert!(guarded.is_unknown());
        assert_eq!(guarded.unknown_reason(), reason);
    }
}
