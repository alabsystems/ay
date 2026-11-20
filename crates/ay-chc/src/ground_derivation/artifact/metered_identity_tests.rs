// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ground_derivation::CHC_GROUND_DERIVATION_MAX_SOURCE_WORK;

fn wide_declarations(common_prefix: bool) -> (ChcProblem, GroundDerivation) {
    let (mut problem, derivation) = tests::fixture();
    let repeated = "s".repeat(6200);
    for index in (0..64).rev() {
        let name = if common_prefix {
            format!("{repeated}{index:02}")
        } else {
            format!("{index:02}{repeated}")
        };
        problem.declare_predicate(
            name,
            vec![ChcSort::Array(
                Box::new(ChcSort::BitVec(64)),
                Box::new(ChcSort::Bool),
            )],
        );
    }
    (problem, derivation)
}

#[test]
fn wire_meter_preserves_both_identities_and_the_original_replay() {
    let (mut problem, derivation) = wide_declarations(false);
    assert_eq!(
        validate_problem_bounds(&problem).unwrap_err().reason,
        ChcGroundDerivationArtifactErrorReason::SourceWorkLimitExceeded
    );
    let artifact = encode_ground_derivation_artifact(&problem, &derivation).unwrap();
    let checked = validate_chc_ground_derivation_artifact(&problem, artifact.bytes()).unwrap();
    assert_eq!(
        checked.normalized_input_sha256(),
        normalized_chc_input_sha256(&problem)
    );
    assert_eq!(
        checked.source_clause_sequence_sha256(),
        ordered_chc_clause_sequence_sha256(&problem)
    );
    let v2 = encode_ground_derivation_artifact_v2(&problem, &derivation).unwrap();
    let checked_v2 = validate_chc_ground_derivation_artifact_v2(&problem, v2.bytes()).unwrap();
    assert_eq!(
        checked_v2.normalized_input_sha256(),
        checked.normalized_input_sha256()
    );
    assert_eq!(
        checked_v2.source_clause_sequence_sha256(),
        checked.source_clause_sequence_sha256()
    );
    // A clause permutation preserves the normalized text; it changes which live
    // source clauses the first two offered steps refer to.
    problem.clauses_mut().swap(0, 1);
    assert_eq!(
        validate_chc_ground_derivation_artifact(&problem, artifact.bytes())
            .unwrap_err()
            .reason,
        ChcGroundDerivationArtifactErrorReason::ClauseSequenceHashMismatch
    );
    // Supply the exact hashes of a changed guard. The same original values now
    // have to fail that guard during replay, after both identities agree.
    problem.clauses_mut().swap(0, 1);
    problem.clauses_mut()[2].body.constraint = Some(ChcExpr::eq(
        ChcExpr::var(crate::ChcVar::new("z", ChcSort::Int)),
        ChcExpr::int(2),
    ));
    let mut changed: GroundDerivationEnvelope = serde_json::from_slice(artifact.bytes()).unwrap();
    changed.normalized_input_sha256 = normalized_chc_input_sha256(&problem);
    changed.source_clause_sequence_sha256 = ordered_chc_clause_sequence_sha256(&problem);
    let rejected =
        validate_chc_ground_derivation_artifact(&problem, &serde_json::to_vec(&changed).unwrap())
            .unwrap_err();
    assert_eq!(
        rejected.reason,
        ChcGroundDerivationArtifactErrorReason::DerivationRejected
    );
    assert_eq!(
        rejected.detail,
        GroundDerivationError::ConstraintFalse { step: 2 }.to_string()
    );
}

#[test]
fn long_comparison_prefixes_exhaust_the_original_wire_grant() {
    let (problem, derivation) = wide_declarations(true);
    let err = encode_ground_derivation_artifact(&problem, &derivation).unwrap_err();
    assert_eq!(
        err.reason,
        ChcGroundDerivationArtifactErrorReason::SourceWorkLimitExceeded
    );
    assert_eq!(
        err.detail,
        "whole-problem canonical sort exceeds work bound"
    );
}

#[test]
fn metered_identity_can_be_cancelled_during_prefix_comparison() {
    use crate::proof_metadata::wire_sort::WireSort;
    use ay_core::original_query::{QueryError, StopReason};
    let (problem, _) = wide_declarations(true);
    let mut grant = CHC_GROUND_DERIVATION_MAX_SOURCE_WORK;
    let mut polls = 0;
    let err = WireSort {
        remaining: &mut grant,
        progress: &mut || {
            polls += 1;
            polls < 1000
        },
    }
    .normalized(&problem)
    .unwrap_err();
    assert!(grant < CHC_GROUND_DERIVATION_MAX_SOURCE_WORK);
    assert_eq!(polls, 1000);
    assert_eq!(err, QueryError::Interrupted(StopReason::Cancelled));
}
