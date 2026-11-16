// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! External consumers obtain views only from a successfully replayed artifact.

use ay_chc::{
    validate_chc_ground_derivation_artifact, validate_chc_ground_derivation_artifact_with_progress,
    ChcExpr, ChcGroundDerivationArtifactErrorReason as Reason, ChcGroundDerivationStepView,
    ChcProblem, ChcValidatedGroundDerivation, ClauseBody, HornClause, SmtValue,
};

// The existing frozen V1 truth-query artifact, independent of private producers.
const TRUTH_ARTIFACT: &[u8] = br#"{"schema":"ay.chc-ground-derivation-artifact/v1","schema_version":1,"role":"unsafe-ground-derivation","normalized_input_schema":"ay.chc.normalized-input/v1","normalized_input_sha256":"23bbc1e41eb6a113b212c79466863072b8e1e2986ef3cb95b9cf31d4ecfa830c","source_clause_sequence_sha256":"11659dc4a46960942dc609b403a74433e3c1039e1e890e33d23b21cf3099c0b1","step_count":1,"query_step":0,"premise_edge_count":0,"binding_count":0,"value_node_count":0,"steps":[{"clause_index":0,"premises":[],"bindings":[]}]}"#;

fn truth_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        true,
    ))));
    problem
}

fn query_view(validated: &ChcValidatedGroundDerivation) -> ChcGroundDerivationStepView<'_> {
    validated
        .step(validated.query_step())
        .expect("validated root")
}

#[test]
fn public_view_borrows_checked_steps_through_public_interfaces() {
    let problem = truth_problem();
    let validated = validate_chc_ground_derivation_artifact(&problem, TRUTH_ARTIFACT)
        .expect("frozen artifact must replay through the public boundary");
    let root = query_view(&validated);
    assert_eq!(root.clause_index(), 0);
    let premises: &[usize] = root.premises();
    assert_eq!(premises, &[] as &[usize]);
    let missing: Option<&SmtValue> = root.source_binding("absent");
    assert!(missing.is_none());
    assert_eq!(root.source_bindings().count(), 0);
    assert!(validated.step(1).is_none());
    assert!(validated.step(usize::MAX).is_none());

    let mut steps = validated.steps();
    assert_eq!(steps.len(), validated.step_count());
    assert_eq!(steps.next().expect("one checked step").clause_index(), 0);
    assert_eq!(steps.len(), 0);
    assert!(steps.next().is_none());
    assert_eq!(validated.binding_count(), 0);
    assert_eq!(validated.premise_edge_count(), 0);
}

#[test]
fn changed_source_and_artifact_cannot_produce_views() {
    let mut changed = ChcProblem::new();
    changed.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        false,
    ))));
    let mismatch = validate_chc_ground_derivation_artifact(&changed, TRUTH_ARTIFACT)
        .expect_err("the view must not grant authority to another problem");
    assert_eq!(mismatch.reason, Reason::ProblemHashMismatch);

    let altered = std::str::from_utf8(TRUTH_ARTIFACT)
        .expect("ASCII fixture")
        .replace("\"clause_index\":0", "\"clause_index\":1");
    let invalid = validate_chc_ground_derivation_artifact(&truth_problem(), altered.as_bytes())
        .expect_err("a missing source clause must not yield a checked step");
    assert_eq!(invalid.reason, Reason::IndexOutOfRange);
}

#[test]
fn refused_validation_has_no_view_and_fresh_retry_can_succeed() {
    let problem = truth_problem();
    let refused = validate_chc_ground_derivation_artifact_with_progress(
        &problem,
        TRUTH_ARTIFACT,
        &mut || false,
    )
    .expect_err("interruption must not publish a capability");
    assert_eq!(refused.reason, Reason::Interrupted);

    let retried = validate_chc_ground_derivation_artifact_with_progress(
        &problem,
        TRUTH_ARTIFACT,
        &mut || true,
    )
    .expect("fresh retry must not inherit refusal");
    assert_eq!(query_view(&retried).clause_index(), 0);
}
