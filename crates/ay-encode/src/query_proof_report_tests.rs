// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use std::time::Duration;

use ay_chc::{
    CancellationToken, ChcExpr, ChcParser, ChcProblem, ChcProofArtifactDigest, ClauseBody,
    HornClause,
};

use crate::invoke::{
    solve_query_obligations_with_checked_proof_report,
    solve_query_obligations_with_checked_proof_report_with_cancellation,
    solve_query_obligations_with_proof_report,
    solve_query_obligations_with_proof_report_with_cancellation, solve_with_proof_report,
    EncodeConfig, ProofMode,
};
use crate::query_proof_report::{
    obligation_set_sha256, QueryObligationBatchProofReport, QueryObligationBatchVerdict,
    QueryObligationProofReportRow, CHC_QUERY_BATCH_PROOF_REPORT_SCHEMA,
    CHC_QUERY_OBLIGATION_SET_SCHEMA,
};
use crate::EncodeError;

const SAFE_MULTI_QUERY: &str = r#"
(set-logic HORN)
(declare-rel error_p0 ())
(declare-rel error_p1 ())
(declare-rel error ())
(rule (=> error_p0 error))
(rule (=> error_p1 error))
(query error)
"#;

const MIXED_MULTI_QUERY: &str = r#"
(set-logic HORN)
(declare-rel reached ())
(declare-rel never ())
(declare-rel error_p0 ())
(declare-rel error_p1 ())
(declare-rel error ())
(rule reached)
(rule (=> reached error_p0))
(rule (=> never error_p1))
(rule (=> error_p0 error))
(rule (=> error_p1 error))
(query error)
"#;

const SINGLE_SAFE_QUERY: &str = r#"
(set-logic HORN)
(declare-rel requested_leaf ())
(declare-rel requested_error ())
(rule (=> requested_leaf requested_error))
(query requested_error)
"#;

const DIFFERENT_SAFE_PROBLEM: &str = r#"
(set-logic HORN)
(declare-rel different_unreachable ())
(query different_unreachable)
"#;

const DIFFERENT_UNSAFE_PROBLEM: &str = r#"
(set-logic HORN)
(declare-rel different_reached ())
(rule different_reached)
(query different_reached)
"#;

fn parse(input: &str) -> ChcProblem {
    ChcParser::parse(input).expect("query proof-report fixture should parse")
}

fn strict_config() -> EncodeConfig {
    EncodeConfig::new()
        .with_proof_mode(ProofMode::Strict)
        .with_timeout(Duration::from_secs(10))
}

fn source_identity(problem: &ChcProblem) -> (String, u64) {
    let normalized = problem.normalized_input();
    (
        problem.normalized_input_sha256(),
        u64::try_from(normalized.len()).expect("test fixture length fits u64"),
    )
}

fn error_rows(ids: &[ay_chc::ChcQueryObligationId]) -> Vec<QueryObligationProofReportRow> {
    ids.iter()
        .cloned()
        .map(|id| QueryObligationProofReportRow::new(id, Err(EncodeError::Cancelled)))
        .collect()
}

#[test]
fn safe_batch_binds_source_rows_and_json() {
    let problem = parse(SAFE_MULTI_QUERY);
    let expected_source = source_identity(&problem);
    let report = solve_query_obligations_with_proof_report(&problem, &strict_config())
        .expect("two unreachable queries should produce a proof-report batch");

    assert_eq!(report.verdict(), QueryObligationBatchVerdict::Safe);
    assert!(report.accepted_as_proof());
    assert_eq!(report.source_normalized_input_sha256(), expected_source.0);
    assert_eq!(report.source_normalized_input_bytes(), expected_source.1);
    assert_eq!(
        report.source_normalized_input_content(),
        problem.normalized_input().as_bytes()
    );
    assert_eq!(
        ChcProofArtifactDigest::from_bytes("query-obligation-set", report.obligation_set_content())
            .sha256,
        report.obligation_set_sha256()
    );
    assert_eq!(report.rows().len(), 2);
    assert_eq!(report.rows()[0].id().label(), "error_p0");
    assert_eq!(report.rows()[1].id().label(), "error_p1");
    assert!(report.rows().iter().all(|row| {
        row.has_identity_input_binding()
            && row
                .outcome()
                .as_ref()
                .is_ok_and(|run| run.proof_run().result().is_safe())
    }));

    let json = report.to_json_value();
    assert_eq!(json["schema"], CHC_QUERY_BATCH_PROOF_REPORT_SCHEMA);
    assert_eq!(
        json["obligation_set"]["schema"],
        CHC_QUERY_OBLIGATION_SET_SCHEMA
    );
    assert_eq!(json["obligation_set"]["count"], 2);
    assert_eq!(json["result"], "safe");
    assert_eq!(json["disposition"], "all-proved");
    assert_eq!(json["accepted_as_proof"], true);
    assert_eq!(json["required_rows_identity_bound"], true);
    assert_eq!(json["serialized_admission"]["admissible"], false);
    assert_eq!(json["rows"][0]["obligation"]["label"], "error_p0");
    assert_eq!(json["rows"][1]["obligation"]["label"], "error_p1");
    assert!(serde_json::to_string(&json)
        .expect("batch JSON should serialize")
        .contains(CHC_QUERY_BATCH_PROOF_REPORT_SCHEMA));
}

#[test]
fn one_refuting_row_makes_the_complete_batch_unsafe() {
    let problem = parse(MIXED_MULTI_QUERY);
    let report = solve_query_obligations_with_proof_report(&problem, &strict_config())
        .expect("mixed query batch should finish every row");

    assert_eq!(report.rows().len(), 2);
    assert!(report.rows()[0]
        .outcome()
        .as_ref()
        .is_ok_and(|run| run.proof_run().result().is_unsafe()));
    assert!(report.rows()[1]
        .outcome()
        .as_ref()
        .is_ok_and(|run| run.proof_run().result().is_safe()));
    assert_eq!(
        report.verdict(),
        QueryObligationBatchVerdict::Unsafe {
            first_refuting_row: 0
        }
    );
    assert!(report.accepted_as_proof());

    let json = report.to_json_value();
    assert_eq!(json["result"], "unsafe");
    assert_eq!(json["disposition"], "refuted");
    assert_eq!(json["first_refuting_row"], 0);
}

#[test]
fn incomplete_error_rows_aggregate_to_unknown_without_being_omitted() {
    let problem = parse(SAFE_MULTI_QUERY);
    let obligations = problem
        .query_obligations()
        .expect("fixture should split into source-ordered obligations");
    let ids: Vec<_> = obligations
        .iter()
        .map(|obligation| obligation.id().clone())
        .collect();
    let rows = vec![
        QueryObligationProofReportRow::new(
            ids[0].clone(),
            Err(EncodeError::Unimplemented("injected row failure")),
        ),
        QueryObligationProofReportRow::new(ids[1].clone(), Err(EncodeError::Cancelled)),
    ];
    let report = QueryObligationBatchProofReport::new(
        problem.normalized_input(),
        &[],
        false,
        &ids,
        rows,
        Duration::ZERO,
    )
    .expect("complete source-ordered error rows remain a valid non-proof batch");

    assert_eq!(report.rows().len(), 2);
    assert_eq!(report.verdict(), QueryObligationBatchVerdict::Unknown);
    assert!(!report.accepted_as_proof());
    assert!(!report.trust_full_verifier_admissible());
    let json = report.to_json_value();
    assert_eq!(json["result"], "unknown");
    assert_eq!(json["disposition"], "inconclusive");
    assert_eq!(json["rows"][0]["invocation"]["error_code"], "unimplemented");
    assert_eq!(
        json["rows"][1]["invocation"]["error_code"],
        "cancelled-before-start"
    );
}

#[test]
fn precancelled_batch_preserves_every_identity_and_is_unknown() {
    let problem = parse(SAFE_MULTI_QUERY);
    let cancellation = CancellationToken::new();
    cancellation.cancel();
    let report = solve_query_obligations_with_proof_report_with_cancellation(
        &problem,
        &strict_config(),
        &cancellation,
    )
    .expect("pre-cancellation should return a complete non-proof envelope");

    assert_eq!(report.rows().len(), 2);
    assert_eq!(report.rows()[0].id().label(), "error_p0");
    assert_eq!(report.rows()[1].id().label(), "error_p1");
    assert!(report
        .rows()
        .iter()
        .all(|row| matches!(row.outcome(), Err(EncodeError::Cancelled))));
    assert_eq!(report.verdict(), QueryObligationBatchVerdict::Unknown);
    assert!(!report.accepted_as_proof());
}

#[test]
fn precancelled_checked_batch_preserves_order_and_fails_closed() {
    let problem = parse(SAFE_MULTI_QUERY);
    let cancellation = CancellationToken::new();
    cancellation.cancel();
    let report = solve_query_obligations_with_checked_proof_report_with_cancellation(
        &problem,
        &strict_config(),
        Duration::from_secs(10),
        &cancellation,
    )
    .expect("pre-cancellation should return a complete non-proof envelope");

    assert_eq!(report.rows().len(), 2);
    assert_eq!(report.rows()[0].id().label(), "error_p0");
    assert_eq!(report.rows()[1].id().label(), "error_p1");
    assert!(report
        .rows()
        .iter()
        .all(|row| matches!(row.outcome(), Err(EncodeError::Cancelled))));
    assert!(report
        .rows()
        .iter()
        .all(|row| row.checked_replay().is_none()));
    assert_eq!(report.verdict(), QueryObligationBatchVerdict::Unknown);
    assert!(!report.accepted_as_proof());
    assert!(!report.trust_full_verifier_admissible());
}

#[test]
fn source_without_any_query_is_rejected_before_batch_construction() {
    let error = solve_query_obligations_with_proof_report(&ChcProblem::new(), &EncodeConfig::new())
        .expect_err("a source without a query must remain invalid");
    assert!(matches!(error, EncodeError::Chc(ay_chc::ChcError::NoQuery)));
}

#[test]
fn obligation_identity_is_stable_and_constructor_rejects_omission_or_reordering() {
    let problem = parse(SAFE_MULTI_QUERY);
    let obligations = problem
        .query_obligations()
        .expect("fixture should split into source-ordered obligations");
    let ids: Vec<_> = obligations
        .iter()
        .map(|obligation| obligation.id().clone())
        .collect();
    let (source_sha256, source_bytes) = source_identity(&problem);
    let source_input = problem.normalized_input();
    let identity = obligation_set_sha256(&source_sha256, source_bytes, &[], false, &ids);

    assert_eq!(
        identity,
        obligation_set_sha256(&source_sha256, source_bytes, &[], false, &ids)
    );
    assert_eq!(identity.len(), 64);
    assert!(identity
        .bytes()
        .all(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f')));

    let mut reversed = ids.clone();
    reversed.reverse();
    assert_ne!(
        identity,
        obligation_set_sha256(&source_sha256, source_bytes, &[], false, &reversed),
        "row order is proof-relevant"
    );
    assert_ne!(
        identity,
        obligation_set_sha256(&source_sha256, source_bytes, &[], false, &ids[..1]),
        "row omission is proof-relevant"
    );
    let duplicate_ids = vec![ids[0].clone(), ids[0].clone()];
    assert_ne!(
        identity,
        obligation_set_sha256(&source_sha256, source_bytes, &[], false, &duplicate_ids),
        "row duplication is proof-relevant"
    );
    assert_ne!(
        identity,
        obligation_set_sha256(&"0".repeat(64), source_bytes, &[], false, &ids),
        "aggregate source identity is proof-relevant"
    );
    let mut pruned_problem = ChcProblem::new();
    pruned_problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        false,
    ))));
    assert_ne!(
        identity,
        obligation_set_sha256(
            &source_sha256,
            source_bytes,
            &pruned_problem.pruned_false_query_ids(),
            false,
            &ids,
        ),
        "vacuously pruned source query identities are proof-relevant"
    );
    assert_ne!(
        identity,
        obligation_set_sha256(&source_sha256, source_bytes, &[], true, &ids),
        "source over-approximation state is proof-relevant"
    );

    let omitted = QueryObligationBatchProofReport::new(
        source_input.clone(),
        &[],
        false,
        &ids,
        error_rows(&ids[..1]),
        Duration::ZERO,
    );
    assert!(matches!(
        omitted,
        Err(EncodeError::Chc(ay_chc::ChcError::Internal(_)))
    ));

    let reordered = QueryObligationBatchProofReport::new(
        source_input.clone(),
        &[],
        false,
        &ids,
        error_rows(&reversed),
        Duration::ZERO,
    );
    assert!(matches!(
        reordered,
        Err(EncodeError::Chc(ay_chc::ChcError::Internal(_)))
    ));

    let duplicated = QueryObligationBatchProofReport::new(
        source_input.clone(),
        &[],
        false,
        &duplicate_ids,
        error_rows(&duplicate_ids),
        Duration::ZERO,
    );
    assert!(matches!(
        duplicated,
        Err(EncodeError::Chc(ay_chc::ChcError::Internal(_)))
    ));

    let complete = QueryObligationBatchProofReport::new(
        source_input,
        &[],
        false,
        &ids,
        error_rows(&ids),
        Duration::ZERO,
    )
    .expect("the exact complete ordered ID set should be accepted");
    assert_eq!(complete.obligation_set_sha256(), identity);
}

#[test]
fn differing_safe_solved_hash_is_unknown_and_never_accepted_for_source() {
    let source = parse(SINGLE_SAFE_QUERY);
    let obligations = source
        .query_obligations()
        .expect("source fixture should have one obligation");
    let id = obligations[0].id().clone();
    let solved = solve_with_proof_report(parse(DIFFERENT_SAFE_PROBLEM), &strict_config())
        .expect("different safe fixture should produce a proof report")
        .with_checked_replay(Duration::from_secs(10));
    assert!(solved.proof_run().result().is_safe());
    assert!(solved.checked_replay().is_some());
    assert_ne!(
        solved.proof_run().metadata().normalized_input_sha256(),
        id.content_sha256()
    );

    let row = QueryObligationProofReportRow::new(id.clone(), Ok(solved));
    assert!(!row.has_identity_input_binding());
    assert!(row.checked_replay().is_none());
    let report = QueryObligationBatchProofReport::new(
        source.normalized_input(),
        &[],
        false,
        std::slice::from_ref(&id),
        vec![row],
        Duration::ZERO,
    )
    .expect("the private test can model AY-owned derived-input association");

    assert_eq!(report.verdict(), QueryObligationBatchVerdict::Unknown);
    assert!(!report.accepted_as_proof());
    assert!(!report.trust_full_verifier_admissible());
    let json = report.to_json_value();
    assert_eq!(json["required_rows_identity_bound"], false);
    assert_eq!(json["replay"]["status"], "not-replayable");
    assert_eq!(json["transcript"]["status"], "non-proof");
    assert_eq!(
        json["trust_full_verifier_non_admission_reason"],
        "aggregate_result_is_non_proof"
    );
    assert_eq!(
        json["rows"][0]["input_binding"]["kind"],
        "ay-owned-derived-input-unattested-for-source-replay"
    );
    assert_eq!(json["rows"][0]["accepted_as_proof"], false);
    assert_eq!(json["rows"][0]["result"], "unknown");
    assert_eq!(json["rows"][0]["solver_result"], "safe");
    assert_eq!(json["rows"][0]["trust_full_verifier_admissible"], false);
}

#[test]
fn differing_unsafe_solved_hash_cannot_refute_source() {
    let source = parse(SINGLE_SAFE_QUERY);
    let obligations = source
        .query_obligations()
        .expect("source fixture should have one obligation");
    let id = obligations[0].id().clone();
    let solved = solve_with_proof_report(parse(DIFFERENT_UNSAFE_PROBLEM), &strict_config())
        .expect("different unsafe fixture should produce a proof report");
    assert!(solved.proof_run().result().is_unsafe());
    assert_ne!(
        solved.proof_run().metadata().normalized_input_sha256(),
        id.content_sha256()
    );

    let report = QueryObligationBatchProofReport::new(
        source.normalized_input(),
        &[],
        false,
        std::slice::from_ref(&id),
        vec![QueryObligationProofReportRow::new(id.clone(), Ok(solved))],
        Duration::ZERO,
    )
    .expect("private test retains the mismatched row as diagnostic evidence");

    assert_eq!(report.verdict(), QueryObligationBatchVerdict::Unknown);
    assert!(!report.accepted_as_proof());
    assert_eq!(
        report.to_json_value()["rows"][0]["accepted_as_proof"],
        false
    );
}

#[test]
fn stripped_body_forall_source_cannot_admit_identity_bound_unsafe_row() {
    let mut source = parse(DIFFERENT_UNSAFE_PROBLEM);
    source.mark_stripped_body_forall();
    let obligations = source
        .query_obligations()
        .expect("source fixture should have one obligation");
    assert!(obligations[0].problem().has_stripped_body_forall());
    let id = obligations[0].id().clone();

    // The over-approximation bit is deliberately outside normalized SMT text,
    // so model the strongest possible internal mistake: an accepted report
    // for the byte-identical unflagged slice is paired with the flagged source.
    let unflagged_slice = parse(DIFFERENT_UNSAFE_PROBLEM)
        .query_obligations()
        .expect("unflagged fixture should have one obligation")
        .into_iter()
        .next()
        .expect("unflagged fixture obligation should survive")
        .into_parts()
        .1;
    let solved = solve_with_proof_report(unflagged_slice, &strict_config())
        .expect("unflagged unsafe fixture should produce a proof report");
    assert!(solved.proof_run().result().is_unsafe());
    assert_eq!(
        solved.proof_run().metadata().normalized_input_sha256(),
        id.content_sha256()
    );

    let report = QueryObligationBatchProofReport::new(
        source.normalized_input(),
        &[],
        true,
        std::slice::from_ref(&id),
        // `.clone()` like the sibling case above: `from_ref(&id)` holds a borrow
        // that lives until the call, so moving `id` into the row is E0505. The
        // Trust toolchain's newer borrow checker accepts it, which is why this
        // only surfaced in the public gate, where the export pins stock 1.97.1.
        vec![QueryObligationProofReportRow::new(id.clone(), Ok(solved))],
        Duration::ZERO,
    )
    .expect("complete identity-bound diagnostic row should remain inspectable");

    assert_eq!(report.verdict(), QueryObligationBatchVerdict::Unknown);
    assert!(!report.accepted_as_proof());
    assert!(!report.trust_full_verifier_admissible());
    let json = report.to_json_value();
    assert_eq!(json["result"], "unknown");
    assert_eq!(json["rows"][0]["result"], "unknown");
    assert_eq!(json["rows"][0]["solver_result"], "unsafe");
    assert_eq!(json["rows"][0]["accepted_as_proof"], false);
    assert_eq!(json["rows"][0]["trust_full_verifier_admissible"], false);
}

#[test]
fn checked_replay_batch_is_typed_full_verifier_admissible() {
    let problem = parse(SAFE_MULTI_QUERY);
    let report = solve_query_obligations_with_checked_proof_report(
        &problem,
        &strict_config(),
        Duration::from_secs(10),
    )
    .expect("checked replay should complete for two trivial safe rows");

    assert_eq!(report.verdict(), QueryObligationBatchVerdict::Safe);
    assert!(report.accepted_as_proof());
    assert!(report.trust_full_verifier_admissible());
    assert!(report.rows().iter().all(|row| {
        row.checked_replay().is_some_and(|checked| {
            checked
                .proof_run()
                .metadata()
                .trust_full_verifier_admissible()
                && !checked.problem_bytes().is_empty()
                && !checked.certificate_bytes().is_empty()
                && checked
                    .run_log_bytes()
                    .is_some_and(|bytes| !bytes.is_empty())
                && !checked.replay_log_bytes().is_empty()
                && !checked.checked_report_bytes().is_empty()
        })
    }));

    let json = report.to_json_value();
    assert_eq!(json["trust_full_verifier_admissible"], true);
    assert_eq!(json["replay"]["status"], "replayable");
    assert_eq!(
        json["serialized_admission"]["admissible"], false,
        "serialized booleans remain diagnostic even when the typed object admits"
    );
}

#[test]
fn live_cancellable_checked_batch_retains_admissible_source_order() {
    let problem = parse(SAFE_MULTI_QUERY);
    let cancellation = CancellationToken::new();
    let report = solve_query_obligations_with_checked_proof_report_with_cancellation(
        &problem,
        &strict_config(),
        Duration::from_secs(10),
        &cancellation,
    )
    .expect("live checked batch should solve and replay both rows");

    assert_eq!(report.verdict(), QueryObligationBatchVerdict::Safe);
    assert!(report.accepted_as_proof());
    assert!(report.trust_full_verifier_admissible());
    assert_eq!(report.rows().len(), 2);
    assert_eq!(report.rows()[0].id().label(), "error_p0");
    assert_eq!(report.rows()[1].id().label(), "error_p1");
    assert!(report
        .rows()
        .iter()
        .all(|row| row.checked_replay().is_some()));
}

#[test]
fn mixed_pruned_and_surviving_queries_preserve_source_accounting() {
    let mut problem = parse(SINGLE_SAFE_QUERY);
    problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        false,
    ))));

    let report = solve_query_obligations_with_checked_proof_report(
        &problem,
        &strict_config(),
        Duration::from_secs(10),
    )
    .expect("one surviving and one vacuous query should produce a complete envelope");

    assert_eq!(report.rows().len(), 1);
    assert_eq!(report.source_query_count(), 2);
    assert_eq!(report.source_pruned_false_query_count(), 1);
    assert_eq!(
        report.source_pruned_false_query_ids(),
        problem.pruned_false_query_ids()
    );
    assert_eq!(report.verdict(), QueryObligationBatchVerdict::Safe);
    assert!(report.accepted_as_proof());
    assert!(report.trust_full_verifier_admissible());

    let json = report.to_json_value();
    assert_eq!(json["obligation_set"]["count"], 2);
    assert_eq!(json["obligation_set"]["surviving_count"], 1);
    assert_eq!(json["obligation_set"]["pruned_false_count"], 1);
    assert_eq!(json["proof_status"], "verified-conjunction");
    assert_eq!(json["replay"]["status"], "replayable-with-source-vacuity");
    assert!(json["trust_full_verifier_non_admission_reason"].is_null());
}
