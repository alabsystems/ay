//! Unit tests for the post-solve CHECKED replay pass (`super`).
//!
//! Includes a byte-faithful replication of model-checker-consumer's Route-B native-proof
//! admission checks (`trust_model_checker_consumer_chc_pdr_evidence_payload`,
//! model-checker-consumer-driver/src/harness_runner.rs) so the transcript JSON AY emits is
//! provably admissible without linking model-checker-consumer.

use super::super::*;
use super::acyclic_exhaustion_replay_obligations;
use crate::engine_result::ValidationEvidence;
use crate::pdr::ChcReplayObligationKind;
use crate::{
    engines, AdaptiveConfig, AdaptivePortfolio, BmcConfig, ChcEngineResult, ChcExpr, ChcParser,
    ChcProblem, ChcSort, ChcVar, InvariantModel, PdrConfig, PredicateInterpretation,
    VerifiedChcResult,
};
use std::time::Duration;

const REPLAY_TEST_BUDGET: Duration = Duration::from_mins(1);

fn parse_problem(input: &str) -> ChcProblem {
    ChcParser::parse(input).expect("CHC fixture should parse")
}

/// Replication of model-checker-consumer's Route-B admission gate on
/// `ay.chc-proof-transcript/v1` JSON. Field checks and rejection labels are
/// ported verbatim from `trust_model_checker_consumer_chc_pdr_evidence_payload`
/// (model-checker-consumer-driver/src/harness_runner.rs:329).
fn route_b_native_proof_admission(metadata: &serde_json::Value) -> Result<(), &'static str> {
    fn string_field<'a>(value: &'a serde_json::Value, path: &[&str]) -> Option<&'a str> {
        let mut cursor = value;
        for key in path {
            cursor = cursor.get(*key)?;
        }
        cursor.as_str()
    }
    fn bool_field(value: &serde_json::Value, path: &[&str]) -> Option<bool> {
        let mut cursor = value;
        for key in path {
            cursor = cursor.get(*key)?;
        }
        cursor.as_bool()
    }
    fn sha256_field<'a>(value: &'a serde_json::Value, path: &[&str]) -> Option<&'a str> {
        string_field(value, path).filter(|digest| {
            digest.len() == 64
                && digest.bytes().all(|byte| byte.is_ascii_hexdigit())
                && digest.bytes().all(|byte| !byte.is_ascii_uppercase())
        })
    }

    if string_field(metadata, &["schema"]) != Some("ay.chc-proof-transcript/v1") {
        return Err("unexpected_schema");
    }
    if bool_field(metadata, &["accepted_as_proof"]) != Some(true) {
        return Err("not_accepted_as_proof");
    }
    if string_field(metadata, &["result"]) != Some("safe") {
        return Err("non_safe_result");
    }
    if string_field(metadata, &["replay", "status"]) != Some("replayable") {
        return Err("replay_not_replayable");
    }
    if string_field(metadata, &["transcript", "status"]) != Some("replayable") {
        return Err("transcript_not_replayable");
    }
    if bool_field(metadata, &["transcript", "metadata_only"]) == Some(true) {
        return Err("transcript_metadata_only");
    }
    string_field(metadata, &["transcript", "uri"])
        .or_else(|| string_field(metadata, &["transcript", "path"]))
        .or_else(|| string_field(metadata, &["transcript_uri"]))
        .or_else(|| string_field(metadata, &["transcript_path"]))
        .filter(|value| !value.trim().is_empty())
        .ok_or("missing_transcript_path")?;
    sha256_field(metadata, &["transcript", "sha256"])
        .or_else(|| sha256_field(metadata, &["transcript", "digest"]))
        .or_else(|| sha256_field(metadata, &["transcript", "hash", "value"]))
        .or_else(|| sha256_field(metadata, &["transcript_sha256"]))
        .ok_or("missing_transcript_sha256")?;
    if sha256_field(metadata, &["replay", "sha256"])
        .or_else(|| sha256_field(metadata, &["replay", "digest"]))
        .or_else(|| sha256_field(metadata, &["replay", "hash", "value"]))
        .or_else(|| sha256_field(metadata, &["replay_log_sha256"]))
        .is_none()
    {
        return Err("missing_replay_sha256");
    }
    if sha256_field(metadata, &["checked_report", "sha256"])
        .or_else(|| sha256_field(metadata, &["checked_report", "digest"]))
        .or_else(|| sha256_field(metadata, &["checked_report", "hash", "value"]))
        .or_else(|| sha256_field(metadata, &["checked_proof_report", "sha256"]))
        .or_else(|| sha256_field(metadata, &["checked_proof_report", "digest"]))
        .or_else(|| sha256_field(metadata, &["checked_proof_report", "hash", "value"]))
        .or_else(|| sha256_field(metadata, &["checked_report_sha256"]))
        .is_none()
    {
        return Err("missing_checked_report_sha256");
    }
    Ok(())
}

fn assert_checked_run_invariants(checked: &super::ChcCheckedReplayRun) {
    assert!(checked.manifest.trust_full_verifier_admissible());
    assert_eq!(
        checked.manifest.cache_admission_status(),
        "admit-checked-proof-evidence"
    );
    let metadata = &checked.proof_run.metadata;
    assert!(metadata.trust_full_verifier_admissible());
    assert_eq!(metadata.replay_status, "replayable");
    assert_eq!(metadata.transcript_status, "replayable");
    assert!(metadata.trust_full_verifier_non_admission_reason.is_none());

    let digests = metadata
        .checked_replay
        .as_ref()
        .expect("checked metadata should carry the private digest set");
    assert!(is_lower_sha256(&digests.transcript_sha256));
    assert!(is_lower_sha256(&digests.replay_log_sha256));
    assert!(is_lower_sha256(&digests.checked_report_sha256));
    assert_eq!(
        digests.checked_report_sha256,
        sha256_hex(&checked.checked_report_bytes)
    );
    assert_eq!(
        digests.replay_log_sha256,
        sha256_hex(&checked.replay_log_bytes)
    );
    if let Some(run_log_bytes) = &checked.run_log_bytes {
        assert_eq!(digests.transcript_sha256, sha256_hex(run_log_bytes));
    }
    assert_eq!(
        digests.summary_identity_sha256,
        checked.summary.identity_sha256()
    );
}

#[test]
fn checked_replay_admits_small_safe_pdr_proof_end_to_end() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (< x 5) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (> x 10)) false)))
(check-sat)
"#,
    );
    let run = engines::solve_pdr_proof(problem.clone(), PdrConfig::default())
        .expect("PDR proof run should not error");
    assert!(run.accepted_as_proof(), "fixture should prove safe");
    assert_eq!(run.metadata.result, "safe");

    let checked = run
        .run_checked_replay(&problem, REPLAY_TEST_BUDGET)
        .expect("checked replay should pass on a verified safe proof");
    assert_checked_run_invariants(&checked);

    // Every UNSAT obligation (initiation/consecution/safety) must carry a
    // native strict-Alethe certificate — the self-contained, no-z3 evidence
    // that it was discharged by a REAL Alethe-verified proof, not a trusted
    // re-run verdict.
    assert!(
        !checked.summary.obligations.is_empty(),
        "safe PDR proof should have replay obligations"
    );
    for obligation in &checked.summary.obligations {
        assert_ne!(obligation.kind, ChcReplayObligationKind::TraceValidity);
        let cert = obligation.strict_cert.as_ref().unwrap_or_else(|| {
            panic!(
                "unsat obligation {} must carry a native strict-Alethe cert",
                obligation.name
            )
        });
        assert_eq!(cert.verdict, "verified");
        assert_eq!(cert.alethe_sha256.len(), 64);
        assert_eq!(cert.bundle_sha256.len(), 64);
    }

    // The strict-cert-bearing summary must round-trip through JSON with a
    // stable identity (the strict cert is part of the obligation identity).
    let summary_json = checked.summary.to_json_value();
    let reparsed = ChcCheckedReplaySummary::from_json_value(&summary_json)
        .expect("strict-cert summary JSON should re-parse");
    assert_eq!(reparsed.obligations, checked.summary.obligations);
    assert_eq!(
        reparsed.identity_sha256(),
        checked.summary.identity_sha256()
    );

    // The upgraded transcript JSON must clear model-checker-consumer's Route-B gate.
    let json = checked.proof_run.metadata.to_json_value();
    assert_eq!(route_b_native_proof_admission(&json), Ok(()));
    assert_eq!(json["trust_full_verifier_admissible"], true);
    assert_eq!(
        json["admission_policy"]["cache_hit_admission"],
        "admit-checked-proof-evidence"
    );

    // The metadata-only baseline is rejected with exactly the wishlist symptom.
    let baseline = run.metadata.to_json_value();
    assert_eq!(
        route_b_native_proof_admission(&baseline),
        Err("replay_not_replayable")
    );
}

#[test]
fn checked_replay_admits_bmc_acyclic_exhaustion_safe() {
    // Two-predicate acyclic DAG: the proof-grade PDR entry decides it through
    // the exact acyclic BMC certificate prepass, yielding an EMPTY invariant
    // model whose replay set is the synthesized depth-exhaustion obligations.
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun A (Int) Bool)
(declare-fun B (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (A x))))
(assert (forall ((x Int) (y Int)) (=> (and (A x) (= y (+ x 1))) (B y))))
(assert (forall ((y Int)) (=> (and (B y) (> y 5)) false)))
(check-sat)
"#,
    );
    let run = engines::solve_pdr_proof(problem.clone(), PdrConfig::default())
        .expect("acyclic proof run should not error");
    assert!(run.accepted_as_proof(), "acyclic fixture should prove safe");
    let VerifiedChcResult::Safe(inv) = &run.result else {
        panic!("acyclic fixture should be safe");
    };
    assert!(
        inv.model().is_empty(),
        "fixture should exercise the empty-model acyclic-exhaustion class"
    );

    let checked = run
        .run_checked_replay(&problem, REPLAY_TEST_BUDGET)
        .expect("checked replay should pass on the acyclic-exhaustion certificate");
    assert_checked_run_invariants(&checked);
    assert!(
        !checked.summary.obligations.is_empty()
            && checked
                .summary
                .obligations
                .iter()
                .all(|obligation| obligation.kind == ChcReplayObligationKind::Safety),
        "acyclic-exhaustion replay must synthesize Safety obligations"
    );
    // Synthesized safety obligations are UNSAT obligations discharged by the
    // native strict-Alethe self-check, so each carries a verified strict cert.
    for obligation in &checked.summary.obligations {
        let cert = obligation
            .strict_cert
            .as_ref()
            .expect("acyclic-exhaustion safety obligation must carry a strict-Alethe cert");
        assert_eq!(cert.verdict, "verified");
    }
    let json = checked.proof_run.metadata.to_json_value();
    assert_eq!(route_b_native_proof_admission(&json), Ok(()));

    // Direct unit check on the synthesized obligation query.
    let obligations =
        acyclic_exhaustion_replay_obligations(&problem).expect("synthesis should succeed");
    assert_eq!(obligations.len(), 1);
    assert_eq!(obligations[0].kind, ChcReplayObligationKind::Safety);
    assert!(obligations[0].smtlib.contains("(check-sat)"));
    assert_eq!(
        crate::smt::executor_adapter::smtlib_first_verdict_via_executor(
            &obligations[0].smtlib,
            Some(Duration::from_secs(20)),
        )
        .as_deref(),
        Some("unsat"),
        "the depth-exhaustion query must independently re-check UNSAT"
    );
}

#[test]
fn checked_replay_validates_unsafe_trace() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x 1)) false)))
(check-sat)
"#,
    );
    let result = AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::test_default())
        .solve_bmc_only(BmcConfig::default().with_max_depth(2));
    assert!(result.is_unsafe(), "BMC fixture should produce Unsafe");
    let run = ChcPdrProofRun::new(&problem, result, "bmc");

    let checked = run
        .run_checked_replay(&problem, REPLAY_TEST_BUDGET)
        .expect("checked replay should validate the unsafe trace");
    assert_checked_run_invariants(&checked);
    assert_eq!(checked.summary.verdict, "unsafe");
    assert_eq!(checked.summary.obligations.len(), 1);
    assert_eq!(
        checked.summary.obligations[0].kind,
        ChcReplayObligationKind::TraceValidity
    );
    // A trace-validity (SAT-witness) obligation has no UNSAT proof, so it
    // carries no strict-Alethe cert — it stays on the trusted ground-eval path.
    assert!(checked.summary.obligations[0].strict_cert.is_none());

    // Route B admits SAFE proofs only; a checked unsafe transcript is still
    // rejected there (by result), never by replayability.
    let json = checked.proof_run.metadata.to_json_value();
    assert_eq!(
        route_b_native_proof_admission(&json),
        Err("non_safe_result")
    );
}

#[test]
fn checked_replay_fails_closed_on_zero_budget_and_keeps_metadata_only() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun A (Int) Bool)
(declare-fun B (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (A x))))
(assert (forall ((x Int) (y Int)) (=> (and (A x) (= y (+ x 1))) (B y))))
(assert (forall ((y Int)) (=> (and (B y) (> y 5)) false)))
(check-sat)
"#,
    );
    let run = engines::solve_pdr_proof(problem.clone(), PdrConfig::default())
        .expect("acyclic proof run should not error");
    assert!(run.accepted_as_proof());

    assert!(run.run_checked_replay(&problem, Duration::ZERO).is_err());

    // The degrading entry point returns the metadata-only transcript, which
    // Route B rejects with exactly the wishlist symptom.
    let metadata = run
        .result
        .checked_proof_transcript_metadata(&problem, "pdr", Duration::ZERO);
    assert!(!metadata.trust_full_verifier_admissible());
    assert_eq!(metadata.replay_status, "replay-artifacts-required");
    assert_eq!(
        route_b_native_proof_admission(&metadata.to_json_value()),
        Err("replay_not_replayable")
    );
}

#[test]
fn checked_replay_rejects_model_that_does_not_discharge_safety() {
    // A bogus "safe" model (Inv := true) does NOT discharge the query clause;
    // the safety obligation replays SAT, so the pass must fail closed and the
    // run must stay metadata-only. (Constructing the sealed result directly is
    // only possible inside the crate — mirrors the tamper tests above.)
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) (> x 0)) false)))
(check-sat)
"#,
    );
    let mut model = InvariantModel::new();
    let pred = problem
        .get_predicate_by_name("Inv")
        .expect("fixture predicate");
    model.set(
        pred.id,
        PredicateInterpretation::new(vec![ChcVar::new("x", ChcSort::Int)], ChcExpr::Bool(true)),
    );
    let result = VerifiedChcResult::from_validated(
        ChcEngineResult::Safe(model),
        ValidationEvidence::FullVerification,
    );
    let run = ChcPdrProofRun::new(&problem, result, "pdr");

    let error = run
        .run_checked_replay(&problem, REPLAY_TEST_BUDGET)
        .expect_err("non-discharging model must fail the checked replay");
    // A safety obligation is an UNSAT obligation now discharged by the native
    // strict-Alethe self-check. A bogus model makes it replay SAT, so no UNSAT
    // certificate is produced and the pass fails closed to metadata-only.
    assert!(
        error
            .to_string()
            .contains("did not produce a native strict-Alethe UNSAT certificate"),
        "failure should name the non-discharging strict-Alethe obligation: {error}"
    );

    let metadata =
        run.result
            .checked_proof_transcript_metadata(&problem, "pdr", REPLAY_TEST_BUDGET);
    assert!(!metadata.trust_full_verifier_admissible());
    assert_eq!(
        route_b_native_proof_admission(&metadata.to_json_value()),
        Err("replay_not_replayable")
    );
}

#[test]
fn parsed_checked_transcript_metadata_is_never_admissible() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun A (Int) Bool)
(declare-fun B (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (A x))))
(assert (forall ((x Int) (y Int)) (=> (and (A x) (= y (+ x 1))) (B y))))
(assert (forall ((y Int)) (=> (and (B y) (> y 5)) false)))
(check-sat)
"#,
    );
    let run = engines::solve_pdr_proof(problem.clone(), PdrConfig::default())
        .expect("acyclic proof run should not error");
    let checked = run
        .run_checked_replay(&problem, REPLAY_TEST_BUDGET)
        .expect("checked replay should pass");
    let json = checked.proof_run.metadata.to_json_value();
    assert_eq!(json["trust_full_verifier_admissible"], true);

    // A JSON round-trip (i.e. any copied/cached transcript) must fail closed:
    // parsing can never reconstruct the private checked-replay digest set.
    let parsed = ChcProofTranscriptMetadata::from_json_value(&json)
        .expect("checked transcript JSON should parse");
    assert!(!parsed.trust_full_verifier_admissible());
    assert_eq!(parsed.replay_status, "replayable");
    assert_eq!(
        parsed.to_json_value()["trust_full_verifier_admissible"],
        false
    );
    // Identity stays stable across the round-trip (admission-key stability).
    assert_eq!(
        parsed.identity_sha256(),
        checked.proof_run.metadata.identity_sha256()
    );
}
