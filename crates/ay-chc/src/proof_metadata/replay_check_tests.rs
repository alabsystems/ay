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
    engines, validate_chc_ground_derivation_artifact, AdaptiveConfig, AdaptivePortfolio, BmcConfig,
    ChcEngineResult, ChcExpr, ChcGroundDerivationArtifactErrorReason, ChcParser, ChcProblem,
    ChcSort, ChcVar, InvariantModel, PdrConfig, PredicateInterpretation, VerifiedChcResult,
    VerifiedCounterexample, CHC_GROUND_DERIVATION_ARTIFACT_V2_ROLE,
    CHC_GROUND_DERIVATION_ARTIFACT_V2_SCHEMA,
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

include!("replay_check_tests/checked_run_assertions.rs");
#[path = "replay_check_tests/strict_bundle.rs"]
mod strict_bundle;
#[path = "replay_check_tests/strict_cert.rs"]
mod strict_cert;

#[test]
fn checked_replay_admits_small_safe_pdr_proof_end_to_end() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#,
    );
    let run = engines::solve_pdr_proof(problem.clone(), PdrConfig::default())
        .expect("PDR proof run should not error");
    assert!(run.accepted_as_proof(), "fixture should prove safe");
    assert_eq!(run.metadata().result(), "safe");

    let checked = run
        .run_checked_replay(REPLAY_TEST_BUDGET)
        .expect("checked replay should pass on a verified safe proof");
    assert_checked_run_invariants(&checked);

    strict_bundle::assert_strict_bundle_rows(&checked);
    checked
        .recheck_with_fresh_ay(REPLAY_TEST_BUDGET)
        .expect("retained checked replay must pass a full fresh AY recheck");

    // The strict-cert-bearing summary must round-trip through JSON with a
    // stable identity (the strict cert is part of the obligation identity).
    let summary_json = checked.summary().to_json_value();
    let reparsed = ChcCheckedReplaySummary::from_json_value(&summary_json)
        .expect("strict-cert summary JSON should re-parse");
    assert_eq!(reparsed.obligations, checked.summary().obligations);
    assert_eq!(
        reparsed.identity_sha256(),
        checked.summary().identity_sha256()
    );

    // The upgraded transcript JSON must clear model-checker-consumer's Route-B gate.
    let json = checked.proof_run().metadata().to_json_value();
    assert_eq!(route_b_native_proof_admission(&json), Ok(()));
    assert_eq!(json["trust_full_verifier_admissible"], true);
    assert_eq!(
        json["admission_policy"]["cache_hit_admission"],
        "admit-checked-proof-evidence"
    );

    // The metadata-only baseline is rejected with exactly the wishlist symptom.
    let baseline = run.metadata().to_json_value();
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
    let VerifiedChcResult::Safe(inv) = run.result() else {
        panic!("acyclic fixture should be safe");
    };
    assert!(
        inv.model().is_empty(),
        "fixture should exercise the empty-model acyclic-exhaustion class"
    );

    let checked = run
        .run_checked_replay(REPLAY_TEST_BUDGET)
        .expect("checked replay should pass on the acyclic-exhaustion certificate");
    assert_checked_run_invariants(&checked);
    assert!(
        !checked.summary().obligations.is_empty()
            && checked
                .summary()
                .obligations
                .iter()
                .all(|obligation| obligation.kind == ChcReplayObligationKind::Safety),
        "acyclic-exhaustion replay must synthesize Safety obligations"
    );
    // Synthesized safety obligations are UNSAT obligations discharged by the
    // native strict bundle checker, so each carries a verified strict cert.
    for obligation in &checked.summary().obligations {
        let cert = obligation
            .strict_cert
            .as_ref()
            .expect("acyclic-exhaustion safety obligation must carry a strict bundle cert");
        assert_eq!(cert.verdict, "verified");
    }
    let json = checked.proof_run().metadata().to_json_value();
    assert_eq!(route_b_native_proof_admission(&json), Ok(()));

    // Direct unit check on the synthesized obligation query.
    let obligations =
        acyclic_exhaustion_replay_obligations(&problem).expect("synthesis should succeed");
    assert_eq!(obligations.len(), 1);
    assert_eq!(obligations[0].kind, ChcReplayObligationKind::Safety);
    assert!(obligations[0].smtlib.contains("(check-sat)"));
    assert_eq!(
        crate::smt::executor_adapter::smtlib_first_verdict_via_executor_until(
            &obligations[0].smtlib,
            ay_core::time::Instant::now() + REPLAY_TEST_BUDGET,
            None,
        )
        .as_deref(),
        Some("unsat"),
        "the depth-exhaustion query must independently re-check UNSAT"
    );
}

#[test]
fn acyclic_replay_obligation_declares_scalar_uf() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun f (Int) Int)
(declare-fun P (Int) Bool)
(assert (forall ((x Int)) (=> (= (f x) 0) (P x))))
(assert (forall ((x Int)) (=> (and (P x) (distinct (f x) 0)) false)))
(check-sat)
"#,
    );

    let obligations = acyclic_exhaustion_replay_obligations(&problem)
        .expect("acyclic UF fixture should produce a replay obligation");
    assert_eq!(obligations.len(), 1);
    let script = &obligations[0].smtlib;
    let declaration = script
        .find("(declare-fun f (Int) Int)")
        .expect("replay script must reconstruct f's declaration");
    let use_site = script
        .find("(f ")
        .expect("expanded reachability formula must use f");
    assert!(
        declaration < use_site,
        "f must be declared before the expanded replay formula: {script}"
    );
}

#[test]
fn checked_replay_admits_acyclic_query_cone_with_dead_end_cycle() {
    // The Dead self-loop is cyclic but cannot reach the query. Proof solving,
    // validation, and replay all apply the same deterministic dead-end strip.
    // Query enumeration and digest binding must nevertheless stay on the
    // original four-clause input.
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun A (Int) Bool)
(declare-fun B (Int) Bool)
(declare-fun Dead (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (A x))))
(assert (forall ((x Int) (y Int)) (=> (and (A x) (= y (+ x 1))) (B y))))
(assert (forall ((x Int) (xp Int))
  (=> (and (Dead x) (> x 0) (= xp (- x 1))) (Dead xp))))
(assert (forall ((y Int)) (=> (and (B y) (> y 5)) false)))
(check-sat)
"#,
    );
    let run = engines::solve_pdr_proof(problem.clone(), PdrConfig::default())
        .expect("dead-end-cycle proof run should not error");
    assert!(
        run.accepted_as_proof(),
        "acyclic query cone should prove safe"
    );
    let VerifiedChcResult::Safe(inv) = run.result() else {
        panic!("dead-end-cycle fixture should be Safe");
    };
    assert!(
        inv.model().is_empty(),
        "fixture should exercise acyclic-exhaustion replay"
    );

    let raw_obligations = acyclic_exhaustion_replay_obligations(&problem)
        .expect("dead-end-cycle replay synthesis should succeed");
    assert_eq!(raw_obligations.len(), 1);
    assert_eq!(
        raw_obligations[0].clause_index, 3,
        "query index must stay on the original, unstripped clause vector"
    );
    assert!(
        raw_obligations[0]
            .smtlib
            .contains(run.metadata().normalized_input_sha256()),
        "replay obligation must retain the original normalized-input binding"
    );

    let checked = run
        .run_checked_replay(REPLAY_TEST_BUDGET)
        .expect("strict replay should reproduce the dead-end strip");
    assert_checked_run_invariants(&checked);
    assert_eq!(checked.summary().obligations.len(), 1);
    let obligation = &checked.summary().obligations[0];
    assert!(
        obligation.strict_cert.is_some(),
        "the stripped expansion must still receive a strict UNSAT certificate"
    );
}

#[test]
fn acyclic_replay_does_not_strip_cycle_that_reaches_query() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Loop (Int) Bool)
(assert (forall ((x Int) (xp Int))
  (=> (and (Loop x) (> x 0) (= xp (- x 1))) (Loop xp))))
(assert (forall ((x Int)) (=> (and (Loop x) (< x 0)) false)))
(check-sat)
"#,
    );

    let error = acyclic_exhaustion_replay_obligations(&problem)
        .expect_err("a cycle in the query cone must remain ineligible");
    assert!(
        error
            .to_string()
            .contains("requires an acyclic clause system"),
        "cycle-in-cone rejection should be explicit: {error}"
    );
}

#[test]
fn dead_end_strip_does_not_hide_reachable_error() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun A (Int) Bool)
(declare-fun B (Int) Bool)
(declare-fun Dead (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (A x))))
(assert (forall ((x Int) (y Int)) (=> (and (A x) (= y x)) (B y))))
(assert (forall ((x Int) (xp Int))
  (=> (and (Dead x) (> x 0) (= xp (- x 1))) (Dead xp))))
(assert (forall ((y Int)) (=> (and (B y) (= y 0)) false)))
(check-sat)
"#,
    );
    let obligations =
        acyclic_exhaustion_replay_obligations(&problem).expect("dead-end strip should succeed");
    assert_eq!(obligations.len(), 1);
    assert_eq!(
        crate::smt::executor_adapter::smtlib_first_verdict_via_executor_until(
            &obligations[0].smtlib,
            ay_core::time::Instant::now() + REPLAY_TEST_BUDGET,
            None,
        )
        .as_deref(),
        Some("sat"),
        "the original reachable error must remain visible after stripping"
    );

    // Even a forged empty-model Safe marker stays non-admissible: strict replay
    // observes SAT and refuses to produce an UNSAT certificate.
    let result = VerifiedChcResult::from_validated(
        ChcEngineResult::Safe(InvariantModel::default()),
        ValidationEvidence::ScalarAcyclicBmcExhaustive { max_depth: 3 },
    );
    let run = ChcPdrProofRun::new(problem.clone(), result, "bmc");
    assert!(
        run.run_checked_replay(REPLAY_TEST_BUDGET).is_err(),
        "reachable error must fail the strict checked-replay gate"
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
    let VerifiedChcResult::Unsafe(verified) = result else {
        unreachable!("asserted Unsafe above")
    };
    let mut counterexample = verified.into_inner();
    counterexample.ground_derivation = None;
    let result = VerifiedChcResult::Unsafe(VerifiedCounterexample::from_validated(counterexample));
    let run = ChcPdrProofRun::new(problem.clone(), result, "bmc");

    let checked = run
        .run_checked_replay(REPLAY_TEST_BUDGET)
        .expect("checked replay should validate the unsafe trace");
    assert_checked_run_invariants(&checked);
    assert_eq!(checked.summary().verdict, "unsafe");
    assert_eq!(checked.summary().schema, CHC_CHECKED_REPLAY_SUMMARY_SCHEMA);
    assert_eq!(checked.summary().obligations.len(), 1);
    assert_eq!(
        checked.summary().obligations[0].kind,
        ChcReplayObligationKind::TraceValidity
    );
    // A trace-validity (SAT-witness) obligation has no UNSAT proof, so it
    // carries no strict bundle cert. This fixture deliberately removed the
    // ground derivation to exercise the legacy fresh-SMT fallback.
    assert!(checked.summary().obligations[0].strict_cert.is_none());
    let payload = checked
        .obligation_payloads()
        .next()
        .expect("trace validity payload");
    assert_eq!(payload.obligation(), &checked.summary().obligations[0]);
    let query_bytes = payload
        .smt_query_bytes()
        .expect("single-predicate fallback retains SMT-LIB");
    assert_eq!(payload.obligation().query.sha256, sha256_hex(query_bytes));
    assert!(payload.strict_bundle_bytes().is_none());
    assert!(payload.alethe_bytes().is_none());
    checked
        .recheck_with_fresh_ay(REPLAY_TEST_BUDGET)
        .expect("retained trace validity query must remain SAT on fresh AY state");

    // Route B admits SAFE proofs only; a checked unsafe transcript is still
    // rejected there (by result), never by replayability.
    let json = checked.proof_run().metadata().to_json_value();
    assert_eq!(
        route_b_native_proof_admission(&json),
        Err("non_safe_result")
    );
}

#[test]
fn checked_replay_validates_multi_predicate_unsafe_ground_derivation() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun GroundPath0 (Int) Bool)
(declare-fun GroundPath1 (Int) Bool)
(assert (GroundPath0 0))
(assert (forall ((x Int)) (=> (GroundPath0 x) (GroundPath1 (+ x 1)))))
(assert (forall ((x Int)) (=> (and (GroundPath1 x) (= x 1)) false)))
(check-sat)
"#,
    );
    let result = AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::test_default())
        .solve_bmc_only(BmcConfig {
            max_depth: 2,
            acyclic_safe: true,
            prefer_exact_acyclic_first: true,
            time_budget: Some(Duration::from_secs(20)),
            enable_k_induction: false,
            enable_adaptive_stepping: false,
            ..BmcConfig::default()
        });
    let VerifiedChcResult::Unsafe(verified) = &result else {
        panic!("multi-predicate reachable fixture must produce Unsafe");
    };
    assert!(
        verified.counterexample().has_ground_derivation(),
        "exact BMC result must retain a deciding ground derivation"
    );
    let result_for_reordered_source = result.clone();

    let run = ChcPdrProofRun::new(problem.clone(), result, "bmc");
    let checked = run
        .run_checked_replay(REPLAY_TEST_BUDGET)
        .expect("multi-predicate ground derivation should admit checked replay");
    assert_checked_run_invariants(&checked);
    assert_eq!(checked.summary().verdict, "unsafe");
    assert_eq!(
        checked.summary().schema,
        CHC_CHECKED_REPLAY_SUMMARY_SCHEMA_V2
    );
    assert_eq!(checked.summary().obligations.len(), 1);
    let row = &checked.summary().obligations[0];
    assert_eq!(row.kind, ChcReplayObligationKind::TraceValidity);
    assert_eq!(
        row.payload_format,
        ChcReplayPayloadFormat::GroundDerivationV1
    );
    assert!(row.strict_cert.is_none());

    let payload = checked
        .obligation_payloads()
        .next()
        .expect("ground derivation payload");
    assert!(payload.smt_query_bytes().is_none());
    let artifact_bytes = payload
        .ground_derivation_artifact_bytes()
        .expect("ground artifact bytes");
    assert_eq!(row.query.sha256, sha256_hex(artifact_bytes));
    assert!(payload.strict_bundle_bytes().is_none());
    assert!(payload.alethe_bytes().is_none());
    let validated = validate_chc_ground_derivation_artifact(&problem, artifact_bytes)
        .expect("transported artifact must validate against the exact source problem");
    assert_eq!(validated.step_count(), 3);
    checked
        .recheck_with_fresh_ay(REPLAY_TEST_BUDGET)
        .expect("fresh source-bound ground replay must remain valid");
    assert!(checked.manifest().trust_full_verifier_admissible());
    assert!(checked
        .proof_run()
        .metadata()
        .trust_full_verifier_admissible());

    let report_json: serde_json::Value =
        serde_json::from_slice(checked.checked_report_bytes()).expect("checked report JSON");
    let reparsed = ChcCheckedReplaySummary::from_json_value(&report_json)
        .expect("v2 ground replay report must round-trip");
    assert_eq!(&reparsed, checked.summary());

    // The finite-UF payload has its own summary schema and artifact role.
    // Exercise the structural parser independently of solver production so an
    // older v2 reader cannot silently reinterpret the new row.
    let mut v3_summary = checked.summary().clone();
    v3_summary.schema = CHC_CHECKED_REPLAY_SUMMARY_SCHEMA_V3;
    v3_summary.obligations[0].payload_format = ChcReplayPayloadFormat::GroundDerivationV2;
    v3_summary.obligations[0].query.role = CHC_GROUND_DERIVATION_ARTIFACT_V2_ROLE.to_string();
    let v3_json = v3_summary.to_json_value();
    assert_eq!(v3_json["schema_version"], 3);
    assert_eq!(
        ChcCheckedReplaySummary::from_json_value(&v3_json)
            .expect("v3 finite-UF row should round-trip structurally"),
        v3_summary
    );

    let mut v2_mislabeled_v3 = v3_json;
    v2_mislabeled_v3["schema"] =
        serde_json::Value::String(CHC_CHECKED_REPLAY_SUMMARY_SCHEMA_V2.to_string());
    v2_mislabeled_v3["schema_version"] = serde_json::Value::from(2);
    assert!(
        ChcCheckedReplaySummary::from_json_value(&v2_mislabeled_v3).is_err(),
        "summary v2 must reject a ground-derivation-v2 row"
    );

    let run_log: serde_json::Value = serde_json::from_slice(
        checked
            .run_log_bytes()
            .expect("self-contained checked run log"),
    )
    .expect("ground run log JSON");
    assert_eq!(run_log["schema"], "ay.chc-checked-replay-run-log/v2");
    assert_eq!(run_log["schema_version"], 2);
    let replay_log: serde_json::Value =
        serde_json::from_slice(checked.replay_log_bytes()).expect("ground replay log JSON");
    assert_eq!(replay_log["schema"], "ay.chc-checked-replay-log/v2");
    assert_eq!(replay_log["schema_version"], 2);

    let parsed_manifest =
        ChcProofEvidenceManifest::from_json_value(&checked.manifest().to_json_value())
            .expect_err("serialized data must not recreate AY's opaque in-process authority");
    assert!(parsed_manifest.reasons().iter().any(|reason| {
        reason.contains("cannot recover AY's in-process replay seal")
            || reason.contains("fresh payload validation")
    }));

    let mut missing_format = report_json.clone();
    missing_format["obligations"][0]
        .as_object_mut()
        .expect("obligation object")
        .remove("payload_format");
    assert!(
        ChcCheckedReplaySummary::from_json_value(&missing_format).is_err(),
        "v2 must not default a missing ground payload format to SMT"
    );

    let mut null_identity = report_json.clone();
    null_identity["obligations"][0]["identity_sha256"] = serde_json::Value::Null;
    assert!(
        ChcCheckedReplaySummary::from_json_value(&null_identity).is_err(),
        "v2 obligation identity must be a concrete lowercase SHA-256"
    );

    let mut wrong_role = report_json.clone();
    wrong_role["obligations"][0]["query"]["role"] =
        serde_json::Value::String("replay-obligation".to_string());
    assert!(
        ChcCheckedReplaySummary::from_json_value(&wrong_role).is_err(),
        "ground bytes under the SMT artifact role must reject"
    );

    let mut reordered = problem.clone();
    reordered.clauses_mut().swap(0, 1);
    assert_eq!(
        reordered.normalized_input_sha256(),
        problem.normalized_input_sha256(),
        "semantic normalized identity deliberately ignores source clause order"
    );
    let reordered_run = ChcPdrProofRun::new(reordered, result_for_reordered_source, "bmc");
    let mut options = ChcProofEvidenceOptions::pdr_strict(&PdrConfig::default());
    options.proof_mode = "checked-replay:bmc".to_string();
    let solver = ChcProofSolverIdentity::new("bmc");
    let obligation_id = format!(
        "ay-chc:checked-replay:{}",
        problem.normalized_input_sha256()
    );
    let reordered_manifest = reordered_run.evidence_manifest_with_replay_evidence(
        options,
        solver,
        obligation_id,
        checked
            .manifest()
            .replay_evidence()
            .expect("checked replay evidence")
            .clone(),
    );
    let reorder_reasons =
        reordered_manifest.checked_replay_summary_rejection_reasons(checked.summary());
    assert!(
        reorder_reasons
            .iter()
            .any(|reason| reason.contains("source_clause_sequence_sha256")),
        "reordered positional source must reject: {reorder_reasons:?}"
    );
    assert_ne!(
        reordered_manifest.cache_lookup_key_sha256(),
        checked.manifest().cache_lookup_key_sha256(),
        "ground replay cache identity must bind positional source clauses"
    );
}

#[test]
fn supplied_smt_evidence_keeps_legacy_trace_replay_when_ground_is_available() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (Inv 0))
(assert (forall ((x Int)) (=> (Inv x) (Inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x 1)) false)))
(check-sat)
"#,
    );
    // Route through the exact executor lane, the one model-checker-consumer's BMC shortcut
    // and the adaptive front probe use (both set a per-depth timeout). Without
    // one, `concrete_scalar_bmc_applicable` hands this cyclic Int fixture to
    // the concrete scalar lane, whose SMT-replayed Unsafe has never carried a
    // ground derivation (unchanged since 3304604e8), so the "ground is
    // available" precondition below could not hold.
    let result = AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::test_default())
        .solve_bmc_only(
            BmcConfig::default()
                .with_max_depth(2)
                .with_time_budget(REPLAY_TEST_BUDGET)
                .with_per_depth_timeout(REPLAY_TEST_BUDGET),
        );
    let VerifiedChcResult::Unsafe(verified) = &result else {
        panic!("reachable fixture must produce Unsafe");
    };
    assert!(verified.counterexample().has_ground_derivation());
    let legacy = verified
        .counterexample()
        .trace_validity_replay_obligations(&problem)
        .expect("single-predicate trace fallback")
        .into_iter()
        .next()
        .expect("one trace obligation");

    let run = ChcPdrProofRun::new(problem.clone(), result, "bmc");
    let mut options = ChcProofEvidenceOptions::pdr_strict(&PdrConfig::default());
    options.proof_mode = "checked-replay:bmc".to_string();
    let solver = ChcProofSolverIdentity::new("bmc");
    let obligation_id = format!(
        "ay-chc:checked-replay:{}",
        problem.normalized_input_sha256()
    );
    let evidence = ChcReplayEvidence::new(
        problem.normalized_input_sha256(),
        options.identity_sha256(),
        solver.identity_sha256(),
        obligation_id.clone(),
        "unsafe",
        "verified-counterexample",
    )
    .with_replay_obligation(ChcReplayObligationArtifact::new(
        legacy.kind,
        ChcProofArtifactDigest::from_bytes("replay-obligation", legacy.smtlib.as_bytes()),
    ));

    let checked = run
        .run_checked_replay_with_binding(
            options,
            solver,
            obligation_id,
            Some(evidence),
            REPLAY_TEST_BUDGET,
        )
        .expect("supplied SMT evidence should select the matching fallback");
    let row = &checked.summary().obligations[0];
    assert_eq!(row.payload_format, ChcReplayPayloadFormat::SmtlibV1);
    assert_eq!(row.query.sha256, sha256_hex(legacy.smtlib.as_bytes()));
    assert!(checked
        .obligation_payloads()
        .next()
        .expect("SMT payload")
        .smt_query_bytes()
        .is_some());
}

#[test]
fn checked_replay_upgrades_ordinary_uf_ground_evidence_to_v2() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun f (Int) Int)
(declare-fun P (Int) Bool)
(assert (P (f 0)))
(assert (forall ((x Int)) (=> (P x) false)))
(check-sat)
"#,
    );
    let result = AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::test_default())
        .solve_bmc_only(BmcConfig {
            max_depth: 2,
            acyclic_safe: true,
            prefer_exact_acyclic_first: true,
            time_budget: Some(Duration::from_secs(20)),
            enable_k_induction: false,
            enable_adaptive_stepping: false,
            ..BmcConfig::default()
        });
    let VerifiedChcResult::Unsafe(verified) = &result else {
        panic!("ordinary-UF fact/query fixture must produce Unsafe");
    };
    assert!(verified.counterexample().has_ground_derivation());
    assert_eq!(
        verified
            .counterexample()
            .ground_derivation_artifact(&problem)
            .expect_err("artifact v1 must remain UF-free")
            .reason,
        ChcGroundDerivationArtifactErrorReason::UnsupportedUninterpretedFunction
    );

    let checked = ChcPdrProofRun::new(problem.clone(), result, "bmc")
        .run_checked_replay(REPLAY_TEST_BUDGET)
        .expect("checked replay should select source-authenticated artifact v2");
    assert_checked_run_invariants(&checked);
    assert_eq!(
        checked.summary().schema,
        CHC_CHECKED_REPLAY_SUMMARY_SCHEMA_V3
    );
    assert_eq!(checked.summary().obligations.len(), 1);
    assert_eq!(
        checked.summary().obligations[0].payload_format,
        ChcReplayPayloadFormat::GroundDerivationV2
    );
    assert_eq!(
        checked.summary().obligations[0].query.role,
        CHC_GROUND_DERIVATION_ARTIFACT_V2_ROLE
    );
    let artifact_bytes = checked
        .obligation_payloads()
        .next()
        .and_then(|payload| payload.ground_derivation_artifact_bytes())
        .expect("checked v2 row retains exact artifact bytes");
    let validated = crate::validate_chc_ground_derivation_artifact_v2(&problem, artifact_bytes)
        .expect("retained v2 artifact must independently validate");
    assert_eq!(
        validated.artifact_schema(),
        CHC_GROUND_DERIVATION_ARTIFACT_V2_SCHEMA
    );
    assert_eq!(validated.uf_observation_count(), 1);
    checked
        .recheck_with_fresh_ay(REPLAY_TEST_BUDGET)
        .expect("fresh replay must dispatch to the v2 validator");
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

    assert!(run.run_checked_replay(Duration::ZERO).is_err());

    // A failed replay cannot mutate the sealed metadata-only run.
    let metadata = run.metadata();
    assert!(!metadata.trust_full_verifier_admissible());
    assert_eq!(metadata.replay_status(), "replay-artifacts-required");
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
    let run = ChcPdrProofRun::new(problem.clone(), result, "pdr");

    let error = run
        .run_checked_replay(REPLAY_TEST_BUDGET)
        .expect_err("non-discharging model must fail the checked replay");
    // A safety obligation is an UNSAT obligation now discharged by the
    // retained native solve (`strict_bundle::discharge_retained`). A bogus
    // model makes it replay SAT, so no bound UNSAT proof is minted and the
    // pass fails closed to metadata-only, for that cause and no other.
    assert!(
        error
            .to_string()
            .contains("retained obligation did not establish UNSAT"),
        "failure should name the non-discharging strict obligation: {error}"
    );
    assert!(!error.to_string().contains("interrupted"), "{error}");

    let metadata = run.metadata();
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
        .run_checked_replay(REPLAY_TEST_BUDGET)
        .expect("checked replay should pass");
    let json = checked.proof_run().metadata().to_json_value();
    assert_eq!(json["trust_full_verifier_admissible"], true);

    // A JSON round-trip (i.e. any copied/cached transcript) must fail closed:
    // parsing can never reconstruct the private checked-replay digest set.
    let parsed = ChcProofTranscriptMetadata::from_json_value(&json)
        .expect("checked transcript JSON should parse");
    assert!(!parsed.trust_full_verifier_admissible());
    assert_eq!(parsed.replay_status(), "replayable");
    assert_eq!(
        parsed.to_json_value()["trust_full_verifier_admissible"],
        false
    );
    // Identity stays stable across the round-trip (admission-key stability).
    assert_eq!(
        parsed.identity_sha256(),
        checked.proof_run().metadata().identity_sha256()
    );
}
