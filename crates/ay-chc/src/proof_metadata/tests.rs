//! Unit tests for CHC proof-metadata / evidence-manifest types (`super`).
//! Extracted verbatim from the parent module to keep it readable.

use super::*;
use crate::engine_result::ValidationEvidence;
use crate::{
    AdaptiveConfig, AdaptivePortfolio, BmcConfig, ChcEngineResult, ChcParser, Counterexample,
    CounterexampleStep, InvariantModel,
};

fn parse_problem(input: &str) -> ChcProblem {
    ChcParser::parse(input).expect("CHC fixture should parse")
}

#[test]
fn normalized_hash_ignores_whitespace_and_clause_order() {
    let first = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#,
    );
    let second = parse_problem(
        r#"
 (set-logic HORN)
 (declare-fun Inv (Int) Bool)
 (assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
 (assert (forall ((x Int) (xp Int))
     (=> (and (= xp (+ x 1)) (Inv x)) (Inv xp))))
 (assert (forall ((x Int)) (=> (= x 0) (Inv x))))
 (check-sat)
"#,
    );

    assert_eq!(
        normalized_chc_input_sha256(&first),
        normalized_chc_input_sha256(&second)
    );
    assert_eq!(first.normalized_input_sha256().len(), 64);
}

#[test]
fn metadata_marks_unknown_budget_as_non_proof() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(check-sat)
"#,
    );
    let result = VerifiedChcResult::from_validated(
        ChcEngineResult::Unknown,
        ValidationEvidence::BmcBudgetExhausted {
            depth_reached: 2,
            max_depth: 10,
        },
    );

    let metadata = result.proof_transcript_metadata(&problem, "pdr");
    assert_eq!(metadata.result(), "unknown");
    assert_eq!(metadata.proof_status(), "non-proof");
    assert!(!metadata.accepted_as_proof());
    assert_eq!(metadata.unknown_reason(), Some("bmc_budget_exhausted"));

    let json = metadata.to_json_value();
    assert_eq!(json["accepted_as_proof"], false);
    assert_eq!(json["proof_status"], "non-proof");
    assert_eq!(json["non_proof_reason"], "bmc_budget_exhausted");
}

#[test]
fn metadata_marks_verified_safe_as_proof_evidence() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(check-sat)
"#,
    );
    let result = VerifiedChcResult::from_validated(
        ChcEngineResult::Safe(InvariantModel::new()),
        ValidationEvidence::FullVerification,
    );

    let metadata = result.proof_transcript_metadata(&problem, "pdr");
    assert_eq!(metadata.result(), "safe");
    assert_eq!(metadata.proof_status(), "verified-invariant");
    assert!(metadata.accepted_as_proof());
    assert!(!metadata.trust_full_verifier_admissible());
    assert_eq!(
        metadata.trust_full_verifier_non_admission_reason(),
        Some("metadata_only_missing_checked_replay_artifacts")
    );
    assert_eq!(metadata.pdr_input_sha256().len(), 64);
    assert!(metadata.normalized_input_bytes() > 0);
}

#[test]
fn consumer_evidence_marks_unknown_fail_closed_with_limit_codes() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#,
    );
    let result = VerifiedChcResult::from_validated(
        ChcEngineResult::Unknown,
        ValidationEvidence::BmcBudgetExhausted {
            depth_reached: 2,
            max_depth: 10,
        },
    );
    let run = ChcPdrProofRun::new(problem.clone(), result, "pdr");

    let evidence = run.consumer_evidence();
    assert_eq!(
        evidence.schema(),
        CHC_PROOF_TRANSCRIPT_CONSUMER_EVIDENCE_SCHEMA
    );
    assert_eq!(evidence.verdict_code(), "unknown");
    assert_eq!(evidence.backend_code(), "ay_chc_pdr");
    assert!(!evidence.accepted_for_consumer());
    assert_eq!(
        evidence.consumer_rejection_code(),
        Some("ay_chc_unknown_bmc_budget_exhausted")
    );
    assert!(!evidence.model_validated());
    assert_eq!(evidence.model_validation_status(), "not_validated");
    assert_eq!(evidence.verification_level_code(), "ay_chc_non_proof");
    assert_eq!(evidence.unknown_reason_code(), Some("bmc_budget_exhausted"));
    assert_eq!(evidence.unknown_limit_code(), Some("bmc_budget_exhausted"));
    assert_eq!(evidence.unknown_depth_reached(), Some(2));
    assert_eq!(evidence.unknown_depth_limit(), Some(10));
    assert_eq!(evidence.query_clause_index(), Some(1));

    let json = evidence.to_json_value();
    assert_eq!(json["accepted_for_consumer"], false);
    assert_eq!(
        json["consumer_rejection_code"],
        "ay_chc_unknown_bmc_budget_exhausted"
    );
    assert_eq!(json["unknown_reason_code"], "bmc_budget_exhausted");
    assert_eq!(json["unknown_limit_code"], "bmc_budget_exhausted");
    assert_eq!(json["unsafe_trace"]["status"], "not_applicable");
    assert_eq!(json["trust_status"], "trust_full_verifier_rejected");
}

#[test]
fn consumer_evidence_carries_validated_unsafe_trace_assignments() {
    let mut problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x 1)) false)))
(check-sat)
"#,
    );
    let action = problem.declare_action("Inc");
    let predicate = problem.predicates()[0].id;
    let result = VerifiedChcResult::from_validated(
        ChcEngineResult::Unsafe(Counterexample::new(vec![
            CounterexampleStep::new(
                predicate,
                [("__p0_a0".to_string(), 0), ("z".to_string(), -1)]
                    .into_iter()
                    .collect(),
            )
            .with_clause(0),
            CounterexampleStep::new(
                predicate,
                [("y".to_string(), 7), ("x".to_string(), 1)]
                    .into_iter()
                    .collect(),
            )
            .with_action(action)
            .with_clause(1),
        ])),
        ValidationEvidence::CounterexampleVerification,
    );
    let run = ChcPdrProofRun::new(problem.clone(), result, "portfolio");

    let evidence = run.consumer_evidence();
    assert_eq!(evidence.verdict_code(), "unsafe");
    assert_eq!(evidence.backend_code(), "ay_chc_portfolio");
    assert!(evidence.accepted_for_consumer());
    assert!(evidence.model_validated());
    assert_eq!(evidence.model_validation_status(), "validated");
    assert_eq!(
        evidence.verification_level_code(),
        "ay_chc_verified_counterexample"
    );
    assert_eq!(evidence.proof_status(), "verified-counterexample");
    assert!(!evidence.trust_full_verifier_admissible());
    assert_eq!(evidence.replay_status(), "replay-artifacts-required");
    assert_eq!(evidence.transcript_status(), "metadata-only");
    assert_eq!(evidence.query_clause_index(), Some(2));

    let trace = evidence
        .unsafe_trace()
        .expect("unsafe evidence should carry a trace");
    assert_eq!(trace.status, "validated_counterexample");
    assert_eq!(trace.step_count, 2);
    assert_eq!(trace.steps[0].predicate_name.as_deref(), Some("Inv"));
    assert_eq!(trace.steps[0].clause_index, Some(0));
    assert_eq!(
        trace.steps[0].assignments,
        vec![
            ChcTraceAssignmentEvidence {
                name: "__p0_a0".to_string(),
                predicate_argument_index: Some(0),
                sort: Some("Int".to_string()),
                value: 0,
            },
            ChcTraceAssignmentEvidence {
                name: "z".to_string(),
                predicate_argument_index: None,
                sort: None,
                value: -1,
            },
        ]
    );
    assert_eq!(trace.steps[1].action_id, Some(action.index() as u64));
    assert_eq!(trace.steps[1].action_name.as_deref(), Some("Inc"));
    assert_eq!(
        trace.steps[1].assignments,
        vec![
            ChcTraceAssignmentEvidence {
                name: "x".to_string(),
                predicate_argument_index: None,
                sort: None,
                value: 1,
            },
            ChcTraceAssignmentEvidence {
                name: "y".to_string(),
                predicate_argument_index: None,
                sort: None,
                value: 7,
            },
        ]
    );

    let json = evidence.to_json_value();
    assert_eq!(json["verdict_code"], "unsafe");
    assert_eq!(json["backend_code"], "ay_chc_portfolio");
    assert_eq!(json["model_validated"], true);
    assert_eq!(
        json["unsafe_trace"]["steps"][0]["assignments"][0]["sort"],
        "Int"
    );
    assert_eq!(
        json["unsafe_trace"]["steps"][0]["assignments"][0]["predicate_argument_index"],
        0
    );
    assert_eq!(json["unsafe_trace"]["steps"][1]["action_name"], "Inc");
}

#[test]
fn consumer_evidence_carries_bmc_concrete_trace_predicate_arguments() {
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
    let VerifiedChcResult::Unsafe(counterexample) = &result else {
        panic!("BMC fixture should produce Unsafe, got {result}");
    };
    let replay_obligations = counterexample
        .counterexample()
        .trace_validity_replay_obligations(&problem)
        .expect("canonical BMC trace assignments should replay");
    assert_eq!(replay_obligations.len(), 1);

    let run = ChcPdrProofRun::new(problem.clone(), result, "bmc");
    let evidence = run.consumer_evidence();
    assert_eq!(evidence.verdict_code(), "unsafe");
    assert!(evidence.accepted_for_consumer());
    assert!(evidence.model_validated());

    let trace = evidence
        .unsafe_trace()
        .expect("unsafe BMC evidence should carry concrete trace material");
    assert_eq!(trace.status, "validated_counterexample");
    assert_eq!(trace.step_count, 2);
    for step in &trace.steps {
        assert_eq!(step.predicate_name.as_deref(), Some("Inv"));
        assert_eq!(step.assignments.len(), 1);
        assert_eq!(
            step.assignments[0].name, "__p0_a0",
            "BMC trace evidence should expose AY-owned canonical predicate argument names"
        );
        assert_eq!(step.assignments[0].predicate_argument_index, Some(0));
        assert_eq!(step.assignments[0].sort.as_deref(), Some("Int"));
    }

    let json = evidence.to_json_value();
    assert_eq!(
        json["unsafe_trace"]["steps"][0]["assignments"][0]["predicate_argument_index"],
        0
    );
    assert_eq!(
        json["unsafe_trace"]["steps"][1]["assignments"][0]["predicate_argument_index"],
        0
    );
}

#[test]
fn bmc_trace_assignment_completeness_accepts_expected_shape() {
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
    let run = ChcPdrProofRun::new(problem.clone(), result, "bmc");
    let evidence = run.consumer_evidence();

    let report = evidence.bmc_unsafe_trace_assignment_completeness(2, 1);
    assert_eq!(
        report.status,
        ChcBmcUnsafeTraceAssignmentCompletenessStatus::Accepted
    );
    assert_eq!(
        report.reason,
        ChcBmcUnsafeTraceAssignmentCompletenessReason::Complete
    );
    assert_eq!(report.status_code, "accepted");
    assert_eq!(report.reason_code, "complete");
    assert!(report.accepted_for_consumer);
    assert!(!report.fail_closed);
    assert_eq!(report.expected_assignment_count, 2);
    assert_eq!(report.covered_assignment_count, 2);
    assert_eq!(
        bmc_unsafe_trace_assignment_completeness(&evidence, 2, 1),
        report
    );

    let json = report.to_json_value();
    assert_eq!(
        json["schema"],
        CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_COMPLETENESS_SCHEMA
    );
    assert_eq!(json["status"], "accepted");
    assert_eq!(json["reason"], "complete");
    assert_eq!(
        json["assignment_contract_schema"],
        CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_CONTRACT_SCHEMA
    );
}

#[test]
fn bmc_trace_assignment_completeness_rejects_missing_and_incomplete_trace() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(check-sat)
"#,
    );
    let safe_run = ChcPdrProofRun::new(
        problem.clone(),
        VerifiedChcResult::from_validated(
            ChcEngineResult::Safe(InvariantModel::new()),
            ValidationEvidence::FullVerification,
        ),
        "pdr",
    );
    let missing = safe_run
        .consumer_evidence()
        .bmc_unsafe_trace_assignment_completeness(1, 1);
    assert_eq!(
        missing.status,
        ChcBmcUnsafeTraceAssignmentCompletenessStatus::Rejected
    );
    assert_eq!(
        missing.reason,
        ChcBmcUnsafeTraceAssignmentCompletenessReason::MissingUnsafeTrace
    );
    assert_eq!(missing.reason_code, "missing_unsafe_trace");
    assert!(missing.fail_closed);
    assert!(!missing.accepted_for_consumer);

    let predicate = problem.predicates()[0].id;
    let unsafe_run = ChcPdrProofRun::new(
        problem.clone(),
        VerifiedChcResult::from_validated(
            ChcEngineResult::Unsafe(Counterexample::new(vec![CounterexampleStep::new(
                predicate,
                [("not_canonical".to_string(), 0)].into_iter().collect(),
            )])),
            ValidationEvidence::CounterexampleVerification,
        ),
        "bmc",
    );
    let incomplete = unsafe_run
        .consumer_evidence()
        .bmc_unsafe_trace_assignment_completeness(1, 1);
    assert_eq!(
        incomplete.reason,
        ChcBmcUnsafeTraceAssignmentCompletenessReason::IncompletePredicateArgumentAssignments
    );
    assert_eq!(
        incomplete.reason_code,
        "incomplete_predicate_argument_assignments"
    );
    assert_eq!(incomplete.first_problem_step_index, Some(0));
    assert_eq!(incomplete.first_problem_predicate_argument_index, Some(0));
    assert_eq!(incomplete.covered_assignment_count, 0);
}

#[test]
fn bmc_trace_assignment_completeness_rejects_bad_assignment_encodings() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x 0)) false)))
(check-sat)
"#,
    );
    let predicate = problem.predicates()[0].id;
    let run = ChcPdrProofRun::new(
        problem.clone(),
        VerifiedChcResult::from_validated(
            ChcEngineResult::Unsafe(Counterexample::new(vec![CounterexampleStep::new(
                predicate,
                [("__p0_a0".to_string(), 0)].into_iter().collect(),
            )])),
            ValidationEvidence::CounterexampleVerification,
        ),
        "bmc",
    );
    let mut evidence = run.consumer_evidence();

    let trace = evidence
        .unsafe_trace
        .as_mut()
        .expect("unsafe fixture should carry trace assignments");
    trace.steps[0].assignments[0].sort = Some("Real".to_string());
    let unsupported = evidence.bmc_unsafe_trace_assignment_completeness(1, 1);
    assert_eq!(
        unsupported.reason,
        ChcBmcUnsafeTraceAssignmentCompletenessReason::UnsupportedSortEncoding
    );
    assert_eq!(
        unsupported.reason_code,
        "ay_chc_bmc_trace_assignment_sort_unsupported"
    );
    assert_eq!(unsupported.first_problem_sort.as_deref(), Some("Real"));

    let trace = evidence
        .unsafe_trace
        .as_mut()
        .expect("unsafe fixture should carry trace assignments");
    trace.steps[0].assignments[0].sort = Some("Bool".to_string());
    trace.steps[0].assignments[0].value = 2;
    let out_of_range = evidence.bmc_unsafe_trace_assignment_completeness(1, 1);
    assert_eq!(
        out_of_range.reason,
        ChcBmcUnsafeTraceAssignmentCompletenessReason::ValueOutOfRange
    );
    assert_eq!(
        out_of_range.reason_code,
        "ay_chc_bmc_trace_assignment_value_out_of_range"
    );
    assert_eq!(out_of_range.first_problem_value, Some(2));
}

#[test]
fn bmc_trace_assignment_contract_describes_downstream_required_shape() {
    let contract = bmc_unsafe_trace_assignment_contract();
    let json = contract.to_json_value();

    assert_eq!(
        json["schema"],
        CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_CONTRACT_SCHEMA
    );
    assert_eq!(json["schema_version"], 1);
    assert_eq!(json["scope"], "unsafe_trace.steps[].assignments[]");
    assert_eq!(json["producer"], "ay_chc_bmc");
    assert_eq!(
        json["canonical_name_format"],
        "__p{predicate_id}_a{predicate_argument_index}"
    );

    let required_fields = json["required_fields"]
        .as_array()
        .expect("contract should expose required assignment fields");
    for field in ["name", "predicate_argument_index", "sort", "value"] {
        assert!(
            required_fields.contains(&serde_json::json!(field)),
            "contract should require {field}"
        );
    }

    let supported_sorts = json["supported_sort_families"]
        .as_array()
        .expect("contract should expose supported sort families");
    for sort in ["Bool", "Int", "BitVec(width)"] {
        assert!(
            supported_sorts.contains(&serde_json::json!(sort)),
            "contract should support {sort}"
        );
    }

    let fail_closed_sorts = json["fail_closed_sort_families"]
        .as_array()
        .expect("contract should expose fail-closed sort families");
    for sort in [
        "Real",
        "Array",
        "Datatype",
        "Uninterpreted",
        "BitVec(value_does_not_fit_i64)",
    ] {
        assert!(
            fail_closed_sorts.contains(&serde_json::json!(sort)),
            "contract should fail closed for {sort}"
        );
    }
    assert_eq!(
        json["unsupported_sort_reason_code"],
        "ay_chc_bmc_trace_assignment_sort_unsupported"
    );
    assert_eq!(
        json["value_out_of_range_reason_code"],
        "ay_chc_bmc_trace_assignment_value_out_of_range"
    );
}

#[test]
fn consumer_evidence_carries_btor2_bv_bmc_trace_predicate_arguments() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv ((_ BitVec 8)) Bool)
(assert (forall ((count (_ BitVec 8))) (=> (= count #x00) (Inv count))))
(assert (forall ((count (_ BitVec 8)) (count_next (_ BitVec 8)))
    (=> (and (Inv count) (= count_next (bvadd count #x01))) (Inv count_next))))
(assert (forall ((count (_ BitVec 8))) (=> (and (Inv count) (= count #x03)) false)))
(check-sat)
"#,
    );
    let result = AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::test_default())
        .solve_bmc_only(BmcConfig::default().with_max_depth(4));
    let VerifiedChcResult::Unsafe(counterexample) = &result else {
        panic!("BTOR2-style BV BMC fixture should produce Unsafe, got {result}");
    };
    let replay_obligations = counterexample
        .counterexample()
        .trace_validity_replay_obligations(&problem)
        .expect("canonical BV BMC trace assignments should replay");
    assert_eq!(replay_obligations.len(), 1);

    let run = ChcPdrProofRun::new(problem.clone(), result, "bmc");
    let evidence = run.consumer_evidence();
    assert_eq!(evidence.verdict_code(), "unsafe");
    assert!(evidence.accepted_for_consumer());
    assert!(evidence.model_validated());

    let trace = evidence
        .unsafe_trace()
        .expect("unsafe BV BMC evidence should carry concrete trace material");
    assert_eq!(trace.status, "validated_counterexample");
    assert_eq!(trace.step_count, 4);
    let values: Vec<_> = trace
        .steps
        .iter()
        .map(|step| {
            assert_eq!(step.predicate_name.as_deref(), Some("Inv"));
            let assignment = step
                .assignments
                .iter()
                .find(|assignment| assignment.name == "__p0_a0")
                .expect("BV BMC trace evidence should expose a canonical predicate argument");
            assert_eq!(
                assignment.name, "__p0_a0",
                "BV BMC trace evidence should expose AY-owned canonical predicate argument names"
            );
            assert_eq!(assignment.predicate_argument_index, Some(0));
            assert_eq!(assignment.sort.as_deref(), Some("BitVec(8)"));
            assignment.value
        })
        .collect();
    assert_eq!(values, vec![0, 1, 2, 3]);

    let json = evidence.to_json_value();
    let contract = &json["unsafe_trace_assignment_contract"];
    assert_eq!(
        contract["schema"],
        CHC_BMC_UNSAFE_TRACE_ASSIGNMENT_CONTRACT_SCHEMA
    );
    assert_eq!(
        contract["canonical_name_format"],
        "__p{predicate_id}_a{predicate_argument_index}"
    );
    assert!(contract["supported_sort_families"]
        .as_array()
        .expect("contract should expose supported sorts")
        .contains(&serde_json::json!("BitVec(width)")));

    let assignment = &json["unsafe_trace"]["steps"][3]["assignments"][0];
    for field in contract["required_fields"]
        .as_array()
        .expect("contract should expose required fields")
    {
        let field = field
            .as_str()
            .expect("required field names should be strings");
        assert!(
            assignment.get(field).is_some_and(|value| !value.is_null()),
            "emitted BTOR2-style assignment should satisfy required field {field}"
        );
    }
    assert_eq!(assignment["name"], "__p0_a0");
    assert_eq!(assignment["predicate_argument_index"], 0);
    assert_eq!(assignment["sort"], "BitVec(8)");
    assert_eq!(assignment["value"], 3);
    assert_eq!(
        format!(
            "__p{}_a{}",
            json["unsafe_trace"]["steps"][3]["predicate_id"]
                .as_u64()
                .expect("predicate_id should be numeric"),
            assignment["predicate_argument_index"]
                .as_u64()
                .expect("predicate_argument_index should be numeric")
        ),
        assignment["name"]
            .as_str()
            .expect("assignment name should be a string")
    );
}

#[test]
fn evidence_manifest_rejects_metadata_only_trust_admission() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(check-sat)
"#,
    );
    let result = VerifiedChcResult::from_validated(
        ChcEngineResult::Safe(InvariantModel::new()),
        ValidationEvidence::FullVerification,
    );
    let run = ChcPdrProofRun::new(problem.clone(), result, "pdr");
    let options = ChcProofEvidenceOptions::pdr_strict(
        &PdrConfig::default()
            .with_max_frames(8)
            .with_max_iterations(100),
    );
    let solver = ChcProofSolverIdentity::new("pdr")
        .with_ay_revision("abc123")
        .with_solver_binary_sha256(
            "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
        );
    let manifest = run.evidence_manifest(options.clone(), solver.clone(), "trust:test:obligation");
    let json = manifest.to_json_value();

    assert!(run.accepted_as_proof());
    assert!(!manifest.trust_full_verifier_admissible());
    assert_eq!(
        manifest.cache_admission_status(),
        "reject-non-admissible-proof-evidence"
    );
    assert_eq!(json["schema"], CHC_EVIDENCE_MANIFEST_SCHEMA);
    assert_eq!(
        json["admission"]["cache_hit_admission"],
        "reject-non-admissible-proof-evidence"
    );
    assert_eq!(
        json["result"]["trust_full_verifier_admissible"],
        serde_json::json!(false)
    );
    assert_eq!(manifest.admission_key_sha256().len(), 64);

    let mut tampered_json = run.metadata().to_json_value();
    tampered_json["trust_full_verifier_admissible"] = serde_json::json!(true);
    let parsed = ChcProofTranscriptMetadata::from_json_value(&tampered_json)
        .expect("well-typed reporting metadata should parse");
    assert!(!parsed.trust_full_verifier_admissible());
    assert_eq!(
        parsed.to_json_value()["trust_full_verifier_admissible"],
        serde_json::json!(false)
    );
}

fn replay_evidence(
    problem: &ChcProblem,
    options: &ChcProofEvidenceOptions,
    solver: &ChcProofSolverIdentity,
    obligation_id: &str,
    result: &str,
    proof_status: &str,
) -> ChcReplayEvidence {
    ChcReplayEvidence::new(
        normalized_chc_input_sha256(problem),
        options.identity_sha256(),
        solver.identity_sha256(),
        obligation_id,
        result,
        proof_status,
    )
    .with_solver_transcript(
        ChcProofArtifactDigest::from_bytes("solver-transcript", b"pdr transcript\n")
            .with_path("artifacts/transcript.jsonl"),
    )
    .with_proof(
        ChcProofArtifactDigest::from_bytes("proof-certificate", b"(ay-chc certificate)\n")
            .with_path("artifacts/certificate.smt2"),
    )
    .with_replay_report(
        ChcProofArtifactDigest::from_bytes("replay-report", b"{\"status\":\"pass\"}\n")
            .with_path("artifacts/replay-report.json"),
    )
    .with_replay_obligation(ChcReplayObligationArtifact::new(
        ChcReplayObligationKind::Initiation,
        ChcProofArtifactDigest::from_bytes("replay-obligation", b"; initiation\n(assert false)\n")
            .with_path("artifacts/000-initiation.smt2"),
    ))
    .with_replay_obligation(ChcReplayObligationArtifact::new(
        ChcReplayObligationKind::Consecution,
        ChcProofArtifactDigest::from_bytes("replay-obligation", b"; consecution\n(assert false)\n")
            .with_path("artifacts/001-consecution.smt2"),
    ))
    .with_replay_obligation(ChcReplayObligationArtifact::new(
        ChcReplayObligationKind::Safety,
        ChcProofArtifactDigest::from_bytes("replay-obligation", b"; safety\n(assert false)\n")
            .with_path("artifacts/002-safety.smt2"),
    ))
}

fn unsafe_trace_replay_evidence(
    problem: &ChcProblem,
    options: &ChcProofEvidenceOptions,
    solver: &ChcProofSolverIdentity,
    obligation_id: &str,
) -> ChcReplayEvidence {
    ChcReplayEvidence::new(
        normalized_chc_input_sha256(problem),
        options.identity_sha256(),
        solver.identity_sha256(),
        obligation_id,
        "unsafe",
        "verified-counterexample",
    )
    .with_solver_transcript(
        ChcProofArtifactDigest::from_bytes("solver-transcript", b"pdr unsafe transcript\n")
            .with_path("artifacts/unsafe-transcript.jsonl"),
    )
    .with_proof(
        ChcProofArtifactDigest::from_bytes("proof-certificate", b"; AY CHC Certificate: UNSAFE\n")
            .with_path("artifacts/unsafe-certificate.smt2"),
    )
    .with_replay_report(
        ChcProofArtifactDigest::from_bytes("replay-report", b"{\"status\":\"pass\"}\n")
            .with_path("artifacts/unsafe-replay-report.json"),
    )
    .with_counterexample(
        ChcProofArtifactDigest::counterexample_from_bytes(b"Inv(0) -> Inv(1) -> false\n")
            .with_path("artifacts/counterexample.trace"),
    )
    .with_replay_obligation(ChcReplayObligationArtifact::new(
        ChcReplayObligationKind::TraceValidity,
        ChcProofArtifactDigest::from_bytes(
            "replay-obligation",
            b"; trace-validity\n(assert true)\n",
        )
        .with_path("artifacts/000-trace-validity.smt2"),
    ))
}

fn checked_summary_for_manifest(manifest: &ChcProofEvidenceManifest) -> ChcCheckedReplaySummary {
    let evidence = manifest
        .replay_evidence
        .as_ref()
        .expect("test manifest should carry replay evidence");
    let obligations = evidence
        .replay_obligations
        .iter()
        .map(|artifact| {
            ChcCheckedReplayObligation::new(
                artifact.kind.as_str(),
                artifact.kind,
                artifact.query.clone(),
                format!("z3 {}", artifact.query.path.as_deref().unwrap_or("<query>")),
                ChcReplayCheckResult::pass(),
            )
        })
        .collect();

    ChcCheckedReplaySummary {
        schema: CHC_CHECKED_REPLAY_SUMMARY_SCHEMA,
        status: "pass".to_string(),
        surface: "CHC certificates".to_string(),
        ay_commit: Some("rev-a".to_string()),
        failure_kind: None,
        diagnostic_only: false,
        verdict: manifest.result.clone(),
        checker: ChcReplayCheckerIdentity::new("z3", "z3 test", true),
        command: "z3 artifacts/*.smt2".to_string(),
        manifest_binding: manifest.checked_replay_manifest_binding(),
        problem: ChcProofArtifactDigest::from_sha256(
            "problem",
            manifest.problem_sha256.clone(),
            manifest.problem_bytes,
        )
        .with_path("artifacts/problem.smt2"),
        certificate: evidence
            .proof
            .clone()
            .expect("test evidence should carry proof"),
        run_log: evidence
            .solver_transcript
            .clone()
            .expect("test evidence should carry transcript"),
        replay_log: evidence
            .replay_report
            .clone()
            .expect("test evidence should carry replay report"),
        result: ChcReplayCheckResult::pass(),
        obligations,
        errors: Vec::new(),
    }
}

fn safe_manifest_with_replay_evidence<F>(
    obligation_id: &str,
    mutate_evidence: F,
) -> ChcProofEvidenceManifest
where
    F: FnOnce(&mut ChcReplayEvidence),
{
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(check-sat)
"#,
    );
    let result = VerifiedChcResult::from_validated(
        ChcEngineResult::Safe(InvariantModel::new()),
        ValidationEvidence::FullVerification,
    );
    let run = ChcPdrProofRun::new(problem.clone(), result, "pdr");
    let options = ChcProofEvidenceOptions::pdr_strict(&PdrConfig::default());
    let solver = ChcProofSolverIdentity::new("pdr")
        .with_ay_revision("rev-a")
        .with_solver_binary_sha256(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        );
    let mut evidence = replay_evidence(
        &problem,
        &options,
        &solver,
        obligation_id,
        "safe",
        "verified-invariant",
    );
    mutate_evidence(&mut evidence);
    run.evidence_manifest_with_replay_evidence(options, solver, obligation_id, evidence)
}

fn admitted_safe_manifest(obligation_id: &str) -> ChcProofEvidenceManifest {
    let manifest = safe_manifest_with_replay_evidence(obligation_id, |_| {});
    let summary = checked_summary_for_manifest(&manifest);
    manifest
        .try_with_checked_replay_summary(summary)
        .expect("matching checked replay summary should admit")
}

#[test]
fn admission_key_is_stable_when_replay_artifact_paths_change() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(check-sat)
"#,
    );
    let result = VerifiedChcResult::from_validated(
        ChcEngineResult::Safe(InvariantModel::new()),
        ValidationEvidence::FullVerification,
    );
    let run = ChcPdrProofRun::new(problem.clone(), result, "pdr");
    let options = ChcProofEvidenceOptions::pdr_strict(&PdrConfig::default());
    let solver = ChcProofSolverIdentity::new("pdr")
        .with_ay_revision("rev-a")
        .with_solver_binary_sha256(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        );
    let obligation_id = "trust:stable:path-independent";

    let first_evidence = replay_evidence(
        &problem,
        &options,
        &solver,
        obligation_id,
        "safe",
        "verified-invariant",
    );
    let second_evidence = replay_evidence(
        &problem,
        &options,
        &solver,
        obligation_id,
        "safe",
        "verified-invariant",
    )
    .with_solver_transcript(
        ChcProofArtifactDigest::from_bytes("solver-transcript", b"pdr transcript\n")
            .with_path("relocated/transcript.jsonl"),
    );

    let first_manifest = run.evidence_manifest_with_replay_evidence(
        options.clone(),
        solver.clone(),
        obligation_id,
        first_evidence,
    );
    let second_manifest =
        run.evidence_manifest_with_replay_evidence(options, solver, obligation_id, second_evidence);

    assert_eq!(
        first_manifest.admission_key_sha256(),
        second_manifest.admission_key_sha256()
    );
    assert_eq!(
        first_manifest.cache_admission_status(),
        "reject-non-admissible-proof-evidence"
    );
    let json = first_manifest.to_json_value();
    assert_eq!(
        json["replay_evidence_binding_status"],
        "hash-bound-unchecked"
    );
    assert_eq!(json["artifacts"]["proof"]["status"], "hash-bound");
    assert_eq!(
        json["admission"]["proof_artifact_sha256"]
            .as_str()
            .unwrap()
            .len(),
        64
    );
}

#[test]
fn replay_evidence_exposes_digest_backed_compiler_artifacts() {
    let manifest = safe_manifest_with_replay_evidence("trust:artifacts:compiler", |evidence| {
        evidence.replay_log = Some(
            ChcProofArtifactDigest::replay_log_from_bytes(b"z3 replay stdout\n")
                .with_path("artifacts/replay.log"),
        );
        evidence.checked_proof_report = Some(
            ChcProofArtifactDigest::checked_proof_report_from_bytes(b"{\"status\":\"pass\"}\n")
                .with_path("artifacts/checked-proof-report.json"),
        );
        evidence.invariant_model = Some(
            ChcProofArtifactDigest::invariant_model_from_bytes(b"(Inv x) := x >= 0\n")
                .with_path("artifacts/invariant-model.smt2"),
        );
    });
    let json = manifest.to_json_value();

    for (field, role) in [
        ("replay_log", "replay-log"),
        ("checked_proof_report", "checked-proof-report"),
        ("invariant_model", "invariant-model"),
    ] {
        let digest_field = format!("{field}_sha256");
        assert_eq!(json["artifacts"][field]["status"], "hash-bound");
        assert_eq!(json["artifacts"][field]["artifact"]["role"], role);
        assert_eq!(
            json["admission"][digest_field.as_str()]
                .as_str()
                .map(str::len),
            Some(64),
            "{field} should expose a direct digest: {json:#}"
        );
    }

    let changed_model =
        safe_manifest_with_replay_evidence("trust:artifacts:compiler", |evidence| {
            evidence.invariant_model = Some(ChcProofArtifactDigest::invariant_model_from_bytes(
                b"(Inv x) := x >= 1\n",
            ));
        });
    assert_ne!(
        manifest.admission_key_sha256(),
        changed_model.admission_key_sha256(),
        "model artifact bytes must be part of the admission identity"
    );

    let wrong_result_artifact =
        safe_manifest_with_replay_evidence("trust:artifacts:wrong-result", |evidence| {
            evidence.counterexample = Some(ChcProofArtifactDigest::counterexample_from_bytes(
                b"safe cannot cex\n",
            ));
        });
    let wrong_json = wrong_result_artifact.to_json_value();
    let reasons = wrong_json["admission"]["non_admission_reasons"]
        .as_array()
        .expect("non-admission reasons");
    assert!(
        reasons
            .iter()
            .any(|reason| reason == "counterexample_artifact_requires_unsafe_result"),
        "safe-result counterexample artifacts must fail closed: {reasons:?}"
    );
}

#[test]
fn checked_replay_summary_admits_when_manifest_binding_and_artifacts_match() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(check-sat)
"#,
    );
    let result = VerifiedChcResult::from_validated(
        ChcEngineResult::Safe(InvariantModel::new()),
        ValidationEvidence::FullVerification,
    );
    let run = ChcPdrProofRun::new(problem.clone(), result, "pdr");
    let options = ChcProofEvidenceOptions::pdr_strict(&PdrConfig::default());
    let solver = ChcProofSolverIdentity::new("pdr")
        .with_ay_revision("rev-a")
        .with_solver_binary_sha256(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        );
    let obligation_id = "trust:checked:summary";
    let evidence = replay_evidence(
        &problem,
        &options,
        &solver,
        obligation_id,
        "safe",
        "verified-invariant",
    );
    let manifest =
        run.evidence_manifest_with_replay_evidence(options, solver, obligation_id, evidence);
    let precheck_key = manifest.admission_key_sha256();
    let summary = checked_summary_for_manifest(&manifest);
    assert!(manifest
        .checked_replay_summary_rejection_reasons(&summary)
        .is_empty());

    let admitted = manifest
        .try_with_checked_replay_summary(summary)
        .expect("matching checked replay summary should admit");
    let json = admitted.to_json_value();

    assert!(admitted.trust_full_verifier_admissible());
    assert_eq!(
        admitted.cache_admission_status(),
        "admit-checked-proof-evidence"
    );
    assert_ne!(admitted.admission_key_sha256(), precheck_key);
    assert_eq!(
        json["replay_evidence_binding_status"],
        "checked-summary-bound"
    );
    assert_eq!(json["checked_replay"]["checker"]["name"], "z3");
    assert_eq!(
        json["admission"]["checked_replay_summary_sha256"]
            .as_str()
            .map(str::len),
        Some(64)
    );
    assert!(
        json["admission"]["non_admission_reasons"]
            .as_array()
            .expect("non-admission reasons")
            .is_empty(),
        "valid checked replay summary should clear metadata-only reasons: {json:#}"
    );
}

#[test]
fn checked_replay_manifest_preserves_precheck_binding_after_admission() {
    let manifest = safe_manifest_with_replay_evidence("trust:checked:precheck-binding", |_| {});
    let precheck_lookup_key = manifest.cache_lookup_key_sha256();
    let precheck_admission_key = manifest.admission_key_sha256();
    let summary = checked_summary_for_manifest(&manifest);

    let admitted = manifest
        .try_with_checked_replay_summary(summary)
        .expect("matching checked replay summary should admit");
    let cached_summary = admitted
        .checked_replay_summary
        .as_ref()
        .expect("admitted manifest should retain checked summary");

    assert_eq!(admitted.cache_lookup_key_sha256(), precheck_lookup_key);
    assert_ne!(admitted.admission_key_sha256(), precheck_admission_key);
    assert_eq!(
        admitted
            .checked_replay_manifest_binding()
            .precheck_admission_key_sha256,
        precheck_admission_key
    );
    assert!(
        admitted
            .checked_replay_summary_rejection_reasons(cached_summary)
            .is_empty(),
        "admitted manifests must be self-validating cache records"
    );
}

#[test]
fn cache_admission_policy_admits_checked_record_for_same_lookup_key() {
    let manifest = safe_manifest_with_replay_evidence("trust:cache:hit", |_| {});
    let summary = checked_summary_for_manifest(&manifest);
    let admitted = manifest
        .clone()
        .try_with_checked_replay_summary(summary)
        .expect("matching checked replay summary should admit");
    let policy = ChcProofQueryCacheAdmissionPolicy::trust_full_verifier();

    let decision = manifest.cache_admission_decision_against(&admitted, &policy);
    let json = decision.to_json_value();

    assert!(decision.admitted(), "cache hit should admit: {json:#}");
    assert_eq!(
        decision.status,
        ChcProofQueryCacheAdmissionStatus::AdmitCheckedProofEvidence
    );
    assert_eq!(
        decision.current_lookup_key_sha256,
        manifest.cache_lookup_key_sha256()
    );
    assert_eq!(
        decision.cached_lookup_key_sha256,
        admitted.cache_lookup_key_sha256()
    );
    assert_eq!(
        json["schema"],
        CHC_PROOF_QUERY_CACHE_ADMISSION_DECISION_SCHEMA
    );
    assert_eq!(
        json["status"],
        ChcProofQueryCacheAdmissionStatus::AdmitCheckedProofEvidence.as_str()
    );
    assert_eq!(
        admitted.to_json_value()["admission"]["cache_lookup_key"]["schema"],
        CHC_PROOF_QUERY_CACHE_LOOKUP_KEY_SCHEMA
    );
}

#[test]
fn cache_admission_policy_rejects_stale_or_unchecked_cache_records() {
    let manifest = safe_manifest_with_replay_evidence("trust:cache:reject", |_| {});
    let summary = checked_summary_for_manifest(&manifest);
    let admitted = manifest
        .clone()
        .try_with_checked_replay_summary(summary)
        .expect("matching checked replay summary should admit");
    let policy = ChcProofQueryCacheAdmissionPolicy::trust_full_verifier();

    let stale_current =
        safe_manifest_with_replay_evidence("trust:cache:reject:other-obligation", |_| {});
    let stale_decision = policy.evaluate_cache_hit(&stale_current, &admitted);
    assert!(!stale_decision.admitted());
    assert_eq!(
        stale_decision.status,
        ChcProofQueryCacheAdmissionStatus::RejectLookupKeyMismatch
    );
    assert!(
        stale_decision
            .reasons
            .iter()
            .any(|reason| reason == "cache_lookup_key_mismatch"),
        "stale cache hit should explain lookup mismatch: {stale_decision:?}"
    );

    let unchecked_cached = safe_manifest_with_replay_evidence("trust:cache:reject", |_| {});
    let unchecked_decision = manifest.cache_admission_decision_against(&unchecked_cached, &policy);
    assert!(!unchecked_decision.admitted());
    assert_eq!(
        unchecked_decision.status,
        ChcProofQueryCacheAdmissionStatus::RejectCachedSummaryMissing
    );
    assert!(
        unchecked_decision
            .reasons
            .iter()
            .any(|reason| reason == "cached_checked_replay_summary_missing"),
        "unchecked cache hit should require checked replay summary: {unchecked_decision:?}"
    );
}

#[test]
fn proof_query_cache_records_hit_miss_stale_and_rejected_metrics() {
    let current = safe_manifest_with_replay_evidence("trust:cache-store:hit", |_| {});
    let admitted = admitted_safe_manifest("trust:cache-store:hit");
    let mut cache = ChcProofQueryCache::new(8);

    let insert_decision = cache.insert(admitted);
    assert!(
        insert_decision.admitted(),
        "checked manifest should be cacheable: {insert_decision:?}"
    );

    let hit = cache.lookup(&current);
    assert_eq!(hit.status, ChcProofQueryCacheLookupStatus::Hit);
    assert!(hit.admitted());
    assert!(hit.admitted_manifest().is_some());

    let miss_current = safe_manifest_with_replay_evidence("trust:cache-store:miss", |_| {});
    let miss = cache.lookup(&miss_current);
    assert_eq!(miss.status, ChcProofQueryCacheLookupStatus::Miss);
    assert!(
        miss.reasons
            .iter()
            .any(|reason| reason == "cache_lookup_key_absent"),
        "miss should report absent lookup key: {miss:?}"
    );

    let mut stale_current = safe_manifest_with_replay_evidence("trust:cache-store:hit", |_| {});
    stale_current.solver = stale_current.solver.clone().with_ay_revision("rev-b");
    let stale = cache.lookup(&stale_current);
    assert_eq!(stale.status, ChcProofQueryCacheLookupStatus::Stale);
    assert!(
        stale
            .reasons
            .iter()
            .any(|reason| reason == "stale_cache_record_for_obligation_identity"),
        "stale lookup should name obligation identity drift: {stale:?}"
    );

    let rejected_insert = cache.insert(safe_manifest_with_replay_evidence(
        "trust:cache-store:reject",
        |_| {},
    ));
    assert_eq!(
        rejected_insert.status,
        ChcProofQueryCacheAdmissionStatus::RejectCachedSummaryMissing
    );

    let metrics = cache.metrics();
    assert_eq!(metrics.lookups, 3);
    assert_eq!(metrics.hits, 1);
    assert_eq!(metrics.misses, 1);
    assert_eq!(metrics.stale, 1);
    assert_eq!(metrics.rejected, 1);
    assert_eq!(metrics.entries, 1);
    let metrics_json = metrics.to_json_value();
    assert_eq!(metrics_json["hit"], serde_json::json!(1));
    assert_eq!(metrics_json["miss"], serde_json::json!(1));
    assert_eq!(metrics_json["stale"], serde_json::json!(1));
    assert_eq!(metrics_json["rejected"], serde_json::json!(1));
    assert_eq!(
        cache.to_json_value()["schema"],
        CHC_PROOF_QUERY_CACHE_SCHEMA
    );
}

#[test]
fn proof_query_cache_repeated_verification_throughput_stress_reuses_admitted_record() {
    const REPEATED_VERIFICATIONS: u64 = 96;
    const REQUIRED_REPLAY_WORK_REDUCTION: u64 = 32;

    let current = safe_manifest_with_replay_evidence("trust:cache-store:stress", |_| {});
    let replay_obligations_per_verification = u64::try_from(
        current
            .replay_evidence()
            .expect("stress manifest should carry replay evidence")
            .replay_obligations
            .len(),
    )
    .expect("replay obligation count should fit u64");
    assert!(
        replay_obligations_per_verification > 0,
        "stress gate must exercise replay obligations"
    );

    let baseline_replay_obligation_checks =
        REPEATED_VERIFICATIONS * replay_obligations_per_verification;
    let mut external_replay_obligation_checks = 0;
    let mut cache = ChcProofQueryCache::new(8);

    for _ in 0..REPEATED_VERIFICATIONS {
        let lookup = cache.lookup(&current);
        let admitted = match lookup.status {
            ChcProofQueryCacheLookupStatus::Hit => lookup
                .admitted_manifest()
                .expect("hit should carry admitted checked proof evidence")
                .clone(),
            ChcProofQueryCacheLookupStatus::Miss => {
                external_replay_obligation_checks += replay_obligations_per_verification;
                let summary = checked_summary_for_manifest(&current);
                let admitted = current
                    .clone()
                    .try_with_checked_replay_summary(summary)
                    .expect("fresh replay summary should admit current manifest");
                let decision = cache.insert(admitted.clone());
                assert!(
                    decision.admitted(),
                    "freshly checked manifest should be cacheable: {decision:?}"
                );
                admitted
            }
            other => panic!("repeated identical verification should not produce {other:?}"),
        };

        assert!(admitted.trust_full_verifier_admissible());
        assert_eq!(
            admitted.cache_lookup_key_sha256(),
            current.cache_lookup_key_sha256()
        );
    }

    let avoided_replay_obligation_checks =
        baseline_replay_obligation_checks - external_replay_obligation_checks;
    assert_eq!(
        external_replay_obligation_checks, replay_obligations_per_verification,
        "only the cold miss should run external replay obligations"
    );
    assert!(
            external_replay_obligation_checks * REQUIRED_REPLAY_WORK_REDUCTION
                <= baseline_replay_obligation_checks,
            "cache stress gate expected at least {REQUIRED_REPLAY_WORK_REDUCTION}x replay-work reduction: \
             baseline={baseline_replay_obligation_checks}, cached={external_replay_obligation_checks}"
        );
    assert!(
        avoided_replay_obligation_checks > 0,
        "stress gate should demonstrate avoided repeated verification work"
    );

    let metrics = cache.metrics();
    assert_eq!(metrics.lookups, REPEATED_VERIFICATIONS);
    assert_eq!(metrics.misses, 1);
    assert_eq!(metrics.hits, REPEATED_VERIFICATIONS - 1);
    assert_eq!(metrics.insertions, 1);
    assert_eq!(metrics.entries, 1);
    assert_eq!(metrics.stale, 0);
    assert_eq!(metrics.replay_failed, 0);
    assert_eq!(metrics.rejected, 0);
    let metrics_json = metrics.to_json_value();
    assert_eq!(
        metrics_json["hits"],
        serde_json::json!(REPEATED_VERIFICATIONS - 1)
    );
    assert_eq!(metrics_json["misses"], serde_json::json!(1));

    let mut stale_current = current.clone();
    stale_current.solver = stale_current.solver.clone().with_ay_revision("rev-b");
    let stale = cache.lookup(&stale_current);
    assert_eq!(stale.status, ChcProofQueryCacheLookupStatus::Stale);
    assert!(!stale.admitted());
    assert!(
        stale
            .reasons
            .iter()
            .any(|reason| reason == "stale_cache_record_for_obligation_identity"),
        "identity drift must fail closed after hot-cache stress: {stale:?}"
    );

    let lookup_key = current.cache_lookup_key_sha256();
    cache
        .entries
        .get_mut(&lookup_key)
        .expect("stress cache should retain admitted entry")
        .manifest
        .checked_replay_summary
        .as_mut()
        .expect("admitted entry should carry checked replay summary")
        .problem
        .sha256 = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff".to_string();

    let replay_failed = cache.lookup(&current);
    assert_eq!(
        replay_failed.status,
        ChcProofQueryCacheLookupStatus::ReplayFailed
    );
    assert!(!replay_failed.admitted());
    assert!(
        replay_failed
            .reasons
            .iter()
            .any(|reason| reason
                .starts_with("cached_checked_replay_summary_invalid:problem.sha256=")),
        "mismatched replay summary must fail closed after hot-cache stress: {replay_failed:?}"
    );

    let final_metrics = cache.metrics();
    assert_eq!(final_metrics.lookups, REPEATED_VERIFICATIONS + 2);
    assert_eq!(final_metrics.hits, REPEATED_VERIFICATIONS - 1);
    assert_eq!(final_metrics.misses, 1);
    assert_eq!(final_metrics.stale, 1);
    assert_eq!(final_metrics.replay_failed, 1);
    assert_eq!(final_metrics.entries, 1);
}

#[test]
fn proof_query_cache_counts_replay_failed_when_cached_summary_is_corrupted() {
    let current = safe_manifest_with_replay_evidence("trust:cache-store:replay-failed", |_| {});
    let admitted = admitted_safe_manifest("trust:cache-store:replay-failed");
    let lookup_key = admitted.cache_lookup_key_sha256();
    let mut cache = ChcProofQueryCache::new(4);
    assert!(cache.insert(admitted).admitted());

    let entry = cache
        .entries
        .get_mut(&lookup_key)
        .expect("inserted cache entry");
    entry
        .manifest
        .checked_replay_summary
        .as_mut()
        .expect("checked replay summary")
        .problem
        .sha256 = "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff".to_string();

    let lookup = cache.lookup(&current);
    assert_eq!(lookup.status, ChcProofQueryCacheLookupStatus::ReplayFailed);
    assert!(
        lookup
            .reasons
            .iter()
            .any(|reason| reason
                .starts_with("cached_checked_replay_summary_invalid:problem.sha256=")),
        "replay-failed lookup should surface summary validation reason: {lookup:?}"
    );
    assert_eq!(cache.metrics().replay_failed, 1);
}

#[test]
fn proof_query_cache_lru_evicts_least_recently_used_record() {
    let first_current = safe_manifest_with_replay_evidence("trust:cache-store:lru:1", |_| {});
    let first = admitted_safe_manifest("trust:cache-store:lru:1");
    let first_key = first.cache_lookup_key_sha256();
    let second = admitted_safe_manifest("trust:cache-store:lru:2");
    let second_key = second.cache_lookup_key_sha256();
    let third = admitted_safe_manifest("trust:cache-store:lru:3");
    let third_key = third.cache_lookup_key_sha256();
    let mut cache = ChcProofQueryCache::new(2);

    assert!(cache.insert(first).admitted());
    assert!(cache.insert(second).admitted());
    assert_eq!(
        cache.lookup(&first_current).status,
        ChcProofQueryCacheLookupStatus::Hit
    );
    assert!(cache.insert(third).admitted());

    assert_eq!(cache.len(), 2);
    assert!(
        cache.entries.contains_key(&first_key),
        "recently hit first entry should survive LRU eviction"
    );
    assert!(
        !cache.entries.contains_key(&second_key),
        "least recently used second entry should be evicted"
    );
    assert!(cache.entries.contains_key(&third_key));
    assert_eq!(cache.metrics().evictions, 1);
}

#[test]
fn proof_query_cache_snapshot_hydrates_admitted_records() {
    let current = safe_manifest_with_replay_evidence("trust:cache-store:hydrate", |_| {});
    let admitted = admitted_safe_manifest("trust:cache-store:hydrate");
    let mut cache = ChcProofQueryCache::new(4);
    assert!(cache.insert(admitted).admitted());
    assert_eq!(
        cache.lookup(&current).status,
        ChcProofQueryCacheLookupStatus::Hit
    );

    let snapshot = cache.to_json_value();
    let mut hydrated = ChcProofQueryCache::from_json_value(&snapshot)
        .expect("deterministic cache snapshot should hydrate");
    let hit = hydrated.lookup(&current);

    assert_eq!(hit.status, ChcProofQueryCacheLookupStatus::Hit);
    assert!(hit.admitted());
    assert_eq!(hydrated.len(), 1);
    assert_eq!(hydrated.metrics().hits, 2);
    assert_eq!(
        hydrated.to_json_value()["entries"][0]["manifest"]["admission"]["cache_lookup_key_sha256"],
        snapshot["entries"][0]["manifest"]["admission"]["cache_lookup_key_sha256"]
    );
}

#[test]
fn proof_query_cache_snapshot_rejects_corrupted_manifest_identity() {
    let admitted = admitted_safe_manifest("trust:cache-store:hydrate-corrupt");
    let mut cache = ChcProofQueryCache::new(4);
    assert!(cache.insert(admitted).admitted());
    let mut snapshot = cache.to_json_value();

    snapshot["entries"][0]["manifest"]["checked_replay_summary"]["certificate"]["sha256"] =
        serde_json::json!("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");

    let error = ChcProofQueryCache::from_json_value(&snapshot)
        .expect_err("corrupt checked summary must reject hydration");
    assert!(
        error
            .reasons()
            .iter()
            .any(|reason| reason.contains("certificate.identity_sha256")
                || reason.contains("manifest checked replay summary invalid")),
        "hydration should surface checked-summary/artifact validation: {:?}",
        error.reasons()
    );
}

#[test]
fn checked_replay_summary_admits_unsafe_trace_validity_binding() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x 1)) false)))
(check-sat)
"#,
    );
    let predicate = problem.predicates()[0].id;
    let result = VerifiedChcResult::from_validated(
        ChcEngineResult::Unsafe(Counterexample::new(vec![
            CounterexampleStep::new(predicate, [("x".to_string(), 0)].into_iter().collect()),
            CounterexampleStep::new(predicate, [("x".to_string(), 1)].into_iter().collect()),
        ])),
        ValidationEvidence::CounterexampleVerification,
    );
    let run = ChcPdrProofRun::new(problem.clone(), result, "pdr");
    let options = ChcProofEvidenceOptions::pdr_strict(&PdrConfig::default());
    let solver = ChcProofSolverIdentity::new("pdr")
        .with_ay_revision("rev-a")
        .with_solver_binary_sha256(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        );
    let obligation_id = "trust:checked:unsafe-trace";
    let evidence = unsafe_trace_replay_evidence(&problem, &options, &solver, obligation_id);
    let manifest =
        run.evidence_manifest_with_replay_evidence(options, solver, obligation_id, evidence);
    let summary = checked_summary_for_manifest(&manifest);

    assert!(manifest
        .checked_replay_summary_rejection_reasons(&summary)
        .is_empty());
    let admitted = manifest
        .try_with_checked_replay_summary(summary)
        .expect("matching unsafe trace-validity summary should admit");

    assert!(admitted.trust_full_verifier_admissible());
    assert_eq!(
        admitted.cache_admission_status(),
        "admit-checked-proof-evidence"
    );
    let admitted_json = admitted.to_json_value();
    assert_eq!(
        admitted_json["checked_replay_summary"]["obligations"][0]["kind"],
        "trace-validity"
    );
    assert_eq!(
        admitted_json["artifacts"]["counterexample"]["artifact"]["role"],
        "counterexample"
    );
    assert_eq!(
        admitted_json["admission"]["counterexample_sha256"]
            .as_str()
            .map(str::len),
        Some(64)
    );
}

#[test]
fn passed_manifest_replay_builder_consumes_unsafe_trace_validity_report() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x 1)) false)))
(check-sat)
"#,
    );
    let predicate = problem.predicates()[0].id;
    let result = VerifiedChcResult::from_validated(
        ChcEngineResult::Unsafe(Counterexample::new(vec![
            CounterexampleStep::new(predicate, [("x".to_string(), 0)].into_iter().collect()),
            CounterexampleStep::new(predicate, [("x".to_string(), 1)].into_iter().collect()),
        ])),
        ValidationEvidence::CounterexampleVerification,
    );
    let run = ChcPdrProofRun::new(problem.clone(), result, "pdr");
    let options = ChcProofEvidenceOptions::pdr_strict(&PdrConfig::default());
    let solver = ChcProofSolverIdentity::new("pdr")
        .with_ay_revision("rev-a")
        .with_solver_binary_sha256(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        );
    let obligation_id = "trust:checked:unsafe-report-builder";
    let mut evidence = unsafe_trace_replay_evidence(&problem, &options, &solver, obligation_id);
    evidence.replay_report = None;
    let manifest =
        run.evidence_manifest_with_replay_evidence(options, solver, obligation_id, evidence);

    let json = manifest.to_json_value();
    assert_eq!(json["artifacts"]["replay_report"]["status"], "missing");
    assert!(
        json["admission"]["non_admission_reasons"]
            .as_array()
            .expect("non-admission reasons")
            .iter()
            .any(|reason| reason.as_str() == Some("missing_checked_replay_report")),
        "manifest should require the external replay report before summary construction: {json:#}"
    );

    let replay_report =
        ChcProofArtifactDigest::from_bytes("replay-report", b"trace-validity: pass\n")
            .with_path("artifacts/unsafe-replay-report.log");
    let manifest = manifest
        .try_with_replay_report_artifact(replay_report)
        .expect("replay report should attach to existing replay evidence");
    let json = manifest.to_json_value();
    assert_eq!(json["artifacts"]["replay_report"]["status"], "hash-bound");
    assert!(
        !json["admission"]["non_admission_reasons"]
            .as_array()
            .expect("non-admission reasons")
            .iter()
            .any(|reason| reason.as_str() == Some("missing_checked_replay_report")),
        "attached replay report should clear the report-specific missing reason: {json:#}"
    );

    let evidence = manifest
        .replay_evidence()
        .expect("manifest should expose replay evidence");
    let query = evidence.replay_obligations[0].query.clone();
    let artifacts = ChcCheckedReplayArtifacts::new(
        ChcProofArtifactDigest::from_bytes("problem", normalized_chc_input(&problem).as_bytes())
            .with_path("artifacts/problem.smt2"),
        evidence
            .proof
            .clone()
            .expect("unsafe replay evidence should carry certificate"),
        evidence
            .solver_transcript
            .clone()
            .expect("unsafe replay evidence should carry run log"),
        evidence
            .replay_report
            .clone()
            .expect("unsafe replay evidence should carry replay report"),
    );
    let checker = ChcReplayCheckerIdentity::new("z3", "z3 test", true);
    let command = "z3 artifacts/000-trace-validity.smt2";
    let obligation = ChcCheckedReplayObligation::new(
        "trace-validity",
        ChcReplayObligationKind::TraceValidity,
        query.clone(),
        command,
        ChcReplayCheckResult::pass(),
    );

    let summary = ChcCheckedReplaySummary::from_passed_manifest_replay(
        &manifest,
        artifacts.clone(),
        checker.clone(),
        command,
        vec![obligation],
    )
    .expect("trace-validity replay should produce a checked summary");
    let admitted = manifest
        .clone()
        .try_with_checked_replay_summary(summary)
        .expect("matching trace-validity summary should admit");
    assert!(admitted.trust_full_verifier_admissible());

    let corrupted = ChcCheckedReplayObligation::new(
        "trace-validity",
        ChcReplayObligationKind::Safety,
        query,
        command,
        ChcReplayCheckResult::pass(),
    );
    let error = ChcCheckedReplaySummary::from_passed_manifest_replay(
        &manifest,
        artifacts,
        checker,
        command,
        vec![corrupted],
    )
    .expect_err("corrupted unsafe replay kind must fail closed");
    assert!(
        error
            .reasons()
            .iter()
            .any(|reason| reason.contains("missing CHC replay obligation kinds: trace-validity")),
        "corrupted trace-validity replay should reject: {:?}",
        error.reasons()
    );
}

#[test]
fn checked_replay_summary_rejects_unsafe_without_trace_validity() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (xp Int)) (=> (and (Inv x) (= xp (+ x 1))) (Inv xp))))
(assert (forall ((x Int)) (=> (and (Inv x) (= x 1)) false)))
(check-sat)
"#,
    );
    let predicate = problem.predicates()[0].id;
    let result = VerifiedChcResult::from_validated(
        ChcEngineResult::Unsafe(Counterexample::new(vec![
            CounterexampleStep::new(predicate, [("x".to_string(), 0)].into_iter().collect()),
            CounterexampleStep::new(predicate, [("x".to_string(), 1)].into_iter().collect()),
        ])),
        ValidationEvidence::CounterexampleVerification,
    );
    let run = ChcPdrProofRun::new(problem.clone(), result, "pdr");
    let options = ChcProofEvidenceOptions::pdr_strict(&PdrConfig::default());
    let solver = ChcProofSolverIdentity::new("pdr")
        .with_ay_revision("rev-a")
        .with_solver_binary_sha256(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        );
    let obligation_id = "trust:checked:unsafe-missing-trace";
    let evidence = unsafe_trace_replay_evidence(&problem, &options, &solver, obligation_id);
    let manifest =
        run.evidence_manifest_with_replay_evidence(options, solver, obligation_id, evidence);
    let mut summary = checked_summary_for_manifest(&manifest);
    summary.obligations[0].kind = ChcReplayObligationKind::Safety;

    let reasons = manifest.checked_replay_summary_rejection_reasons(&summary);

    assert!(
        reasons
            .iter()
            .any(|reason| reason.contains("missing CHC replay obligation kinds: trace-validity")),
        "unsafe summaries without trace-validity should reject: {reasons:?}"
    );
    assert!(
        reasons
            .iter()
            .any(|reason| reason.contains("is not expected for unsafe CHC replay")),
        "unexpected unsafe obligation kinds should reject: {reasons:?}"
    );
}

#[test]
fn checked_replay_summary_rejects_stale_manifest_and_artifact_bindings() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(check-sat)
"#,
    );
    let result = VerifiedChcResult::from_validated(
        ChcEngineResult::Safe(InvariantModel::new()),
        ValidationEvidence::FullVerification,
    );
    let run = ChcPdrProofRun::new(problem.clone(), result, "pdr");
    let options = ChcProofEvidenceOptions::pdr_strict(&PdrConfig::default());
    let solver = ChcProofSolverIdentity::new("pdr")
        .with_ay_revision("rev-a")
        .with_solver_binary_sha256(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        );
    let obligation_id = "trust:checked:stale";
    let evidence = replay_evidence(
        &problem,
        &options,
        &solver,
        obligation_id,
        "safe",
        "verified-invariant",
    );
    let manifest =
        run.evidence_manifest_with_replay_evidence(options, solver, obligation_id, evidence);
    let mut summary = checked_summary_for_manifest(&manifest);
    summary.manifest_binding.options_sha256 =
        "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".to_string();
    summary.certificate.sha256 =
        "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc".to_string();

    let reasons = manifest.checked_replay_summary_rejection_reasons(&summary);
    assert!(
        reasons
            .iter()
            .any(|reason| reason.contains("manifest_binding.options_sha256")),
        "expected stale options binding rejection, got {reasons:?}"
    );
    assert!(
        reasons
            .iter()
            .any(|reason| reason.contains("certificate.sha256")),
        "expected certificate artifact rejection, got {reasons:?}"
    );
    let error = manifest
        .try_with_checked_replay_summary(summary)
        .expect_err("stale checked replay summary must reject");
    assert_eq!(error.reasons(), reasons.as_slice());
}

#[test]
fn checked_replay_summary_rejects_stale_manifest_obligation_identity_binding() {
    let manifest =
        safe_manifest_with_replay_evidence("trust:checked:stale-obligation-identity", |_| {});
    let mut summary = checked_summary_for_manifest(&manifest);
    summary.manifest_binding.replay_obligation_identity_sha256[0] =
        "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".to_string();

    let reasons = manifest.checked_replay_summary_rejection_reasons(&summary);

    assert!(
        reasons
            .iter()
            .any(|reason| reason.contains("manifest_binding.replay_obligation_identity_sha256")),
        "expected stale obligation identity binding rejection, got {reasons:?}"
    );
    assert!(manifest.try_with_checked_replay_summary(summary).is_err());
}

#[test]
fn checked_replay_summary_rejects_wrong_artifact_roles() {
    let manifest = safe_manifest_with_replay_evidence("trust:checked:artifact-roles", |_| {});
    let mut summary = checked_summary_for_manifest(&manifest);
    summary.certificate.role = "solver-transcript".to_string();
    summary.obligations[0].query.role = "proof-certificate".to_string();

    let reasons = manifest.checked_replay_summary_rejection_reasons(&summary);

    assert!(
        reasons.iter().any(|reason| reason.contains(
            "certificate.role=\"solver-transcript\" does not match expected \"proof-certificate\""
        )),
        "certificate role mismatch should reject: {reasons:?}"
    );
    assert!(
            reasons.iter().any(|reason| reason.contains(
                "obligations[0].query.role=\"proof-certificate\" does not match expected \"replay-obligation\""
            )),
            "obligation query role mismatch should reject: {reasons:?}"
        );
}

#[test]
fn checked_replay_summary_rejects_wrong_problem_artifact_hash() {
    let manifest =
        safe_manifest_with_replay_evidence("trust:checked:wrong-problem-artifact", |_| {});
    let mut summary = checked_summary_for_manifest(&manifest);
    summary.problem.sha256 =
        "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb".to_string();

    let reasons = manifest.checked_replay_summary_rejection_reasons(&summary);

    assert!(
        reasons
            .iter()
            .any(|reason| reason.contains("problem.sha256")),
        "wrong problem artifact hash should reject: {reasons:?}"
    );
    assert!(manifest.try_with_checked_replay_summary(summary).is_err());
}

#[test]
fn checked_replay_summary_rejects_stale_artifact_byte_descriptors() {
    let manifest = safe_manifest_with_replay_evidence("trust:checked:stale-artifact-bytes", |_| {});
    let mut summary = checked_summary_for_manifest(&manifest);
    summary.problem.bytes += 1;
    summary.run_log.bytes += 1;
    summary.certificate.bytes += 1;
    summary.replay_log.bytes += 1;
    summary.obligations[0].query.bytes += 1;

    let reasons = manifest.checked_replay_summary_rejection_reasons(&summary);

    for expected in [
        "problem.bytes",
        "run_log.bytes",
        "certificate.bytes",
        "replay_log.bytes",
        "checked_replay_obligation_query_descriptors",
    ] {
        assert!(
            reasons.iter().any(|reason| reason.contains(expected)),
            "expected {expected} rejection, got {reasons:?}"
        );
    }
    assert!(manifest.try_with_checked_replay_summary(summary).is_err());
}

#[test]
fn admission_rejects_missing_replay_obligation_artifacts() {
    let manifest =
        safe_manifest_with_replay_evidence("trust:reject:missing-replay-obligations", |evidence| {
            evidence.replay_obligations.clear();
        });
    let json = manifest.to_json_value();
    let reasons = json["admission"]["non_admission_reasons"]
        .as_array()
        .expect("non admission reasons should be an array");

    assert_eq!(json["artifacts"]["replay_obligations"]["status"], "missing");
    assert!(
        reasons
            .iter()
            .any(|reason| reason == "missing_replay_obligation_artifacts"),
        "missing replay obligations should be explicit in admission reasons: {reasons:?}"
    );

    let summary = checked_summary_for_manifest(&manifest);
    let rejection = manifest.checked_replay_summary_rejection_reasons(&summary);
    assert!(
        rejection
            .iter()
            .any(|reason| reason == "obligations is empty"),
        "checked replay must still reject without obligation rows: {rejection:?}"
    );
    assert!(manifest.try_with_checked_replay_summary(summary).is_err());
}

#[test]
fn checked_replay_summary_rejects_swapped_obligation_kind_query_descriptors() {
    let manifest =
        safe_manifest_with_replay_evidence("trust:checked:swapped-obligation-kind", |_| {});
    let mut summary = checked_summary_for_manifest(&manifest);
    let first_query = summary.obligations[0].query.clone();
    summary.obligations[0].query = summary.obligations[1].query.clone();
    summary.obligations[1].query = first_query;

    let reasons = manifest.checked_replay_summary_rejection_reasons(&summary);

    assert!(
        reasons
            .iter()
            .any(|reason| reason.contains("checked_replay_obligation_kind_query_descriptors")),
        "kind/query swaps should reject even when query hash sets still match: {reasons:?}"
    );
    assert!(manifest.try_with_checked_replay_summary(summary).is_err());
}

#[test]
fn checked_replay_summary_from_json_rejects_missing_artifact_byte_descriptors() {
    let manifest =
        safe_manifest_with_replay_evidence("trust:checked:missing-artifact-bytes", |_| {});
    let summary = checked_summary_for_manifest(&manifest);
    let mut json = summary.to_json_value();

    json["certificate"]
        .as_object_mut()
        .expect("certificate artifact")
        .remove("bytes");
    json["obligations"].as_array_mut().expect("obligations")[0]["query"]
        .as_object_mut()
        .expect("obligation query artifact")
        .remove("bytes");

    let error = ChcCheckedReplaySummary::from_json_value(&json)
        .expect_err("parsed replay summaries must require artifact byte descriptors");
    let reasons = error.reasons();
    for expected in [
        "certificate.bytes is missing",
        "obligations[0].query.bytes is missing",
    ] {
        assert!(
            reasons.iter().any(|reason| reason == expected),
            "missing {expected} in {reasons:?}"
        );
    }
}

#[test]
fn checked_replay_summary_from_json_requires_complete_artifact_rows() {
    let manifest =
        safe_manifest_with_replay_evidence("trust:checked:complete-artifact-rows", |_| {});
    let summary = checked_summary_for_manifest(&manifest);
    let mut json = summary.to_json_value();

    json["certificate"]
        .as_object_mut()
        .expect("certificate artifact")
        .remove("role");
    json["run_log"]
        .as_object_mut()
        .expect("run log artifact")
        .remove("schema_version");
    json["replay_log"]["schema_version"] = serde_json::json!(2);
    json["obligations"].as_array_mut().expect("obligations")[0]["query"]
        .as_object_mut()
        .expect("obligation query artifact")
        .remove("schema");

    let error = ChcCheckedReplaySummary::from_json_value(&json)
        .expect_err("parsed replay summaries must require complete artifact rows");
    let reasons = error.reasons();
    for expected in [
        "certificate.role is missing",
        "run_log.schema_version is missing",
        "replay_log.schema_version=2 does not match expected 1",
        "obligations[0].query.schema is missing",
    ] {
        assert!(
            reasons.iter().any(|reason| reason == expected),
            "missing {expected} in {reasons:?}"
        );
    }
}

#[test]
fn checked_replay_summary_from_json_requires_summary_schema_versions() {
    let manifest =
        safe_manifest_with_replay_evidence("trust:checked:summary-schema-versions", |_| {});
    let summary = checked_summary_for_manifest(&manifest);
    let mut json = summary.to_json_value();

    json.as_object_mut()
        .expect("summary object")
        .remove("schema_version");
    json["manifest_binding"]["schema_version"] = serde_json::json!(2);

    let error = ChcCheckedReplaySummary::from_json_value(&json)
        .expect_err("summary and manifest binding schema versions must be checked");
    let reasons = error.reasons();
    for expected in [
        "schema_version is missing",
        "manifest_binding.schema_version=2 does not match expected 1",
    ] {
        assert!(
            reasons.iter().any(|reason| reason == expected),
            "missing {expected} in {reasons:?}"
        );
    }
}

#[test]
fn checked_replay_summary_from_json_requires_checker_identity_schema() {
    let manifest = safe_manifest_with_replay_evidence("trust:checked:checker-schema", |_| {});
    let summary = checked_summary_for_manifest(&manifest);
    let mut json = summary.to_json_value();

    json["checker"]
        .as_object_mut()
        .expect("checker identity object")
        .remove("schema");
    json["checker"]["schema_version"] = serde_json::json!(2);

    let error = ChcCheckedReplaySummary::from_json_value(&json)
        .expect_err("checker identity schema metadata must be checked");
    let reasons = error.reasons();
    for expected in [
        "checker.schema is missing",
        "checker.schema_version=2 does not match expected 1",
    ] {
        assert!(
            reasons.iter().any(|reason| reason == expected),
            "missing {expected} in {reasons:?}"
        );
    }
}

#[test]
fn checked_replay_summary_from_json_requires_result_schema() {
    let manifest = safe_manifest_with_replay_evidence("trust:checked:result-schema", |_| {});
    let summary = checked_summary_for_manifest(&manifest);
    let mut json = summary.to_json_value();

    assert_eq!(json["result"]["schema"], CHC_REPLAY_CHECK_RESULT_SCHEMA);
    assert_eq!(json["result"]["schema_version"], serde_json::json!(1));
    assert_eq!(
        json["obligations"][0]["result"]["schema"],
        CHC_REPLAY_CHECK_RESULT_SCHEMA
    );
    assert_eq!(
        json["obligations"][0]["result"]["schema_version"],
        serde_json::json!(1)
    );

    json["result"]
        .as_object_mut()
        .expect("top-level result object")
        .remove("schema");
    json["obligations"][0]["result"]["schema_version"] = serde_json::json!(2);

    let error = ChcCheckedReplaySummary::from_json_value(&json)
        .expect_err("checked replay result schema metadata must be checked");
    let reasons = error.reasons();
    for expected in [
        "result.schema is missing",
        "obligations[0].result.schema_version=2 does not match expected 1",
    ] {
        assert!(
            reasons.iter().any(|reason| reason == expected),
            "missing {expected} in {reasons:?}"
        );
    }
}

#[test]
fn checked_replay_summary_from_json_rejects_missing_obligation_identity_binding() {
    let manifest =
        safe_manifest_with_replay_evidence("trust:checked:missing-obligation-identity", |_| {});
    let summary = checked_summary_for_manifest(&manifest);
    let mut json = summary.to_json_value();

    json["manifest_binding"]
        .as_object_mut()
        .expect("manifest binding object")
        .remove("replay_obligation_identity_sha256");

    let error = ChcCheckedReplaySummary::from_json_value(&json)
        .expect_err("missing replay obligation identity binding must reject");

    assert!(
        error.reasons().iter().any(|reason| {
            reason == "manifest_binding.replay_obligation_identity_sha256 is missing"
        }),
        "expected missing obligation identity binding rejection, got {:?}",
        error.reasons()
    );
}

#[test]
fn checked_replay_summary_from_json_rejects_stale_embedded_identities() {
    let manifest =
        safe_manifest_with_replay_evidence("trust:checked:stale-embedded-identity", |_| {});
    let summary = checked_summary_for_manifest(&manifest);
    let json = summary.to_json_value();
    let stale =
        serde_json::json!("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff");

    fn expect_identity_rejection<F>(base: &serde_json::Value, label: &str, mutate: F)
    where
        F: FnOnce(&mut serde_json::Value),
    {
        let mut json = base.clone();
        mutate(&mut json);
        let error = ChcCheckedReplaySummary::from_json_value(&json)
            .expect_err("stale embedded identity must reject");
        assert!(
            error.reasons().iter().any(|reason| {
                reason.contains(label) && reason.contains("does not match recomputed")
            }),
            "expected stale {label} rejection, got {:?}",
            error.reasons()
        );
    }

    expect_identity_rejection(&json, "identity_sha256", |json| {
        json["identity_sha256"] = stale.clone();
    });
    expect_identity_rejection(&json, "checker.identity_sha256", |json| {
        json["checker"]["identity_sha256"] = stale.clone();
    });
    expect_identity_rejection(&json, "manifest_binding.identity_sha256", |json| {
        json["manifest_binding"]["identity_sha256"] = stale.clone();
    });
    expect_identity_rejection(&json, "certificate.identity_sha256", |json| {
        json["certificate"]["identity_sha256"] = stale.clone();
    });
    expect_identity_rejection(&json, "obligations[0].identity_sha256", |json| {
        json["obligations"][0]["identity_sha256"] = stale.clone();
    });

    let mut malformed = json;
    malformed["run_log"]["identity_sha256"] = serde_json::json!("not-a-sha256");
    let error = ChcCheckedReplaySummary::from_json_value(&malformed)
        .expect_err("malformed embedded identity must reject");
    assert!(
        error
            .reasons()
            .iter()
            .any(|reason| reason == "run_log.identity_sha256 is not lowercase hex SHA-256"),
        "expected malformed run_log identity rejection, got {:?}",
        error.reasons()
    );
}

#[test]
fn checked_replay_summary_rejects_status_only_pass_claims() {
    let shallow = serde_json::json!({
        "schema": CHC_CHECKED_REPLAY_SUMMARY_SCHEMA,
        "status": "pass",
        "surface": "CHC certificates",
        "verdict": "safe",
    });

    let error = ChcCheckedReplaySummary::from_json_value(&shallow)
        .expect_err("status-only summary must not parse as checked replay evidence");
    let reasons = error.reasons();
    for expected in [
        "checker is not an object",
        "manifest_binding is missing",
        "problem is missing",
        "certificate is missing",
        "run_log is missing",
        "replay_log is missing",
        "result is not an object",
        "obligations is empty",
    ] {
        assert!(
            reasons.iter().any(|reason| reason == expected),
            "missing {expected} in {reasons:?}"
        );
    }
}

#[test]
fn admission_rejects_stale_or_mismatched_replay_evidence() {
    let problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(check-sat)
"#,
    );
    let stale_problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 1) (Inv x))))
(check-sat)
"#,
    );
    let result = VerifiedChcResult::from_validated(
        ChcEngineResult::Safe(InvariantModel::new()),
        ValidationEvidence::FullVerification,
    );
    let run = ChcPdrProofRun::new(problem.clone(), result, "pdr");
    let options = ChcProofEvidenceOptions::pdr_strict(&PdrConfig::default());
    let solver = ChcProofSolverIdentity::new("pdr")
        .with_ay_revision("rev-a")
        .with_solver_binary_sha256(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        );
    let obligation_id = "trust:reject:stale";
    let matching = replay_evidence(
        &problem,
        &options,
        &solver,
        obligation_id,
        "safe",
        "verified-invariant",
    );
    let stale = ChcReplayEvidence::new(
        normalized_chc_input_sha256(&stale_problem),
        options.identity_sha256(),
        solver.identity_sha256(),
        "trust:reject:other-obligation",
        "unknown",
        "non-proof",
    )
    .with_solver_transcript(
        ChcProofArtifactDigest::from_bytes("solver-transcript", b"old transcript\n")
            .with_path("old/transcript.jsonl"),
    )
    .with_proof(
        ChcProofArtifactDigest::from_bytes("proof-certificate", b"old proof\n")
            .with_path("old/proof.smt2"),
    );

    let matching_manifest = run.evidence_manifest_with_replay_evidence(
        options.clone(),
        solver.clone(),
        obligation_id,
        matching,
    );
    let stale_manifest =
        run.evidence_manifest_with_replay_evidence(options, solver, obligation_id, stale);

    assert_ne!(
        matching_manifest.admission_key_sha256(),
        stale_manifest.admission_key_sha256()
    );
    let json = stale_manifest.to_json_value();
    let reasons = json["admission"]["non_admission_reasons"]
        .as_array()
        .expect("non admission reasons should be an array");
    assert_eq!(json["replay_evidence_binding_status"], "mismatched");
    for reason in [
        "replay_evidence_problem_hash_mismatch",
        "replay_evidence_obligation_id_mismatch",
        "replay_evidence_result_mismatch",
        "replay_evidence_proof_status_mismatch",
        "missing_checked_replay_report",
    ] {
        assert!(
            reasons.iter().any(|entry| entry == reason),
            "missing {reason} in {reasons:?}"
        );
    }
    assert_eq!(
        stale_manifest.cache_admission_status(),
        "reject-non-admissible-proof-evidence"
    );
}

#[test]
fn admission_rejects_replay_evidence_with_wrong_artifact_role() {
    let manifest = safe_manifest_with_replay_evidence("trust:reject:artifact-role", |evidence| {
        evidence.proof = Some(
            ChcProofArtifactDigest::from_bytes("solver-transcript", b"(ay-chc certificate)\n")
                .with_path("artifacts/certificate.smt2"),
        );
    });
    let json = manifest.to_json_value();
    let reasons = json["admission"]["non_admission_reasons"]
        .as_array()
        .expect("non admission reasons should be an array");

    assert_eq!(json["replay_evidence_binding_status"], "mismatched");
    assert!(
        reasons.iter().any(|reason| reason
            .as_str()
            .is_some_and(|reason| reason.starts_with("proof_artifact_role_mismatch:"))),
        "wrong proof artifact role should reject manifest evidence: {reasons:?}"
    );
}

#[test]
fn admission_key_changes_with_problem_options_solver_and_transcript() {
    let first_problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(check-sat)
"#,
    );
    let second_problem = parse_problem(
        r#"(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 1) (Inv x))))
(check-sat)
"#,
    );
    let fresh_result = || {
        VerifiedChcResult::from_validated(
            ChcEngineResult::Safe(InvariantModel::new()),
            ValidationEvidence::FullVerification,
        )
    };
    let base_run = ChcPdrProofRun::new(first_problem.clone(), fresh_result(), "pdr");
    let base_options = ChcProofEvidenceOptions::pdr_strict(
        &PdrConfig::default()
            .with_max_frames(8)
            .with_max_iterations(100),
    );
    let base_solver = ChcProofSolverIdentity::new("pdr")
        .with_ay_revision("rev-a")
        .with_solver_binary_sha256(
            "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        );
    let base = base_run
        .evidence_manifest(
            base_options.clone(),
            base_solver.clone(),
            "caller:obligation",
        )
        .admission_key_sha256();

    let changed_problem_run = ChcPdrProofRun::new(second_problem, fresh_result(), "pdr");
    let changed_problem = changed_problem_run
        .evidence_manifest(
            base_options.clone(),
            base_solver.clone(),
            "caller:obligation",
        )
        .admission_key_sha256();
    assert_ne!(base, changed_problem);

    let mut changed_options = base_options.clone();
    changed_options.max_frames += 1;
    let changed_options_key = base_run
        .evidence_manifest(changed_options, base_solver.clone(), "caller:obligation")
        .admission_key_sha256();
    assert_ne!(base, changed_options_key);

    let changed_solver = base_solver.clone().with_ay_revision("rev-b");
    let changed_solver_key = base_run
        .evidence_manifest(base_options.clone(), changed_solver, "caller:obligation")
        .admission_key_sha256();
    assert_ne!(base, changed_solver_key);

    let changed_transcript = ChcPdrProofRun::new(first_problem, fresh_result(), "pdr-alternate");
    let changed_transcript_key = changed_transcript
        .evidence_manifest(base_options, base_solver, "caller:obligation")
        .admission_key_sha256();
    assert_ne!(base, changed_transcript_key);
}
