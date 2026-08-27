// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Trust evidence unit tests.

use super::*;
use crate::drat::DratReplayInput;
use crate::ReplayInput;

const UNSAT_CNF: &[u8] = b"p cnf 1 2\n1 0\n-1 0\n";
const UNSAT_LRAT: &[u8] = b"3 0 1 2 0\n";
const UNSAT_DRAT: &[u8] = b"0\n";

#[test]
fn sealed_evidence_contract_uses_v2_schema_ids() {
    assert!(TRUST_NATIVE_VERIFIER_V2_REPLAY_EVIDENCE_SCHEMA.ends_with("/v2"));
    assert!(TRUST_NATIVE_VERIFIER_V2_SOLVER_EVIDENCE_SCHEMA.ends_with("/v2"));
    assert!(TRUST_NATIVE_VERIFIER_V2_OWNER_REPORT_SCHEMA.ends_with("/v2"));
}

#[test]
fn trust_engine_as_str_emits_rebranded_wire_names() {
    assert_eq!(TrustEngine::VerificationConsumer.as_str(), "verification-consumer");
    assert_eq!(TrustEngine::ModelCheckerConsumer.as_str(), "model-checker-consumer");
    assert_eq!(TrustEngine::DeductiveChecks.as_str(), "deductive-checks");
    assert_eq!(TrustEngine::Ty.as_str(), "ty");
}

#[test]
fn trust_engine_from_str_accepts_rebranded_wire_names() {
    assert_eq!(
        TrustEngine::from_str("verification-consumer"),
        Some(TrustEngine::VerificationConsumer)
    );
    assert_eq!(
        TrustEngine::from_str("model-checker-consumer"),
        Some(TrustEngine::ModelCheckerConsumer)
    );
    assert_eq!(
        TrustEngine::from_str("deductive-checks"),
        Some(TrustEngine::DeductiveChecks)
    );
    assert_eq!(TrustEngine::from_str("ty"), Some(TrustEngine::Ty));
    assert_eq!(TrustEngine::from_str("nope"), None);
}

#[test]
fn trust_engine_from_str_still_accepts_legacy_wire_names() {
    // Back-compat: evidence persisted under the old names must still load.
    assert_eq!(TrustEngine::from_str("quantifier_consumer"), Some(TrustEngine::VerificationConsumer));
    assert_eq!(TrustEngine::from_str("certificate_consumer"), Some(TrustEngine::DeductiveChecks));
    assert_eq!(TrustEngine::from_str("tla2"), Some(TrustEngine::Ty));
}

#[test]
fn trust_engine_from_str_no_longer_accepts_zani() {
    // The legacy `zani` name has been fully removed; only `model-checker-consumer`
    // resolves to the BMC/CHC reachability engine now.
    assert_eq!(TrustEngine::from_str("zani"), None);
    assert_eq!(
        TrustEngine::from_str("model-checker-consumer"),
        Some(TrustEngine::ModelCheckerConsumer)
    );
}

#[test]
fn solver_mode_and_counterexample_format_emit_rebranded_wire_names() {
    assert_eq!(SolverMode::Ty.as_str(), "ty");
    assert_eq!(CounterexampleEvidenceFormat::TyTrace.as_str(), "ty_trace");
}

#[test]
fn lrat_evidence_records_owner_resource_hashes_and_kernel_strength() {
    let context = TrustReplayContext::new(TrustEngine::VerificationConsumer, SolverMode::Smt, "QF_UF")
        .with_resource_policy(ResourcePolicy::bounded(
            Some(1_000),
            Some(128 * 1024 * 1024),
        ));
    let input = ReplayInput {
        cnf: UNSAT_CNF,
        proof: UNSAT_LRAT,
    };
    let evidence = TrustReplayEvidence::from_lrat(&context, &input).expect("LRAT evidence");

    assert_eq!(
        evidence.schema(),
        TRUST_NATIVE_VERIFIER_V2_REPLAY_EVIDENCE_SCHEMA
    );
    assert_eq!(evidence.owning_engine(), TrustEngine::VerificationConsumer);
    assert_eq!(evidence.solver_mode(), SolverMode::Smt);
    assert_eq!(evidence.theory_set(), "QF_UF");
    assert_eq!(evidence.resource_policy().timeout_ms, Some(1_000));
    assert_eq!(
        evidence.resource_policy().memory_limit_bytes,
        Some(128 * 1024 * 1024)
    );
    assert_eq!(evidence.solver_status(), SolverStatus::Unsat);
    assert_eq!(
        evidence.replay_status(),
        ReplayEvidenceStatus::VerifiedUnsat
    );
    assert_eq!(evidence.proof_strength(), ProofStrength::LratKernelChecked);
    assert_eq!(
        evidence.artifact_hashes(),
        &ReplayInputHashes::from_bytes(UNSAT_CNF, UNSAT_LRAT)
    );
    assert_eq!(evidence.artifact_hashes().cnf_sha256.len(), 64);
    assert_eq!(evidence.artifact_hashes().proof_sha256.len(), 64);
    assert_eq!(evidence.proof_metadata().proof_format, ProofFormat::Lrat);
    assert_eq!(
        evidence.proof_metadata().proof_kernel,
        ProofKernel::LratChecker
    );
    assert!(evidence.proof_metadata().deterministic_replay);
    assert_eq!(evidence.proof_metadata().original_clause_count, 2);
    assert_eq!(evidence.proof_metadata().proof_step_count, 1);
    assert_eq!(evidence.proof_metadata().steps_replayed, 1);
}

#[test]
fn drat_evidence_records_model_checker_consumer_chc_lane_and_rup_kernel() {
    let context = TrustReplayContext::new(TrustEngine::ModelCheckerConsumer, SolverMode::ChcPdr, "HORN")
        .with_resource_policy(ResourcePolicy::bounded(Some(5_000), None));
    let input = DratReplayInput {
        cnf: UNSAT_CNF,
        proof: UNSAT_DRAT,
    };
    let evidence = TrustReplayEvidence::from_drat(&context, &input).expect("DRAT evidence");

    assert_eq!(evidence.owning_engine(), TrustEngine::ModelCheckerConsumer);
    assert_eq!(evidence.solver_mode(), SolverMode::ChcPdr);
    assert_eq!(evidence.theory_set(), "HORN");
    assert_eq!(evidence.resource_policy().timeout_ms, Some(5_000));
    assert_eq!(evidence.resource_policy().memory_limit_bytes, None);
    assert_eq!(
        evidence.replay_status(),
        ReplayEvidenceStatus::VerifiedUnsat
    );
    assert_eq!(
        evidence.proof_strength(),
        ProofStrength::DratRupKernelChecked
    );
    assert_eq!(evidence.proof_metadata().proof_format, ProofFormat::Drat);
    assert_eq!(
        evidence.proof_metadata().proof_kernel,
        ProofKernel::DratRupChecker
    );
    assert!(evidence.proof_metadata().deterministic_replay);
    assert_eq!(evidence.proof_metadata().add_step_count, 1);
    assert_eq!(evidence.proof_metadata().steps_replayed, 1);
}

#[test]
fn rejected_drat_replay_solver_evidence_reports_unknown_through_owner() {
    let context = TrustReplayContext::new(TrustEngine::ModelCheckerConsumer, SolverMode::ChcPdr, "HORN");
    let input = DratReplayInput {
        cnf: b"p cnf 1 1\n1 0\n",
        proof: b"0\n",
    };
    let replay = TrustReplayEvidence::from_drat(&context, &input).expect("DRAT evidence");

    let evidence = TrustSolverEvidence::from_proof_replay(replay);
    let report = evidence.owner_report();

    assert_eq!(evidence.solver_status(), SolverStatus::Unknown);
    assert_eq!(report.solver_status(), SolverStatus::Unknown);
    assert_eq!(report.evidence_kind(), TrustEvidenceKind::ProofReplay);
    assert_eq!(
        report.replay_status(),
        Some(ReplayEvidenceStatus::ProofRejected)
    );
    assert_eq!(report.proof_strength(), Some(ProofStrength::Rejected));
}

#[test]
fn rejected_lrat_evidence_does_not_claim_checked_strength() {
    let context = TrustReplayContext::new(TrustEngine::DeductiveChecks, SolverMode::Sat, "CNF");
    let input = ReplayInput {
        cnf: UNSAT_CNF,
        proof: b"3 0 1 0\n",
    };
    let evidence = TrustReplayEvidence::from_lrat(&context, &input).expect("LRAT evidence");

    assert_eq!(evidence.owning_engine(), TrustEngine::DeductiveChecks);
    assert_eq!(
        evidence.replay_status(),
        ReplayEvidenceStatus::ProofRejected
    );
    assert_eq!(evidence.proof_strength(), ProofStrength::Rejected);
    assert_eq!(evidence.solver_status(), SolverStatus::Unknown);
}

#[test]
fn rejected_proof_replay_solver_evidence_reports_unknown_through_owner() {
    let context = TrustReplayContext::new(TrustEngine::DeductiveChecks, SolverMode::Sat, "CNF");
    let input = ReplayInput {
        cnf: UNSAT_CNF,
        proof: b"3 0 1 0\n",
    };
    let replay = TrustReplayEvidence::from_lrat(&context, &input).expect("LRAT evidence");

    let evidence = TrustSolverEvidence::from_proof_replay(replay);
    let report = evidence.owner_report();

    assert_eq!(evidence.solver_status(), SolverStatus::Unknown);
    assert_eq!(report.solver_status(), SolverStatus::Unknown);
    assert_eq!(report.evidence_kind(), TrustEvidenceKind::ProofReplay);
    assert_eq!(
        report.replay_status(),
        Some(ReplayEvidenceStatus::ProofRejected)
    );
    assert_eq!(report.proof_strength(), Some(ProofStrength::Rejected));
}

#[test]
fn proof_replay_solver_evidence_reports_unsat_through_owner() {
    let context = TrustReplayContext::new(TrustEngine::VerificationConsumer, SolverMode::Smt, "QF_UF");
    let input = ReplayInput {
        cnf: UNSAT_CNF,
        proof: UNSAT_LRAT,
    };
    let replay = TrustReplayEvidence::from_lrat(&context, &input).expect("LRAT evidence");

    let evidence = TrustSolverEvidence::from_proof_replay(replay);

    assert_eq!(
        evidence.schema(),
        TRUST_NATIVE_VERIFIER_V2_SOLVER_EVIDENCE_SCHEMA
    );
    assert_eq!(evidence.owning_engine(), TrustEngine::VerificationConsumer);
    assert_eq!(evidence.solver_status(), SolverStatus::Unsat);
    assert_eq!(evidence.payload().kind(), TrustEvidenceKind::ProofReplay);
    let report = evidence.owner_report();
    assert_eq!(
        report.schema(),
        TRUST_NATIVE_VERIFIER_V2_OWNER_REPORT_SCHEMA
    );
    assert_eq!(report.owning_engine(), TrustEngine::VerificationConsumer);
    assert_eq!(report.reported_through(), TrustEngine::VerificationConsumer);
    assert_eq!(report.substrate(), AY_TRUST_SUBSTRATE);
    assert_eq!(report.solver_status(), SolverStatus::Unsat);
    assert_eq!(report.evidence_kind(), TrustEvidenceKind::ProofReplay);
    assert_eq!(
        report.replay_status(),
        Some(ReplayEvidenceStatus::VerifiedUnsat)
    );
    assert_eq!(
        report.proof_strength(),
        Some(ProofStrength::LratKernelChecked)
    );
    assert_eq!(report.cnf_sha256(), Some(sha256_hex(UNSAT_CNF).as_str()));
    assert_eq!(report.proof_sha256(), Some(sha256_hex(UNSAT_LRAT).as_str()));
    assert!(report.deterministic_replay());

    let mut reports = Vec::new();
    evidence.report_to(&mut reports);
    assert_eq!(reports, vec![report]);
}

#[test]
fn raw_model_evidence_is_visible_but_cannot_establish_sat() {
    let context = TrustReplayContext::new(TrustEngine::Ty, SolverMode::Smt, "QF_LIA");
    let model_bytes = b"(model (define-fun x () Int 7))\n";
    let model = ModelEvidence::from_bytes(ModelEvidenceFormat::SmtLib2, model_bytes);

    let evidence = TrustSolverEvidence::from_model(&context, model.clone());

    assert_eq!(evidence.owning_engine(), TrustEngine::Ty);
    assert_eq!(evidence.solver_status(), SolverStatus::Unknown);
    assert!(matches!(
        evidence.payload(),
        TrustSolverEvidencePayload::Model(payload)
            if payload.format() == ModelEvidenceFormat::SmtLib2
                && payload.model_sha256() == model.model_sha256()
                && payload.validation() == ArtifactValidationStatus::NotEstablished
    ));
    let report = evidence.owner_report();
    assert_eq!(report.reported_through(), TrustEngine::Ty);
    assert_eq!(report.solver_status(), SolverStatus::Unknown);
    assert_eq!(report.evidence_kind(), TrustEvidenceKind::Model);
    assert_eq!(report.model_sha256(), Some(model.model_sha256()));
    assert_eq!(report.proof_sha256(), None);
    assert_eq!(report.replay_status(), None);
    assert_eq!(
        report.artifact_validation(),
        Some(ArtifactValidationStatus::NotEstablished)
    );
    assert!(!report.deterministic_replay());
}

#[test]
fn raw_counterexample_is_visible_but_cannot_establish_sat() {
    let context = TrustReplayContext::new(TrustEngine::ModelCheckerConsumer, SolverMode::ChcPdr, "HORN");
    let cex_bytes = b"state0 -> state1 -> unsafe\n";
    let counterexample =
        CounterexampleEvidence::from_bytes(CounterexampleEvidenceFormat::ChcTrace, cex_bytes);

    let evidence = TrustSolverEvidence::from_counterexample(&context, counterexample.clone());

    assert_eq!(evidence.owning_engine(), TrustEngine::ModelCheckerConsumer);
    assert_eq!(evidence.solver_mode(), SolverMode::ChcPdr);
    assert_eq!(evidence.solver_status(), SolverStatus::Unknown);
    assert!(matches!(
        evidence.payload(),
        TrustSolverEvidencePayload::Counterexample(payload)
            if payload.format() == CounterexampleEvidenceFormat::ChcTrace
                && payload.counterexample_sha256() == counterexample.counterexample_sha256()
                && payload.validation() == ArtifactValidationStatus::NotEstablished
    ));
    let report = evidence.owner_report();
    assert_eq!(report.reported_through(), TrustEngine::ModelCheckerConsumer);
    assert_eq!(report.solver_status(), SolverStatus::Unknown);
    assert_eq!(report.evidence_kind(), TrustEvidenceKind::Counterexample);
    assert_eq!(
        report.counterexample_sha256(),
        Some(counterexample.counterexample_sha256())
    );
    assert_eq!(report.proof_strength(), None);
    assert_eq!(
        report.artifact_validation(),
        Some(ArtifactValidationStatus::NotEstablished)
    );
}

#[test]
fn unknown_and_timeout_solver_evidence_keep_statuses_and_reasons() {
    let context = TrustReplayContext::new(TrustEngine::DeductiveChecks, SolverMode::Sat, "CNF")
        .with_resource_policy(ResourcePolicy::bounded(Some(2_500), None));

    let unknown = TrustSolverEvidence::unknown(&context, "incomplete proof-trusted");
    assert_eq!(unknown.solver_status(), SolverStatus::Unknown);
    let unknown_report = unknown.owner_report();
    assert_eq!(unknown_report.evidence_kind(), TrustEvidenceKind::Unknown);
    assert_eq!(
        unknown_report.unknown_reason(),
        Some("incomplete proof-trusted")
    );
    assert_eq!(unknown_report.reported_through(), TrustEngine::DeductiveChecks);

    let timeout = TrustSolverEvidence::timeout(
        &context,
        TimeoutEvidence::new(ResourceLimit::Timeout, Some(2_501)),
    );
    assert_eq!(timeout.solver_status(), SolverStatus::Timeout);
    let timeout_report = timeout.owner_report();
    assert_eq!(timeout_report.evidence_kind(), TrustEvidenceKind::Timeout);
    assert_eq!(
        timeout_report.timeout(),
        Some(TimeoutEvidence::new(ResourceLimit::Timeout, Some(2_501)))
    );
    assert_eq!(timeout_report.resource_policy().timeout_ms, Some(2_500));
    assert_eq!(timeout_report.reported_through(), TrustEngine::DeductiveChecks);
}

#[test]
fn lrat_evidence_is_bound_to_the_exact_checked_bytes() {
    let context = TrustReplayContext::new(TrustEngine::DeductiveChecks, SolverMode::Sat, "CNF");
    let verified = TrustReplayEvidence::from_lrat(
        &context,
        &ReplayInput {
            cnf: UNSAT_CNF,
            proof: UNSAT_LRAT,
        },
    )
    .expect("verified LRAT evidence");
    let changed_cnf = b"p cnf 1 1\n1 0\n";
    let rejected = TrustReplayEvidence::from_lrat(
        &context,
        &ReplayInput {
            cnf: changed_cnf,
            proof: UNSAT_LRAT,
        },
    )
    .expect("parseable changed-input evidence");

    assert_eq!(verified.solver_status(), SolverStatus::Unsat);
    assert_eq!(rejected.solver_status(), SolverStatus::Unknown);
    assert_eq!(
        rejected.artifact_hashes(),
        &ReplayInputHashes::from_bytes(changed_cnf, UNSAT_LRAT)
    );
    assert_ne!(
        verified.artifact_hashes().cnf_sha256,
        rejected.artifact_hashes().cnf_sha256
    );
}

#[test]
fn every_payload_derives_the_same_status_as_its_owner_report() {
    let context = TrustReplayContext::new(TrustEngine::DeductiveChecks, SolverMode::Sat, "CNF");
    let cases = [
        TrustSolverEvidence::from_model(
            &context,
            ModelEvidence::from_bytes(ModelEvidenceFormat::Text, b"candidate"),
        ),
        TrustSolverEvidence::from_counterexample(
            &context,
            CounterexampleEvidence::from_bytes(CounterexampleEvidenceFormat::Text, b"candidate"),
        ),
        TrustSolverEvidence::unknown(&context, "not established"),
        TrustSolverEvidence::timeout(&context, TimeoutEvidence::new(ResourceLimit::Timeout, None)),
    ];

    for evidence in cases {
        assert_eq!(evidence.solver_status(), evidence.payload().solver_status());
        assert_eq!(
            evidence.solver_status(),
            evidence.owner_report().solver_status()
        );
    }
}
