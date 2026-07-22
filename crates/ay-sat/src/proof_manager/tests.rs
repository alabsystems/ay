// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for ProofManager (DRAT/LRAT proof emission and validation).

use super::{
    LearnedLratDryRunProofArtifactImportReject, LearnedLratMainProofAuthorityReject,
    LearnedLratMaterializationReplay, LearnedLratMaterializationStatus,
    LearnedLratProofOutAppendReject, LearnedLratReplayRow, LearnedLratReplayRowKind, ProofAddKind,
    ProofManager, LEARNED_LRAT_AUTHORITY_EXTERNAL_CHECKER_REQUIRED,
    LEARNED_LRAT_AUTHORITY_EXTERNAL_CHECKER_VERIFIED, LEARNED_LRAT_AUTHORITY_FAIL_CLOSED,
    LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA,
};
use crate::decompose::{DecomposeProofEmitContext, DecomposeProofOutRecordKind};
use crate::fmla_runtime_ledger::{
    replay_fmla_postcheck_admission, ExternalProofCheckerVerdictArtifactRef,
    FmlaPostCheckAdmissionReplayInput, FmlaPostCheckAdmissionReplayRecord,
    FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT,
    FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_SCHEMA,
};
use crate::proof::ProofOutput;
use crate::test_util::lit;
use crate::Literal;

const FMLA_RETAINED_PROOF_OUT_PATH: &str = "runs/fmla/proof/proof.out";

fn decompose_context(sidecar_row_index: usize) -> DecomposeProofEmitContext {
    DecomposeProofEmitContext {
        transaction_id: 42,
        sidecar_context_token: String::from(concat!("decompose-lrat-", "42")),
        sidecar_row_index,
        source_row_id: "decompose-lrat-source-7".to_string(),
        obligation_id: format!("decompose-lrat-42-{sidecar_row_index}"),
    }
}

fn fmla_learned_lrat_complete_replay() -> LearnedLratMaterializationReplay {
    LearnedLratMaterializationReplay {
        checker_visible_id: 10,
        materialization_status: LearnedLratMaterializationStatus::RetainedDependenciesComplete,
        rows: vec![
            LearnedLratReplayRow {
                kind: LearnedLratReplayRowKind::MaterializerAdd,
                checker_visible_id: 9,
                clause_lits_dimacs: vec![1, 5],
                checker_visible_lrat_hints: vec![1, 6, 3],
            },
            LearnedLratReplayRow {
                kind: LearnedLratReplayRowKind::LearnedAdd,
                checker_visible_id: 10,
                clause_lits_dimacs: vec![1, -2],
                checker_visible_lrat_hints: vec![6, 9, 1],
            },
        ],
        proof_out_emitted: false,
        proof_writer_io_error: false,
    }
}

fn accepted_external_checker_verdict_artifact_for_proof(
    proof_out_bytes: &[u8],
) -> ExternalProofCheckerVerdictArtifactRef {
    let hash = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
    let proof_hash = ProofManager::sha256_hex(proof_out_bytes);
    ExternalProofCheckerVerdictArtifactRef {
        schema: FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_SCHEMA.to_string(),
        runtime_field: FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT
            .runtime_field
            .to_string(),
        artifact_path: "runs/fmla/proof/fmla-main-lrat-external-checker-verdict.json".to_string(),
        artifact_sha256: hash.to_string(),
        checker_path: "/opt/satcomp/bin/cake_lpr".to_string(),
        checker_sha256: hash.to_string(),
        checker_command: format!(
            "/opt/satcomp/bin/cake_lpr benchmarks/FmlaEquivChain_4_6_6.sanitized.cnf {FMLA_RETAINED_PROOF_OUT_PATH}"
        ),
        checker_argv: vec![
            "/opt/satcomp/bin/cake_lpr".to_string(),
            "benchmarks/FmlaEquivChain_4_6_6.sanitized.cnf".to_string(),
            FMLA_RETAINED_PROOF_OUT_PATH.to_string(),
        ],
        checker_exit_code: 0,
        proof_out_path: FMLA_RETAINED_PROOF_OUT_PATH.to_string(),
        proof_out_sha256: proof_hash,
        checked_dimacs_path: "benchmarks/FmlaEquivChain_4_6_6.sanitized.cnf".to_string(),
        checked_dimacs_sha256: hash.to_string(),
        verdict: FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT
            .accepted_verdict
            .to_string(),
    }
}

fn accepted_fmla_postcheck_replay_for_proof(
    proof_out_bytes: &[u8],
) -> FmlaPostCheckAdmissionReplayRecord {
    accepted_fmla_postcheck_replay_for_proof_rows(proof_out_bytes, 1)
}

fn accepted_fmla_postcheck_replay_for_proof_rows(
    proof_out_bytes: &[u8],
    proof_obligation_rows: u64,
) -> FmlaPostCheckAdmissionReplayRecord {
    replay_fmla_postcheck_admission(
        FmlaPostCheckAdmissionReplayInput {
            materializer_attempts: 1,
            materializer_proof_emit_records_seen: 1,
            materializer_records: proof_obligation_rows,
            materializer_fail_closed: 1,
            materializer_missing_runtime_records: 0,
            preprocess_tx_fail_closed: 1,
            preprocess_tx_committed: 0,
        },
        Some(accepted_external_checker_verdict_artifact_for_proof(
            proof_out_bytes,
        )),
    )
    .expect("valid post-check replay fixture should commit checker-backed admission")
}

fn authorized_fmla_replay_json_for_proof_rows(
    proof_out_path: &std::path::Path,
    proof_out_bytes: &[u8],
    proof_obligation_rows: u64,
) -> serde_json::Value {
    let proof_dir = proof_out_path.parent().expect("proof.out parent");
    std::fs::create_dir_all(proof_dir).expect("create proof.out parent");
    let checker_artifact_path =
        proof_dir.join(FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT.artifact_file_name);
    let checker_artifact_body = b"checker verdict";
    std::fs::write(&checker_artifact_path, checker_artifact_body)
        .expect("write retained checker verdict artifact");
    let checker_path = proof_dir.join("cake_lpr").display().to_string();
    let checked_dimacs_path = proof_dir.join("input.cnf").display().to_string();
    let proof_out_path = proof_out_path.display().to_string();
    let checker_command = format!("{checker_path} {checked_dimacs_path} {proof_out_path}");
    serde_json::json!({
        "schema": crate::fmla_runtime_ledger::FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_SCHEMA,
        "status": "committed_checker_backed_admission",
        "proof_obligation_rows": proof_obligation_rows,
        "external_proof_checker_verdict_artifact_rows": proof_obligation_rows,
        "learned_lrat_main_proof_authority_status": "authorized",
        "learned_lrat_main_proof_authority_external_checker_verified": true,
        "learned_lrat_main_proof_authority_proof_out_contains_lrat_fragment": true,
        "learned_lrat_main_proof_authority_authorizes_main_proof_out": true,
        "external_proof_checker_verdict_artifact": checker_artifact_path.display().to_string(),
        "external_proof_checker_verdict_artifact_sha256": ProofManager::sha256_hex(checker_artifact_body),
        "external_proof_checker_verdict_artifact_schema": FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_SCHEMA,
        "external_proof_checker_verdict_artifact_runtime_field": FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT.runtime_field,
        "external_proof_checker_verdict": FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT.accepted_verdict,
        "external_proof_checker_path": checker_path,
        "external_proof_checker_sha256": "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
        "external_proof_checker_command": checker_command,
        "external_proof_checker_argv": [checker_path, checked_dimacs_path, proof_out_path],
        "external_proof_checker_dimacs_path": checked_dimacs_path,
        "external_proof_checker_dimacs_sha256": "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef",
        "checker_exit_code": 0,
        "learned_lrat_main_proof_authority_proof_out_path": proof_out_path,
        "learned_lrat_main_proof_authority_proof_out_sha256": ProofManager::sha256_hex(proof_out_bytes),
    })
}

fn add_fmla_padding_originals(manager: &mut ProofManager, count: u64) {
    manager.register_original_clause(&[lit(0, true)]);
    manager.register_clause_id(1);
    for clause_id in 2..=count {
        manager.register_original_clause(&[lit(0, true), lit((clause_id * 2) as u32, true)]);
        manager.register_clause_id(clause_id);
    }
}

#[test]
fn test_lrat_hint_validation_rejects_unknown_hint_id() {
    let output = ProofOutput::lrat_text(Vec::new(), 1);
    let mut manager = ProofManager::new(output, 2);
    manager.register_original_clause(&[lit(0, true)]);
    manager.register_clause_id(1);
    let derived = [lit(0, true)];
    let added = manager
        .emit_add(&derived, &[1], ProofAddKind::Derived)
        .expect("derived add should succeed");
    assert_eq!(added, 2);

    // Hint 99 is unknown. Derived LRAT additions must fail closed instead of
    // writing a line with the essential hint silently stripped.
    let bad_id = manager
        .emit_add(&[lit(1, true)], &[99], ProofAddKind::Derived)
        .expect("structural failure is reported through the proof-error latch");
    assert_eq!(bad_id, 0);
    assert!(manager.has_io_error());
}

#[test]
#[cfg(debug_assertions)]
fn test_lrat_chain_verifier_catches_bad_hints_via_manager() {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 3);
    manager.register_original_clause(&[lit(0, true), lit(1, true)]);
    manager.register_clause_id(1);
    manager.register_original_clause(&[lit(0, false), lit(1, true)]);
    manager.register_clause_id(2);
    let clause_id = manager
        .emit_add(&[lit(1, true)], &[1, 2], ProofAddKind::Derived)
        .expect("valid LRAT add should succeed");
    assert!(clause_id > 0);
}

#[test]
#[cfg(debug_assertions)]
fn test_lrat_chain_verifier_skips_non_empty_derived_clauses() {
    // Non-empty derived clauses skip online LRAT verification (#7108).
    // The online checker cannot verify all learned clause chains because
    // the resolution chain references reason clauses whose non-resolved
    // literals aren't established by any hint. Non-empty derived clauses
    // are added as originals to keep the checker DB correct.
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 3);

    manager.register_original_clause(&[lit(0, true), lit(1, true)]);
    manager.register_clause_id(1);

    let result = manager.emit_add(&[lit(0, false), lit(1, false)], &[1], ProofAddKind::Derived);
    assert!(result.is_ok(), "emit_add should succeed");
    // No LRAT failure: non-empty derived clauses are added as originals.
    assert_eq!(
        manager.lrat_failures(),
        0,
        "non-empty derived clauses skip online LRAT verification"
    );
}

#[test]
fn test_block_lrat_for_theory_lemmas_noops_emission() {
    let output = ProofOutput::lrat_text(Vec::new(), 0);
    let mut manager = ProofManager::new(output, 1);
    manager.block_lrat_for_theory_lemmas();
    let add_id = manager
        .emit_add(&[lit(0, true), lit(0, false)], &[1], ProofAddKind::Derived)
        .expect("blocked LRAT add should be a no-op");
    assert_eq!(add_id, 0);
    manager
        .emit_delete(&[lit(0, true)], 1)
        .expect("blocked LRAT delete should be a no-op");
    assert_eq!(manager.added_count(), 0);
}

#[test]
fn test_lrat_axiom_add_without_hints_is_skipped() {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 2);
    let clause = [lit(0, true), lit(1, true)];
    let added = manager
        .emit_add(&clause, &[], ProofAddKind::Axiom)
        .expect("skip path should be non-failing");
    assert_eq!(added, 0);
    assert_eq!(manager.added_count(), 0);
}

#[test]
fn test_lrat_trusted_transform_without_hints_is_hidden_and_fails_closed() {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 2);
    let clause = [lit(0, true), lit(1, true)];
    let added = manager
        .emit_add(&clause, &[], ProofAddKind::TrustedTransform)
        .expect("hiding a TrustedTransform should not be an I/O error");
    assert_ne!(added, 0, "internal bookkeeping still reserves an ID");
    assert_eq!(manager.added_count(), 0, "no unproved LRAT line is written");
    assert!(manager.has_lrat_authority_fail_closed());
    assert!(manager.has_io_error());
}

#[test]
fn test_lrat_derived_empty_without_hints_is_hidden_and_fails_closed() {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 1);
    manager.register_original_clause(&[lit(0, true)]);
    manager.register_clause_id(1);
    manager.register_original_clause(&[lit(0, false)]);
    manager.register_clause_id(2);

    let hidden_id = manager
        .emit_add(&[], &[], ProofAddKind::Derived)
        .expect("missing-hint empty derivation is hidden without an I/O write");
    assert_eq!(hidden_id, 3, "bookkeeping still reserves the derived ID");
    assert_eq!(manager.added_count(), 0);
    assert!(manager.has_lrat_authority_fail_closed());
    assert!(manager.has_io_error());

    let repeated_id = manager
        .emit_add(&[], &[], ProofAddKind::Derived)
        .expect("repeated missing-hint empty derivation remains hidden");
    assert_eq!(repeated_id, hidden_id);

    let proof = manager
        .into_output()
        .into_vec()
        .expect("writer remains readable");
    assert!(proof.is_empty(), "invalid `3 0 0` must never be serialized");
}

#[test]
fn test_decompose_scoped_observer_skips_unproved_trusted_lrat_add() {
    let output = ProofOutput::lrat_text(Vec::new(), 0);
    let mut manager = ProofManager::new(output, 2);
    let clause = [lit(0, true), lit(1, true)];
    let context = decompose_context(0);

    let added = manager
        .emit_add_with_decompose_context(&clause, &[], ProofAddKind::TrustedTransform, &context)
        .expect("scoped decompose add should fail closed without I/O failure");

    assert_ne!(added, 0);
    assert_eq!(manager.added_count(), 0);
    assert!(manager.scoped_decompose_proof_emit_records().is_empty());
    assert!(manager.has_lrat_authority_fail_closed());
}

#[test]
fn test_decompose_scoped_observer_skips_suppressed_lrat_add() {
    let output = ProofOutput::lrat_text(Vec::new(), 0);
    let mut manager = ProofManager::new(output, 2);
    let clause = [lit(0, true), lit(1, true)];
    let context = decompose_context(0);

    let added = manager
        .emit_add_with_decompose_context(&clause, &[], ProofAddKind::Axiom, &context)
        .expect("suppressed scoped decompose add should not fail");

    assert_eq!(added, 0);
    assert_eq!(manager.added_count(), 0);
    assert!(manager.scoped_decompose_proof_emit_records().is_empty());
}

#[test]
fn test_decompose_scoped_observer_records_successful_lrat_delete_once() {
    let output = ProofOutput::lrat_text(Vec::new(), 1);
    let mut manager = ProofManager::new(output, 2);
    let clause = [lit(0, true), lit(1, true)];
    manager.register_original_clause(&clause);
    manager.register_clause_id(1);
    let context = decompose_context(1);

    manager
        .emit_delete_with_decompose_context(&clause, 1, &context)
        .expect("scoped decompose delete should emit");
    manager
        .emit_delete_with_decompose_context(&clause, 1, &context)
        .expect("duplicate scoped decompose delete should be skipped");

    let records = manager.scoped_decompose_proof_emit_records();
    assert_eq!(records.len(), 1);
    assert_eq!(records[0].context, context);
    assert_eq!(
        records[0].proof_out_record_kind,
        DecomposeProofOutRecordKind::Delete
    );
    assert_eq!(records[0].proof_field, "deletion_proof_steps");
    assert_eq!(records[0].checker_visible_id, 1);
    assert_eq!(records[0].delete_source_id, Some(1));
    assert_eq!(records[0].clause_lits_dimacs, vec![1, 2]);
    assert_eq!(records[0].proof_manager_mode, "lrat");
    assert!(records[0].solver_runtime_emitted);
    assert!(!records[0].proof_writer_io_error);
    assert!(!records[0].external_checker_verified);
}

#[test]
fn test_fmla_learned_lrat_dry_run_requires_external_checker_before_authority() {
    let replay = fmla_learned_lrat_complete_replay();

    let artifact =
        ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(&replay);

    assert_eq!(
        artifact.materialization_status,
        LearnedLratMaterializationStatus::RetainedDependenciesComplete
    );
    assert_eq!(artifact.rows.len(), 2);
    assert_eq!(
        artifact.lrat_fragment,
        "9 1 5 0 1 6 3 0\n10 1 -2 0 6 9 1 0\n"
    );
    assert!(!artifact.proof_out_emitted);
    assert!(!artifact.proof_writer_io_error);
    assert!(artifact.external_checker_required);
    assert!(!artifact.external_checker_verified);
    assert_eq!(
        artifact.main_proof_authority_reason,
        LEARNED_LRAT_AUTHORITY_EXTERNAL_CHECKER_REQUIRED
    );
    assert!(
        !artifact.authorizes_main_proof_out,
        "checker-visible dry-run fragments are not Main proof.out authority without a same-run checker verdict"
    );
}

#[test]
fn test_fmla_learned_lrat_main_proof_authority_requires_same_run_checker_verdict() {
    let dry_run = ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(
        &fmla_learned_lrat_complete_replay(),
    );
    let proof_out = format!("c prefix retained by wrapper\n{}", dry_run.lrat_fragment);
    let checker_verdict =
        accepted_external_checker_verdict_artifact_for_proof(proof_out.as_bytes());

    let authority = ProofManager::validate_fmla_learned_lrat_main_proof_authority(
        &dry_run,
        &checker_verdict,
        proof_out.as_bytes(),
    )
    .expect("same-run checked proof_out should authorize the retained fragment");

    assert_eq!(authority.checker_visible_id, 10);
    assert_eq!(
        authority.materialization_status,
        LearnedLratMaterializationStatus::RetainedDependenciesComplete
    );
    assert_eq!(authority.proof_out_path, FMLA_RETAINED_PROOF_OUT_PATH);
    assert_eq!(authority.proof_out_sha256, checker_verdict.proof_out_sha256);
    assert!(authority.external_checker_verified);
    assert!(authority.proof_out_contains_lrat_fragment);
    assert_eq!(
        authority.main_proof_authority_reason,
        LEARNED_LRAT_AUTHORITY_EXTERNAL_CHECKER_VERIFIED
    );
    assert!(authority.authorizes_main_proof_out);
}

#[test]
fn test_fmla_learned_lrat_main_proof_authority_accepts_postcheck_replay_bridge() {
    let dry_run = ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(
        &fmla_learned_lrat_complete_replay(),
    );
    let proof_out = format!("c prefix retained by wrapper\n{}", dry_run.lrat_fragment);
    let postcheck_replay = accepted_fmla_postcheck_replay_for_proof(proof_out.as_bytes());

    let authority =
        ProofManager::validate_fmla_learned_lrat_main_proof_authority_from_postcheck_replay(
            &dry_run,
            &postcheck_replay,
            FMLA_RETAINED_PROOF_OUT_PATH,
            proof_out.as_bytes(),
        )
        .expect("checker-backed post-check replay should authorize the retained fragment");

    assert_eq!(authority.checker_visible_id, 10);
    assert_eq!(authority.proof_out_path, FMLA_RETAINED_PROOF_OUT_PATH);
    assert!(authority.external_checker_verified);
    assert!(authority.proof_out_contains_lrat_fragment);
    assert!(authority.authorizes_main_proof_out);
}

#[test]
fn test_fmla_learned_lrat_main_proof_authority_consumes_materializer_producer_replay() {
    let mut manager = ProofManager::new(ProofOutput::lrat_text(Vec::new(), 8), 20);
    add_fmla_padding_originals(&mut manager, 8);

    let materializer_context = DecomposeProofEmitContext {
        transaction_id: 42,
        sidecar_context_token: "fmla-guarded-equiv-support-cover-lrat-42".to_string(),
        sidecar_row_index: 0,
        source_row_id: "fmla-guarded-equiv-support-cover-source-1".to_string(),
        obligation_id: "fmla-guarded-equiv-support-cover-42-0".to_string(),
    };
    let materializer_clause = [lit(0, true), lit(4, true)];
    let materializer_source_ids = [1, 6, 3];
    let materializer_id = manager
        .emit_add_with_decompose_context(
            &materializer_clause,
            &materializer_source_ids,
            ProofAddKind::Derived,
            &materializer_context,
        )
        .expect("emit materializer proof row");
    manager.mark_lrat_authority_fail_closed();
    let learned_clause = [lit(0, true), lit(1, false)];
    let learned_id = manager.reserve_lrat_id_for_backward();
    manager.record_fmla_learned_lrat_authority_fail_closed(
        learned_id,
        &learned_clause,
        &[1, materializer_id, 6],
        &[6, materializer_id, 1],
    );

    let dry_run_fragments = manager.dry_run_fmla_learned_lrat_materialization_fragments();
    assert_eq!(dry_run_fragments.len(), 1);
    let dry_run = &dry_run_fragments[0];
    assert_eq!(
        dry_run.materialization_status,
        LearnedLratMaterializationStatus::RetainedDependenciesComplete
    );
    assert_eq!(dry_run.rows.len(), 2);
    assert!(dry_run.external_checker_required);
    assert!(!dry_run.authorizes_main_proof_out);

    let proof_out = format!(
        "c same-run proof.out retained by wrapper\n{}",
        dry_run.lrat_fragment
    );
    let postcheck_replay = accepted_fmla_postcheck_replay_for_proof_rows(
        proof_out.as_bytes(),
        dry_run.rows.len() as u64,
    );
    let authority =
        ProofManager::validate_fmla_learned_lrat_main_proof_authority_from_postcheck_replay(
            dry_run,
            &postcheck_replay,
            FMLA_RETAINED_PROOF_OUT_PATH,
            proof_out.as_bytes(),
        )
        .expect("materializer-produced dry-run fragment should consume checker-backed replay");

    assert_eq!(authority.checker_visible_id, learned_id);
    assert_eq!(authority.proof_out_path, FMLA_RETAINED_PROOF_OUT_PATH);
    assert!(authority.external_checker_verified);
    assert!(authority.proof_out_contains_lrat_fragment);
    assert!(authority.authorizes_main_proof_out);
}

#[test]
fn test_fmla_learned_lrat_authorized_append_writes_only_reserved_learned_row() {
    let mut manager = ProofManager::new(ProofOutput::lrat_text(Vec::new(), 8), 20);
    add_fmla_padding_originals(&mut manager, 8);

    let materializer_context = DecomposeProofEmitContext {
        transaction_id: 42,
        sidecar_context_token: "fmla-guarded-equiv-support-cover-lrat-42".to_string(),
        sidecar_row_index: 0,
        source_row_id: "fmla-guarded-equiv-support-cover-source-1".to_string(),
        obligation_id: "fmla-guarded-equiv-support-cover-42-0".to_string(),
    };
    let materializer_id = manager
        .emit_add_with_decompose_context(
            &[lit(0, true), lit(4, true)],
            &[1, 6, 3],
            ProofAddKind::Derived,
            &materializer_context,
        )
        .expect("emit materializer proof row");
    manager.mark_lrat_authority_fail_closed();
    let learned_id = manager.reserve_lrat_id_for_backward();
    manager.record_fmla_learned_lrat_authority_fail_closed(
        learned_id,
        &[lit(0, true), lit(1, false)],
        &[1, materializer_id, 6],
        &[6, materializer_id, 1],
    );

    let dry_run = manager
        .dry_run_fmla_learned_lrat_materialization_fragments()
        .pop()
        .expect("complete dry-run fragment");
    assert_eq!(
        dry_run.lrat_fragment,
        "9 1 5 0 1 6 3 0\n10 1 -2 0 6 9 1 0\n"
    );
    let retained = tempfile::tempdir().expect("retained proof dir");
    let retained_proof_out_path = retained.path().join("proof.out");
    let replay = authorized_fmla_replay_json_for_proof_rows(
        &retained_proof_out_path,
        dry_run.lrat_fragment.as_bytes(),
        dry_run.rows.len() as u64,
    );

    let appended = manager
        .append_authorized_fmla_learned_lrat_fragment_from_replay_json(
            &replay,
            &retained_proof_out_path.display().to_string(),
        )
        .expect("checker-backed replay should authorize learned row append");
    assert_eq!(appended, 1);

    let proof = String::from_utf8(
        manager
            .into_output()
            .into_vec()
            .expect("proof bytes should extract"),
    )
    .expect("LRAT text should be UTF-8");
    assert_eq!(
        proof, "9 1 5 0 1 6 3 0\n10 1 -2 0 6 9 1 0\n",
        "materializer row stays single-emitted and the reserved learned row is appended"
    );
}

#[test]
fn test_fmla_learned_lrat_authorized_append_rejects_diagnostic_rows() {
    let mut manager = ProofManager::new(ProofOutput::lrat_text(Vec::new(), 8), 20);
    add_fmla_padding_originals(&mut manager, 8);
    manager.mark_lrat_authority_fail_closed();
    let learned_id = manager.reserve_lrat_id_for_backward();
    manager.record_fmla_learned_lrat_authority_fail_closed(
        learned_id,
        &[lit(0, true), lit(1, false)],
        &[1, 6],
        &[6, 1],
    );
    let diagnostic = manager
        .dry_run_fmla_learned_lrat_materialization_fragments()
        .pop()
        .expect("diagnostic dry-run fragment");
    assert_eq!(
        diagnostic.materialization_status,
        LearnedLratMaterializationStatus::FailClosedMissingMaterializerDependency
    );
    let retained = tempfile::tempdir().expect("retained proof dir");
    let retained_proof_out_path = retained.path().join("proof.out");
    let replay = authorized_fmla_replay_json_for_proof_rows(
        &retained_proof_out_path,
        diagnostic.lrat_fragment.as_bytes(),
        diagnostic.rows.len() as u64,
    );

    let err = manager
        .append_authorized_fmla_learned_lrat_fragment_from_replay_json(
            &replay,
            &retained_proof_out_path.display().to_string(),
        )
        .expect_err("diagnostic-only dry-run rows must not authorize proof output append");
    assert_eq!(err, LearnedLratProofOutAppendReject::NoCompleteDryRun);
    assert_eq!(manager.added_count(), 0);
}

#[test]
fn test_fmla_learned_lrat_dry_run_artifact_envelope_round_trips_producer_replay() {
    let mut manager = ProofManager::new(ProofOutput::lrat_text(Vec::new(), 8), 20);
    add_fmla_padding_originals(&mut manager, 8);

    let materializer_context = DecomposeProofEmitContext {
        transaction_id: 42,
        sidecar_context_token: "fmla-guarded-equiv-support-cover-lrat-42".to_string(),
        sidecar_row_index: 0,
        source_row_id: "fmla-guarded-equiv-support-cover-source-1".to_string(),
        obligation_id: "fmla-guarded-equiv-support-cover-42-0".to_string(),
    };
    let materializer_id = manager
        .emit_add_with_decompose_context(
            &[lit(0, true), lit(4, true)],
            &[1, 6, 3],
            ProofAddKind::Derived,
            &materializer_context,
        )
        .expect("emit materializer proof row");
    manager.mark_lrat_authority_fail_closed();
    let learned_id = manager.reserve_lrat_id_for_backward();
    manager.record_fmla_learned_lrat_authority_fail_closed(
        learned_id,
        &[lit(0, true), lit(1, false)],
        &[1, materializer_id, 6],
        &[6, materializer_id, 1],
    );

    let dry_run = manager
        .dry_run_fmla_learned_lrat_materialization_fragments()
        .pop()
        .expect("producer should expose one dry-run fragment");
    let envelope = ProofManager::export_fmla_learned_lrat_dry_run_proof_artifact(&dry_run);
    assert_eq!(envelope.schema, LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA);
    assert_eq!(
        envelope.lrat_fragment_sha256,
        ProofManager::sha256_hex(dry_run.lrat_fragment.as_bytes())
    );

    let json =
        ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_to_json_value(&envelope);
    let parsed_envelope =
        ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_from_json_value(&json)
            .expect("typed dry-run artifact envelope should parse from JSON");
    let imported = ProofManager::import_fmla_learned_lrat_dry_run_proof_artifact(parsed_envelope)
        .expect("valid dry-run artifact envelope should import fail-closed");
    assert_eq!(imported, dry_run);
    assert!(
        !imported.authorizes_main_proof_out,
        "serialized dry-run rows remain non-authoritative until same-run post-check replay"
    );

    let proof_out = format!("c retained proof.out\n{}", imported.lrat_fragment);
    let postcheck_replay = accepted_fmla_postcheck_replay_for_proof_rows(
        proof_out.as_bytes(),
        imported.rows.len() as u64,
    );
    let authority =
        ProofManager::validate_fmla_learned_lrat_main_proof_authority_from_postcheck_replay(
            &imported,
            &postcheck_replay,
            FMLA_RETAINED_PROOF_OUT_PATH,
            proof_out.as_bytes(),
        )
        .expect("imported dry-run fragment can feed the existing checker-backed replay validator");
    assert_eq!(authority.checker_visible_id, learned_id);
    assert!(authority.authorizes_main_proof_out);
}

#[test]
fn test_fmla_learned_lrat_dry_run_artifact_import_rejects_payload_mismatch() {
    let dry_run = ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(
        &fmla_learned_lrat_complete_replay(),
    );
    let envelope = ProofManager::export_fmla_learned_lrat_dry_run_proof_artifact(&dry_run);
    let mut json =
        ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_to_json_value(&envelope);
    let drifted_fragment = format!("{}11 0 1 0\n", dry_run.lrat_fragment);
    json["lrat_fragment"] = serde_json::Value::String(drifted_fragment.clone());
    json["lrat_fragment_sha256"] =
        serde_json::Value::String(ProofManager::sha256_hex(drifted_fragment.as_bytes()));

    let parsed_envelope =
        ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_from_json_value(&json)
            .expect("payload drift still has a syntactically valid envelope");
    let err = ProofManager::import_fmla_learned_lrat_dry_run_proof_artifact(parsed_envelope)
        .expect_err("fragment bytes must exactly match serialized dry-run rows");

    assert_eq!(
        err,
        LearnedLratDryRunProofArtifactImportReject::LratFragmentRowsMismatch
    );
}

#[test]
fn test_fmla_learned_lrat_dry_run_artifact_import_rejects_row_line_mismatch() {
    let dry_run = ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(
        &fmla_learned_lrat_complete_replay(),
    );
    let envelope = ProofManager::export_fmla_learned_lrat_dry_run_proof_artifact(&dry_run);
    let mut json =
        ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_to_json_value(&envelope);
    json["rows"][0]["lrat_line"] = serde_json::Value::String("9 1 5 0 1 0\n".to_string());
    let row_fragment = format!(
        "{}{}",
        json["rows"][0]["lrat_line"].as_str().unwrap(),
        json["rows"][1]["lrat_line"].as_str().unwrap()
    );
    json["lrat_fragment"] = serde_json::Value::String(row_fragment.clone());
    json["lrat_fragment_sha256"] =
        serde_json::Value::String(ProofManager::sha256_hex(row_fragment.as_bytes()));

    let parsed_envelope =
        ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_from_json_value(&json)
            .expect("row-line drift still has a syntactically valid envelope");
    let err = ProofManager::import_fmla_learned_lrat_dry_run_proof_artifact(parsed_envelope)
        .expect_err("row lrat_line must match row fields");

    assert_eq!(
        err,
        LearnedLratDryRunProofArtifactImportReject::LratFragmentRowsMismatch
    );
}

#[test]
fn test_fmla_learned_lrat_dry_run_artifact_import_rejects_pre_authorized_payload() {
    let dry_run = ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(
        &fmla_learned_lrat_complete_replay(),
    );
    let envelope = ProofManager::export_fmla_learned_lrat_dry_run_proof_artifact(&dry_run);
    let mut json =
        ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_to_json_value(&envelope);
    json["authorizes_main_proof_out"] = serde_json::Value::Bool(true);

    let parsed_envelope =
        ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_from_json_value(&json)
            .expect("pre-authorized payload is syntactically valid JSON");
    let err = ProofManager::import_fmla_learned_lrat_dry_run_proof_artifact(parsed_envelope)
        .expect_err("dry-run import must not accept pre-authorized Main proof_out authority");

    assert_eq!(
        err,
        LearnedLratDryRunProofArtifactImportReject::InvalidAuthorityState
    );
}

#[test]
fn test_fmla_learned_lrat_dry_run_artifact_import_rejects_materializer_only_promotion() {
    let replay = LearnedLratMaterializationReplay {
        checker_visible_id: 10,
        materialization_status:
            LearnedLratMaterializationStatus::FailClosedIncompleteLearnedDependency,
        rows: vec![LearnedLratReplayRow {
            kind: LearnedLratReplayRowKind::MaterializerAdd,
            checker_visible_id: 9,
            clause_lits_dimacs: vec![1, 5],
            checker_visible_lrat_hints: vec![1, 6, 3],
        }],
        proof_out_emitted: false,
        proof_writer_io_error: false,
    };
    let dry_run =
        ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(&replay);
    let envelope = ProofManager::export_fmla_learned_lrat_dry_run_proof_artifact(&dry_run);
    let mut json =
        ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_to_json_value(&envelope);
    json["materialization_status"] =
        serde_json::Value::String("retained_dependencies_complete".to_string());
    json["external_checker_required"] = serde_json::Value::Bool(true);
    json["main_proof_authority_reason"] =
        serde_json::Value::String(LEARNED_LRAT_AUTHORITY_EXTERNAL_CHECKER_REQUIRED.to_string());

    let parsed_envelope =
        ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_from_json_value(&json)
            .expect("promoted materializer-only envelope is syntactically valid");
    let err = ProofManager::import_fmla_learned_lrat_dry_run_proof_artifact(parsed_envelope)
        .expect_err("materializer-only retained rows must not import as complete dry-run proof");

    assert_eq!(
        err,
        LearnedLratDryRunProofArtifactImportReject::ReplayRowsMalformed
    );
}

#[test]
fn test_fmla_learned_lrat_dry_run_artifact_import_rejects_schema_mismatch() {
    let dry_run = ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(
        &fmla_learned_lrat_complete_replay(),
    );
    let envelope = ProofManager::export_fmla_learned_lrat_dry_run_proof_artifact(&dry_run);
    let mut json =
        ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_to_json_value(&envelope);
    json["schema"] =
        serde_json::Value::String("ay.fmla-learned-lrat-dry-run-proof-artifact/v0".to_string());

    let parsed_envelope =
        ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_from_json_value(&json)
            .expect("schema drift is an import-time validation error");
    let err = ProofManager::import_fmla_learned_lrat_dry_run_proof_artifact(parsed_envelope)
        .expect_err("schema mismatch must fail closed");

    assert_eq!(
        err,
        LearnedLratDryRunProofArtifactImportReject::SchemaMismatch {
            observed: "ay.fmla-learned-lrat-dry-run-proof-artifact/v0".to_string()
        }
    );
}

#[test]
fn test_fmla_learned_lrat_main_proof_authority_rejects_uncommitted_postcheck_replay() {
    let dry_run = ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(
        &fmla_learned_lrat_complete_replay(),
    );
    let proof_out = format!("c prefix retained by wrapper\n{}", dry_run.lrat_fragment);
    let mut postcheck_replay = accepted_fmla_postcheck_replay_for_proof(proof_out.as_bytes());
    postcheck_replay.status = "fail_closed_missing_external_checker";

    let err = ProofManager::validate_fmla_learned_lrat_main_proof_authority_from_postcheck_replay(
        &dry_run,
        &postcheck_replay,
        FMLA_RETAINED_PROOF_OUT_PATH,
        proof_out.as_bytes(),
    )
    .expect_err("non-committed post-check replay must not authorize Main proof_out");

    assert_eq!(
        err,
        LearnedLratMainProofAuthorityReject::PostCheckReplayNotCommitted {
            schema: postcheck_replay.schema,
            status: "fail_closed_missing_external_checker"
        }
    );
}

#[test]
fn test_fmla_learned_lrat_main_proof_authority_rejects_wrong_retained_proof_path() {
    let dry_run = ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(
        &fmla_learned_lrat_complete_replay(),
    );
    let proof_out = format!("c prefix retained by wrapper\n{}", dry_run.lrat_fragment);
    let postcheck_replay = accepted_fmla_postcheck_replay_for_proof(proof_out.as_bytes());
    let wrong_retained_path = "runs/other/proof/proof.out";

    let err = ProofManager::validate_fmla_learned_lrat_main_proof_authority_from_postcheck_replay(
        &dry_run,
        &postcheck_replay,
        wrong_retained_path,
        proof_out.as_bytes(),
    )
    .expect_err("post-check replay must bind to the same retained proof.out path");

    assert_eq!(
        err,
        LearnedLratMainProofAuthorityReject::ProofOutPathMismatch {
            retained_proof_out_path: wrong_retained_path.to_string(),
            checker_proof_out_path: FMLA_RETAINED_PROOF_OUT_PATH.to_string(),
        }
    );
}

#[test]
fn test_fmla_learned_lrat_main_proof_authority_rejects_partial_postcheck_replay() {
    let dry_run = ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(
        &fmla_learned_lrat_complete_replay(),
    );
    let proof_out = format!("c prefix retained by wrapper\n{}", dry_run.lrat_fragment);
    let mut postcheck_replay = accepted_fmla_postcheck_replay_for_proof(proof_out.as_bytes());
    postcheck_replay.external_checker_verdict_artifact_rows = 0;

    let err = ProofManager::validate_fmla_learned_lrat_main_proof_authority_from_postcheck_replay(
        &dry_run,
        &postcheck_replay,
        FMLA_RETAINED_PROOF_OUT_PATH,
        proof_out.as_bytes(),
    )
    .expect_err("partial post-check replay must not authorize Main proof_out");

    assert_eq!(
        err,
        LearnedLratMainProofAuthorityReject::PostCheckReplayCheckerRowMismatch {
            proof_obligation_rows: 1,
            external_checker_verdict_artifact_rows: 0
        }
    );
}

#[test]
fn test_fmla_learned_lrat_main_proof_authority_rejects_stale_proof_hash() {
    let dry_run = ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(
        &fmla_learned_lrat_complete_replay(),
    );
    let proof_out = format!("c prefix retained by wrapper\n{}", dry_run.lrat_fragment);
    let stale_checker_verdict =
        accepted_external_checker_verdict_artifact_for_proof(b"stale proof.out\n");

    let err = ProofManager::validate_fmla_learned_lrat_main_proof_authority(
        &dry_run,
        &stale_checker_verdict,
        proof_out.as_bytes(),
    )
    .expect_err("proof_out bytes must match retained checker verdict hash");

    assert_eq!(
        err,
        LearnedLratMainProofAuthorityReject::ProofOutSha256Mismatch
    );
}

#[test]
fn test_fmla_learned_lrat_main_proof_authority_rejects_missing_fragment() {
    let dry_run = ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(
        &fmla_learned_lrat_complete_replay(),
    );
    let proof_out = b"c checked proof.out without retained learned fragment\n11 0 1 0\n";
    let checker_verdict = accepted_external_checker_verdict_artifact_for_proof(proof_out);

    let err = ProofManager::validate_fmla_learned_lrat_main_proof_authority(
        &dry_run,
        &checker_verdict,
        proof_out,
    )
    .expect_err("checked proof_out must contain the serialized dry-run LRAT fragment");

    assert_eq!(
        err,
        LearnedLratMainProofAuthorityReject::ProofOutMissingDryRunFragment
    );
}

#[test]
fn test_fmla_learned_lrat_main_proof_authority_rejects_unverified_verdict() {
    let dry_run = ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(
        &fmla_learned_lrat_complete_replay(),
    );
    let proof_out = format!("c prefix retained by wrapper\n{}", dry_run.lrat_fragment);
    let mut checker_verdict =
        accepted_external_checker_verdict_artifact_for_proof(proof_out.as_bytes());
    checker_verdict.verdict = "NOT_VERIFIED".to_string();

    let err = ProofManager::validate_fmla_learned_lrat_main_proof_authority(
        &dry_run,
        &checker_verdict,
        proof_out.as_bytes(),
    )
    .expect_err("unverified external checker verdict must not authorize Main proof_out");

    assert_eq!(
        err,
        LearnedLratMainProofAuthorityReject::ExternalCheckerVerdictNotAccepted {
            reason: "external_checker_verdict_not_verified_unsat"
        }
    );
}

#[test]
fn test_fmla_learned_lrat_main_proof_authority_rejects_pre_authorized_dry_run_state() {
    let mut dry_run = ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(
        &fmla_learned_lrat_complete_replay(),
    );
    dry_run.external_checker_verified = true;
    dry_run.authorizes_main_proof_out = true;
    dry_run.main_proof_authority_reason = LEARNED_LRAT_AUTHORITY_EXTERNAL_CHECKER_VERIFIED;
    let proof_out = format!("c prefix retained by wrapper\n{}", dry_run.lrat_fragment);
    let checker_verdict =
        accepted_external_checker_verdict_artifact_for_proof(proof_out.as_bytes());

    let err = ProofManager::validate_fmla_learned_lrat_main_proof_authority(
        &dry_run,
        &checker_verdict,
        proof_out.as_bytes(),
    )
    .expect_err("Main proof authority must only upgrade an unverified dry-run artifact");

    assert_eq!(
        err,
        LearnedLratMainProofAuthorityReject::DryRunInvalidAuthorityState
    );
}

#[test]
fn test_fmla_learned_lrat_main_proof_authority_rejects_fail_closed_dry_run() {
    let replay = LearnedLratMaterializationReplay {
        checker_visible_id: 10,
        materialization_status:
            LearnedLratMaterializationStatus::FailClosedMissingMaterializerDependency,
        rows: Vec::new(),
        proof_out_emitted: false,
        proof_writer_io_error: false,
    };
    let dry_run =
        ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(&replay);
    let proof_out = b"c externally checked proof without complete dry-run materialization\n";
    let checker_verdict = accepted_external_checker_verdict_artifact_for_proof(proof_out);

    let err = ProofManager::validate_fmla_learned_lrat_main_proof_authority(
        &dry_run,
        &checker_verdict,
        proof_out,
    )
    .expect_err("fail-closed dry-run materialization must not authorize Main proof_out");

    assert_eq!(
        err,
        LearnedLratMainProofAuthorityReject::DryRunNotComplete {
            materialization_status:
                LearnedLratMaterializationStatus::FailClosedMissingMaterializerDependency
        }
    );
}

#[test]
fn test_fmla_learned_lrat_dry_run_no_records_artifact_round_trips_fail_closed() {
    let dry_run = ProofManager::fail_closed_no_fmla_learned_lrat_dry_run_proof_artifact();
    let envelope = ProofManager::export_fmla_learned_lrat_dry_run_proof_artifact(&dry_run);
    let json =
        ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_to_json_value(&envelope);
    assert_eq!(
        json["materialization_status"].as_str(),
        Some("fail_closed_no_learned_lrat_authority_records")
    );

    let parsed_envelope =
        ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_from_json_value(&json)
            .expect("no-records artifact envelope should parse");
    let imported = ProofManager::import_fmla_learned_lrat_dry_run_proof_artifact(parsed_envelope)
        .expect("no-records artifact must import as a fail-closed diagnostic");

    assert_eq!(imported.checker_visible_id, 0);
    assert_eq!(
        imported.materialization_status,
        LearnedLratMaterializationStatus::FailClosedNoLearnedLratAuthorityRecords
    );
    assert!(imported.rows.is_empty());
    assert_eq!(imported.lrat_fragment, "");
    assert!(!imported.external_checker_required);
    assert!(!imported.external_checker_verified);
    assert_eq!(
        imported.main_proof_authority_reason,
        LEARNED_LRAT_AUTHORITY_FAIL_CLOSED
    );
    assert!(!imported.authorizes_main_proof_out);

    let proof_out = b"c externally checked proof without learned authority records\n";
    let checker_verdict = accepted_external_checker_verdict_artifact_for_proof(proof_out);
    let err = ProofManager::validate_fmla_learned_lrat_main_proof_authority(
        &imported,
        &checker_verdict,
        proof_out,
    )
    .expect_err("no-records diagnostic must not authorize Main proof_out");

    assert_eq!(
        err,
        LearnedLratMainProofAuthorityReject::DryRunNotComplete {
            materialization_status:
                LearnedLratMaterializationStatus::FailClosedNoLearnedLratAuthorityRecords
        }
    );
}

#[test]
fn test_fmla_learned_lrat_dry_run_retains_fail_closed_materializer_rows() {
    let replay = LearnedLratMaterializationReplay {
        checker_visible_id: 10,
        materialization_status:
            LearnedLratMaterializationStatus::FailClosedIncompleteLearnedDependency,
        rows: vec![LearnedLratReplayRow {
            kind: LearnedLratReplayRowKind::MaterializerAdd,
            checker_visible_id: 9,
            clause_lits_dimacs: vec![1, 5],
            checker_visible_lrat_hints: vec![1, 6, 3],
        }],
        proof_out_emitted: false,
        proof_writer_io_error: false,
    };

    let dry_run =
        ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(&replay);

    assert_eq!(
        dry_run.materialization_status,
        LearnedLratMaterializationStatus::FailClosedIncompleteLearnedDependency
    );
    assert_eq!(dry_run.rows.len(), 1);
    assert_eq!(
        dry_run.rows[0].kind,
        LearnedLratReplayRowKind::MaterializerAdd
    );
    assert_eq!(dry_run.rows[0].lrat_line, "9 1 5 0 1 6 3 0\n");
    assert_eq!(dry_run.lrat_fragment, dry_run.rows[0].lrat_line);
    assert!(!dry_run.external_checker_required);
    assert!(!dry_run.external_checker_verified);
    assert_eq!(
        dry_run.main_proof_authority_reason,
        LEARNED_LRAT_AUTHORITY_FAIL_CLOSED
    );
    assert!(!dry_run.authorizes_main_proof_out);

    let envelope = ProofManager::export_fmla_learned_lrat_dry_run_proof_artifact(&dry_run);
    let json =
        ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_to_json_value(&envelope);
    assert_eq!(
        json["rows"][0]["lrat_line"].as_str(),
        Some("9 1 5 0 1 6 3 0\n")
    );
    let parsed_envelope =
        ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_from_json_value(&json)
            .expect("fail-closed materializer fragment envelope should parse");
    let imported = ProofManager::import_fmla_learned_lrat_dry_run_proof_artifact(parsed_envelope)
        .expect("fail-closed materializer fragment should import as diagnostic-only");
    assert_eq!(imported, dry_run);
}

#[test]
fn test_fmla_learned_lrat_main_proof_authority_rejects_fail_closed_retained_rows() {
    let replay = LearnedLratMaterializationReplay {
        checker_visible_id: 10,
        materialization_status:
            LearnedLratMaterializationStatus::FailClosedIncompleteLearnedDependency,
        rows: vec![LearnedLratReplayRow {
            kind: LearnedLratReplayRowKind::MaterializerAdd,
            checker_visible_id: 9,
            clause_lits_dimacs: vec![1, 5],
            checker_visible_lrat_hints: vec![1, 6, 3],
        }],
        proof_out_emitted: false,
        proof_writer_io_error: false,
    };
    let dry_run =
        ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(&replay);
    let proof_out = format!(
        "c checked diagnostic-only fragment\n{}",
        dry_run.lrat_fragment
    );
    let checker_verdict =
        accepted_external_checker_verdict_artifact_for_proof(proof_out.as_bytes());

    let err = ProofManager::validate_fmla_learned_lrat_main_proof_authority(
        &dry_run,
        &checker_verdict,
        proof_out.as_bytes(),
    )
    .expect_err("fail-closed retained rows must not authorize Main proof_out");

    assert_eq!(
        err,
        LearnedLratMainProofAuthorityReject::DryRunNotComplete {
            materialization_status:
                LearnedLratMaterializationStatus::FailClosedIncompleteLearnedDependency
        }
    );
    assert!(!dry_run.authorizes_main_proof_out);
}

#[test]
fn test_fmla_learned_lrat_dry_run_rejects_malformed_fail_closed_materializer_rows() {
    let replay = LearnedLratMaterializationReplay {
        checker_visible_id: 10,
        materialization_status:
            LearnedLratMaterializationStatus::FailClosedIncompleteLearnedDependency,
        rows: vec![
            LearnedLratReplayRow {
                kind: LearnedLratReplayRowKind::MaterializerAdd,
                checker_visible_id: 9,
                clause_lits_dimacs: vec![1, 5],
                checker_visible_lrat_hints: vec![11],
            },
            LearnedLratReplayRow {
                kind: LearnedLratReplayRowKind::MaterializerAdd,
                checker_visible_id: 11,
                clause_lits_dimacs: vec![2, 7],
                checker_visible_lrat_hints: vec![1, 6],
            },
        ],
        proof_out_emitted: false,
        proof_writer_io_error: false,
    };

    let dry_run =
        ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(&replay);

    assert_eq!(
        dry_run.materialization_status,
        LearnedLratMaterializationStatus::FailClosedMalformedReplayRows
    );
    assert!(dry_run.rows.is_empty());
    assert_eq!(dry_run.lrat_fragment, "");
    assert_eq!(
        dry_run.main_proof_authority_reason,
        LEARNED_LRAT_AUTHORITY_FAIL_CLOSED
    );
    assert!(!dry_run.authorizes_main_proof_out);
}

#[test]
fn test_fmla_learned_lrat_dry_run_rejects_malformed_replay_rows() {
    let materializer_row = LearnedLratReplayRow {
        kind: LearnedLratReplayRowKind::MaterializerAdd,
        checker_visible_id: 9,
        clause_lits_dimacs: vec![1, 5],
        checker_visible_lrat_hints: vec![1, 6, 3],
    };
    let learned_row = LearnedLratReplayRow {
        kind: LearnedLratReplayRowKind::LearnedAdd,
        checker_visible_id: 10,
        clause_lits_dimacs: vec![1, -2],
        checker_visible_lrat_hints: vec![6, 9, 1],
    };
    let malformed_cases = [
        (
            "zero row id",
            vec![
                LearnedLratReplayRow {
                    checker_visible_id: 0,
                    ..materializer_row.clone()
                },
                learned_row.clone(),
            ],
        ),
        (
            "learned row before materializer",
            vec![learned_row.clone(), materializer_row.clone()],
        ),
        (
            "future replay dependency",
            vec![
                LearnedLratReplayRow {
                    checker_visible_lrat_hints: vec![10],
                    ..materializer_row.clone()
                },
                learned_row.clone(),
            ],
        ),
        (
            "learned row without materializer dependency",
            vec![
                materializer_row.clone(),
                LearnedLratReplayRow {
                    checker_visible_lrat_hints: vec![6, 1],
                    ..learned_row.clone()
                },
            ],
        ),
        (
            "zero hint",
            vec![
                materializer_row,
                LearnedLratReplayRow {
                    checker_visible_lrat_hints: vec![6, 0, 9, 1],
                    ..learned_row
                },
            ],
        ),
    ];

    for (case_name, rows) in malformed_cases {
        let replay = LearnedLratMaterializationReplay {
            checker_visible_id: 10,
            materialization_status: LearnedLratMaterializationStatus::RetainedDependenciesComplete,
            rows,
            proof_out_emitted: false,
            proof_writer_io_error: false,
        };

        let artifact =
            ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(&replay);
        assert_eq!(
            artifact.materialization_status,
            LearnedLratMaterializationStatus::FailClosedMalformedReplayRows,
            "{case_name} must fail closed"
        );
        assert!(
            artifact.rows.is_empty(),
            "{case_name} must not serialize dry-run rows"
        );
        assert_eq!(artifact.lrat_fragment, "");
        assert!(!artifact.proof_out_emitted);
        assert!(!artifact.proof_writer_io_error);
        assert!(!artifact.external_checker_required);
        assert!(!artifact.external_checker_verified);
        assert_eq!(
            artifact.main_proof_authority_reason,
            LEARNED_LRAT_AUTHORITY_FAIL_CLOSED
        );
        assert!(!artifact.authorizes_main_proof_out);
    }
}

#[test]
fn test_drat_trusted_transform_emits_normally() {
    let output = ProofOutput::drat_text(Vec::new());
    let mut manager = ProofManager::new(output, 2);
    manager.register_original_clause(&[lit(0, true), lit(1, true)]);
    let clause = [lit(0, false), lit(1, false)];
    let added = manager
        .emit_add(&clause, &[], ProofAddKind::TrustedTransform)
        .expect("DRAT add should succeed");
    assert_eq!(added, 0);
    assert_eq!(manager.added_count(), 1);
}

fn manager_with_complementary_unit_origins() -> ProofManager {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 2);
    // Register full original clauses so the LRAT chain checker has
    // clause content for RUP verification (not just IDs).
    manager.register_original_clause(&[lit(0, true)]); // clause 1: (a)
    manager.register_clause_id(1);
    manager.register_original_clause(&[lit(0, false)]); // clause 2: (!a)
    manager.register_clause_id(2);
    manager
}

fn assert_lrat_delete_line(del_line: &str, empty_clause_id: u64) {
    assert!(del_line.contains(" d "));
    assert!(del_line.contains(&format!(" {empty_clause_id} ")));
    assert!(del_line.ends_with(" 0") || del_line.ends_with(" 0 "));
    let parts: Vec<&str> = del_line.split_whitespace().collect();
    assert!(parts.len() >= 4);
    let step_id: u64 = parts[0].parse().expect("step_id should be numeric");
    assert!(step_id > empty_clause_id);
    assert_eq!(parts[1], "d");
    assert_eq!(parts[parts.len() - 1], "0");
}

fn lrat_hint_section(line: &str) -> Vec<&str> {
    let parts: Vec<&str> = line.split_whitespace().collect();
    let first_zero = parts.iter().position(|&p| p == "0").unwrap();
    parts[first_zero + 1..parts.len() - 1].to_vec()
}

#[test]
fn test_signed_lrat_add_preserves_negative_hint_order() {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 3);
    manager.register_original_clause(&[lit(0, true)]);
    manager.register_clause_id(1);
    manager.register_original_clause(&[lit(1, true)]);
    manager.register_clause_id(2);

    let clause_id = manager
        .emit_add_signed_lrat_hints(&[lit(2, true)], &[-1, -2], ProofAddKind::Derived)
        .expect("signed LRAT add should write");
    assert_eq!(clause_id, 3);
    assert!(!manager.has_io_error());

    let text =
        String::from_utf8(manager.into_output().into_vec().expect("flush ok")).expect("UTF-8");
    let line = text.lines().next().expect("one signed LRAT line");
    assert_eq!(
        lrat_hint_section(line),
        vec!["-1", "-2"],
        "signed LRAT output must preserve negative hints exactly: {text}"
    );
}

#[test]
fn test_signed_lrat_binary_add_encodes_negative_hints() {
    let output = ProofOutput::lrat_binary(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 3);
    manager.register_original_clause(&[lit(0, true)]);
    manager.register_clause_id(1);
    manager.register_original_clause(&[lit(1, true)]);
    manager.register_clause_id(2);

    let clause_id = manager
        .emit_add_signed_lrat_hints(&[lit(2, true)], &[-1, 2], ProofAddKind::Derived)
        .expect("signed binary LRAT add should write");
    assert_eq!(clause_id, 3);

    let bytes = manager.into_output().into_vec().expect("flush ok");
    let steps = ay_lrat_check::lrat_parser::parse_binary_lrat(&bytes)
        .expect("binary LRAT with signed hints should parse");
    assert_eq!(steps.len(), 1);
    match &steps[0] {
        ay_lrat_check::lrat_parser::LratStep::Add { id, hints, .. } => {
            assert_eq!(*id, 3);
            assert_eq!(hints, &vec![-1, 2]);
        }
        other => panic!("expected signed add step, got {other:?}"),
    }
}

#[test]
fn test_signed_lrat_preflight_validates_groups_and_references() {
    let output = ProofOutput::lrat_text(Vec::new(), 1);
    let mut manager = ProofManager::new(output, 2);
    manager.register_original_clause(&[lit(0, true)]);
    manager.register_clause_id(1);
    let clause = [lit(1, true)];

    assert_eq!(
        manager.preflight_forward_lrat_add_signed_with_planned_ids(
            &clause,
            &[-1, 1],
            ProofAddKind::Derived,
            &[],
        ),
        Ok(()),
        "a RAT witness ID may also occur in that group's RUP chain"
    );
    assert_eq!(
        manager.preflight_forward_lrat_add_signed_with_planned_ids(
            &clause,
            &[-1, 1, 1],
            ProofAddKind::Derived,
            &[],
        ),
        Err(super::PlannedForwardAddReject::DuplicateHint),
        "positive hints remain unique within one RAT witness group"
    );
    assert_eq!(
        manager.preflight_forward_lrat_add_signed_with_planned_ids(
            &clause,
            &[-2],
            ProofAddKind::Derived,
            &[],
        ),
        Err(super::PlannedForwardAddReject::UnknownHint),
        "signed preflight rejects unknown non-planned IDs"
    );
    assert_eq!(
        manager.preflight_forward_lrat_add_signed_with_planned_ids(
            &clause,
            &[-2],
            ProofAddKind::Derived,
            &[2],
        ),
        Ok(()),
        "signed preflight accepts planned checker-visible IDs"
    );
}

fn dimacs_text(num_vars: usize, clauses: &[Vec<Literal>]) -> String {
    let mut out = format!("p cnf {num_vars} {}\n", clauses.len());
    for clause in clauses {
        for &lit in clause {
            let var = lit.variable().index() as i32 + 1;
            let dimacs_lit = if lit.is_positive() { var } else { -var };
            out.push_str(&format!("{dimacs_lit} "));
        }
        out.push_str("0\n");
    }
    out
}

fn assert_lrat_add_steps_verify(num_vars: usize, clauses: &[Vec<Literal>], proof: &str) {
    let dimacs = dimacs_text(num_vars, clauses);
    let cnf = ay_lrat_check::dimacs::parse_cnf_with_ids(dimacs.as_bytes())
        .expect("test DIMACS must parse");
    let steps =
        ay_lrat_check::lrat_parser::parse_text_lrat(proof).expect("emitted LRAT must parse");
    let mut checker = ay_lrat_check::checker::LratChecker::new(cnf.num_vars);
    for (id, clause) in &cnf.clauses {
        assert!(checker.add_original(*id, clause), "original {id}");
    }
    for step in steps {
        match step {
            ay_lrat_check::lrat_parser::LratStep::Add { id, clause, hints } => assert!(
                checker.add_derived(id, &clause, &hints),
                "derived LRAT add {id} must verify: {}",
                checker.stats_summary()
            ),
            ay_lrat_check::lrat_parser::LratStep::Delete { ids } => {
                for id in ids {
                    assert!(checker.delete(id), "delete {id}");
                }
            }
        }
    }
}

#[test]
fn hidden_trusted_transform_never_becomes_a_standalone_lrat_axiom() {
    let originals = vec![vec![lit(0, true)], vec![lit(0, false)]];
    let output = ProofOutput::lrat_text(Vec::new(), originals.len() as u64);
    let mut manager = ProofManager::new(output, 2);
    for (index, clause) in originals.iter().enumerate() {
        manager.register_original_clause(clause);
        manager.register_clause_id(index as u64 + 1);
    }

    let hidden_id = manager
        .emit_add(
            &[lit(0, true), lit(1, true)],
            &[],
            ProofAddKind::TrustedTransform,
        )
        .expect("trusted transform is hidden without an I/O failure");
    assert_eq!(hidden_id, 3);
    let empty_id = manager
        .emit_add(&[], &[1, 2], ProofAddKind::Derived)
        .expect("independent empty-clause chain emits");
    assert_eq!(empty_id, 4);
    assert!(manager.has_lrat_authority_fail_closed());

    let proof = String::from_utf8(
        manager
            .into_output()
            .into_vec()
            .expect("proof output remains readable"),
    )
    .expect("text LRAT is UTF-8");
    assert_eq!(
        proof.lines().count(),
        1,
        "hidden transform has no LRAT line"
    );
    assert_lrat_add_steps_verify(2, &originals, &proof);
}

fn implication_chain_clauses(len: usize) -> Vec<Vec<Literal>> {
    assert!(len >= 2);
    let mut clauses = Vec::with_capacity(len);
    clauses.push(vec![lit(0, true)]);
    for var in 1..len {
        clauses.push(vec![lit((var - 1) as u32, false), lit(var as u32, true)]);
    }
    clauses
}

#[test]
fn test_emit_delete_empty_clause_produces_valid_lrat_deletion() {
    let mut manager = manager_with_complementary_unit_origins();
    let empty_clause_id = manager
        .emit_add(&[], &[1, 2], ProofAddKind::Derived)
        .expect("empty clause derivation should succeed");
    assert_eq!(empty_clause_id, 3);
    manager
        .emit_delete(&[], empty_clause_id)
        .expect("empty clause deletion should succeed");

    // The deleted ID should be removed from the known set (always-on #5005).
    assert!(
        !manager.known_lrat_ids.contains(empty_clause_id),
        "deleted empty-clause ID must be removed from known set"
    );

    // Extract the LRAT text output and verify format.
    let output = manager.into_output();
    let text = String::from_utf8(output.into_vec().expect("flush ok"))
        .expect("LRAT output should be valid UTF-8");
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.len(), 2);
    assert!(lines[0].starts_with("3 "));
    assert_lrat_delete_line(lines[1], empty_clause_id);
}

#[test]
#[cfg(debug_assertions)]
fn test_emit_add_rejects_empty_axiom_clause() {
    let output = ProofOutput::drat_text(Vec::new());
    let mut manager = ProofManager::new(output, 1);
    let bad = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = manager.emit_add(&[], &[], ProofAddKind::Axiom);
    }));
    assert!(bad.is_err(), "expected empty-axiom assertion");
}

#[test]
fn test_verify_unsat_chain_passes_after_valid_proof() {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 2);

    // Register originals: (a) and (!a).
    manager.register_original_clause(&[lit(0, true)]);
    manager.register_clause_id(1);
    manager.register_original_clause(&[lit(0, false)]);
    manager.register_clause_id(2);

    // Derive empty clause with hints [1, 2].
    let _ = manager
        .emit_add(&[], &[1, 2], ProofAddKind::Derived)
        .expect("empty clause derivation should succeed");

    // verify_unsat_chain should pass — IDs are tracked and non-empty.
    manager.verify_unsat_chain();
}

#[test]
fn test_last_add_tracks_scalar_metadata() {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 2);

    manager.register_original_clause(&[lit(0, true)]);
    manager.register_clause_id(1);
    manager.register_original_clause(&[lit(0, false)]);
    manager.register_clause_id(2);

    let non_empty_id = manager
        .emit_add(&[lit(0, true)], &[1], ProofAddKind::Derived)
        .expect("non-empty derivation should succeed");
    let last = manager.last_add.expect("last add should be tracked");
    assert_eq!(last.id, non_empty_id);
    assert_eq!(last.len, 1);
    assert!(!last.is_empty);

    let empty_id = manager
        .emit_add(&[], &[1, 2], ProofAddKind::Derived)
        .expect("empty clause derivation should succeed");
    let last = manager.last_add.expect("last add should be tracked");
    assert_eq!(last.id, empty_id);
    assert_eq!(last.len, 0);
    assert!(last.is_empty);
    manager.verify_unsat_chain();
}

#[test]
fn test_verify_unsat_chain_skipped_for_drat_mode() {
    let output = ProofOutput::drat_text(Vec::new());
    let manager = ProofManager::new(output, 1);
    // Should not panic — DRAT mode skips LRAT chain checks.
    manager.verify_unsat_chain();
}

#[test]
fn test_verify_unsat_chain_skipped_when_theory_blocked() {
    let output = ProofOutput::lrat_text(Vec::new(), 0);
    let mut manager = ProofManager::new(output, 1);
    manager.block_lrat_for_theory_lemmas();
    // Should not panic — theory-blocked proofs skip LRAT checks.
    manager.verify_unsat_chain();
}

#[test]
#[cfg(debug_assertions)]
fn test_lrat_chain_verifier_receives_deduped_hints() {
    // Verify that the online LratChecker receives deduped hints, matching
    // what goes to the LRAT file and standalone ay-lrat-check binary.
    // Duplicate hints are semantically harmless for RUP (SatisfiedUnit
    // no-op) but the checker should see the same chain as external tools.
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 3);

    // Register (a ∨ b) and (¬a ∨ b).
    manager.register_original_clause(&[lit(0, true), lit(1, true)]);
    manager.register_clause_id(1);
    manager.register_original_clause(&[lit(0, false), lit(1, true)]);
    manager.register_clause_id(2);

    // Derive (b) with duplicate hints [1, 2, 1]. The dedup at the output
    // boundary removes the duplicate, so both the file and online checker
    // see [1, 2]. This must not panic — the deduped chain is valid.
    let clause_id = manager
        .emit_add(&[lit(1, true)], &[1, 2, 1], ProofAddKind::Derived)
        .expect("deduped hints should produce valid chain");
    assert!(clause_id > 0);
    assert_eq!(manager.lrat_failures(), 0);

    // Verify the LRAT file also received deduped hints.
    let text =
        String::from_utf8(manager.into_output().into_vec().expect("flush ok")).expect("UTF-8");
    let add_line = text.lines().next().expect("at least one line");
    // Format: "3 1 0 1 2 0" — clause_id=3, lits=[1], hints=[1,2].
    // NOT "3 1 0 1 2 1 0" (with duplicate hint 1).
    let parts: Vec<&str> = add_line.split_whitespace().collect();
    // Find the hint section (after the second "0").
    let first_zero = parts.iter().position(|&p| p == "0").unwrap();
    let hints_section = &parts[first_zero + 1..parts.len() - 1];
    assert_eq!(
        hints_section,
        &["1", "2"],
        "LRAT file should have deduped hints [1, 2], not [1, 2, 1]"
    );
}

#[test]
fn test_lrat_file_hint_filtering_reuses_scratch_for_large_chains() {
    let output = ProofOutput::lrat_text(Vec::new(), 9);
    let mut manager = ProofManager::new(output, 2);

    for id in 1..=9 {
        manager.register_original_clause(&[lit(0, true)]);
        manager.register_clause_id(id);
    }

    manager.file_hints_buf = Vec::with_capacity(16);
    manager.file_hints_buf.push(777);
    manager.file_hints_seen.insert(777);
    let initial_hint_capacity = manager.file_hints_buf.capacity();

    let clause_id = manager
        .emit_add(
            &[lit(0, true)],
            &[1, 2, 3, 4, 5, 6, 7, 8, 9, 2, 1],
            ProofAddKind::Derived,
        )
        .expect("large file hint chain should be filtered and emitted");
    assert_eq!(clause_id, 10);
    assert!(manager.file_hints_buf.is_empty());
    assert!(manager.file_hints_buf.capacity() >= initial_hint_capacity);
    assert!(manager.file_hints_seen.is_empty());

    let text =
        String::from_utf8(manager.into_output().into_vec().expect("flush ok")).expect("UTF-8");
    let add_line = text.lines().next().expect("at least one LRAT add line");
    let parts: Vec<&str> = add_line.split_whitespace().collect();
    let first_zero = parts.iter().position(|&p| p == "0").unwrap();
    let hints_section = &parts[first_zero + 1..parts.len() - 1];
    assert_eq!(
        hints_section,
        &["1", "2", "3", "4", "5", "6", "7", "8", "9"],
        "large-chain file filtering must preserve first-occurrence hint order"
    );
}

#[test]
fn test_emit_add_rejects_trusted_hints_for_derived_lrat() {
    let output = ProofOutput::lrat_text(Vec::new(), 1);
    let mut manager = ProofManager::new(output, 2);
    manager.register_original_clause(&[lit(0, true)]);
    manager.register_clause_id(1);

    let trusted_id = manager
        .emit_add(&[lit(1, true)], &[], ProofAddKind::TrustedTransform)
        .expect("trusted unit should reserve an LRAT ID");
    assert_eq!(trusted_id, 2);

    let derived_id = manager
        .emit_add(
            &[lit(0, true), lit(1, true)],
            &[1, trusted_id],
            ProofAddKind::Derived,
        )
        .expect("structural failure is reported through the proof-error latch");
    assert_eq!(derived_id, 0);
    assert!(manager.has_io_error());

    let text =
        String::from_utf8(manager.into_output().into_vec().expect("flush ok")).expect("UTF-8");
    let lines: Vec<&str> = text.lines().collect();
    assert!(
        lines.is_empty(),
        "trusted transform unit reserves an ID without a file line, and rejected derived add must not write one"
    );
}

#[test]
fn test_emit_add_rejects_deleted_hints_for_derived_lrat() {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 2);
    manager.register_original_clause(&[lit(0, true)]);
    manager.register_clause_id(1);
    manager.register_original_clause(&[lit(1, true)]);
    manager.register_clause_id(2);

    manager
        .emit_delete(&[lit(1, true)], 2)
        .expect("delete should succeed");

    let derived_id = manager
        .emit_add(&[lit(0, true)], &[1, 2], ProofAddKind::Derived)
        .expect("structural failure is reported through the proof-error latch");
    assert_eq!(derived_id, 0);
    assert!(manager.has_io_error());

    let text =
        String::from_utf8(manager.into_output().into_vec().expect("flush ok")).expect("UTF-8");
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.len(), 1);
    assert!(lines[0].contains(" d "));
}

// --- #8603: Memory cleanup tests ---

#[test]
fn test_clear_backward_reserved_ids_releases_memory() {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 2);

    // Register originals so the ID space is populated.
    manager.register_original_clause(&[lit(0, true)]);
    manager.register_clause_id(1);

    // Reserve IDs for backward reconstruction.
    let id1 = manager.reserve_lrat_id_for_backward();
    let id2 = manager.reserve_lrat_id_for_backward();
    assert_ne!(id1, 0);
    assert_ne!(id2, 0);
    assert!(manager.backward_reserved_ids.contains(id1));
    assert!(manager.backward_reserved_ids.contains(id2));

    // Clear backward reserved IDs (simulating post-UNSAT finalization).
    manager.clear_backward_reserved_ids();

    assert!(
        manager.backward_reserved_ids.is_empty(),
        "backward_reserved_ids should be empty after clear"
    );
    assert_eq!(
        manager.backward_reserved_ids.capacity(),
        0,
        "backward_reserved_ids should have 0 capacity after clear_and_shrink()"
    );
}

#[test]
fn test_shrink_known_ids_after_batch_delete() {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 4);

    // Register a batch of originals.
    for i in 1..=100u64 {
        manager.register_original_clause(&[lit(0, true)]);
        manager.register_clause_id(i);
    }
    assert_eq!(manager.known_lrat_ids.len(), 100);
    let cap_before = manager.known_lrat_ids.capacity();
    assert!(cap_before >= 100);

    // Delete most of them (the low end of the ID range).
    for i in 1..=90u64 {
        manager
            .emit_delete(&[lit(0, true)], i)
            .expect("delete should succeed");
    }
    assert_eq!(manager.known_lrat_ids.len(), 10);
    // Capacity should still span the full ID range (bitmap doesn't auto-shrink).
    assert!(
        manager.known_lrat_ids.capacity() >= 100,
        "bitmap capacity should still span the full ID range"
    );

    // Shrink releases excess capacity by advancing low_water past the
    // deleted prefix and truncating trailing zero bits.
    manager.shrink_known_ids();
    let cap_after = manager.known_lrat_ids.capacity();
    assert!(
        cap_after <= cap_before,
        "capacity should not grow from shrink_to_fit ({cap_before} -> {cap_after})"
    );
    assert!(
        cap_after < 100,
        "after low_water advance, capacity should be well below the full ID range \
         (got {cap_after})"
    );
    // The logical contents are unchanged.
    assert_eq!(manager.known_lrat_ids.len(), 10);
    for i in 91..=100u64 {
        assert!(
            manager.known_lrat_ids.contains(i),
            "ID {i} should still be known"
        );
    }
    // And the deleted IDs remain absent.
    for i in 1..=90u64 {
        assert!(
            !manager.known_lrat_ids.contains(i),
            "ID {i} should remain absent after shrink"
        );
    }
}

#[test]
fn test_shrink_known_ids_after_reduction_is_pressure_gated() {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 4);

    for i in 1..=100u64 {
        manager.register_original_clause(&[lit(0, true)]);
        manager.register_clause_id(i);
    }
    for i in 1..=90u64 {
        manager
            .emit_delete(&[lit(0, true)], i)
            .expect("delete should succeed");
    }

    let cap_before = manager.known_lrat_ids.capacity();
    assert!(
        cap_before >= 100,
        "fixture should leave over-provisioned known-id bitmap"
    );
    assert_eq!(manager.known_lrat_ids_deleted_since_shrink, 90);

    manager.shrink_known_ids_after_reduction(false);
    assert_eq!(
        manager.known_lrat_ids.capacity(),
        cap_before,
        "ordinary reductions must not rebuild live-ID storage"
    );
    assert_eq!(
        manager.known_lrat_ids_deleted_since_shrink, 90,
        "skipped shrink must retain deletion pressure for a later GC point"
    );

    manager.shrink_known_ids_after_reduction(true);
    assert!(
        manager.known_lrat_ids.capacity() < cap_before,
        "pressure-gated shrink should reclaim known-id bitmap capacity"
    );
    assert_eq!(
        manager.known_lrat_ids_deleted_since_shrink, 0,
        "successful shrink resets deletion pressure"
    );
    for i in 91..=100u64 {
        assert!(
            manager.known_lrat_ids.contains(i),
            "ID {i} should still be known"
        );
    }
}

#[test]
fn test_shrink_known_ids_after_reduction_noops_without_deletions() {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 4);

    for i in 1..=100u64 {
        manager.register_original_clause(&[lit(0, true)]);
        manager.register_clause_id(i);
    }

    let cap_before = manager.known_lrat_ids.capacity();
    manager.shrink_known_ids_after_reduction(true);
    assert_eq!(
        manager.known_lrat_ids.capacity(),
        cap_before,
        "pressure without LRAT ID deletions must not rebuild live-ID storage"
    );
}

#[test]
#[cfg(debug_assertions)]
fn test_cleanup_debug_tracking_caps_deleted_ids() {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 4);

    // Register and delete enough clauses to exceed the threshold.
    let threshold = 50;
    for i in 1..=(threshold as u64 + 10) {
        manager.register_original_clause(&[lit(0, true)]);
        manager.register_clause_id(i);
    }
    for i in 1..=(threshold as u64 + 10) {
        manager
            .emit_delete(&[lit(0, true)], i)
            .expect("delete should succeed");
    }
    assert!(
        manager.deleted_lrat_ids.len() > threshold,
        "deleted_lrat_ids should exceed threshold"
    );

    // Cleanup should clear the set since it exceeds threshold.
    manager.cleanup_debug_tracking(threshold);
    assert!(
        manager.deleted_lrat_ids.is_empty(),
        "deleted_lrat_ids should be cleared after exceeding threshold"
    );
    assert_eq!(
        manager.deleted_lrat_ids.capacity(),
        0,
        "deleted_lrat_ids should have 0 capacity after shrink_to(0)"
    );
}

#[test]
#[cfg(debug_assertions)]
fn test_cleanup_debug_tracking_noop_below_threshold() {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 4);

    // Register and delete a few clauses (below threshold).
    for i in 1..=5u64 {
        manager.register_original_clause(&[lit(0, true)]);
        manager.register_clause_id(i);
    }
    for i in 1..=5u64 {
        manager
            .emit_delete(&[lit(0, true)], i)
            .expect("delete should succeed");
    }
    let count_before = manager.deleted_lrat_ids.len();
    assert!(count_before > 0);

    // Cleanup with a high threshold should be a no-op.
    manager.cleanup_debug_tracking(1_000_000);
    assert_eq!(
        manager.deleted_lrat_ids.len(),
        count_before,
        "deleted_lrat_ids should be unchanged when below threshold"
    );
}

#[test]
fn test_emit_backward_step_skips_non_reserved_ids() {
    let output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut manager = ProofManager::new(output, 2);

    // Register an original.
    manager.register_original_clause(&[lit(0, true)]);
    manager.register_clause_id(1);

    // Emit a forward-path clause (via emit_add, not reserve_lrat_id_for_backward).
    let forward_id = manager
        .emit_add(&[lit(0, true), lit(1, true)], &[1], ProofAddKind::Derived)
        .expect("emit_add should succeed");
    assert_ne!(forward_id, 0);
    let adds_before = manager.added_count();

    // Backward step for this ID should be skipped (not in backward_reserved_ids).
    manager
        .emit_backward_step(forward_id, &[lit(0, true), lit(1, true)], &[1])
        .expect("backward step should succeed");
    assert_eq!(
        manager.added_count(),
        adds_before,
        "no new addition should be written for forward-emitted clause"
    );
}

#[test]
fn test_emit_backward_empty_hint_step_is_hidden_and_fails_closed() {
    let output = ProofOutput::lrat_text(Vec::new(), 1);
    let mut manager = ProofManager::new(output, 1);
    manager.register_original_clause(&[lit(0, true)]);
    manager.register_clause_id(1);
    let target_id = manager.reserve_lrat_id_for_backward();

    manager
        .emit_backward_step(target_id, &[lit(0, true)], &[])
        .expect("missing hints are a structural failure, not writer I/O");

    assert_eq!(manager.added_count(), 0);
    assert!(manager.backward_reserved_ids.contains(target_id));
    assert!(manager.has_lrat_authority_fail_closed());
    assert!(manager.has_io_error());
    assert!(manager.into_output().into_vec().unwrap().is_empty());
}

#[test]
fn test_emit_backward_step_preserves_reused_rat_helpers_across_groups() {
    // C1=(a), C2=(~a v b), C3=(~a v ~b). Deriving (a) as RAT can use C1
    // as the conflict helper in both witness groups; reuse across groups is
    // valid even though a duplicate within one group is not.
    let originals = vec![
        vec![lit(0, true)],
        vec![lit(0, false), lit(1, true)],
        vec![lit(0, false), lit(1, false)],
    ];
    let output = ProofOutput::lrat_text(Vec::new(), originals.len() as u64);
    let mut manager = ProofManager::new(output, 2);
    for (index, clause) in originals.iter().enumerate() {
        manager.register_original_clause(clause);
        manager.register_clause_id(index as u64 + 1);
    }
    let target_id = manager.reserve_lrat_id_for_backward();

    manager
        .emit_backward_step(target_id, &[lit(0, true)], &[-2, 1, -3, 1])
        .expect("valid signed RAT step should emit");

    assert!(!manager.has_io_error());
    assert!(!manager.backward_reserved_ids.contains(target_id));
    let proof = String::from_utf8(manager.into_output().into_vec().unwrap()).unwrap();
    assert_eq!(proof, "4 1 0 -2 1 -3 1 0\n");
    assert_lrat_add_steps_verify(2, &originals, &proof);
}

#[test]
fn test_delete_of_backward_reserved_clause_is_not_serialized_before_backfill() {
    let originals = vec![vec![lit(0, true)]];
    let output = ProofOutput::lrat_text(Vec::new(), 1);
    let mut manager = ProofManager::new(output, 1);
    manager.register_original_clause(&originals[0]);
    manager.register_clause_id(1);
    let target_id = manager.reserve_lrat_id_for_backward();

    manager
        .emit_delete(&[lit(0, true)], target_id)
        .expect("unwritten deletion is suppressed");
    assert_eq!(manager.deleted_count(), 0);
    assert!(manager.backward_reserved_ids.contains(target_id));

    manager
        .emit_backward_step(target_id, &[lit(0, true)], &[1])
        .expect("reachable historical clause can still be backfilled");
    assert!(manager.is_known_lrat_id(target_id));

    let proof = String::from_utf8(manager.into_output().into_vec().unwrap()).unwrap();
    assert_eq!(proof, "2 1 0 1 0\n");
    assert_lrat_add_steps_verify(1, &originals, &proof);
}

#[test]
fn test_emit_backward_step_rejects_pending_reserved_hints() {
    let output = ProofOutput::lrat_text(Vec::new(), 1);
    let mut manager = ProofManager::new(output, 2);

    manager.register_original_clause(&[lit(0, true)]);
    manager.register_clause_id(1);

    let pending_dep_id = manager.reserve_lrat_id_for_backward();
    let target_id = manager.reserve_lrat_id_for_backward();
    assert_eq!(pending_dep_id, 2);
    assert_eq!(target_id, 3);

    manager
        .emit_backward_step(
            target_id,
            &[lit(1, true)],
            &[1, pending_dep_id as i64, target_id as i64, 1, 0, -7],
        )
        .expect("invalid backward step should fail closed without writer I/O");

    assert!(
        manager.backward_reserved_ids.contains(pending_dep_id),
        "unemitted dependency should remain pending"
    );
    assert!(
        manager.backward_reserved_ids.contains(target_id),
        "suppressed backward ID must remain pending"
    );
    assert!(
        manager.has_io_error(),
        "invalid pending/self/negative backward hints must latch proof structural failure"
    );

    let text =
        String::from_utf8(manager.into_output().into_vec().expect("flush ok")).expect("UTF-8");
    assert!(
        text.is_empty(),
        "a malformed RAT/RUP chain must be suppressed as a whole: {text}"
    );
}

#[test]
fn test_emit_backward_step_allows_emitted_reserved_hints_once() {
    let output = ProofOutput::lrat_text(Vec::new(), 1);
    let mut manager = ProofManager::new(output, 2);

    manager.register_original_clause(&[lit(0, true)]);
    manager.register_clause_id(1);

    let dep_id = manager.reserve_lrat_id_for_backward();
    let target_id = manager.reserve_lrat_id_for_backward();
    assert_eq!(dep_id, 2);
    assert_eq!(target_id, 3);

    manager
        .emit_backward_step(dep_id, &[lit(1, true)], &[1])
        .expect("dependency step should write first");
    assert!(
        !manager.backward_reserved_ids.contains(dep_id),
        "written dependency must become file-visible for later backward steps"
    );

    manager
        .emit_backward_step(
            target_id,
            &[lit(0, true), lit(1, true)],
            &[dep_id as i64, 1],
        )
        .expect("target step should write");
    assert!(
        !manager.has_io_error(),
        "valid emitted backward dependency hints must not latch proof structural failure"
    );

    let text =
        String::from_utf8(manager.into_output().into_vec().expect("flush ok")).expect("UTF-8");
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.len(), 2);
    let dep_id_text = dep_id.to_string();
    assert_eq!(
        lrat_hint_section(lines[1]),
        vec![dep_id_text.as_str(), "1"],
        "previously emitted backward IDs should remain usable: {text}"
    );
}

#[test]
fn test_emit_backward_step_clean_large_hints_avoid_u64_materialization() {
    let hint_count = 12usize;
    let clauses = implication_chain_clauses(hint_count);
    let output = ProofOutput::lrat_text(Vec::new(), clauses.len() as u64);
    let mut manager = ProofManager::new(output, hint_count);

    for (idx, clause) in clauses.iter().enumerate() {
        manager.register_original_clause(clause);
        manager.register_clause_id((idx + 1) as u64);
    }
    assert_eq!(
        manager.file_hints_buf.capacity(),
        0,
        "fixture should start with no retained u64 hint materialization buffer"
    );

    let target_id = manager.reserve_lrat_id_for_backward();
    assert_eq!(target_id, hint_count as u64 + 1);
    let hints: Vec<i64> = (1..=hint_count as i64).collect();
    let target_clause = [lit((hint_count - 1) as u32, true)];

    manager
        .emit_backward_step(target_id, &target_clause, &hints)
        .expect("clean backward LRAT step should write");
    assert!(
        !manager.has_io_error(),
        "clean visible backward hints must not latch structural failure"
    );
    assert_eq!(
        manager.file_hints_buf.capacity(),
        0,
        "clean backward LRAT hints should write directly without Vec<u64> materialization"
    );

    let text =
        String::from_utf8(manager.into_output().into_vec().expect("flush ok")).expect("UTF-8");
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.len(), 1);
    let expected_hint_strings: Vec<String> = (1..=hint_count).map(|id| id.to_string()).collect();
    let expected_hint_refs: Vec<&str> = expected_hint_strings.iter().map(String::as_str).collect();
    assert_eq!(
        lrat_hint_section(lines[0]),
        expected_hint_refs,
        "direct clean backward LRAT output must preserve hint order: {text}"
    );
    assert_lrat_add_steps_verify(hint_count, &clauses, &text);
}

#[test]
fn test_emit_backward_step_large_pending_hint_still_fails_closed() {
    let hint_count = 12usize;
    let clauses = implication_chain_clauses(hint_count);
    let output = ProofOutput::lrat_text(Vec::new(), clauses.len() as u64);
    let mut manager = ProofManager::new(output, hint_count);

    for (idx, clause) in clauses.iter().enumerate() {
        manager.register_original_clause(clause);
        manager.register_clause_id((idx + 1) as u64);
    }

    let pending_id = manager.reserve_lrat_id_for_backward();
    let target_id = manager.reserve_lrat_id_for_backward();
    let mut hints: Vec<i64> = (1..=hint_count as i64).collect();
    hints.push(pending_id as i64);

    manager
        .emit_backward_step(target_id, &[lit((hint_count - 1) as u32, true)], &hints)
        .expect("structural failure is latched, not surfaced as writer I/O");

    assert!(
        manager.has_io_error(),
        "pending backward hint must latch fail-closed structural proof failure"
    );
    assert!(
        manager.backward_reserved_ids.contains(pending_id),
        "invalid pending dependency should remain pending"
    );
    assert!(
        manager.backward_reserved_ids.contains(target_id),
        "invalid target step must remain pending"
    );

    let text =
        String::from_utf8(manager.into_output().into_vec().expect("flush ok")).expect("UTF-8");
    assert!(
        text.is_empty(),
        "invalid pending hint must suppress the entire LRAT step: {text}"
    );
}
