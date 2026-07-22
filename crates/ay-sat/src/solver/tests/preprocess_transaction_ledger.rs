// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Execution-path preprocessing transaction ledger tests.

use super::*;
use crate::decompose::{
    DecomposeProofEmitContext, DecomposeProofEmitRecord, DecomposeProofOutRecordKind,
    FmlaGuardedEquivOverlayLratBinaryRow, FmlaGuardedEquivOverlayLratSidecar,
    FmlaGuardedEquivSupportCoverLratSidecar,
};
use crate::fmla_runtime_ledger::{
    materialize_fmla_guarded_equiv_lrat_records, materialize_main_lrat_rewrite_records,
    materialize_source_bound_multiplier_lrat_records, replay_fmla_postcheck_admission,
    source_bound_multiplier_lrat_replay_test_proof_records_from_sidecars,
    source_bound_multiplier_lrat_sidecars_from_original_source_plan_rows,
    source_bound_multiplier_lrat_sidecars_from_plan_rows,
    validate_fmla_learned_lrat_main_proof_authority_from_json_postcheck_replay,
    validate_source_bound_multiplier_original_source_bindings,
    ExternalProofCheckerVerdictArtifactRef, FmlaLearnedLratMainProofAuthorityReplayRecord,
    FmlaPostCheckAdmissionReplayInput, FmlaPostCheckAdmissionReplayRecord,
    FmlaPostCheckAdmissionReplayReject, MainProofRewriteLedgerMaterializerConfig,
    MainProofRewriteLedgerMaterializerReject, SourceBoundMultiplierLratPlanAdapterReject,
    SourceBoundMultiplierLratPlanBridgeReject, SourceBoundMultiplierLratPlanRow,
    SourceBoundMultiplierLratRowKind, SourceBoundMultiplierLratSidecarRow,
    SourceBoundMultiplierOriginalSourceBindingReject,
    FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT,
    FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_SCHEMA,
    FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_SCHEMA,
};
use crate::preprocess_transaction::{
    ModelReconstructionWitnessStatus, PreprocessPass, PreprocessTransactionCommitError,
    PreprocessTransactionDraft, PreprocessTransactionLedger, PreprocessTransactionOutcome,
    ProofObligationStatus, RouteAdmissionPacket, RouteAdmissionPacketKind,
    RouteAdmissionPacketStatus,
};
use crate::proof_manager::{
    LearnedLratMaterializationReplay, LearnedLratMaterializationStatus, LearnedLratReplayRow,
    LearnedLratReplayRowKind, ProofManager,
};
use crate::ProofOutput;
use sha2::{Digest, Sha256};

const FMLA_RETAINED_PROOF_OUT_PATH: &str = "runs/fmla/proof/proof.out";

fn add_fmla_like_chain(solver: &mut Solver) -> (Literal, Literal, Literal, Literal) {
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let y = Literal::positive(Variable(3));

    solver.add_clause(vec![x0.negated(), x1]);
    solver.add_clause(vec![x1.negated(), x2]);
    solver.add_clause(vec![x2.negated(), x0]);
    solver.add_clause(vec![x2, y]);
    solver.initialize_watches();
    (x0, x1, x2, y)
}

fn retained_decompose_lrat_sidecar_fixture() -> (
    Vec<crate::decompose::DecomposeLratDryRunSidecar>,
    Vec<DecomposeProofEmitContext>,
) {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 4);
    let mut solver = Solver::with_proof_output(4, proof);
    add_fmla_like_chain(&mut solver);

    solver.decompose();

    assert_eq!(solver.decompose_lrat_dry_run_sidecars().len(), 1);
    let sidecars = solver.decompose_lrat_dry_run_sidecars().to_vec();
    let contexts = solver
        .inproc
        .decompose_engine
        .lrat_proof_emit_contexts()
        .to_vec();
    assert_eq!(contexts.len(), sidecars.len());
    (sidecars, contexts)
}

fn proof_record(
    context: &DecomposeProofEmitContext,
    proof_field: &'static str,
    proof_out_record_kind: DecomposeProofOutRecordKind,
    checker_visible_id: u64,
    delete_source_id: Option<u64>,
    clause_lits_dimacs: Vec<i64>,
    lrat_hints: Vec<u64>,
) -> DecomposeProofEmitRecord {
    DecomposeProofEmitRecord {
        context: context.clone(),
        proof_field,
        proof_out_record_kind,
        checker_visible_id,
        delete_source_id,
        clause_lits_dimacs,
        lrat_hints,
        proof_manager_mode: "lrat",
        solver_runtime_emitted: true,
        proof_writer_io_error: false,
        external_checker_verified: false,
    }
}

fn complete_proof_records(
    sidecar: &crate::decompose::DecomposeLratDryRunSidecar,
    context: &DecomposeProofEmitContext,
) -> Vec<DecomposeProofEmitRecord> {
    let mut records = Vec::new();
    for step in &sidecar.equivalence_steps {
        records.push(proof_record(
            context,
            "derived_clause_proof_steps",
            DecomposeProofOutRecordKind::Add,
            step.planned_lit_to_repr_add_id,
            None,
            vec![step.representative_lit, -step.original_lit],
            step.lit_to_repr_source_ids.clone(),
        ));
        records.push(proof_record(
            context,
            "derived_clause_proof_steps",
            DecomposeProofOutRecordKind::Add,
            step.planned_repr_to_lit_add_id,
            None,
            vec![step.original_lit, -step.representative_lit],
            step.repr_to_lit_source_ids.clone(),
        ));
    }
    records.push(proof_record(
        context,
        "derived_clause_proof_steps",
        DecomposeProofOutRecordKind::Add,
        sidecar.planned_rewrite_add_id,
        None,
        sidecar.rewritten_clause_lits.clone(),
        sidecar.rewrite_hints.clone(),
    ));
    records.push(proof_record(
        context,
        "deletion_proof_steps",
        DecomposeProofOutRecordKind::Delete,
        sidecar.source_delete_id,
        Some(sidecar.source_delete_id),
        sidecar.source_clause_lits.clone(),
        Vec::new(),
    ));
    records
}

fn accepted_external_checker_verdict_artifact() -> ExternalProofCheckerVerdictArtifactRef {
    let hash = "0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";
    ExternalProofCheckerVerdictArtifactRef {
        schema: FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_SCHEMA.to_string(),
        runtime_field: FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT
            .runtime_field
            .to_string(),
        artifact_path: "runs/fmla/proof/fmla-main-lrat-external-checker-verdict.json".to_string(),
        artifact_sha256: hash.to_string(),
        checker_path: "/opt/satcomp/bin/cake_lpr".to_string(),
        checker_sha256: hash.to_string(),
        checker_command:
            "/opt/satcomp/bin/cake_lpr benchmarks/FmlaEquivChain_4_6_6.sanitized.cnf runs/fmla/proof/proof.out"
                .to_string(),
        checker_argv: vec![
            "/opt/satcomp/bin/cake_lpr".to_string(),
            "benchmarks/FmlaEquivChain_4_6_6.sanitized.cnf".to_string(),
            "runs/fmla/proof/proof.out".to_string(),
        ],
        checker_exit_code: 0,
        proof_out_path: "runs/fmla/proof/proof.out".to_string(),
        proof_out_sha256: hash.to_string(),
        checked_dimacs_path: "benchmarks/FmlaEquivChain_4_6_6.sanitized.cnf".to_string(),
        checked_dimacs_sha256: hash.to_string(),
        verdict: FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT
            .accepted_verdict
            .to_string(),
    }
}

fn sha256_hex(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    format!("{:x}", hasher.finalize())
}

fn source_bound_dimacs_lits(lits: &[i64]) -> Vec<Literal> {
    lits.iter()
        .map(|&lit| {
            let dimacs_lit = i32::try_from(lit).expect("fixture DIMACS literal fits i32");
            Literal::from_dimacs(dimacs_lit)
        })
        .collect()
}

fn source_bound_multiplier_fixture_proof_manager(
    plan_rows: &[SourceBoundMultiplierLratPlanRow],
) -> ProofManager {
    let first_add_id = plan_rows
        .iter()
        .filter(|row| row.row_kind != SourceBoundMultiplierLratRowKind::SourceDelete)
        .map(|row| row.checker_visible_id)
        .min()
        .expect("fixture must include at least one add row");
    let original_count = first_add_id.saturating_sub(1);
    let max_var = plan_rows
        .iter()
        .flat_map(|row| {
            row.source_clause_lits
                .iter()
                .chain(row.clause_lits_dimacs.iter())
        })
        .map(|lit| lit.unsigned_abs() as usize)
        .max()
        .unwrap_or(1);

    let mut source_by_id = std::collections::BTreeMap::new();
    for row in plan_rows {
        source_by_id
            .entry(row.source_clause_id)
            .or_insert_with(|| row.source_clause_lits.clone());
    }

    let mut manager = ProofManager::new(
        ProofOutput::lrat_text(Vec::<u8>::new(), original_count),
        max_var,
    );
    for clause_id in 1..=original_count {
        let clause_lits = source_by_id
            .get(&clause_id)
            .cloned()
            .unwrap_or_else(|| vec![1]);
        let clause = source_bound_dimacs_lits(&clause_lits);
        manager.register_original_clause(&clause);
        manager.register_clause_id(clause_id);
    }
    manager
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

fn fmla_learned_lrat_dry_run_artifact_json_and_proof_out() -> (serde_json::Value, Vec<u8>) {
    let dry_run = ProofManager::dry_run_fmla_learned_lrat_materialization_fragment_from_replay(
        &fmla_learned_lrat_complete_replay(),
    );
    let proof_out = format!(
        "c same-run proof.out retained by wrapper\n{}",
        dry_run.lrat_fragment
    )
    .into_bytes();
    let envelope = ProofManager::export_fmla_learned_lrat_dry_run_proof_artifact(&dry_run);
    let json =
        ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_to_json_value(&envelope);
    (json, proof_out)
}

fn fmla_learned_lrat_fail_closed_materializer_rows_artifact_json() -> serde_json::Value {
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
    assert_eq!(
        dry_run.rows.len(),
        1,
        "diagnostic materializer rows are retained but must not authorize proof.out"
    );
    assert!(!dry_run.external_checker_required);
    assert!(!dry_run.external_checker_verified);
    assert!(!dry_run.authorizes_main_proof_out);

    let envelope = ProofManager::export_fmla_learned_lrat_dry_run_proof_artifact(&dry_run);
    ProofManager::fmla_learned_lrat_dry_run_proof_artifact_envelope_to_json_value(&envelope)
}

fn accepted_external_checker_verdict_artifact_for_proof(
    proof_out_bytes: &[u8],
) -> ExternalProofCheckerVerdictArtifactRef {
    let mut artifact = accepted_external_checker_verdict_artifact();
    artifact.checker_command = format!(
        "/opt/satcomp/bin/cake_lpr benchmarks/FmlaEquivChain_4_6_6.sanitized.cnf {FMLA_RETAINED_PROOF_OUT_PATH}"
    );
    artifact.checker_argv = vec![
        "/opt/satcomp/bin/cake_lpr".to_string(),
        "benchmarks/FmlaEquivChain_4_6_6.sanitized.cnf".to_string(),
        FMLA_RETAINED_PROOF_OUT_PATH.to_string(),
    ];
    artifact.proof_out_path = FMLA_RETAINED_PROOF_OUT_PATH.to_string();
    artifact.proof_out_sha256 = sha256_hex(proof_out_bytes);
    artifact
}

fn accepted_fmla_postcheck_replay_for_proof_rows(
    proof_out_bytes: &[u8],
    proof_obligation_rows: u64,
) -> FmlaPostCheckAdmissionReplayRecord {
    replay_fmla_postcheck_admission(
        FmlaPostCheckAdmissionReplayInput {
            materializer_attempts: 1,
            materializer_proof_emit_records_seen: proof_obligation_rows,
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
    .expect("valid checker-backed replay fixture should commit")
}

fn assert_learned_lrat_authority_fail_closed(
    replay: &FmlaLearnedLratMainProofAuthorityReplayRecord,
    reason: &str,
) {
    assert_eq!(replay.status, "fail_closed");
    assert_eq!(replay.reason.as_deref(), Some(reason));
    assert_eq!(replay.checker_visible_id, None);
    assert_eq!(replay.proof_out_path, None);
    assert_eq!(replay.proof_out_sha256, None);
    assert!(!replay.external_checker_verified);
    assert!(!replay.proof_out_contains_lrat_fragment);
    assert!(!replay.authorizes_main_proof_out);
}

fn fmla_guarded_equiv_lrat_fixture(
    transaction_id: u64,
) -> (
    Vec<FmlaGuardedEquivOverlayLratSidecar>,
    Vec<FmlaGuardedEquivSupportCoverLratSidecar>,
    Vec<DecomposeProofEmitRecord>,
) {
    let overlay = FmlaGuardedEquivOverlayLratSidecar {
        guard_lit_dimacs: 1,
        lhs_lit_dimacs: 2,
        rhs_lit_dimacs: 3,
        guard_unit_proof_id: 7,
        forward_binary: FmlaGuardedEquivOverlayLratBinaryRow {
            planned_add_id: 10,
            clause_lits_dimacs: vec![-2, 3],
            guarded_ternary_source_id: 4,
            guard_unit_proof_id: 7,
            lrat_hints: vec![4, 7],
        },
        reverse_binary: FmlaGuardedEquivOverlayLratBinaryRow {
            planned_add_id: 11,
            clause_lits_dimacs: vec![2, -3],
            guarded_ternary_source_id: 5,
            guard_unit_proof_id: 7,
            lrat_hints: vec![5, 7],
        },
    };
    let support = FmlaGuardedEquivSupportCoverLratSidecar {
        planned_add_id: 12,
        support_clause_id: 8,
        support_guard_lits_dimacs: vec![1],
        source_lit_dimacs: 2,
        destination_lits_dimacs: vec![3],
        clause_lits_dimacs: vec![2, 3],
        directional_ternary_source_ids: vec![6],
        lrat_hints: vec![6, 8],
    };
    let records = vec![
        proof_record(
            &DecomposeProofEmitContext::from_fmla_guarded_equiv_overlay_binary(
                transaction_id,
                0,
                "forward",
                &overlay.forward_binary,
            ),
            "derived_clause_proof_steps",
            DecomposeProofOutRecordKind::Add,
            overlay.forward_binary.planned_add_id,
            None,
            overlay.forward_binary.clause_lits_dimacs.clone(),
            overlay.forward_binary.lrat_hints.clone(),
        ),
        proof_record(
            &DecomposeProofEmitContext::from_fmla_guarded_equiv_overlay_binary(
                transaction_id,
                0,
                "reverse",
                &overlay.reverse_binary,
            ),
            "derived_clause_proof_steps",
            DecomposeProofOutRecordKind::Add,
            overlay.reverse_binary.planned_add_id,
            None,
            overlay.reverse_binary.clause_lits_dimacs.clone(),
            overlay.reverse_binary.lrat_hints.clone(),
        ),
        proof_record(
            &DecomposeProofEmitContext::from_fmla_guarded_equiv_support_cover(
                transaction_id,
                0,
                &support,
            ),
            "derived_clause_proof_steps",
            DecomposeProofOutRecordKind::Add,
            support.planned_add_id,
            None,
            support.clause_lits_dimacs.clone(),
            support.lrat_hints.clone(),
        ),
    ];

    (vec![overlay], vec![support], records)
}

fn source_bound_multiplier_lrat_plan_rows_fixture() -> Vec<SourceBoundMultiplierLratPlanRow> {
    vec![
        SourceBoundMultiplierLratPlanRow {
            row_kind: SourceBoundMultiplierLratRowKind::StrengtheningAdd,
            source_clause_id: 4,
            source_clause_lits: vec![1, -2],
            checker_visible_id: 20,
            delete_source_id: None,
            clause_lits_dimacs: vec![1, 3],
            lrat_hints: vec![4, 8],
        },
        SourceBoundMultiplierLratPlanRow {
            row_kind: SourceBoundMultiplierLratRowKind::ResolventAdd,
            source_clause_id: 5,
            source_clause_lits: vec![-1, 2],
            checker_visible_id: 21,
            delete_source_id: None,
            clause_lits_dimacs: vec![3, 4],
            lrat_hints: vec![20, 5],
        },
        SourceBoundMultiplierLratPlanRow {
            row_kind: SourceBoundMultiplierLratRowKind::SourceDelete,
            source_clause_id: 4,
            source_clause_lits: vec![1, -2],
            checker_visible_id: 4,
            delete_source_id: Some(4),
            clause_lits_dimacs: vec![1, -2],
            lrat_hints: Vec::new(),
        },
        SourceBoundMultiplierLratPlanRow {
            row_kind: SourceBoundMultiplierLratRowKind::ConservationAdd,
            source_clause_id: 6,
            source_clause_lits: vec![5, -6],
            checker_visible_id: 23,
            delete_source_id: None,
            clause_lits_dimacs: vec![5, 6],
            lrat_hints: vec![20, 21],
        },
        SourceBoundMultiplierLratPlanRow {
            row_kind: SourceBoundMultiplierLratRowKind::EquivalenceAdd,
            source_clause_id: 7,
            source_clause_lits: vec![-7, 8],
            checker_visible_id: 24,
            delete_source_id: None,
            clause_lits_dimacs: vec![-7, 8],
            lrat_hints: vec![6, 23],
        },
        SourceBoundMultiplierLratPlanRow {
            row_kind: SourceBoundMultiplierLratRowKind::ContradictionAdd,
            source_clause_id: 8,
            source_clause_lits: vec![9],
            checker_visible_id: 25,
            delete_source_id: None,
            clause_lits_dimacs: Vec::new(),
            lrat_hints: vec![24, 7],
        },
    ]
}

fn source_bound_multiplier_lrat_fixture(
    transaction_id: u64,
) -> (
    Vec<SourceBoundMultiplierLratSidecarRow>,
    Vec<DecomposeProofEmitRecord>,
) {
    let plan_rows = source_bound_multiplier_lrat_plan_rows_fixture();
    let original_sources = source_bound_multiplier_original_source_fixture();
    let adapted = source_bound_multiplier_lrat_sidecars_from_original_source_plan_rows(
        &plan_rows,
        original_sources.iter().map(Vec::as_slice),
    )
    .expect("source-bound BVE/multiplier plan rows must bind original DIMACS sources");
    assert_eq!(adapted.source_binding_stats.rows_checked, 6);
    let rows = adapted.sidecars;
    let mut proof_manager = source_bound_multiplier_fixture_proof_manager(&plan_rows);
    let records = source_bound_multiplier_lrat_replay_test_proof_records_from_sidecars(
        &mut proof_manager,
        transaction_id,
        &rows,
    )
    .expect("source-bound rows must replay through the fixture proof manager");

    (rows, records)
}

fn source_bound_multiplier_original_source_fixture() -> Vec<Vec<Literal>> {
    vec![
        vec![Literal::positive(Variable(0))],
        vec![Literal::positive(Variable(0))],
        vec![Literal::positive(Variable(0))],
        source_bound_dimacs_lits(&[1, -2]),
        source_bound_dimacs_lits(&[-1, 2]),
        source_bound_dimacs_lits(&[5, -6]),
        source_bound_dimacs_lits(&[-7, 8]),
        source_bound_dimacs_lits(&[9]),
    ]
}

fn fmla_postcheck_replay_input() -> FmlaPostCheckAdmissionReplayInput {
    FmlaPostCheckAdmissionReplayInput {
        materializer_attempts: 1,
        materializer_proof_emit_records_seen: 3,
        materializer_records: 3,
        materializer_fail_closed: 1,
        materializer_missing_runtime_records: 0,
        preprocess_tx_fail_closed: 1,
        preprocess_tx_committed: 0,
    }
}

#[test]
fn test_preprocess_transaction_ledger_records_decompose_commit() {
    let mut solver = Solver::new(4);
    let (x0, _x1, x2, y) = add_fmla_like_chain(&mut solver);
    assert!(
        solver.process_initial_clauses().is_none(),
        "fixture should not have an initial conflict"
    );
    let epoch_before = solver.cold.clause_db_changes;

    solver.decompose();

    let stats = solver.preprocessing_transaction_stats();
    assert_eq!(stats.started, 1);
    assert_eq!(stats.committed, 1);
    assert_eq!(stats.fail_closed, 0);
    assert_eq!(stats.proof_obligation_not_required, 1);
    assert_eq!(stats.reconstruction_witness_present, 1);
    assert_eq!(stats.reconstruction_witness_not_applicable, 0);
    assert!(stats.touched_variables_total >= 3);
    assert!(stats.eliminated_variables_total >= 1);
    assert!(stats.planned_substitutions_total >= 1);
    assert_eq!(stats.retained_completed, 1);

    let record = solver
        .inproc
        .preprocess_transactions
        .last_completed()
        .expect("decompose commit transaction must be retained");
    assert_eq!(record.mutation_epoch, epoch_before);
    assert_eq!(record.pass_name, PreprocessPass::Decompose);
    assert_eq!(record.outcome, PreprocessTransactionOutcome::Committed);
    assert_eq!(
        record.model_reconstruction_witness,
        ModelReconstructionWitnessStatus::Present
    );
    assert!(record.touched_variables.contains(&x2.variable().index()));
    assert!(record.touched_variables.contains(&y.variable().index()));
    assert!(record.eliminated_variables.contains(&x2.variable().index()));
    assert!(record.planned_substitutions.iter().any(|subst| {
        subst.variable == x2.variable().index()
            && subst.representative_variable == x0.variable().index()
    }));
}

#[test]
fn test_preprocess_transaction_ledger_records_lrat_decompose_fail_closed() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 4);
    let mut solver = Solver::with_proof_output(4, proof);
    let (x0, _x1, x2, y) = add_fmla_like_chain(&mut solver);

    assert!(solver.cold.lrat_enabled, "fixture must exercise LRAT clamp");
    assert!(
        solver.arena.indices().any(|idx| {
            solver.arena.is_active(idx) && {
                let lits = solver.arena.literals(idx);
                lits.contains(&x2) && lits.contains(&y)
            }
        }),
        "fixture should contain the pre-rewrite target clause"
    );

    solver.decompose();

    let stats = solver.preprocessing_transaction_stats();
    assert_eq!(stats.started, 1);
    assert_eq!(stats.committed, 0);
    assert_eq!(stats.fail_closed, 1);
    assert_eq!(stats.proof_obligation_satisfied, 1);
    assert_eq!(stats.reconstruction_witness_not_applicable, 1);
    assert_eq!(stats.reconstruction_witness_present, 0);
    assert_eq!(stats.fail_closed_decompose_lrat_clamped_after_dry_run, 1);
    assert!(stats.eliminated_variables_total >= 1);
    assert!(stats.planned_substitutions_total >= 1);

    let record = solver
        .inproc
        .preprocess_transactions
        .last_completed()
        .expect("LRAT fail-closed transaction must be retained");
    assert_eq!(record.pass_name, PreprocessPass::Decompose);
    assert_eq!(record.outcome, PreprocessTransactionOutcome::FailClosed);
    assert_eq!(record.proof_obligation, ProofObligationStatus::Satisfied);
    assert_eq!(
        record.model_reconstruction_witness,
        ModelReconstructionWitnessStatus::NotApplicable
    );
    assert!(record
        .fail_closed_reason
        .as_deref()
        .unwrap_or_default()
        .contains("clamped"));
    assert!(record.planned_substitutions.iter().any(|subst| {
        subst.variable == x2.variable().index()
            && subst.representative_variable == x0.variable().index()
    }));
    assert!(record.eliminated_variables.contains(&x2.variable().index()));

    assert!(
        solver.arena.indices().any(|idx| {
            solver.arena.is_active(idx) && {
                let lits = solver.arena.literals(idx);
                lits.contains(&x2) && lits.contains(&y)
            }
        }),
        "fail-closed LRAT transaction must leave the original target active"
    );
    assert!(
        !solver.arena.indices().any(|idx| {
            solver.arena.is_active(idx) && {
                let lits = solver.arena.literals(idx);
                lits.contains(&x0) && lits.contains(&y)
            }
        }),
        "fail-closed LRAT transaction must not install the rewritten target"
    );
}

#[test]
fn test_fmla_main_lrat_rewrite_materializer_is_default_off() {
    let (sidecars, contexts) = retained_decompose_lrat_sidecar_fixture();
    let records = complete_proof_records(&sidecars[0], &contexts[0]);

    let materialized = materialize_main_lrat_rewrite_records(
        MainProofRewriteLedgerMaterializerConfig::default(),
        &sidecars,
        &contexts,
        &records,
    )
    .expect("disabled materializer must stay inert");

    assert!(materialized.records.is_empty());
    assert!(!materialized.stats.enabled);
    assert_eq!(materialized.stats.sidecar_rows_seen, 1);
    assert_eq!(materialized.stats.records_materialized, 0);
    assert!(!materialized.stats.fail_closed);
}

#[test]
fn test_fmla_guarded_equiv_lrat_materializer_is_default_off() {
    let transaction_id = 77;
    let (overlay_sidecars, support_sidecars, records) =
        fmla_guarded_equiv_lrat_fixture(transaction_id);

    let stats = materialize_fmla_guarded_equiv_lrat_records(
        MainProofRewriteLedgerMaterializerConfig::default(),
        transaction_id,
        &overlay_sidecars,
        &support_sidecars,
        &records,
    )
    .expect("disabled guarded-equivalence materializer must stay inert");

    assert!(!stats.enabled);
    assert_eq!(stats.sidecar_rows_seen, 2);
    assert_eq!(stats.proof_emit_records_seen, 3);
    assert_eq!(stats.records_materialized, 0);
    assert_eq!(stats.external_checker_verdict_artifact_rows, 0);
}

#[test]
fn test_fmla_guarded_equiv_lrat_materializer_binds_overlay_and_support_rows() {
    let transaction_id = 77;
    let (overlay_sidecars, support_sidecars, records) =
        fmla_guarded_equiv_lrat_fixture(transaction_id);
    let artifact = accepted_external_checker_verdict_artifact();

    let stats = materialize_fmla_guarded_equiv_lrat_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            require_external_checker_verdict: true,
            external_checker_verdict_artifact: Some(artifact),
        },
        transaction_id,
        &overlay_sidecars,
        &support_sidecars,
        &records,
    )
    .expect("accepted checker verdict must authorize all add-only Fmla rows");

    assert!(stats.enabled);
    assert_eq!(stats.sidecar_rows_seen, 2);
    assert_eq!(stats.proof_emit_records_seen, 3);
    assert_eq!(stats.records_materialized, 3);
    assert_eq!(stats.derived_clause_proof_steps_materialized, 3);
    assert_eq!(stats.deletion_proof_steps_materialized, 0);
    assert_eq!(stats.external_checker_verdict_artifact_rows, 3);
}

#[test]
fn test_fmla_guarded_equiv_lrat_materializer_rejects_missing_external_checker_verdict() {
    let transaction_id = 77;
    let (overlay_sidecars, support_sidecars, records) =
        fmla_guarded_equiv_lrat_fixture(transaction_id);

    let reject = materialize_fmla_guarded_equiv_lrat_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            require_external_checker_verdict: true,
            external_checker_verdict_artifact: None,
        },
        transaction_id,
        &overlay_sidecars,
        &support_sidecars,
        &records,
    )
    .expect_err("Main route must fail closed without an external checker verdict");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::MissingExternalCheckerVerdict {
            sidecar_row_index: 0,
            checker_visible_id: 10,
            materialized_records: 3,
            required_artifact: FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT,
        }
    );
}

#[test]
fn test_fmla_guarded_equiv_lrat_materializer_rejects_missing_add_row() {
    let transaction_id = 77;
    let (overlay_sidecars, support_sidecars, mut records) =
        fmla_guarded_equiv_lrat_fixture(transaction_id);
    records.retain(|record| record.checker_visible_id != 11);

    let reject = materialize_fmla_guarded_equiv_lrat_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            ..MainProofRewriteLedgerMaterializerConfig::default()
        },
        transaction_id,
        &overlay_sidecars,
        &support_sidecars,
        &records,
    )
    .expect_err("missing overlay reverse add row must fail closed");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::MissingAddRecord {
            sidecar_row_index: 0,
            checker_visible_id: 11,
        }
    );
}

#[test]
fn test_fmla_guarded_equiv_lrat_materializer_rejects_support_hint_mismatch() {
    let transaction_id = 77;
    let (overlay_sidecars, support_sidecars, mut records) =
        fmla_guarded_equiv_lrat_fixture(transaction_id);
    records
        .iter_mut()
        .find(|record| record.checker_visible_id == 12)
        .expect("fixture must include support row")
        .lrat_hints = vec![8, 6];

    let reject = materialize_fmla_guarded_equiv_lrat_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            ..MainProofRewriteLedgerMaterializerConfig::default()
        },
        transaction_id,
        &overlay_sidecars,
        &support_sidecars,
        &records,
    )
    .expect_err("support row with wrong LRAT hints must fail closed");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::ProofRecordPayloadMismatch {
            sidecar_row_index: 0,
            checker_visible_id: 12,
            field: "lrat_hints",
        }
    );
}

#[test]
fn test_source_bound_multiplier_lrat_materializer_is_default_off() {
    let transaction_id = 9761;
    let (sidecars, records) = source_bound_multiplier_lrat_fixture(transaction_id);

    let stats = materialize_source_bound_multiplier_lrat_records(
        MainProofRewriteLedgerMaterializerConfig::default(),
        transaction_id,
        &sidecars,
        std::iter::empty::<&[Literal]>(),
        &records,
    )
    .expect("disabled source-bound multiplier materializer must stay inert")
    .stats;

    assert!(!stats.enabled);
    assert_eq!(stats.sidecar_rows_seen, 6);
    assert_eq!(stats.proof_emit_records_seen, 6);
    assert_eq!(stats.records_materialized, 0);
    assert_eq!(stats.external_checker_verdict_artifact_rows, 0);
}

#[test]
fn test_source_bound_multiplier_lrat_plan_bridge_rejects_add_without_hints() {
    let reject =
        source_bound_multiplier_lrat_sidecars_from_plan_rows(&[SourceBoundMultiplierLratPlanRow {
            row_kind: SourceBoundMultiplierLratRowKind::ResolventAdd,
            source_clause_id: 5,
            source_clause_lits: vec![-1, 2],
            checker_visible_id: 20,
            delete_source_id: None,
            clause_lits_dimacs: vec![3, 4],
            lrat_hints: Vec::new(),
        }])
        .expect_err("source-bound BVE plan add without LRAT hints must fail closed");

    assert_eq!(
        reject,
        SourceBoundMultiplierLratPlanBridgeReject::AddMissingHints { plan_row_index: 0 }
    );
}

#[test]
fn test_source_bound_multiplier_lrat_plan_adapter_binds_original_sources_before_replay() {
    let plan_rows = source_bound_multiplier_lrat_plan_rows_fixture();
    let original_sources = source_bound_multiplier_original_source_fixture();

    let adapted = source_bound_multiplier_lrat_sidecars_from_original_source_plan_rows(
        &plan_rows,
        original_sources.iter().map(Vec::as_slice),
    )
    .expect("source-bound plan adapter must bind original sources before replay");

    assert_eq!(adapted.sidecars.len(), 6);
    assert_eq!(adapted.source_binding_stats.rows_checked, 6);
    assert_eq!(adapted.source_binding_stats.unique_source_rows_checked, 5);
    assert_eq!(adapted.source_binding_stats.first_source_clause_id, Some(4));
    assert_eq!(adapted.source_binding_stats.last_source_clause_id, Some(8));
}

#[test]
fn test_source_bound_multiplier_lrat_plan_adapter_rejects_original_source_drift() {
    let plan_rows = source_bound_multiplier_lrat_plan_rows_fixture();
    let mut original_sources = source_bound_multiplier_original_source_fixture();
    original_sources[3] = source_bound_dimacs_lits(&[1, 2]);

    let reject = source_bound_multiplier_lrat_sidecars_from_original_source_plan_rows(
        &plan_rows,
        original_sources.iter().map(Vec::as_slice),
    )
    .expect_err("source-bound plan adapter must fail closed on original source drift");

    assert_eq!(
        reject,
        SourceBoundMultiplierLratPlanAdapterReject::OriginalSourceBinding(
            SourceBoundMultiplierOriginalSourceBindingReject::SourceClauseLiteralMismatch {
                sidecar_row_index: 0,
                source_clause_id: 4,
                expected: vec![1, -2],
                observed: vec![1, 2],
            },
        )
    );
}

#[test]
fn test_source_bound_multiplier_original_source_binding_accepts_exact_dimacs_rows() {
    let transaction_id = 9761;
    let (sidecars, _) = source_bound_multiplier_lrat_fixture(transaction_id);
    let original_sources = source_bound_multiplier_original_source_fixture();

    let stats = validate_source_bound_multiplier_original_source_bindings(
        &sidecars,
        original_sources.iter().map(Vec::as_slice),
    )
    .expect("exact original DIMACS source rows must bind");

    assert_eq!(stats.rows_checked, 6);
    assert_eq!(stats.unique_source_rows_checked, 5);
    assert_eq!(stats.first_source_clause_id, Some(4));
    assert_eq!(stats.last_source_clause_id, Some(8));
}

#[test]
fn test_source_bound_multiplier_original_source_binding_rejects_literal_drift() {
    let transaction_id = 9761;
    let (sidecars, _) = source_bound_multiplier_lrat_fixture(transaction_id);
    let mut original_sources = source_bound_multiplier_original_source_fixture();
    original_sources[4] = source_bound_dimacs_lits(&[-1, -2]);

    let reject = validate_source_bound_multiplier_original_source_bindings(
        &sidecars,
        original_sources.iter().map(Vec::as_slice),
    )
    .expect_err("source literal drift must fail closed");

    assert_eq!(
        reject,
        SourceBoundMultiplierOriginalSourceBindingReject::SourceClauseLiteralMismatch {
            sidecar_row_index: 1,
            source_clause_id: 5,
            expected: vec![-1, 2],
            observed: vec![-1, -2],
        }
    );
}

#[test]
fn test_source_bound_multiplier_original_source_binding_rejects_missing_source_row() {
    let transaction_id = 9761;
    let (mut sidecars, _) = source_bound_multiplier_lrat_fixture(transaction_id);
    sidecars[0].source_clause_id = 99;
    let original_sources = source_bound_multiplier_original_source_fixture();

    let reject = validate_source_bound_multiplier_original_source_bindings(
        &sidecars,
        original_sources.iter().map(Vec::as_slice),
    )
    .expect_err("out-of-range source row must fail closed");

    assert_eq!(
        reject,
        SourceBoundMultiplierOriginalSourceBindingReject::SourceClauseIdOutOfRange {
            sidecar_row_index: 0,
            source_clause_id: 99,
            original_clause_count: 8,
        }
    );
}

#[test]
fn test_source_bound_multiplier_original_source_binding_rejects_delete_drift() {
    let transaction_id = 9761;
    let (mut sidecars, _) = source_bound_multiplier_lrat_fixture(transaction_id);
    sidecars[2].delete_source_id = Some(5);
    let original_sources = source_bound_multiplier_original_source_fixture();

    let reject = validate_source_bound_multiplier_original_source_bindings(
        &sidecars,
        original_sources.iter().map(Vec::as_slice),
    )
    .expect_err("delete row must target the same original source row");

    assert_eq!(
        reject,
        SourceBoundMultiplierOriginalSourceBindingReject::DeleteSourceIdMismatch {
            sidecar_row_index: 2,
            source_clause_id: 4,
            delete_source_id: Some(5),
        }
    );
}

#[test]
fn test_source_bound_multiplier_lrat_materializer_binds_rows_with_checker_artifact() {
    let transaction_id = 9761;
    let (sidecars, records) = source_bound_multiplier_lrat_fixture(transaction_id);
    let original_sources = source_bound_multiplier_original_source_fixture();

    let materialization = materialize_source_bound_multiplier_lrat_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            require_external_checker_verdict: true,
            external_checker_verdict_artifact: Some(accepted_external_checker_verdict_artifact()),
        },
        transaction_id,
        &sidecars,
        original_sources.iter().map(Vec::as_slice),
        &records,
    )
    .expect("accepted checker verdict must bind all source-bound multiplier rows");

    let stats = materialization.stats;
    assert!(stats.enabled);
    assert_eq!(stats.sidecar_rows_seen, 6);
    assert_eq!(stats.proof_emit_records_seen, 6);
    assert_eq!(stats.records_materialized, 6);
    assert_eq!(stats.derived_clause_proof_steps_materialized, 5);
    assert_eq!(stats.deletion_proof_steps_materialized, 1);
    assert_eq!(stats.external_checker_verdict_artifact_rows, 6);

    assert_eq!(materialization.records.len(), 6);
    for record in materialization.records {
        assert!(record.external_checker_verified);
        assert!(record.external_checker_verdict_artifact.is_some());
    }
}
#[test]
fn test_source_bound_multiplier_lrat_materializer_rejects_original_source_drift() {
    let transaction_id = 9761;
    let (sidecars, records) = source_bound_multiplier_lrat_fixture(transaction_id);
    let mut original_sources = source_bound_multiplier_original_source_fixture();
    original_sources[3] = source_bound_dimacs_lits(&[1, 2]);

    let reject = materialize_source_bound_multiplier_lrat_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            ..MainProofRewriteLedgerMaterializerConfig::default()
        },
        transaction_id,
        &sidecars,
        original_sources.iter().map(Vec::as_slice),
        &records,
    )
    .expect_err("source-bound multiplier materializer must bind original DIMACS rows");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::OriginalSourceBinding(
            SourceBoundMultiplierOriginalSourceBindingReject::SourceClauseLiteralMismatch {
                sidecar_row_index: 0,
                source_clause_id: 4,
                expected: vec![1, -2],
                observed: vec![1, 2],
            },
        )
    );
}

#[test]
fn test_source_bound_multiplier_lrat_materializer_rejects_missing_external_checker() {
    let transaction_id = 9761;
    let (sidecars, records) = source_bound_multiplier_lrat_fixture(transaction_id);
    let original_sources = source_bound_multiplier_original_source_fixture();

    let reject = materialize_source_bound_multiplier_lrat_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            require_external_checker_verdict: true,
            external_checker_verdict_artifact: None,
        },
        transaction_id,
        &sidecars,
        original_sources.iter().map(Vec::as_slice),
        &records,
    )
    .expect_err("source-bound multiplier route must fail closed without checker verdict");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::MissingExternalCheckerVerdict {
            sidecar_row_index: 0,
            checker_visible_id: 20,
            materialized_records: 6,
            required_artifact: FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT,
        }
    );
}

#[test]
fn test_source_bound_multiplier_lrat_materializer_rejects_missing_runtime_row() {
    let transaction_id = 9761;
    let (sidecars, mut records) = source_bound_multiplier_lrat_fixture(transaction_id);
    let original_sources = source_bound_multiplier_original_source_fixture();
    records.retain(|record| record.checker_visible_id != 21);

    let reject = materialize_source_bound_multiplier_lrat_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            ..MainProofRewriteLedgerMaterializerConfig::default()
        },
        transaction_id,
        &sidecars,
        original_sources.iter().map(Vec::as_slice),
        &records,
    )
    .expect_err("missing resolvent runtime row must fail closed");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::MissingAddRecord {
            sidecar_row_index: 1,
            checker_visible_id: 21,
        }
    );
}

#[test]
fn test_source_bound_multiplier_lrat_materializer_rejects_hint_drift() {
    let transaction_id = 9761;
    let (sidecars, mut records) = source_bound_multiplier_lrat_fixture(transaction_id);
    let original_sources = source_bound_multiplier_original_source_fixture();
    records
        .iter_mut()
        .find(|record| record.checker_visible_id == 20)
        .expect("fixture must include strengthening add row")
        .lrat_hints = vec![8, 4];

    let reject = materialize_source_bound_multiplier_lrat_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            ..MainProofRewriteLedgerMaterializerConfig::default()
        },
        transaction_id,
        &sidecars,
        original_sources.iter().map(Vec::as_slice),
        &records,
    )
    .expect_err("hint drift must fail closed");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::ProofRecordPayloadMismatch {
            sidecar_row_index: 0,
            checker_visible_id: 20,
            field: "lrat_hints",
        }
    );
}

#[test]
fn test_source_bound_multiplier_lrat_materializer_rejects_sidecar_index_drift() {
    let transaction_id = 9761;
    let (mut sidecars, records) = source_bound_multiplier_lrat_fixture(transaction_id);
    let original_sources = source_bound_multiplier_original_source_fixture();
    sidecars[1].sidecar_row_index = 4;

    let reject = materialize_source_bound_multiplier_lrat_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            ..MainProofRewriteLedgerMaterializerConfig::default()
        },
        transaction_id,
        &sidecars,
        original_sources.iter().map(Vec::as_slice),
        &records,
    )
    .expect_err("sidecar row-index drift must fail closed");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::ContextRowMismatch {
            expected: 1,
            observed: 4,
        }
    );
}

#[test]
fn test_fmla_postcheck_admission_replay_commits_checker_backed_route() {
    let artifact = accepted_external_checker_verdict_artifact();

    let replay =
        replay_fmla_postcheck_admission(fmla_postcheck_replay_input(), Some(artifact.clone()))
            .expect("post-check artifact must replay checker-backed Fmla admission");

    assert_eq!(
        replay.schema,
        FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_SCHEMA
    );
    assert_eq!(replay.status, "committed_checker_backed_admission");
    assert_eq!(replay.proof_obligation_rows, 3);
    assert_eq!(replay.external_checker_verdict_artifact_rows, 3);
    assert_eq!(replay.pre_replay_materializer_fail_closed, 1);
    assert_eq!(replay.pre_replay_preprocess_tx_fail_closed, 1);
    assert_eq!(replay.post_replay_preprocess_tx_committed, 1);
    assert_eq!(replay.external_checker_verdict_artifact, artifact);
}

#[test]
fn test_fmla_postcheck_admission_replay_rejects_missing_checker_artifact() {
    let reject = replay_fmla_postcheck_admission(fmla_postcheck_replay_input(), None)
        .expect_err("post-check replay must fail closed without checker artifact");

    assert_eq!(
        reject,
        FmlaPostCheckAdmissionReplayReject::MissingExternalCheckerVerdict
    );
}

#[test]
fn test_fmla_postcheck_admission_replay_rejects_spoofed_checker_artifact() {
    let mut artifact = accepted_external_checker_verdict_artifact();
    artifact.checker_exit_code = 1;

    let reject = replay_fmla_postcheck_admission(fmla_postcheck_replay_input(), Some(artifact))
        .expect_err("post-check replay must reject spoofed checker artifact");

    assert_eq!(
        reject,
        FmlaPostCheckAdmissionReplayReject::ExternalCheckerVerdictNotAccepted {
            reason: "external_checker_verdict_nonzero_exit_code",
        }
    );
}

#[test]
fn test_fmla_postcheck_admission_replay_rejects_non_checker_fail_closed_path() {
    let mut input = fmla_postcheck_replay_input();
    input.materializer_missing_runtime_records = 1;

    let reject =
        replay_fmla_postcheck_admission(input, Some(accepted_external_checker_verdict_artifact()))
            .expect_err("post-check replay must only clear missing-checker fail-closed path");

    assert_eq!(
        reject,
        FmlaPostCheckAdmissionReplayReject::MissingRuntimeRows
    );
}

#[test]
fn test_fmla_learned_lrat_postcheck_replay_authorizes_same_run_checked_proof_out() {
    let (dry_run_artifact, proof_out) = fmla_learned_lrat_dry_run_artifact_json_and_proof_out();
    let postcheck_replay = accepted_fmla_postcheck_replay_for_proof_rows(&proof_out, 2);

    let replay = validate_fmla_learned_lrat_main_proof_authority_from_json_postcheck_replay(
        &dry_run_artifact,
        &postcheck_replay,
        FMLA_RETAINED_PROOF_OUT_PATH,
        &proof_out,
    );

    assert_eq!(replay.status, "authorized");
    assert_eq!(replay.reason, None);
    assert_eq!(replay.checker_visible_id, Some(10));
    assert_eq!(
        replay.proof_out_path.as_deref(),
        Some(FMLA_RETAINED_PROOF_OUT_PATH)
    );
    assert_eq!(
        replay.proof_out_sha256.as_deref(),
        Some(
            postcheck_replay
                .external_checker_verdict_artifact
                .proof_out_sha256
                .as_str()
        )
    );
    assert!(replay.external_checker_verified);
    assert!(replay.proof_out_contains_lrat_fragment);
    assert!(replay.authorizes_main_proof_out);
}

#[test]
fn test_fmla_learned_lrat_postcheck_replay_rejects_missing_proof_out_bytes() {
    let (dry_run_artifact, proof_out) = fmla_learned_lrat_dry_run_artifact_json_and_proof_out();
    let postcheck_replay = accepted_fmla_postcheck_replay_for_proof_rows(&proof_out, 2);

    let replay = validate_fmla_learned_lrat_main_proof_authority_from_json_postcheck_replay(
        &dry_run_artifact,
        &postcheck_replay,
        FMLA_RETAINED_PROOF_OUT_PATH,
        b"",
    );

    assert_learned_lrat_authority_fail_closed(&replay, "proof_out_sha256_mismatch");
}

#[test]
fn test_fmla_learned_lrat_postcheck_replay_rejects_missing_external_verdict_rows() {
    let (dry_run_artifact, proof_out) = fmla_learned_lrat_dry_run_artifact_json_and_proof_out();
    let mut postcheck_replay = accepted_fmla_postcheck_replay_for_proof_rows(&proof_out, 2);
    postcheck_replay.external_checker_verdict_artifact_rows = 0;

    let replay = validate_fmla_learned_lrat_main_proof_authority_from_json_postcheck_replay(
        &dry_run_artifact,
        &postcheck_replay,
        FMLA_RETAINED_PROOF_OUT_PATH,
        &proof_out,
    );

    assert_learned_lrat_authority_fail_closed(&replay, "postcheck_replay_checker_row_mismatch");
}

#[test]
fn test_fmla_learned_lrat_postcheck_replay_rejects_stale_checked_proof_fragment() {
    let (dry_run_artifact, _proof_out) = fmla_learned_lrat_dry_run_artifact_json_and_proof_out();
    let stale_proof_out =
        b"c externally checked proof.out without retained learned fragment\n11 0 1 0\n";
    let postcheck_replay = accepted_fmla_postcheck_replay_for_proof_rows(stale_proof_out, 2);

    let replay = validate_fmla_learned_lrat_main_proof_authority_from_json_postcheck_replay(
        &dry_run_artifact,
        &postcheck_replay,
        FMLA_RETAINED_PROOF_OUT_PATH,
        stale_proof_out,
    );

    assert_learned_lrat_authority_fail_closed(&replay, "proof_out_missing_dry_run_fragment");
}

#[test]
fn test_fmla_learned_lrat_postcheck_replay_rejects_malformed_dry_run_fragment() {
    let (mut dry_run_artifact, proof_out) = fmla_learned_lrat_dry_run_artifact_json_and_proof_out();
    let drifted_fragment = format!(
        "{}11 0 1 0\n",
        dry_run_artifact["lrat_fragment"]
            .as_str()
            .expect("fixture has LRAT fragment")
    );
    dry_run_artifact["lrat_fragment"] = serde_json::Value::String(drifted_fragment.clone());
    dry_run_artifact["lrat_fragment_sha256"] =
        serde_json::Value::String(sha256_hex(drifted_fragment.as_bytes()));
    let postcheck_replay = accepted_fmla_postcheck_replay_for_proof_rows(&proof_out, 2);

    let replay = validate_fmla_learned_lrat_main_proof_authority_from_json_postcheck_replay(
        &dry_run_artifact,
        &postcheck_replay,
        FMLA_RETAINED_PROOF_OUT_PATH,
        &proof_out,
    );

    assert_learned_lrat_authority_fail_closed(
        &replay,
        "dry_run_artifact_lrat_fragment_rows_mismatch",
    );
}

#[test]
fn test_fmla_learned_lrat_postcheck_replay_rejects_materializer_rows_without_authority() {
    let dry_run_artifact = fmla_learned_lrat_fail_closed_materializer_rows_artifact_json();
    assert_eq!(
        dry_run_artifact["rows"]
            .as_array()
            .expect("fixture retains diagnostic rows")
            .len(),
        1
    );
    assert_eq!(
        dry_run_artifact["authorizes_main_proof_out"].as_bool(),
        Some(false)
    );
    let fragment = dry_run_artifact["lrat_fragment"]
        .as_str()
        .expect("fixture has retained diagnostic fragment");
    let proof_out = format!("c checked diagnostic-only fragment\n{fragment}").into_bytes();
    let postcheck_replay = accepted_fmla_postcheck_replay_for_proof_rows(&proof_out, 1);

    let replay = validate_fmla_learned_lrat_main_proof_authority_from_json_postcheck_replay(
        &dry_run_artifact,
        &postcheck_replay,
        FMLA_RETAINED_PROOF_OUT_PATH,
        &proof_out,
    );

    assert_learned_lrat_authority_fail_closed(&replay, "learned_lrat_dry_run_not_complete");
}

#[test]
fn test_fmla_main_lrat_rewrite_materializer_binds_sidecar_to_add_delete_rows() {
    let (sidecars, contexts) = retained_decompose_lrat_sidecar_fixture();
    let records = complete_proof_records(&sidecars[0], &contexts[0]);

    let materialized = materialize_main_lrat_rewrite_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            ..MainProofRewriteLedgerMaterializerConfig::default()
        },
        &sidecars,
        &contexts,
        &records,
    )
    .expect("complete scoped proof rows must materialize");

    assert_eq!(materialized.stats.proof_emit_records_seen, 4);
    assert_eq!(materialized.records.len(), 4);
    assert_eq!(materialized.stats.records_materialized, 4);
    assert_eq!(
        materialized.stats.derived_clause_proof_steps_materialized,
        3
    );
    assert_eq!(materialized.stats.deletion_proof_steps_materialized, 1);
    assert!(materialized
        .records
        .iter()
        .all(|record| record.solver_runtime_emitted));
    assert!(materialized
        .records
        .iter()
        .all(|record| !record.proof_writer_io_error));
    assert!(materialized
        .records
        .iter()
        .all(|record| !record.external_checker_verified));
    assert!(materialized
        .records
        .iter()
        .all(|record| record.external_checker_verdict_artifact.is_none()));
    assert!(materialized.records.iter().any(|record| {
        record.proof_out_record_kind == DecomposeProofOutRecordKind::Delete
            && record.delete_source_id == Some(4)
            && record.source_clause_id == 4
    }));
}

#[test]
fn test_fmla_main_lrat_rewrite_materializer_binds_external_checker_verdict_artifact() {
    let (sidecars, contexts) = retained_decompose_lrat_sidecar_fixture();
    let records = complete_proof_records(&sidecars[0], &contexts[0]);
    let artifact = accepted_external_checker_verdict_artifact();

    let materialized = materialize_main_lrat_rewrite_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            require_external_checker_verdict: true,
            external_checker_verdict_artifact: Some(artifact.clone()),
        },
        &sidecars,
        &contexts,
        &records,
    )
    .expect("accepted external checker verdict artifact must bind");

    assert_eq!(materialized.records.len(), 4);
    assert_eq!(materialized.stats.external_checker_verdict_artifact_rows, 4);
    assert!(materialized
        .records
        .iter()
        .all(|record| record.external_checker_verified));
    assert!(materialized.records.iter().all(|record| {
        record
            .external_checker_verdict_artifact
            .as_ref()
            .is_some_and(|artifact| {
                artifact.runtime_field
                    == FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT.runtime_field
                    && artifact.checker_exit_code
                        == FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT.checker_exit_code
            })
    }));
    assert!(materialized
        .records
        .iter()
        .all(|record| record.external_checker_verdict_artifact.as_ref() == Some(&artifact)));
}

#[test]
fn test_fmla_main_lrat_rewrite_materializer_rejects_missing_external_checker_verdict() {
    let (sidecars, contexts) = retained_decompose_lrat_sidecar_fixture();
    let records = complete_proof_records(&sidecars[0], &contexts[0]);

    let reject = materialize_main_lrat_rewrite_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            require_external_checker_verdict: true,
            external_checker_verdict_artifact: None,
        },
        &sidecars,
        &contexts,
        &records,
    )
    .expect_err("route-admission materializer must require an external checker verdict");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::MissingExternalCheckerVerdict {
            sidecar_row_index: 0,
            checker_visible_id: 5,
            materialized_records: 4,
            required_artifact: FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT,
        }
    );
}

#[test]
fn test_fmla_main_lrat_rewrite_materializer_rejects_malformed_checker_verdict_artifact() {
    let (sidecars, contexts) = retained_decompose_lrat_sidecar_fixture();
    let records = complete_proof_records(&sidecars[0], &contexts[0]);
    let mut artifact = accepted_external_checker_verdict_artifact();
    artifact.schema = "fixture.invalid-schema/v1".to_string();

    let reject = materialize_main_lrat_rewrite_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            require_external_checker_verdict: true,
            external_checker_verdict_artifact: Some(artifact),
        },
        &sidecars,
        &contexts,
        &records,
    )
    .expect_err("malformed external checker verdict artifact must fail closed");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::ExternalCheckerVerdictNotAccepted {
            sidecar_row_index: 0,
            checker_visible_id: 5,
            reason: "external_checker_verdict_schema_mismatch",
        }
    );
}

#[test]
fn test_fmla_main_lrat_rewrite_materializer_rejects_checker_verdict_wrong_runtime_field() {
    let (sidecars, contexts) = retained_decompose_lrat_sidecar_fixture();
    let records = complete_proof_records(&sidecars[0], &contexts[0]);
    let mut artifact = accepted_external_checker_verdict_artifact();
    artifact.runtime_field = "external_proof_checker_verdict".to_string();

    let reject = materialize_main_lrat_rewrite_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            require_external_checker_verdict: true,
            external_checker_verdict_artifact: Some(artifact),
        },
        &sidecars,
        &contexts,
        &records,
    )
    .expect_err("checker verdict must bind the expected runtime ledger field");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::ExternalCheckerVerdictNotAccepted {
            sidecar_row_index: 0,
            checker_visible_id: 5,
            reason: "external_checker_verdict_runtime_field_mismatch",
        }
    );
}

#[test]
fn test_fmla_main_lrat_rewrite_materializer_rejects_checker_verdict_wrong_artifact_name() {
    let (sidecars, contexts) = retained_decompose_lrat_sidecar_fixture();
    let records = complete_proof_records(&sidecars[0], &contexts[0]);
    let mut artifact = accepted_external_checker_verdict_artifact();
    artifact.artifact_path = "runs/fmla/proof/proof-checker-verdict.json".to_string();

    let reject = materialize_main_lrat_rewrite_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            require_external_checker_verdict: true,
            external_checker_verdict_artifact: Some(artifact),
        },
        &sidecars,
        &contexts,
        &records,
    )
    .expect_err("checker verdict must bind the retained Fmla Main/LRAT artifact row");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::ExternalCheckerVerdictNotAccepted {
            sidecar_row_index: 0,
            checker_visible_id: 5,
            reason: "external_checker_verdict_artifact_path_mismatch",
        }
    );
}

#[test]
fn test_fmla_main_lrat_rewrite_materializer_rejects_checker_verdict_nonzero_exit() {
    let (sidecars, contexts) = retained_decompose_lrat_sidecar_fixture();
    let records = complete_proof_records(&sidecars[0], &contexts[0]);
    let mut artifact = accepted_external_checker_verdict_artifact();
    artifact.checker_exit_code = 1;

    let reject = materialize_main_lrat_rewrite_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            require_external_checker_verdict: true,
            external_checker_verdict_artifact: Some(artifact),
        },
        &sidecars,
        &contexts,
        &records,
    )
    .expect_err("checker verdict must come from a successful external checker process");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::ExternalCheckerVerdictNotAccepted {
            sidecar_row_index: 0,
            checker_visible_id: 5,
            reason: "external_checker_verdict_nonzero_exit_code",
        }
    );
}

#[test]
fn test_fmla_main_lrat_rewrite_materializer_rejects_checker_verdict_not_bound_to_proof_out() {
    let (sidecars, contexts) = retained_decompose_lrat_sidecar_fixture();
    let records = complete_proof_records(&sidecars[0], &contexts[0]);
    let mut artifact = accepted_external_checker_verdict_artifact();
    artifact.proof_out_path = "runs/fmla/proof/manual.lrat".to_string();
    artifact.checker_command =
        "/opt/satcomp/bin/cake_lpr benchmarks/FmlaEquivChain_4_6_6.sanitized.cnf runs/fmla/proof/manual.lrat"
            .to_string();

    let reject = materialize_main_lrat_rewrite_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            require_external_checker_verdict: true,
            external_checker_verdict_artifact: Some(artifact),
        },
        &sidecars,
        &contexts,
        &records,
    )
    .expect_err("checker verdict must bind the wrapper-produced proof.out path");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::ExternalCheckerVerdictNotAccepted {
            sidecar_row_index: 0,
            checker_visible_id: 5,
            reason: "proof_out_path_not_wrapper_proof_out",
        }
    );
}

#[test]
fn test_fmla_main_lrat_rewrite_materializer_rejects_checker_argv_proof_out_spoof() {
    let (sidecars, contexts) = retained_decompose_lrat_sidecar_fixture();
    let records = complete_proof_records(&sidecars[0], &contexts[0]);
    let mut artifact = accepted_external_checker_verdict_artifact();
    artifact.checker_command =
        "/opt/satcomp/bin/cake_lpr benchmarks/FmlaEquivChain_4_6_6.sanitized.cnf runs/fmla/proof/proof.out.stale"
            .to_string();
    artifact.checker_argv[2] = "runs/fmla/proof/proof.out.stale".to_string();

    let reject = materialize_main_lrat_rewrite_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            require_external_checker_verdict: true,
            external_checker_verdict_artifact: Some(artifact),
        },
        &sidecars,
        &contexts,
        &records,
    )
    .expect_err("checker argv must bind the exact wrapper proof.out path");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::ExternalCheckerVerdictNotAccepted {
            sidecar_row_index: 0,
            checker_visible_id: 5,
            reason: "checker_argv_not_bound_to_checked_inputs",
        }
    );
}

#[test]
fn test_fmla_main_lrat_rewrite_materializer_rejects_checker_argv_dimacs_spoof() {
    let (sidecars, contexts) = retained_decompose_lrat_sidecar_fixture();
    let records = complete_proof_records(&sidecars[0], &contexts[0]);
    let mut artifact = accepted_external_checker_verdict_artifact();
    artifact.checker_command =
        "/opt/satcomp/bin/cake_lpr benchmarks/FmlaEquivChain_4_6_6.sanitized.cnf.bak runs/fmla/proof/proof.out"
            .to_string();
    artifact.checker_argv[1] = "benchmarks/FmlaEquivChain_4_6_6.sanitized.cnf.bak".to_string();

    let reject = materialize_main_lrat_rewrite_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            require_external_checker_verdict: true,
            external_checker_verdict_artifact: Some(artifact),
        },
        &sidecars,
        &contexts,
        &records,
    )
    .expect_err("checker argv must bind the exact checked DIMACS path");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::ExternalCheckerVerdictNotAccepted {
            sidecar_row_index: 0,
            checker_visible_id: 5,
            reason: "checker_argv_not_bound_to_checked_inputs",
        }
    );
}

#[test]
fn test_fmla_main_lrat_rewrite_materializer_rejects_missing_delete_binding() {
    let (sidecars, contexts) = retained_decompose_lrat_sidecar_fixture();
    let mut records = complete_proof_records(&sidecars[0], &contexts[0]);
    records.retain(|record| record.proof_out_record_kind != DecomposeProofOutRecordKind::Delete);

    let reject = materialize_main_lrat_rewrite_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            ..MainProofRewriteLedgerMaterializerConfig::default()
        },
        &sidecars,
        &contexts,
        &records,
    )
    .expect_err("missing deletion proof row must fail closed");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::MissingDeleteRecord {
            sidecar_row_index: 0,
            delete_source_id: 4,
        }
    );
}

#[test]
fn test_fmla_main_lrat_rewrite_materializer_rejects_non_runtime_record() {
    let (sidecars, contexts) = retained_decompose_lrat_sidecar_fixture();
    let mut records = complete_proof_records(&sidecars[0], &contexts[0]);
    records[0].solver_runtime_emitted = false;

    let reject = materialize_main_lrat_rewrite_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            ..MainProofRewriteLedgerMaterializerConfig::default()
        },
        &sidecars,
        &contexts,
        &records,
    )
    .expect_err("non-runtime proof row must fail closed");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::RuntimeProofRecordNotEmitted {
            sidecar_row_index: 0,
            checker_visible_id: 5,
        }
    );
}

#[test]
fn test_fmla_main_lrat_rewrite_materializer_rejects_external_verdict_injection() {
    let (sidecars, contexts) = retained_decompose_lrat_sidecar_fixture();
    let mut records = complete_proof_records(&sidecars[0], &contexts[0]);
    records[0].external_checker_verified = true;

    let reject = materialize_main_lrat_rewrite_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            ..MainProofRewriteLedgerMaterializerConfig::default()
        },
        &sidecars,
        &contexts,
        &records,
    )
    .expect_err("unchecked external verdict must fail closed");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::ExternalCheckerVerdictNotAccepted {
            sidecar_row_index: 0,
            checker_visible_id: 5,
            reason: "proof_record_injected_external_checker_verdict",
        }
    );
}

#[test]
fn test_fmla_main_lrat_rewrite_materializer_rejects_add_hint_mismatch() {
    let (sidecars, contexts) = retained_decompose_lrat_sidecar_fixture();
    let mut records = complete_proof_records(&sidecars[0], &contexts[0]);
    records[0].lrat_hints = vec![sidecars[0].source_clause_id];

    let reject = materialize_main_lrat_rewrite_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            ..MainProofRewriteLedgerMaterializerConfig::default()
        },
        &sidecars,
        &contexts,
        &records,
    )
    .expect_err("add row with wrong LRAT hints must fail closed");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::ProofRecordPayloadMismatch {
            sidecar_row_index: 0,
            checker_visible_id: 5,
            field: "lrat_hints",
        }
    );
}

#[test]
fn test_fmla_main_lrat_rewrite_materializer_rejects_delete_clause_mismatch() {
    let (sidecars, contexts) = retained_decompose_lrat_sidecar_fixture();
    let mut records = complete_proof_records(&sidecars[0], &contexts[0]);
    let delete_record = records
        .iter_mut()
        .find(|record| record.proof_out_record_kind == DecomposeProofOutRecordKind::Delete)
        .expect("fixture must include a delete row");
    delete_record.clause_lits_dimacs = sidecars[0].rewritten_clause_lits.clone();

    let reject = materialize_main_lrat_rewrite_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            ..MainProofRewriteLedgerMaterializerConfig::default()
        },
        &sidecars,
        &contexts,
        &records,
    )
    .expect_err("delete row with wrong clause payload must fail closed");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::ProofRecordPayloadMismatch {
            sidecar_row_index: 0,
            checker_visible_id: 4,
            field: "clause_lits_dimacs",
        }
    );
}

#[test]
fn test_fmla_main_lrat_rewrite_materializer_rejects_non_lrat_proof_rows() {
    let (sidecars, contexts) = retained_decompose_lrat_sidecar_fixture();
    let mut records = complete_proof_records(&sidecars[0], &contexts[0]);
    records[0].proof_manager_mode = "drat";

    let reject = materialize_main_lrat_rewrite_records(
        MainProofRewriteLedgerMaterializerConfig {
            enabled: true,
            ..MainProofRewriteLedgerMaterializerConfig::default()
        },
        &sidecars,
        &contexts,
        &records,
    )
    .expect_err("non-LRAT proof-manager rows must fail closed");

    assert_eq!(
        reject,
        MainProofRewriteLedgerMaterializerReject::ProofRecordPayloadMismatch {
            sidecar_row_index: 0,
            checker_visible_id: 5,
            field: "proof_manager_mode",
        }
    );
}

#[test]
fn test_route_admission_packet_retained_and_fail_closed_in_transaction_ledger() {
    let mut ledger = PreprocessTransactionLedger::new();
    let id = ledger.begin(PreprocessTransactionDraft {
        mutation_epoch: 11,
        pass_name: PreprocessPass::Decompose,
        touched_variables: vec![0, 1, 2],
        eliminated_variables: Vec::new(),
        equivalent_variables: vec![(1, 0)],
        planned_substitutions: Vec::new(),
        proof_obligation: ProofObligationStatus::Satisfied,
        model_reconstruction_witness: ModelReconstructionWitnessStatus::NotApplicable,
    });

    assert_eq!(
        ledger.route_admission_packet(id),
        Some(RouteAdmissionPacket::default())
    );
    assert!(ledger.set_route_admission_packet(
        id,
        RouteAdmissionPacket {
            kind: RouteAdmissionPacketKind::FmlaEquivChainMainLrat,
            status: RouteAdmissionPacketStatus::Incomplete,
            original_dimacs_rows: 31,
            original_clause_authority_rows: 0,
            proof_obligation_rows: 0,
            model_reconstruction_rows: 0,
            external_proof_checker_verdict_artifact_rows: 0,
        },
    ));

    let err = ledger
        .commit(id)
        .expect_err("incomplete route admission packet must fail closed");

    assert_eq!(
        err,
        PreprocessTransactionCommitError::RouteAdmissionPacketNotReady
    );
    let stats = ledger.stats();
    assert_eq!(stats.started, 1);
    assert_eq!(stats.committed, 0);
    assert_eq!(stats.fail_closed, 1);
    assert_eq!(stats.fail_closed_other, 1);
    let record = ledger
        .last_completed()
        .expect("route-admission fail-closed record retained");
    assert_eq!(record.outcome, PreprocessTransactionOutcome::FailClosed);
    assert_eq!(
        record.route_admission_packet.kind,
        RouteAdmissionPacketKind::FmlaEquivChainMainLrat
    );
    assert_eq!(
        record.route_admission_packet.status,
        RouteAdmissionPacketStatus::Incomplete
    );
    assert_eq!(
        record.fail_closed_reason.as_deref(),
        Some("route admission packet incomplete")
    );
}
