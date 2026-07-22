// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Decompose (SCC-based equivalent literal substitution) structural tests.
//!
//! These tests verify the clause-rewriting behavior of decompose without
//! requiring LRAT proof output. LRAT proof generation during decompose is
//! intentionally disabled (#8197) pending correct proof chain implementation.
//! The tests exercise the same equivalence chains and rewriting logic but
//! assert on structural outcomes (clause DB state) rather than proof stream.

use super::*;
use crate::decompose::{
    DecomposeLratDryRunExport, DecomposeLratDryRunSidecar, DecomposeLratEquivalenceStep,
    DecomposeProofOutRecordKind, FmlaGuardedEquivOverlayLratBinaryRow,
    FmlaGuardedEquivOverlayLratSidecar, FmlaGuardedEquivSupportCoverLratSidecar,
};
use crate::preprocess_transaction::{
    ModelReconstructionWitnessStatus, PreprocessPass, PreprocessTransactionCommitError,
    PreprocessTransactionDraft, PreprocessTransactionLedger, PreprocessTransactionOutcome,
    ProofObligationStatus, RouteAdmissionPacket, RouteAdmissionPacketKind,
    RouteAdmissionPacketStatus,
};
use crate::solver::inprocessing::FMLA_MAIN_LRAT_PREFLIGHT_MAX_PROOF_ROWS;
use crate::ProofOutput;

fn active_clause_lits(solver: &Solver) -> Vec<Vec<Literal>> {
    solver
        .arena
        .indices()
        .filter(|&idx| solver.arena.is_active(idx))
        .map(|idx| solver.arena.literals(idx).to_vec())
        .collect()
}

fn active_clause_exists(solver: &Solver, expected: &[Literal]) -> bool {
    solver.arena.indices().any(|idx| {
        solver.arena.is_active(idx) && solver.arena.len_of(idx) == expected.len() && {
            let lits = solver.arena.literals(idx);
            expected.iter().all(|lit| lits.contains(lit))
        }
    })
}

fn active_clause_index(solver: &Solver, expected: &[Literal]) -> usize {
    solver
        .arena
        .indices()
        .find(|&idx| {
            solver.arena.is_active(idx) && solver.arena.len_of(idx) == expected.len() && {
                let lits = solver.arena.literals(idx);
                expected.iter().all(|lit| lits.contains(lit))
            }
        })
        .expect("expected active clause")
}

fn dimacs_lits(lits: &[i64]) -> Vec<Literal> {
    lits.iter()
        .map(|&lit| Literal::from_dimacs(i32::try_from(lit).expect("DIMACS literal fits i32")))
        .collect()
}

fn assert_complete_packet_with_authority_gap_fails_closed(
    original_clause_authority_rows: u64,
    proof_obligation_rows: u64,
) {
    assert!(
        original_clause_authority_rows < proof_obligation_rows,
        "fixture must leave an original-clause authority gap"
    );

    let mut ledger = PreprocessTransactionLedger::new();
    let id = ledger.begin(PreprocessTransactionDraft {
        mutation_epoch: 1,
        pass_name: PreprocessPass::Decompose,
        touched_variables: vec![0, 1],
        eliminated_variables: Vec::new(),
        equivalent_variables: Vec::new(),
        planned_substitutions: Vec::new(),
        proof_obligation: ProofObligationStatus::Satisfied,
        model_reconstruction_witness: ModelReconstructionWitnessStatus::NotApplicable,
    });
    assert!(ledger.set_route_admission_packet(
        id,
        RouteAdmissionPacket {
            kind: RouteAdmissionPacketKind::FmlaEquivChainMainLrat,
            status: RouteAdmissionPacketStatus::Complete,
            original_dimacs_rows: 1,
            original_clause_authority_rows,
            proof_obligation_rows,
            model_reconstruction_rows: 0,
            external_proof_checker_verdict_artifact_rows: proof_obligation_rows,
        },
    ));

    let err = ledger
        .commit(id)
        .expect_err("authority gap must fail closed even with checker artifact row counts");
    assert_eq!(
        err,
        PreprocessTransactionCommitError::RouteAdmissionPacketNotReady
    );
    let record = ledger
        .last_completed()
        .expect("authority-gap fail-closed record retained");
    assert_eq!(record.outcome, PreprocessTransactionOutcome::FailClosed);
    assert_eq!(
        record.fail_closed_reason.as_deref(),
        Some("route admission packet missing original clause authority")
    );
}

#[test]
fn test_fmla_overlay_authority_gap_fails_closed_for_zero_source_id() {
    let proof_rows = 2;
    let mut sidecar = FmlaGuardedEquivOverlayLratSidecar {
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

    assert_eq!(
        Solver::fmla_guarded_equiv_original_clause_authority_rows(&[sidecar.clone()], &[]),
        proof_rows
    );

    sidecar.forward_binary.guarded_ternary_source_id = 0;
    let authority_rows = Solver::fmla_guarded_equiv_original_clause_authority_rows(&[sidecar], &[]);

    assert_eq!(authority_rows, 1);
    assert_complete_packet_with_authority_gap_fails_closed(authority_rows, proof_rows);
}

#[test]
fn test_fmla_support_cover_authority_gap_fails_closed_for_hint_order_mismatch() {
    let proof_rows = 1;
    let mut sidecar = FmlaGuardedEquivSupportCoverLratSidecar {
        planned_add_id: 12,
        support_clause_id: 8,
        support_guard_lits_dimacs: vec![1, 2],
        source_lit_dimacs: 3,
        destination_lits_dimacs: vec![4, 5],
        clause_lits_dimacs: vec![-3, 4, 5],
        directional_ternary_source_ids: vec![6, 7],
        lrat_hints: vec![6, 7, 8],
    };

    assert_eq!(
        Solver::fmla_guarded_equiv_original_clause_authority_rows(&[], &[sidecar.clone()]),
        proof_rows
    );

    sidecar.lrat_hints = vec![7, 6, 8];
    let authority_rows = Solver::fmla_guarded_equiv_original_clause_authority_rows(&[], &[sidecar]);

    assert_eq!(authority_rows, 0);
    assert_complete_packet_with_authority_gap_fails_closed(authority_rows, proof_rows);
}

#[test]
fn test_decompose_rewrite_authority_gap_fails_closed_for_mismatched_source_id_and_hint_order() {
    let proof_rows = 4;
    let sidecar = DecomposeLratDryRunSidecar {
        source_clause_id: 4,
        source_clause_lits: vec![3, 4],
        rewritten_clause_lits: vec![1, 4],
        equivalence_steps: vec![DecomposeLratEquivalenceStep {
            original_lit: 3,
            representative_lit: 1,
            lit_to_repr_source_ids: vec![3],
            repr_to_lit_source_ids: vec![1, 2],
            planned_lit_to_repr_add_id: 5,
            planned_repr_to_lit_add_id: 6,
        }],
        rewrite_hints: vec![5, 4],
        planned_rewrite_add_id: 7,
        source_delete_id: 4,
    };

    assert_eq!(
        Solver::decompose_main_lrat_original_clause_authority_rows(std::slice::from_ref(&sidecar)),
        proof_rows
    );

    let mut delete_source_mismatch = sidecar.clone();
    delete_source_mismatch.source_delete_id = 9;
    let authority_rows =
        Solver::decompose_main_lrat_original_clause_authority_rows(&[delete_source_mismatch]);
    assert_eq!(authority_rows, 3);
    assert_complete_packet_with_authority_gap_fails_closed(authority_rows, proof_rows);

    let mut rewrite_hint_order_mismatch = sidecar;
    rewrite_hint_order_mismatch.rewrite_hints = vec![4, 5];
    let authority_rows =
        Solver::decompose_main_lrat_original_clause_authority_rows(&[rewrite_hint_order_mismatch]);
    assert_eq!(authority_rows, 3);
    assert_complete_packet_with_authority_gap_fails_closed(authority_rows, proof_rows);
}

fn render_dimacs_fixture(num_vars: usize, clauses: &[Vec<Literal>]) -> String {
    let mut dimacs = format!("p cnf {num_vars} {}\n", clauses.len());
    for clause in clauses {
        for lit in clause {
            dimacs.push_str(&format!("{} ", lit.to_dimacs()));
        }
        dimacs.push_str("0\n");
    }
    dimacs
}

fn fmla_guarded_equiv_fixture() -> Vec<Vec<Literal>> {
    let pos = |var| Literal::positive(Variable(var));
    let neg = |var| Literal::negative(Variable(var));
    let mut clauses = vec![(0..6).map(pos).collect()];
    for lhs in 0..6 {
        for rhs in (lhs + 1)..6 {
            clauses.push(vec![neg(lhs), neg(rhs)]);
        }
    }
    clauses.push(vec![neg(0), neg(6), pos(7)]);
    clauses.push(vec![neg(0), neg(7), pos(6)]);
    clauses
}

fn fmla_guarded_equiv_support_cover_fixture() -> Vec<Vec<Literal>> {
    let pos = |var| Literal::positive(Variable(var));
    let neg = |var| Literal::negative(Variable(var));
    let mut clauses = vec![(0..6).map(pos).collect()];
    for lhs in 0..6 {
        for rhs in (lhs + 1)..6 {
            clauses.push(vec![neg(lhs), neg(rhs)]);
        }
    }
    for guard in 0..6 {
        let destination = 7 + guard;
        clauses.push(vec![neg(guard), neg(6), pos(destination)]);
        clauses.push(vec![neg(guard), neg(destination), pos(6)]);
    }
    clauses
}

fn fmla_equiv_chain_data_formula() -> Option<crate::DimacsFormula> {
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/FmlaEquivChain.cnf");
    if !path.exists() {
        eprintln!("FmlaEquivChain.cnf fixture missing, skipping");
        return None;
    }
    let content = std::fs::read_to_string(&path).expect("read FmlaEquivChain.cnf");
    Some(crate::parse_dimacs(&content).expect("parse FmlaEquivChain.cnf"))
}

fn render_decompose_lrat_dry_run_replay(sidecar: &DecomposeLratDryRunSidecar) -> String {
    let mut proof = String::new();
    for step in &sidecar.equivalence_steps {
        proof.push_str(&format!(
            "{} {} {} 0",
            step.planned_lit_to_repr_add_id, step.representative_lit, -step.original_lit
        ));
        for &hint in &step.lit_to_repr_source_ids {
            proof.push_str(&format!(" {hint}"));
        }
        proof.push_str(" 0\n");

        proof.push_str(&format!(
            "{} {} {} 0",
            step.planned_repr_to_lit_add_id, step.original_lit, -step.representative_lit
        ));
        for &hint in &step.repr_to_lit_source_ids {
            proof.push_str(&format!(" {hint}"));
        }
        proof.push_str(" 0\n");
    }

    proof.push_str(&format!("{}", sidecar.planned_rewrite_add_id));
    for &lit in &sidecar.rewritten_clause_lits {
        proof.push_str(&format!(" {lit}"));
    }
    proof.push_str(" 0");
    for &hint in &sidecar.rewrite_hints {
        proof.push_str(&format!(" {hint}"));
    }
    proof.push_str(" 0\n");
    proof
}

fn render_fmla_guarded_equiv_overlay_lrat_replay(
    sidecar: &FmlaGuardedEquivOverlayLratSidecar,
) -> String {
    let mut proof = String::new();
    for row in [&sidecar.forward_binary, &sidecar.reverse_binary] {
        proof.push_str(&format!("{}", row.planned_add_id));
        for &lit in &row.clause_lits_dimacs {
            proof.push_str(&format!(" {lit}"));
        }
        proof.push_str(" 0");
        for &hint in &row.lrat_hints {
            proof.push_str(&format!(" {hint}"));
        }
        proof.push_str(" 0\n");
    }
    proof
}

fn verify_lrat_fixture(dimacs: &str, proof: &str) {
    let cnf = ay_lrat_check::dimacs::parse_cnf_with_ids(dimacs.as_bytes())
        .expect("bounded decompose sidecar CNF must parse");
    let steps = ay_lrat_check::lrat_parser::parse_text_lrat(proof)
        .expect("decompose sidecar LRAT must parse");
    let mut checker = ay_lrat_check::checker::LratChecker::new(cnf.num_vars);
    for (id, clause) in &cnf.clauses {
        assert!(checker.add_original(*id, clause));
    }
    for step in &steps {
        match step {
            ay_lrat_check::lrat_parser::LratStep::Add { id, clause, hints } => {
                assert!(
                    checker.add_derived(*id, clause, hints),
                    "retained decompose dry-run addition {id} should be checker-visible"
                );
            }
            ay_lrat_check::lrat_parser::LratStep::Delete { ids } => {
                for &id in ids {
                    assert!(checker.delete(id), "dry-run delete ID {id} should be live");
                }
            }
        }
    }
}

fn repo_root_for_decompose_artifacts() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("crate should live under repo/crates/ay-sat")
        .to_path_buf()
}

fn producer_revision_for_decompose_artifact() -> String {
    std::process::Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()
        .and_then(|output| {
            output
                .status
                .success()
                .then(|| String::from_utf8_lossy(&output.stdout).trim().to_string())
        })
        .filter(|revision| !revision.is_empty())
        .unwrap_or_else(|| "ay-sat-test-unknown-revision".to_string())
}

#[test]
fn test_lrat_decompose_request_is_fail_closed() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 3);
    let mut solver = Solver::with_proof_output(3, proof);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));

    // x0 <-> x1 gives decompose a non-trivial SCC, and this clause would
    // rewrite to (x0 | x2) if the LRAT decompose body executed.
    solver.add_clause_db(&[x0.negated(), x1], false);
    solver.add_clause_db(&[x1.negated(), x0], false);
    solver.add_clause_db(&[x1, x2], false);
    solver.initialize_watches();

    assert!(solver.cold.lrat_enabled, "test must run in LRAT mode");

    solver.decompose();

    assert_eq!(
        solver.decompose_stats().rounds,
        0,
        "LRAT decompose must not execute until equivalence chains have proof-ID-complete hints"
    );
    let rewritten_exists = solver.arena.indices().any(|idx| {
        solver.arena.is_active(idx) && solver.arena.len_of(idx) == 2 && {
            let lits = solver.arena.literals(idx);
            lits.contains(&x0) && lits.contains(&x2)
        }
    });
    assert!(
        !rewritten_exists,
        "requested LRAT decompose must not rewrite clauses while fail-closed"
    );
}

#[test]
fn test_lrat_decompose_equivalence_chain_preflight_fails_closed_before_mutation() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 4);
    let mut solver = Solver::with_proof_output(4, proof);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let y = Literal::positive(Variable(3));

    // Minimal Fmla-like chain from #9237: x0 -> x1 -> x2 -> x0, with
    // target clause (x2 | y). A non-LRAT decompose run rewrites the target
    // to (x0 | y). LRAT mode must remain fail-closed before mutation until
    // the checker-visible equivalence preflight is complete.
    solver.add_clause_db(&[x0.negated(), x1], false);
    solver.add_clause_db(&[x1.negated(), x2], false);
    solver.add_clause_db(&[x2.negated(), x0], false);
    solver.add_clause_db(&[x2, y], false);
    solver.initialize_watches();

    assert!(solver.cold.lrat_enabled, "test must run in LRAT mode");
    assert!(
        active_clause_exists(&solver, &[x2, y]),
        "setup must contain the original Fmla-like target clause"
    );
    assert!(
        !active_clause_exists(&solver, &[x0, y]),
        "setup must not already contain the rewritten clause"
    );

    let clauses_before = active_clause_lits(&solver);
    let clause_ids_before = solver.cold.clause_ids.clone();
    let reconstruction_before = solver.inproc.reconstruction.len();
    let trail_len_before = solver.trail.len();
    let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
    let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

    solver.decompose();

    assert_eq!(
        solver.decompose_stats().rounds,
        0,
        "LRAT decompose preflight must reject before running SCC substitution"
    );
    assert_eq!(
        active_clause_lits(&solver),
        clauses_before,
        "fail-closed LRAT decompose preflight must not mutate active clauses"
    );
    assert_eq!(
        solver.cold.clause_ids, clause_ids_before,
        "fail-closed LRAT decompose preflight must not reserve or rewrite proof IDs"
    );
    assert_eq!(
        solver.inproc.reconstruction.len(),
        reconstruction_before,
        "fail-closed LRAT decompose preflight must not record reconstruction entries"
    );
    assert_eq!(
        solver.trail.len(),
        trail_len_before,
        "fail-closed LRAT decompose preflight must not enqueue units"
    );
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().added_count(),
        proof_added_before,
        "fail-closed LRAT decompose preflight must not emit LRAT additions"
    );
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().deleted_count(),
        proof_deleted_before,
        "fail-closed LRAT decompose preflight must not emit LRAT deletions"
    );
    assert!(
        active_clause_exists(&solver, &[x2, y]),
        "original target clause must stay active after fail-closed preflight"
    );
    assert!(
        !active_clause_exists(&solver, &[x0, y]),
        "rewritten target clause must not appear while preflight rejects"
    );
    assert!(
        !solver.var_lifecycle.is_removed(x1.variable().index())
            && !solver.var_lifecycle.is_removed(x2.variable().index()),
        "fail-closed preflight must not mark equivalent variables as removed"
    );
}

#[test]
fn test_lrat_decompose_preflight_rejects_missing_source_id_before_mutation() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 4);
    let mut solver = Solver::with_proof_output(4, proof);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let y = Literal::positive(Variable(3));

    solver.add_clause_db(&[x0.negated(), x1], false);
    solver.add_clause_db(&[x1.negated(), x2], false);
    solver.add_clause_db(&[x2.negated(), x0], false);
    solver.add_clause_db(&[x2, y], false);
    solver.initialize_watches();

    let target_idx = active_clause_index(&solver, &[x2, y]);
    solver.cold.clause_ids[target_idx] = 0;
    let clauses_before = active_clause_lits(&solver);
    let clause_ids_before = solver.cold.clause_ids.clone();
    let reconstruction_before = solver.inproc.reconstruction.len();
    let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
    let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

    solver.decompose();

    assert_eq!(solver.decompose_stats().rounds, 0);
    assert_eq!(
        active_clause_lits(&solver),
        clauses_before,
        "missing source-ID reject must happen before clause mutation"
    );
    assert_eq!(
        solver.cold.clause_ids, clause_ids_before,
        "missing source-ID reject must not rewrite proof IDs"
    );
    assert_eq!(
        solver.inproc.reconstruction.len(),
        reconstruction_before,
        "missing source-ID reject must not record reconstruction entries"
    );
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().added_count(),
        proof_added_before
    );
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().deleted_count(),
        proof_deleted_before
    );

    let preflight = solver.decompose_lrat_preflight_stats();
    assert_eq!(preflight.attempts, 1);
    assert_eq!(preflight.transaction_candidates, 4);
    assert_eq!(preflight.dry_run_emitted, 0);
    assert_eq!(preflight.dry_run_rejected, 1);
    assert_eq!(preflight.missing_source_id, 1);
    assert!(solver.decompose_lrat_dry_run_sidecars().is_empty());
    let ledger = solver.preprocessing_transaction_stats();
    assert_eq!(ledger.fail_closed, 1);
    assert_eq!(ledger.proof_obligation_rejected, 1);
}

#[test]
fn test_lrat_decompose_preflight_rejects_missing_chain_edge_id_before_mutation() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 4);
    let mut solver = Solver::with_proof_output(4, proof);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let y = Literal::positive(Variable(3));

    solver.add_clause_db(&[x0.negated(), x1], false);
    solver.add_clause_db(&[x1.negated(), x2], false);
    solver.add_clause_db(&[x2.negated(), x0], false);
    solver.add_clause_db(&[x2, y], false);
    solver.initialize_watches();

    let chain_edge_idx = active_clause_index(&solver, &[x2.negated(), x0]);
    solver.cold.clause_ids[chain_edge_idx] = 0;
    let clauses_before = active_clause_lits(&solver);
    let clause_ids_before = solver.cold.clause_ids.clone();
    let reconstruction_before = solver.inproc.reconstruction.len();
    let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
    let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

    solver.decompose();

    assert_eq!(solver.decompose_stats().rounds, 0);
    assert_eq!(
        active_clause_lits(&solver),
        clauses_before,
        "missing chain-edge reject must happen before clause mutation"
    );
    assert_eq!(
        solver.cold.clause_ids, clause_ids_before,
        "missing chain-edge reject must not rewrite proof IDs"
    );
    assert_eq!(
        solver.inproc.reconstruction.len(),
        reconstruction_before,
        "missing chain-edge reject must not record reconstruction entries"
    );
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().added_count(),
        proof_added_before
    );
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().deleted_count(),
        proof_deleted_before
    );

    let preflight = solver.decompose_lrat_preflight_stats();
    assert_eq!(preflight.attempts, 1);
    assert_eq!(preflight.transaction_candidates, 4);
    assert_eq!(preflight.dry_run_emitted, 0);
    assert_eq!(preflight.dry_run_rejected, 1);
    assert_eq!(preflight.missing_chain_edge_id, 1);
    assert!(solver.decompose_lrat_dry_run_sidecars().is_empty());
    let ledger = solver.preprocessing_transaction_stats();
    assert_eq!(ledger.fail_closed, 1);
    assert_eq!(ledger.proof_obligation_rejected, 1);
}

#[test]
fn test_lrat_decompose_equivalence_chain_preflight_exports_checker_sidecar() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 4);
    let mut solver = Solver::with_proof_output(4, proof);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let y = Literal::positive(Variable(3));
    let clauses = vec![
        vec![x0.negated(), x1],
        vec![x1.negated(), x2],
        vec![x2.negated(), x0],
        vec![x2, y],
    ];
    for clause in &clauses {
        solver.add_clause_db(clause, false);
    }
    solver.initialize_watches();

    let clauses_before = active_clause_lits(&solver);
    let clause_ids_before = solver.cold.clause_ids.clone();
    let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
    let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

    solver.decompose();

    assert_eq!(
        solver.decompose_stats().rounds,
        0,
        "LRAT decompose dry-run must restore normal decompose stats before rejecting"
    );
    assert_eq!(
        active_clause_lits(&solver),
        clauses_before,
        "LRAT decompose dry-run sidecar must not mutate active clauses"
    );
    assert_eq!(
        solver.cold.clause_ids, clause_ids_before,
        "LRAT decompose dry-run sidecar must not rewrite proof IDs"
    );
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().added_count(),
        proof_added_before,
        "LRAT decompose dry-run sidecar must not emit proof additions"
    );
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().deleted_count(),
        proof_deleted_before,
        "LRAT decompose dry-run sidecar must not emit proof deletions"
    );

    let preflight = solver.decompose_lrat_preflight_stats();
    assert_eq!(preflight.attempts, 1);
    assert_eq!(preflight.transaction_candidates, 4);
    assert_eq!(preflight.no_substitution, 0);
    assert_eq!(preflight.empty_candidates, 0);
    assert_eq!(preflight.dry_run_emitted, 1);
    assert_eq!(preflight.dry_run_rejected, 0);
    assert_eq!(preflight.proof_obligations, 3);
    assert_eq!(preflight.reconstruction_witnesses, 1);
    let default_record = solver
        .inproc
        .preprocess_transactions
        .last_completed()
        .expect("LRAT decompose preflight transaction should be retained");
    assert_eq!(
        default_record.route_admission_packet.kind,
        RouteAdmissionPacketKind::None,
        "main rewrite route packet must stay default-off"
    );
    assert_eq!(
        default_record.route_admission_packet.status,
        RouteAdmissionPacketStatus::NotAttempted,
        "main rewrite route packet must not be attempted by default"
    );

    let sidecars = solver.decompose_lrat_dry_run_sidecars();
    assert_eq!(
        sidecars.len(),
        1,
        "LRAT decompose preflight must retain one bounded dry-run sidecar"
    );
    let sidecar = &sidecars[0];
    assert_eq!(sidecar.source_clause_id, 4);
    assert_eq!(sidecar.source_clause_lits, vec![3, 4]);
    assert_eq!(sidecar.rewritten_clause_lits, vec![1, 4]);
    assert_eq!(sidecar.planned_rewrite_add_id, 7);
    assert_eq!(sidecar.rewrite_hints, vec![5, 4]);
    assert_eq!(sidecar.source_delete_id, 4);
    assert_eq!(sidecar.equivalence_steps.len(), 1);
    let step = &sidecar.equivalence_steps[0];
    assert_eq!(step.original_lit, 3);
    assert_eq!(step.representative_lit, 1);
    assert_eq!(step.lit_to_repr_source_ids, vec![3]);
    assert_eq!(step.repr_to_lit_source_ids, vec![1, 2]);
    assert_eq!(step.planned_lit_to_repr_add_id, 5);
    assert_eq!(step.planned_repr_to_lit_add_id, 6);

    let dimacs = render_dimacs_fixture(4, &clauses);
    let replay = render_decompose_lrat_dry_run_replay(sidecar);
    verify_lrat_fixture(&dimacs, &replay);

    let artifact_dir = repo_root_for_decompose_artifacts()
        .join("target")
        .join("sat-preflight-artifacts")
        .join("decompose-9296");
    std::fs::create_dir_all(&artifact_dir).expect("create decompose sidecar artifact dir");
    let dimacs_path = artifact_dir.join("fmla-like-equivalence-chain.cnf");
    let proof_path = artifact_dir.join("fmla-like-equivalence-chain-dry-run.lrat");
    let sidecar_path = artifact_dir.join("decompose-dry-run-sidecar.json");
    std::fs::write(&dimacs_path, &dimacs).expect("write decompose dry-run DIMACS");
    std::fs::write(&proof_path, &replay).expect("write decompose dry-run LRAT replay");

    let dimacs_uri = dimacs_path.display().to_string();
    let proof_uri = proof_path.display().to_string();
    let sidecar_uri = sidecar_path.display().to_string();
    let producer_revision = producer_revision_for_decompose_artifact();
    let export = DecomposeLratDryRunExport {
        source_dimacs_uri: &dimacs_uri,
        lrat_proof_uri: &proof_uri,
        transform_transaction_uri: &sidecar_uri,
        benchmark_id: "unit:fmla-like-equivalence-chain",
        family: "FmlaEquivChain",
        num_vars: 4,
        num_clauses: clauses.len() as u64,
        producer_revision: Some(&producer_revision),
    };
    let sidecar_json = sidecar.to_decompose_equivalence_lrat_dry_run_json(&export);
    std::fs::write(
        &sidecar_path,
        format!(
            "{}\n",
            serde_json::to_string_pretty(&sidecar_json).expect("serialize decompose sidecar JSON")
        ),
    )
    .expect("write decompose dry-run JSON sidecar");

    let persisted: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(&sidecar_path).expect("read decompose dry-run JSON sidecar"),
    )
    .expect("parse persisted decompose dry-run JSON sidecar");
    assert_eq!(
        persisted["transform_transaction_uri"],
        serde_json::json!(sidecar_uri)
    );
    assert_eq!(persisted["family"], serde_json::json!("FmlaEquivChain"));
    assert_eq!(persisted["source_clause_id"], serde_json::json!(4));
    assert_eq!(persisted["planned_rewrite_add_id"], serde_json::json!(7));
    assert_eq!(
        persisted["equivalence_steps"][0]["lit_to_repr_source_ids"],
        serde_json::json!([3])
    );

    eprintln!(
        "decompose_lrat_dry_run_sidecar_json={}",
        sidecar_path.display()
    );
}

#[test]
fn test_lrat_decompose_preflight_materializer_replays_runtime_rows() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 4);
    let mut solver = Solver::with_proof_output(4, proof);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let y = Literal::positive(Variable(3));
    let clauses = vec![
        vec![x0.negated(), x1],
        vec![x1.negated(), x2],
        vec![x2.negated(), x0],
        vec![x2, y],
    ];
    for clause in &clauses {
        solver.add_clause_db(clause, false);
    }
    solver.initialize_watches();
    solver
        .inproc
        .decompose_engine
        .set_lrat_main_rewrite_materializer_preflight_enabled(true);

    let clauses_before = active_clause_lits(&solver);
    let clause_ids_before = solver.cold.clause_ids.clone();
    let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
    let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

    solver.decompose();

    assert_eq!(solver.decompose_stats().rounds, 0);
    assert_eq!(
        active_clause_lits(&solver),
        clauses_before,
        "materializer admission must not mutate LRAT decompose clauses"
    );
    assert_eq!(
        solver.cold.clause_ids, clause_ids_before,
        "materializer admission must not reserve or rewrite LRAT IDs"
    );
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().added_count(),
        proof_added_before + 3,
        "opt-in materializer replay must emit the three planned add rows"
    );
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().deleted_count(),
        proof_deleted_before + 1,
        "opt-in materializer replay must emit the planned delete row"
    );

    let preflight = solver.decompose_lrat_preflight_stats();
    assert_eq!(preflight.dry_run_emitted, 1);
    assert_eq!(preflight.proof_obligations, 3);
    assert_eq!(preflight.reconstruction_witnesses, 1);
    assert_eq!(preflight.main_rewrite_materializer_attempts, 1);
    assert_eq!(
        preflight.main_rewrite_materializer_proof_emit_records_seen,
        4
    );
    assert_eq!(preflight.main_rewrite_materializer_records, 4);
    assert_eq!(
        preflight.main_rewrite_materializer_fail_closed, 1,
        "runtime rows materialize, but route admission must fail closed without an external checker verdict"
    );
    assert_eq!(
        preflight.main_rewrite_materializer_missing_runtime_records,
        0
    );

    let proof_records = solver
        .proof_manager
        .as_ref()
        .unwrap()
        .scoped_decompose_proof_emit_records();
    assert_eq!(proof_records.len(), 4);
    assert_eq!(proof_records[0].checker_visible_id, 5);
    assert_eq!(proof_records[0].clause_lits_dimacs, vec![1, -3]);
    assert_eq!(proof_records[0].lrat_hints, vec![3]);
    assert_eq!(proof_records[1].checker_visible_id, 6);
    assert_eq!(proof_records[1].clause_lits_dimacs, vec![3, -1]);
    assert_eq!(proof_records[1].lrat_hints, vec![1, 2]);
    assert_eq!(proof_records[2].checker_visible_id, 7);
    assert_eq!(proof_records[2].clause_lits_dimacs, vec![1, 4]);
    assert_eq!(proof_records[2].lrat_hints, vec![5, 4]);
    assert_eq!(proof_records[3].checker_visible_id, 4);
    assert_eq!(proof_records[3].delete_source_id, Some(4));
    assert_eq!(proof_records[3].clause_lits_dimacs, vec![3, 4]);
    assert!(proof_records
        .iter()
        .all(|record| record.solver_runtime_emitted));
    assert!(proof_records
        .iter()
        .all(|record| !record.external_checker_verified));

    let sidecar = solver.decompose_lrat_dry_run_sidecars()[0].clone();
    let proof_text = String::from_utf8(
        solver
            .proof_manager
            .take()
            .expect("proof manager should remain installed")
            .into_output()
            .into_vec()
            .expect("flush opt-in runtime replay proof"),
    )
    .expect("LRAT proof output must be UTF-8 text");
    let add_replay = render_decompose_lrat_dry_run_replay(&sidecar);
    assert!(
        proof_text.starts_with(&add_replay),
        "runtime proof output must begin with the retained sidecar add replay"
    );
    assert!(
        proof_text.contains("8 d 4 0\n"),
        "runtime proof output must flush the retained sidecar delete row"
    );
    verify_lrat_fixture(&render_dimacs_fixture(4, &clauses), &proof_text);

    let record = solver
        .inproc
        .preprocess_transactions
        .last_completed()
        .expect("LRAT decompose preflight transaction should be retained");
    assert_eq!(record.outcome, PreprocessTransactionOutcome::FailClosed);
    assert_eq!(
        record.route_admission_packet.kind,
        RouteAdmissionPacketKind::FmlaEquivChainMainLrat
    );
    assert_eq!(
        record.route_admission_packet.status,
        RouteAdmissionPacketStatus::Rejected
    );
    assert_eq!(record.route_admission_packet.original_dimacs_rows, 1);
    assert_eq!(
        record.route_admission_packet.original_clause_authority_rows, 4,
        "each retained add/delete proof row must have source-clause authority"
    );
    assert_eq!(record.route_admission_packet.proof_obligation_rows, 4);
    assert_eq!(record.route_admission_packet.model_reconstruction_rows, 1);
    assert_eq!(
        record
            .route_admission_packet
            .external_proof_checker_verdict_artifact_rows,
        0,
        "default-off runtime path must not fabricate checker-verdict artifacts"
    );
}

#[test]
fn test_fmla_decompose_lrat_preflight_route_runs_once_without_clause_mutation() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 4);
    let mut solver = Solver::with_proof_output(4, proof);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let y = Literal::positive(Variable(3));
    for clause in [
        vec![x0.negated(), x1],
        vec![x1.negated(), x2],
        vec![x2.negated(), x0],
        vec![x2, y],
    ] {
        solver.add_clause_db(&clause, false);
    }
    solver.initialize_watches();
    solver.disable_all_inprocessing();
    solver.set_sat_comp_main_conflict_pruning(true);
    solver.set_fmla_decompose_lrat_preflight_route_enabled(true);
    solver.cold.next_inprobe_conflict = 0;
    solver.num_conflicts = 1;

    assert!(
        !solver.is_decompose_enabled(),
        "route setup must not reopen broad LRAT decompose"
    );
    let clauses_before = active_clause_lits(&solver);
    let clause_ids_before = solver.cold.clause_ids.clone();
    let reconstruction_before = solver.inproc.reconstruction.len();
    let trail_len_before = solver.trail.len();
    let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
    let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

    assert!(
        !solver.run_restart_inprocessing(),
        "Fmla preflight route is an admission dry-run, not an UNSAT derivation"
    );

    assert!(
        solver.cold.fmla_decompose_lrat_preflight_route_consumed,
        "route must be consumed after the first scheduler opportunity"
    );
    assert_eq!(solver.decompose_stats().rounds, 0);
    assert_eq!(active_clause_lits(&solver), clauses_before);
    assert_eq!(solver.cold.clause_ids, clause_ids_before);
    assert_eq!(solver.inproc.reconstruction.len(), reconstruction_before);
    assert_eq!(solver.trail.len(), trail_len_before);
    assert!(
        !solver.is_decompose_enabled(),
        "route must leave broad LRAT decompose clamped"
    );
    assert!(
        !solver
            .inproc
            .decompose_engine
            .lrat_main_rewrite_materializer_preflight_enabled(),
        "route must restore the internal materializer preflight flag"
    );
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().added_count(),
        proof_added_before + 3,
        "route should exercise the existing runtime-row materializer"
    );
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().deleted_count(),
        proof_deleted_before + 1,
        "route should exercise the existing planned delete row"
    );

    let preflight = solver.decompose_lrat_preflight_stats();
    assert_eq!(preflight.attempts, 1);
    assert_eq!(preflight.transaction_candidates, 4);
    assert_eq!(preflight.no_substitution, 0);
    assert_eq!(preflight.empty_candidates, 0);
    assert_eq!(preflight.dry_run_emitted, 1);
    assert_eq!(preflight.proof_obligations, 3);
    assert_eq!(preflight.reconstruction_witnesses, 1);
    assert_eq!(preflight.main_rewrite_materializer_attempts, 1);
    assert_eq!(preflight.main_rewrite_materializer_records, 4);
    assert_eq!(
        preflight.main_rewrite_materializer_fail_closed, 1,
        "route admission must fail closed without an external checker verdict"
    );

    solver.cold.next_inprobe_conflict = 0;
    solver.num_conflicts = solver.num_conflicts.saturating_add(1);
    assert!(
        !solver.run_restart_inprocessing(),
        "consumed Fmla preflight route must not rerun"
    );
    assert_eq!(
        solver.decompose_lrat_preflight_stats().attempts,
        1,
        "route must be exactly-once for this solver"
    );
}

#[test]
fn test_fmla_decompose_lrat_preflight_route_runs_at_solve_startup() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 8);
    let mut solver = Solver::with_proof_output(8, proof);

    for clause in fmla_guarded_equiv_fixture() {
        assert!(solver.add_clause(clause));
    }
    solver.set_preprocess_enabled(false);
    solver.set_sat_comp_main_conflict_pruning(true);
    solver.set_fmla_decompose_lrat_preflight_route_enabled(true);

    let _ = solver.solve_no_assumptions(|| true);

    assert!(
        solver.cold.fmla_decompose_lrat_preflight_route_consumed,
        "solve startup must consume the Fmla LRAT preflight route before scheduler fallback"
    );
    let preflight = solver.decompose_lrat_preflight_stats();
    assert_eq!(preflight.attempts, 1);
    assert_eq!(preflight.no_substitution, 1);
    assert_eq!(preflight.fmla_lift_attempts, 1);
    assert_eq!(preflight.fmla_lift_detected, 1);
    assert_eq!(preflight.fmla_lift_guarded_equiv_pairs, 1);
    assert_eq!(preflight.fmla_lift_source_ids_missing, 0);
    assert_eq!(preflight.fmla_lift_first_missing_source_id, 0);
}

#[test]
fn test_fmla_startup_route_materializes_support_cover_rows_before_preprocessing() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 13);
    let mut solver = Solver::with_proof_output(13, proof);
    let fixture = fmla_guarded_equiv_support_cover_fixture();

    for clause in &fixture {
        assert!(solver.add_clause(clause.clone()));
    }
    solver.set_preprocess_enabled(false);
    solver.set_sat_comp_main_conflict_pruning(true);
    solver.set_fmla_decompose_lrat_preflight_route_enabled(true);

    let mutation_epoch_before = solver.cold.clause_db_changes;
    let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
    let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

    let _ = solver.solve_no_assumptions(|| true);

    assert!(
        solver.cold.fmla_decompose_lrat_preflight_route_consumed,
        "startup route must run before scheduler-only preprocessing"
    );
    assert!(
        solver
            .inproc
            .decompose_engine
            .fmla_guarded_equiv_overlay_lrat_sidecars()
            .is_empty(),
        "support-cover rows must not require assigned guard-unit overlay rows"
    );

    let support_sidecars = solver
        .inproc
        .decompose_engine
        .fmla_guarded_equiv_support_cover_lrat_sidecars();
    assert_eq!(support_sidecars.len(), 1);
    let support_sidecar = support_sidecars[0].clone();
    assert!(
        support_sidecar.planned_add_id > fixture.len() as u64,
        "support-cover proof id must be derived, not a source clause id"
    );
    assert_eq!(support_sidecar.support_clause_id, 1);
    assert_eq!(
        support_sidecar.support_guard_lits_dimacs,
        vec![1, 2, 3, 4, 5, 6]
    );
    assert_eq!(support_sidecar.source_lit_dimacs, 7);
    assert_eq!(
        support_sidecar.destination_lits_dimacs,
        vec![8, 9, 10, 11, 12, 13]
    );
    assert_eq!(
        support_sidecar.clause_lits_dimacs,
        vec![-7, 8, 9, 10, 11, 12, 13]
    );
    assert_eq!(
        support_sidecar.directional_ternary_source_ids,
        vec![17, 19, 21, 23, 25, 27]
    );
    assert_eq!(support_sidecar.lrat_hints, vec![17, 19, 21, 23, 25, 27, 1]);
    let support_clause = dimacs_lits(&support_sidecar.clause_lits_dimacs);
    assert!(
        active_clause_exists(&solver, &support_clause),
        "support-cover runtime row should become a live solver clause"
    );
    assert_eq!(
        solver.clause_id(ClauseRef(
            active_clause_index(&solver, &support_clause) as u32
        )),
        support_sidecar.planned_add_id
    );
    assert!(
        solver.cold.clause_db_changes > mutation_epoch_before,
        "support-cover runtime row must be visible to later propagation/search"
    );

    let proof_manager = solver.proof_manager.as_ref().unwrap();
    assert_eq!(
        proof_manager.added_count(),
        proof_added_before + 1,
        "startup route should emit exactly one support-cover LRAT row"
    );
    assert_eq!(
        proof_manager.deleted_count(),
        proof_deleted_before,
        "support-cover startup route must remain add-only"
    );

    let proof_records = proof_manager.scoped_decompose_proof_emit_records();
    assert_eq!(proof_records.len(), 1);
    assert!(proof_records
        .iter()
        .all(|record| record.solver_runtime_emitted));
    assert!(proof_records
        .iter()
        .all(|record| !record.external_checker_verified));
    assert_eq!(
        proof_records[0].context.sidecar_context_token,
        "fmla-guarded-equiv-support-cover-lrat-0"
    );
    assert_eq!(
        proof_records[0].context.source_row_id,
        "fmla-guarded-equiv-support-cover-source-1"
    );
    assert_eq!(
        proof_records[0].context.obligation_id,
        "fmla-guarded-equiv-support-cover-0-0"
    );
    assert_eq!(
        proof_records[0].proof_out_record_kind,
        DecomposeProofOutRecordKind::Add
    );
    assert_eq!(
        proof_records[0].checker_visible_id,
        support_sidecar.planned_add_id
    );
    assert_eq!(
        proof_records[0].clause_lits_dimacs,
        support_sidecar.clause_lits_dimacs
    );
    assert_eq!(proof_records[0].lrat_hints, support_sidecar.lrat_hints);
    assert!(
        solver.lrat_hint_id_visible(support_sidecar.planned_add_id),
        "emitted support-cover row must be checker-visible for later proof hints"
    );

    let record = solver
        .inproc
        .preprocess_transactions
        .last_completed()
        .expect("support-cover route record should be retained");
    assert_eq!(record.mutation_epoch, mutation_epoch_before);
    assert_eq!(record.outcome, PreprocessTransactionOutcome::FailClosed);
    assert_eq!(record.proof_obligation, ProofObligationStatus::Satisfied);
    assert_eq!(
        record.route_admission_packet.kind,
        RouteAdmissionPacketKind::FmlaEquivChainMainLrat
    );
    assert_eq!(
        record.route_admission_packet.status,
        RouteAdmissionPacketStatus::Rejected
    );
    assert_eq!(record.route_admission_packet.original_dimacs_rows, 1);
    assert_eq!(
        record.route_admission_packet.original_clause_authority_rows, 1,
        "support-cover add row must ledger its support and directional ternary sources"
    );
    assert_eq!(record.route_admission_packet.proof_obligation_rows, 1);
    assert_eq!(record.route_admission_packet.model_reconstruction_rows, 0);
    assert_eq!(
        record
            .route_admission_packet
            .external_proof_checker_verdict_artifact_rows,
        0
    );
    assert!(
        record
            .fail_closed_reason
            .as_deref()
            .unwrap_or_default()
            .contains("missing external checker verdict"),
        "route must fail closed until an external checker artifact is attached"
    );

    let preflight = solver.decompose_lrat_preflight_stats();
    assert_eq!(preflight.attempts, 1);
    assert_eq!(
        preflight.no_substitution, 0,
        "Fmla support-cover rows must not fall through into the unrelated SCC no-substitution path"
    );
    assert_eq!(preflight.dry_run_rejected, 0);
    assert_eq!(preflight.fmla_lift_attempts, 1);
    assert_eq!(preflight.fmla_lift_detected, 1);
    assert_eq!(preflight.fmla_lift_guarded_equiv_pairs, 6);
    assert_eq!(preflight.fmla_lift_unique_source_ids_checked, 28);
    assert_eq!(preflight.fmla_lift_source_ids_checked, 28);
    assert_eq!(preflight.fmla_lift_source_ids_visible, 28);
    assert_eq!(preflight.fmla_lift_source_ids_missing, 0);
    assert_eq!(preflight.fmla_lift_first_missing_source_id, 0);
    assert_eq!(
        preflight.fmla_lift_proof_ready, 1,
        "all emitted support-cover LRAT rows should make the add-only proof route ready"
    );
    assert_eq!(
        preflight.fmla_lift_model_ready, 1,
        "add-only support-cover rows require no model reconstruction witness"
    );
    assert_eq!(preflight.fmla_lift_destructive_allowed, 0);
    assert_eq!(preflight.main_rewrite_materializer_attempts, 1);
    assert_eq!(
        preflight.main_rewrite_materializer_proof_emit_records_seen,
        1
    );
    assert_eq!(preflight.main_rewrite_materializer_records, 1);
    assert_eq!(
        preflight.main_rewrite_materializer_fail_closed, 1,
        "support-cover materializer must fail closed until checker evidence is attached"
    );
    assert_eq!(
        preflight.main_rewrite_materializer_missing_runtime_records,
        0
    );

    let proof_text = String::from_utf8(
        solver
            .proof_manager
            .take()
            .expect("proof manager should remain installed")
            .into_output()
            .into_vec()
            .expect("flush support-cover proof rows"),
    )
    .expect("LRAT proof output must be UTF-8 text");
    let proof_steps = ay_lrat_check::lrat_parser::parse_text_lrat(&proof_text)
        .expect("support-cover LRAT output must parse");
    assert!(
        proof_steps.iter().any(|step| matches!(
            step,
            ay_lrat_check::lrat_parser::LratStep::Add { id, clause, .. }
                if *id == support_sidecar.planned_add_id
                    && clause.iter().map(|lit| lit.to_dimacs()).collect::<Vec<_>>()
                        == vec![-7, 8, 9, 10, 11, 12, 13]
        )),
        "proof output must contain the derived support-cover row"
    );
    verify_lrat_fixture(&render_dimacs_fixture(13, &fixture), &proof_text);
}

#[test]
fn test_fmla_startup_route_rejects_hidden_support_cover_source_ids() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 13);
    let mut solver = Solver::with_proof_output(13, proof);
    let fixture = fmla_guarded_equiv_support_cover_fixture();

    for clause in &fixture {
        assert!(solver.add_clause(clause.clone()));
    }
    solver
        .proof_emit_delete(&fixture[0], 1)
        .expect("hide one-hot support source id");
    assert!(!solver.lrat_hint_id_visible(1));
    solver.set_preprocess_enabled(false);
    solver.set_sat_comp_main_conflict_pruning(true);
    solver.set_fmla_decompose_lrat_preflight_route_enabled(true);

    let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
    let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

    let _ = solver.solve_no_assumptions(|| true);

    assert!(solver.cold.fmla_decompose_lrat_preflight_route_consumed);
    assert!(
        solver
            .inproc
            .decompose_engine
            .fmla_guarded_equiv_overlay_lrat_sidecars()
            .is_empty(),
        "overlay rows must not hide missing support-cover source ids"
    );
    assert!(
        solver
            .inproc
            .decompose_engine
            .fmla_guarded_equiv_support_cover_lrat_sidecars()
            .is_empty(),
        "support-cover rows must be rejected when the support source id is hidden"
    );

    let proof_manager = solver.proof_manager.as_ref().unwrap();
    assert_eq!(proof_manager.added_count(), proof_added_before);
    assert_eq!(proof_manager.deleted_count(), proof_deleted_before);
    assert!(
        proof_manager
            .scoped_decompose_proof_emit_records()
            .is_empty(),
        "rejected hidden-support path must not emit overlay proof records"
    );
    assert!(
        solver
            .inproc
            .preprocess_transactions
            .last_completed()
            .is_none(),
        "missing source ids must fail closed before route-admission records"
    );

    let preflight = solver.decompose_lrat_preflight_stats();
    assert_eq!(preflight.fmla_lift_attempts, 1);
    assert_eq!(preflight.fmla_lift_detected, 1);
    assert_eq!(preflight.fmla_lift_unique_source_ids_checked, 28);
    assert_eq!(preflight.fmla_lift_source_ids_visible, 27);
    assert_eq!(preflight.fmla_lift_source_ids_missing, 1);
    assert_eq!(preflight.fmla_lift_first_missing_source_id, 1);
}

#[test]
fn test_fmla_startup_route_rejects_hidden_guarded_ternary_source_ids() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 13);
    let mut solver = Solver::with_proof_output(13, proof);
    let fixture = fmla_guarded_equiv_support_cover_fixture();

    for clause in &fixture {
        assert!(solver.add_clause(clause.clone()));
    }
    solver
        .proof_emit_delete(&fixture[16], 17)
        .expect("hide forward guarded-ternary source id");
    assert!(!solver.lrat_hint_id_visible(17));
    solver.set_preprocess_enabled(false);
    solver.set_sat_comp_main_conflict_pruning(true);
    solver.set_fmla_decompose_lrat_preflight_route_enabled(true);

    let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
    let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

    let _ = solver.solve_no_assumptions(|| true);

    assert!(solver.cold.fmla_decompose_lrat_preflight_route_consumed);
    assert!(
        solver
            .inproc
            .decompose_engine
            .fmla_guarded_equiv_overlay_lrat_sidecars()
            .is_empty(),
        "overlay rows must not hide missing support-cover ternary source ids"
    );
    assert!(
        solver
            .inproc
            .decompose_engine
            .fmla_guarded_equiv_support_cover_lrat_sidecars()
            .is_empty(),
        "support-cover rows must be rejected when a directional ternary source id is hidden"
    );

    let proof_manager = solver.proof_manager.as_ref().unwrap();
    assert_eq!(
        proof_manager.added_count(),
        proof_added_before,
        "hidden ternary source must prevent support-cover LRAT rows"
    );
    assert_eq!(proof_manager.deleted_count(), proof_deleted_before);
    assert!(
        proof_manager
            .scoped_decompose_proof_emit_records()
            .is_empty(),
        "rejected hidden-ternary path must not emit overlay proof records"
    );
    assert!(
        solver
            .inproc
            .preprocess_transactions
            .last_completed()
            .is_none(),
        "missing directional source ids must fail closed before route-admission records"
    );

    let preflight = solver.decompose_lrat_preflight_stats();
    assert_eq!(preflight.fmla_lift_attempts, 1);
    assert_eq!(preflight.fmla_lift_detected, 1);
    assert_eq!(preflight.fmla_lift_unique_source_ids_checked, 28);
    assert_eq!(preflight.fmla_lift_source_ids_visible, 27);
    assert_eq!(preflight.fmla_lift_source_ids_missing, 1);
    assert_eq!(preflight.fmla_lift_first_missing_source_id, 17);
}

#[test]
fn test_fmla_guarded_equiv_lift_preflight_telemetry_stays_closed() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 8);
    let mut solver = Solver::with_proof_output(8, proof);

    for clause in fmla_guarded_equiv_fixture() {
        assert!(solver.add_clause(clause));
    }
    solver.initialize_watches();
    solver.disable_all_inprocessing();
    solver.set_sat_comp_main_conflict_pruning(true);
    solver.set_fmla_decompose_lrat_preflight_route_enabled(true);
    solver.cold.next_inprobe_conflict = 0;
    solver.num_conflicts = 1;

    let clauses_before = active_clause_lits(&solver);
    let clause_ids_before = solver.cold.clause_ids.clone();
    let reconstruction_before = solver.inproc.reconstruction.len();
    let trail_len_before = solver.trail.len();

    assert!(
        !solver.run_restart_inprocessing(),
        "guarded-equivalence telemetry must not derive a solver result"
    );

    assert!(solver.cold.fmla_decompose_lrat_preflight_route_consumed);
    assert_eq!(active_clause_lits(&solver), clauses_before);
    assert_eq!(solver.cold.clause_ids, clause_ids_before);
    assert_eq!(solver.inproc.reconstruction.len(), reconstruction_before);
    assert_eq!(solver.trail.len(), trail_len_before);

    let preflight = solver.decompose_lrat_preflight_stats();
    assert_eq!(preflight.attempts, 1);
    assert_eq!(preflight.no_substitution, 1);
    assert_eq!(preflight.transaction_candidates, 0);
    assert_eq!(preflight.fmla_lift_attempts, 1);
    assert_eq!(preflight.fmla_lift_detected, 1);
    assert_eq!(preflight.fmla_lift_rejection_code, 0);
    assert_eq!(preflight.fmla_lift_onehot_groups, 1);
    assert_eq!(preflight.fmla_lift_guarded_equiv_pairs, 1);
    assert_eq!(preflight.fmla_lift_guarded_equiv_guards, 1);
    assert_eq!(preflight.fmla_lift_directional_ternary_witnesses, 2);
    assert_eq!(preflight.fmla_lift_touched_vars, 8);
    assert_eq!(preflight.fmla_lift_runtime_records, 6);
    assert_eq!(preflight.fmla_lift_witness_checker_passed, 1);
    assert_eq!(preflight.fmla_lift_all_witness_pairs_checked, 1);
    assert_eq!(preflight.fmla_lift_all_witness_pairs_missing_guard_group, 0);
    assert_eq!(preflight.fmla_lift_source_id_refs_checked, 18);
    assert_eq!(preflight.fmla_lift_unique_source_ids_checked, 18);
    assert_eq!(preflight.fmla_lift_source_ids_checked, 18);
    assert_eq!(
        preflight.fmla_lift_source_ids_visible + preflight.fmla_lift_source_ids_missing,
        preflight.fmla_lift_unique_source_ids_checked
    );
    if preflight.fmla_lift_source_ids_missing == 0 {
        assert_eq!(preflight.fmla_lift_first_missing_source_id, 0);
    } else {
        assert!(preflight.fmla_lift_first_missing_source_id > 0);
    }
    assert_eq!(preflight.fmla_lift_proof_ready, 0);
    assert_eq!(preflight.fmla_lift_model_ready, 0);
    assert_eq!(preflight.fmla_lift_destructive_allowed, 0);
}

#[test]
fn test_real_fmla_guarded_equiv_overlay_plans_support_cover_without_guard_units() {
    let Some(formula) = fmla_equiv_chain_data_formula() else {
        return;
    };
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), formula.num_clauses as u64);
    let mut solver = Solver::with_proof_output(formula.num_vars, proof);

    for clause in &formula.clauses {
        assert!(solver.add_clause(clause.clone()));
    }

    let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
    let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

    solver.record_fmla_guarded_equiv_lift_preflight();
    let preflight = solver.decompose_lrat_preflight_stats();
    assert_eq!(
        preflight.fmla_lift_detected, 1,
        "real Fmla fixture must exercise the guarded-equivalence route surface"
    );
    assert!(
        preflight.fmla_lift_guarded_equiv_pairs > 0,
        "real Fmla fixture should expose guarded-equivalence candidates"
    );

    solver.record_fmla_guarded_equiv_overlay_lrat_packet();
    assert!(
        solver
            .inproc
            .decompose_engine
            .fmla_guarded_equiv_overlay_lrat_sidecars()
            .is_empty(),
        "overlay binaries require assigned solver-visible level-0 guard-unit proof IDs"
    );
    let support_sidecars = solver
        .inproc
        .decompose_engine
        .fmla_guarded_equiv_support_cover_lrat_sidecars();
    assert_eq!(
        support_sidecars.len(),
        FMLA_MAIN_LRAT_PREFLIGHT_MAX_PROOF_ROWS,
        "real Fmla fixture should retain a bounded proof-safe support-cover prefix"
    );
    let representative = support_sidecars
        .iter()
        .find(|sidecar| {
            sidecar.support_clause_id == 2_593
                && sidecar.clause_lits_dimacs
                    == vec![-3_889, 5_185, 5_401, 5_617, 5_833, 6_049, 6_265]
        })
        .expect("real Fmla fixture should retain representative support-cover sidecar");
    assert_eq!(
        representative.support_guard_lits_dimacs,
        vec![27_217, 27_218, 27_220, 27_223, 27_227, 27_232]
    );
    assert_eq!(
        representative.directional_ternary_source_ids,
        vec![173_569, 174_001, 174_433, 174_865, 175_297, 175_729]
    );
    assert_eq!(
        representative.lrat_hints,
        vec![173_569, 174_001, 174_433, 174_865, 175_297, 175_729, 2_593]
    );

    assert_eq!(
        solver.proof_manager.as_ref().unwrap().added_count(),
        proof_added_before,
        "packet planning must not emit support-cover add rows until runtime replay is enabled"
    );
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().deleted_count(),
        proof_deleted_before,
        "guarded-equivalence overlay must remain add-only even when rejected"
    );
    assert!(
        solver
            .proof_manager
            .as_ref()
            .unwrap()
            .scoped_decompose_proof_emit_records()
            .is_empty(),
        "packet planning alone must not create scoped runtime proof-output records"
    );
    assert!(
        solver
            .inproc
            .preprocess_transactions
            .last_completed()
            .is_none(),
        "packet planning alone must not fabricate a route-admission transaction"
    );
}

#[test]
fn test_fmla_guarded_equiv_overlay_materializes_derived_guard_unit_proof_ids() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 9);
    let mut solver = Solver::with_proof_output(9, proof);
    let mut fixture = fmla_guarded_equiv_fixture();
    let guard = Literal::positive(Variable(0));
    let support = Literal::positive(Variable(8));
    fixture.push(vec![support]);
    fixture.push(vec![support.negated(), guard]);

    for clause in &fixture {
        assert!(solver.add_clause(clause.clone()));
    }
    solver.initialize_watches();
    let support_unit_idx = active_clause_index(&solver, &[support]);
    let support_unit_id = solver.clause_id(ClauseRef(support_unit_idx as u32));
    if !solver.var_is_assigned(support.variable().index()) {
        solver.enqueue(support, None);
    }
    solver.record_unit_proof_id_for_lit(support, support_unit_id);
    let guard_reason_idx = active_clause_index(&solver, &[support.negated(), guard]);
    solver.enqueue(guard, Some(ClauseRef(guard_reason_idx as u32)));
    assert_eq!(
        solver.lit_value(guard),
        Some(true),
        "support unit reason must assign the overlay guard at level 0"
    );

    let guard_reason_id = solver.clause_id(ClauseRef(guard_reason_idx as u32));
    assert_eq!(
        solver.level0_var_proof_id_for_lit(guard),
        None,
        "binary-implied guard needs a materialized unit proof ID before overlay LRAT hints"
    );

    let clauses_before = active_clause_lits(&solver);
    let clause_ids_before = solver.cold.clause_ids.clone();
    let reconstruction_before = solver.inproc.reconstruction.len();
    let trail_len_before = solver.trail.len();
    let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
    let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

    solver.record_fmla_guarded_equiv_lift_preflight();
    solver.record_fmla_guarded_equiv_overlay_lrat_packet();

    let guard_unit_id = solver
        .level0_var_proof_id_for_lit(guard)
        .expect("overlay packet should materialize a visible guard unit proof ID");
    assert_ne!(
        guard_unit_id, guard_reason_id,
        "overlay hints must use the derived unit proof, not the binary reason clause"
    );
    let proof_added_after_packet = solver.proof_manager.as_ref().unwrap().added_count();
    assert!(
        proof_added_after_packet > proof_added_before,
        "packet construction should materialize missing level-0 unit proof IDs"
    );
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().deleted_count(),
        proof_deleted_before,
        "guard unit materialization must not delete proof rows"
    );

    assert_eq!(active_clause_lits(&solver), clauses_before);
    assert_eq!(solver.cold.clause_ids, clause_ids_before);
    assert_eq!(solver.inproc.reconstruction.len(), reconstruction_before);
    assert_eq!(solver.trail.len(), trail_len_before);

    let sidecars = solver
        .inproc
        .decompose_engine
        .fmla_guarded_equiv_overlay_lrat_sidecars();
    assert_eq!(sidecars.len(), 1);
    let sidecar = sidecars[0].clone();
    assert_eq!(sidecar.guard_unit_proof_id, guard_unit_id);
    assert_eq!(sidecar.forward_binary.lrat_hints, vec![17, guard_unit_id]);
    assert_eq!(sidecar.reverse_binary.lrat_hints, vec![18, guard_unit_id]);

    solver
        .inproc
        .decompose_engine
        .set_lrat_main_rewrite_materializer_preflight_enabled(true);
    assert!(solver.try_emit_fmla_guarded_equiv_overlay_lrat_runtime_rows());
    solver
        .inproc
        .decompose_engine
        .set_lrat_main_rewrite_materializer_preflight_enabled(false);

    let forward_clause = dimacs_lits(&sidecar.forward_binary.clause_lits_dimacs);
    let reverse_clause = dimacs_lits(&sidecar.reverse_binary.clause_lits_dimacs);
    assert_eq!(
        active_clause_lits(&solver).len(),
        clauses_before.len() + 2,
        "overlay proof-output rows should become live solver clauses"
    );
    assert!(active_clause_exists(&solver, &forward_clause));
    assert!(active_clause_exists(&solver, &reverse_clause));
    assert_eq!(
        solver.clause_id(ClauseRef(
            active_clause_index(&solver, &forward_clause) as u32
        )),
        sidecar.forward_binary.planned_add_id
    );
    assert_eq!(
        solver.clause_id(ClauseRef(
            active_clause_index(&solver, &reverse_clause) as u32
        )),
        sidecar.reverse_binary.planned_add_id
    );
    assert!(
        solver.cold.clause_ids.starts_with(&clause_ids_before),
        "installing overlay rows must preserve existing clause IDs"
    );
    assert_eq!(solver.inproc.reconstruction.len(), reconstruction_before);
    assert_eq!(solver.trail.len(), trail_len_before);
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().added_count(),
        proof_added_after_packet + 2,
        "both overlay binaries should be emitted and installed after guard materialization"
    );
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().deleted_count(),
        proof_deleted_before,
        "guarded-equivalence overlay must remain add-only"
    );
    #[cfg(debug_assertions)]
    assert_eq!(
        solver.cold.pending_forward_check, None,
        "installing emitted overlay rows must discharge the forward-check obligation"
    );
    assert_eq!(
        solver.cold.next_clause_id,
        sidecar.reverse_binary.planned_add_id + 1,
        "installing overlay rows must leave the next LRAT id after the emitted rows"
    );
    assert_eq!(
        solver
            .proof_manager
            .as_ref()
            .unwrap()
            .planned_forward_add_ids(1)
            .expect("next planned proof id")[0],
        sidecar.reverse_binary.planned_add_id + 1,
        "proof writer and clause DB must remain synchronized after install"
    );
    let proof_records = solver
        .proof_manager
        .as_ref()
        .unwrap()
        .scoped_decompose_proof_emit_records();
    assert_eq!(proof_records.len(), 2);
    assert!(proof_records
        .iter()
        .all(|record| record.proof_out_record_kind == DecomposeProofOutRecordKind::Add));
    assert!(proof_records
        .iter()
        .all(|record| record.solver_runtime_emitted));
    assert!(proof_records
        .iter()
        .all(|record| !record.external_checker_verified));

    let record = solver
        .inproc
        .preprocess_transactions
        .last_completed()
        .expect("overlay route record should be retained");
    assert_eq!(record.outcome, PreprocessTransactionOutcome::FailClosed);
    assert_eq!(record.proof_obligation, ProofObligationStatus::Satisfied);
    assert_eq!(
        record.route_admission_packet.kind,
        RouteAdmissionPacketKind::FmlaEquivChainMainLrat
    );
    assert_eq!(
        record.route_admission_packet.status,
        RouteAdmissionPacketStatus::Rejected
    );
    assert_eq!(record.route_admission_packet.original_dimacs_rows, 1);
    assert_eq!(
        record.route_admission_packet.original_clause_authority_rows, 2,
        "overlay binary rows must ledger their guarded ternary and guard-unit sources"
    );
    assert_eq!(record.route_admission_packet.proof_obligation_rows, 2);

    let proof_text = String::from_utf8(
        solver
            .proof_manager
            .take()
            .expect("proof manager should remain installed")
            .into_output()
            .into_vec()
            .expect("flush overlay proof rows"),
    )
    .expect("LRAT proof output must be UTF-8 text");
    verify_lrat_fixture(&render_dimacs_fixture(9, &fixture), &proof_text);
}

#[test]
fn test_fmla_guarded_equiv_overlay_lrat_sidecar_stays_add_only() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 8);
    let mut solver = Solver::with_proof_output(8, proof);
    let mut fixture = fmla_guarded_equiv_fixture();
    let guard = Literal::positive(Variable(0));
    fixture.push(vec![guard]);

    for clause in &fixture {
        assert!(solver.add_clause(clause.clone()));
    }
    solver.initialize_watches();
    let unit_idx = active_clause_index(&solver, &[guard]);
    let guard_unit_id = solver.clause_id(ClauseRef(unit_idx as u32));
    if !solver.var_is_assigned(guard.variable().index()) {
        solver.enqueue(guard, None);
    }
    solver.record_unit_proof_id_for_lit(guard, guard_unit_id);

    let clauses_before = active_clause_lits(&solver);
    let clause_ids_before = solver.cold.clause_ids.clone();
    let reconstruction_before = solver.inproc.reconstruction.len();
    let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
    let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

    solver.record_fmla_guarded_equiv_lift_preflight();
    solver.record_fmla_guarded_equiv_overlay_lrat_packet();

    assert_eq!(active_clause_lits(&solver), clauses_before);
    assert_eq!(solver.cold.clause_ids, clause_ids_before);
    assert_eq!(solver.inproc.reconstruction.len(), reconstruction_before);
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().added_count(),
        proof_added_before,
        "overlay packet is retained as planned rows only"
    );
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().deleted_count(),
        proof_deleted_before,
        "guarded-equivalence overlay must not fabricate delete rows"
    );

    let sidecars = solver
        .inproc
        .decompose_engine
        .fmla_guarded_equiv_overlay_lrat_sidecars();
    assert_eq!(sidecars.len(), 1);
    let sidecar = &sidecars[0];
    assert_eq!(sidecar.guard_lit_dimacs, 1);
    assert_eq!(sidecar.lhs_lit_dimacs, 7);
    assert_eq!(sidecar.rhs_lit_dimacs, 8);
    assert_eq!(sidecar.guard_unit_proof_id, guard_unit_id);
    assert_eq!(sidecar.forward_binary.clause_lits_dimacs, vec![-7, 8]);
    assert_eq!(sidecar.reverse_binary.clause_lits_dimacs, vec![-8, 7]);
    assert_eq!(sidecar.forward_binary.guarded_ternary_source_id, 17);
    assert_eq!(sidecar.reverse_binary.guarded_ternary_source_id, 18);
    assert_eq!(sidecar.forward_binary.lrat_hints, vec![17, guard_unit_id]);
    assert_eq!(sidecar.reverse_binary.lrat_hints, vec![18, guard_unit_id]);
    assert_eq!(
        sidecar.reverse_binary.planned_add_id,
        sidecar.forward_binary.planned_add_id + 1
    );

    let dimacs = render_dimacs_fixture(8, &fixture);
    let lrat = render_fmla_guarded_equiv_overlay_lrat_replay(sidecar);
    verify_lrat_fixture(&dimacs, &lrat);

    let preflight = solver.decompose_lrat_preflight_stats();
    assert_eq!(preflight.fmla_lift_proof_ready, 0);
    assert_eq!(preflight.fmla_lift_model_ready, 0);
    assert_eq!(preflight.fmla_lift_destructive_allowed, 0);
}

#[test]
fn test_fmla_guarded_equiv_overlay_lrat_emits_add_rows_as_solver_clauses() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 8);
    let mut solver = Solver::with_proof_output(8, proof);
    let mut fixture = fmla_guarded_equiv_fixture();
    let guard = Literal::positive(Variable(0));
    fixture.push(vec![guard]);

    for clause in &fixture {
        assert!(solver.add_clause(clause.clone()));
    }
    solver.initialize_watches();
    let unit_idx = active_clause_index(&solver, &[guard]);
    let guard_unit_id = solver.clause_id(ClauseRef(unit_idx as u32));
    if !solver.var_is_assigned(guard.variable().index()) {
        solver.enqueue(guard, None);
    }
    solver.record_unit_proof_id_for_lit(guard, guard_unit_id);

    let clauses_before = active_clause_lits(&solver);
    let clause_ids_before = solver.cold.clause_ids.clone();
    let reconstruction_before = solver.inproc.reconstruction.len();
    let trail_len_before = solver.trail.len();
    let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
    let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

    solver.record_fmla_guarded_equiv_lift_preflight();
    solver.record_fmla_guarded_equiv_overlay_lrat_packet();
    let sidecar = solver
        .inproc
        .decompose_engine
        .fmla_guarded_equiv_overlay_lrat_sidecars()[0]
        .clone();
    solver
        .inproc
        .decompose_engine
        .set_lrat_main_rewrite_materializer_preflight_enabled(true);
    assert!(solver.try_emit_fmla_guarded_equiv_overlay_lrat_runtime_rows());
    solver
        .inproc
        .decompose_engine
        .set_lrat_main_rewrite_materializer_preflight_enabled(false);

    let forward_clause = dimacs_lits(&sidecar.forward_binary.clause_lits_dimacs);
    let reverse_clause = dimacs_lits(&sidecar.reverse_binary.clause_lits_dimacs);
    assert_eq!(
        active_clause_lits(&solver).len(),
        clauses_before.len() + 2,
        "overlay proof-output rows should become live solver clauses"
    );
    assert!(active_clause_exists(&solver, &forward_clause));
    assert!(active_clause_exists(&solver, &reverse_clause));
    assert_eq!(
        solver.clause_id(ClauseRef(
            active_clause_index(&solver, &forward_clause) as u32
        )),
        sidecar.forward_binary.planned_add_id
    );
    assert_eq!(
        solver.clause_id(ClauseRef(
            active_clause_index(&solver, &reverse_clause) as u32
        )),
        sidecar.reverse_binary.planned_add_id
    );
    assert!(
        solver.cold.clause_ids.starts_with(&clause_ids_before),
        "installing overlay rows must preserve existing clause IDs"
    );
    assert_eq!(solver.inproc.reconstruction.len(), reconstruction_before);
    assert_eq!(solver.trail.len(), trail_len_before);
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().added_count(),
        proof_added_before + 2,
        "overlay proof-output slice should emit both retained add rows"
    );
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().deleted_count(),
        proof_deleted_before,
        "overlay proof-output slice must remain add-only"
    );
    #[cfg(debug_assertions)]
    assert_eq!(
        solver.cold.pending_forward_check, None,
        "installing emitted overlay rows must discharge the forward-check obligation"
    );
    assert_eq!(
        solver.cold.next_clause_id,
        sidecar.reverse_binary.planned_add_id + 1,
        "installing overlay rows must leave the next LRAT id after the emitted rows"
    );
    assert_eq!(
        solver
            .proof_manager
            .as_ref()
            .unwrap()
            .planned_forward_add_ids(1)
            .expect("next planned proof id")[0],
        sidecar.reverse_binary.planned_add_id + 1,
        "proof writer and clause DB must remain synchronized after install"
    );
    let proof_records = solver
        .proof_manager
        .as_ref()
        .unwrap()
        .scoped_decompose_proof_emit_records();
    assert_eq!(
        proof_records.len(),
        2,
        "overlay add rows must be bound to scoped runtime proof records"
    );
    assert_eq!(
        proof_records[0].context.sidecar_context_token,
        "fmla-guarded-equiv-overlay-lrat-0"
    );
    assert_eq!(proof_records[0].context.sidecar_row_index, 0);
    assert_eq!(
        proof_records[0].context.source_row_id,
        "fmla-guarded-equiv-overlay-source-17"
    );
    assert_eq!(
        proof_records[0].context.obligation_id,
        "fmla-guarded-equiv-overlay-0-0-forward"
    );
    assert_eq!(
        proof_records[1].context.source_row_id,
        "fmla-guarded-equiv-overlay-source-18"
    );
    assert_eq!(
        proof_records[1].context.obligation_id,
        "fmla-guarded-equiv-overlay-0-0-reverse"
    );
    assert_eq!(
        proof_records[0].proof_out_record_kind,
        DecomposeProofOutRecordKind::Add
    );
    assert_eq!(proof_records[0].proof_field, "derived_clause_proof_steps");
    assert_eq!(
        proof_records[0].checker_visible_id,
        sidecar.forward_binary.planned_add_id
    );
    assert_eq!(
        proof_records[0].clause_lits_dimacs,
        sidecar.forward_binary.clause_lits_dimacs
    );
    assert_eq!(
        proof_records[0].lrat_hints,
        sidecar.forward_binary.lrat_hints
    );
    assert_eq!(
        proof_records[1].checker_visible_id,
        sidecar.reverse_binary.planned_add_id
    );
    assert_eq!(
        proof_records[1].clause_lits_dimacs,
        sidecar.reverse_binary.clause_lits_dimacs
    );
    assert_eq!(
        proof_records[1].lrat_hints,
        sidecar.reverse_binary.lrat_hints
    );
    assert!(proof_records
        .iter()
        .all(|record| record.solver_runtime_emitted));
    assert!(proof_records
        .iter()
        .all(|record| !record.external_checker_verified));

    let record = solver
        .inproc
        .preprocess_transactions
        .last_completed()
        .expect("overlay route record should be retained");
    assert_eq!(record.outcome, PreprocessTransactionOutcome::FailClosed);
    assert_eq!(record.proof_obligation, ProofObligationStatus::Satisfied);
    assert_eq!(
        record.route_admission_packet.kind,
        RouteAdmissionPacketKind::FmlaEquivChainMainLrat
    );
    assert_eq!(
        record.route_admission_packet.status,
        RouteAdmissionPacketStatus::Rejected
    );
    assert_eq!(record.route_admission_packet.original_dimacs_rows, 1);
    assert_eq!(
        record.route_admission_packet.original_clause_authority_rows, 2,
        "overlay binary rows must ledger their guarded ternary and guard-unit sources"
    );
    assert_eq!(record.route_admission_packet.proof_obligation_rows, 2);
    assert_eq!(record.route_admission_packet.model_reconstruction_rows, 0);
    assert_eq!(
        record
            .route_admission_packet
            .external_proof_checker_verdict_artifact_rows,
        0
    );

    let proof_text = String::from_utf8(
        solver
            .proof_manager
            .take()
            .expect("proof manager should remain installed")
            .into_output()
            .into_vec()
            .expect("flush overlay proof rows"),
    )
    .expect("LRAT proof output must be UTF-8 text");
    assert_eq!(
        proof_text,
        render_fmla_guarded_equiv_overlay_lrat_replay(&sidecar)
    );
    verify_lrat_fixture(&render_dimacs_fixture(8, &fixture), &proof_text);

    let preflight = solver.decompose_lrat_preflight_stats();
    assert_eq!(
        preflight.fmla_lift_proof_ready, 1,
        "all emitted overlay LRAT rows should make the add-only proof route ready"
    );
    assert_eq!(
        preflight.fmla_lift_model_ready, 1,
        "add-only overlay rows require no model reconstruction witness"
    );
    assert_eq!(preflight.fmla_lift_destructive_allowed, 0);
}

#[test]
fn test_fmla_guarded_equiv_overlay_lrat_planned_id_mismatch_does_not_install_clause() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 8);
    let mut solver = Solver::with_proof_output(8, proof);
    let mut fixture = fmla_guarded_equiv_fixture();
    let guard = Literal::positive(Variable(0));
    fixture.push(vec![guard]);

    for clause in &fixture {
        assert!(solver.add_clause(clause.clone()));
    }
    solver.initialize_watches();
    let unit_idx = active_clause_index(&solver, &[guard]);
    let guard_unit_id = solver.clause_id(ClauseRef(unit_idx as u32));
    if !solver.var_is_assigned(guard.variable().index()) {
        solver.enqueue(guard, None);
    }
    solver.record_unit_proof_id_for_lit(guard, guard_unit_id);

    solver.record_fmla_guarded_equiv_lift_preflight();
    solver.record_fmla_guarded_equiv_overlay_lrat_packet();
    let mut sidecars = solver
        .inproc
        .decompose_engine
        .fmla_guarded_equiv_overlay_lrat_sidecars()
        .to_vec();
    let original_sidecar = sidecars[0].clone();
    sidecars[0].forward_binary.planned_add_id += 99;
    solver
        .inproc
        .decompose_engine
        .set_fmla_guarded_equiv_overlay_lrat_sidecars(sidecars);

    let clauses_before = active_clause_lits(&solver);
    let clause_ids_before = solver.cold.clause_ids.clone();
    let clause_db_changes_before = solver.cold.clause_db_changes;
    let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
    let forward_clause = dimacs_lits(&original_sidecar.forward_binary.clause_lits_dimacs);
    let reverse_clause = dimacs_lits(&original_sidecar.reverse_binary.clause_lits_dimacs);

    solver
        .inproc
        .decompose_engine
        .set_lrat_main_rewrite_materializer_preflight_enabled(true);
    assert!(solver.try_emit_fmla_guarded_equiv_overlay_lrat_runtime_rows());
    solver
        .inproc
        .decompose_engine
        .set_lrat_main_rewrite_materializer_preflight_enabled(false);

    assert_eq!(
        active_clause_lits(&solver),
        clauses_before,
        "planned-ID mismatch must fail before mutating the live clause DB"
    );
    assert_eq!(solver.cold.clause_ids, clause_ids_before);
    assert_eq!(solver.cold.clause_db_changes, clause_db_changes_before);
    assert!(!active_clause_exists(&solver, &forward_clause));
    assert!(!active_clause_exists(&solver, &reverse_clause));
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().added_count(),
        proof_added_before,
        "planned-ID mismatch must fail before emitting an LRAT row"
    );
    #[cfg(debug_assertions)]
    assert_eq!(solver.cold.pending_forward_check, None);
}

#[test]
fn test_fmla_support_cover_lrat_planned_id_mismatch_does_not_install_clause() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 13);
    let mut solver = Solver::with_proof_output(13, proof);
    let fixture = fmla_guarded_equiv_support_cover_fixture();

    for clause in &fixture {
        assert!(solver.add_clause(clause.clone()));
    }

    solver.record_fmla_guarded_equiv_lift_preflight();
    solver.record_fmla_guarded_equiv_overlay_lrat_packet();
    assert!(
        solver
            .inproc
            .decompose_engine
            .fmla_guarded_equiv_overlay_lrat_sidecars()
            .is_empty(),
        "support-cover fixture should not need overlay guard-unit rows"
    );
    let mut support_sidecars = solver
        .inproc
        .decompose_engine
        .fmla_guarded_equiv_support_cover_lrat_sidecars()
        .to_vec();
    let original_sidecar = support_sidecars[0].clone();
    support_sidecars[0].planned_add_id += 99;
    solver
        .inproc
        .decompose_engine
        .set_fmla_guarded_equiv_support_cover_lrat_sidecars(support_sidecars);

    let clauses_before = active_clause_lits(&solver);
    let clause_ids_before = solver.cold.clause_ids.clone();
    let clause_db_changes_before = solver.cold.clause_db_changes;
    let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
    let support_clause = dimacs_lits(&original_sidecar.clause_lits_dimacs);

    solver
        .inproc
        .decompose_engine
        .set_lrat_main_rewrite_materializer_preflight_enabled(true);
    assert!(solver.try_emit_fmla_guarded_equiv_overlay_lrat_runtime_rows());
    solver
        .inproc
        .decompose_engine
        .set_lrat_main_rewrite_materializer_preflight_enabled(false);

    assert_eq!(
        active_clause_lits(&solver),
        clauses_before,
        "support-cover planned-ID mismatch must fail before mutating the live clause DB"
    );
    assert_eq!(solver.cold.clause_ids, clause_ids_before);
    assert_eq!(solver.cold.clause_db_changes, clause_db_changes_before);
    assert!(!active_clause_exists(&solver, &support_clause));
    assert_eq!(
        solver.proof_manager.as_ref().unwrap().added_count(),
        proof_added_before,
        "support-cover planned-ID mismatch must fail before emitting an LRAT row"
    );
    #[cfg(debug_assertions)]
    assert_eq!(solver.cold.pending_forward_check, None);
}

#[test]
fn test_lrat_decompose_preflight_reports_no_substitution_empty_exit() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 3);
    let mut solver = Solver::with_proof_output(3, proof);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    for clause in [vec![x0, x1], vec![x1.negated(), x2]] {
        solver.add_clause_db(&clause, false);
    }
    solver.initialize_watches();

    solver.decompose();

    let preflight = solver.decompose_lrat_preflight_stats();
    assert_eq!(preflight.attempts, 1);
    assert_eq!(preflight.no_substitution, 1);
    assert_eq!(preflight.transaction_candidates, 0);
    assert_eq!(preflight.empty_candidates, 0);
    assert_eq!(preflight.dry_run_emitted, 0);
    assert_eq!(preflight.dry_run_rejected, 1);
    assert!(
        solver
            .inproc
            .preprocess_transactions
            .last_completed()
            .is_none(),
        "no-substitution LRAT preflight should not open a transaction"
    );
}

#[test]
fn test_decompose_rewrite_includes_root_false_literal() {
    let mut solver: Solver = Solver::new(5);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let a = Literal::positive(Variable(2));
    let y = Literal::positive(Variable(3));
    let z = Literal::positive(Variable(4));

    // a and (not-a or not-y) propagate y=false at level 0.
    solver.add_clause(vec![a]);
    solver.add_clause(vec![a.negated(), y.negated()]);

    // x0 equiv x1, so (x1 or y or z) rewrites to (x0 or z) after dropping y.
    solver.add_clause(vec![x1.negated(), x0]);
    solver.add_clause(vec![x0.negated(), x1]);
    solver.add_clause(vec![x1, y, z]);

    solver.initialize_watches();
    assert!(
        solver.process_initial_clauses().is_none(),
        "initial units should not conflict"
    );
    assert!(
        !solver.propagate_check_unsat(),
        "root propagation should assign y=false without conflict"
    );
    assert_eq!(
        solver.get_var_assignment(y.variable().index()),
        Some(false),
        "setup must establish the root-false literal used by decompose"
    );

    solver.decompose();

    let rewritten_exists = solver.arena.indices().any(|idx| {
        solver.arena.is_active(idx) && solver.arena.len_of(idx) == 2 && {
            let lits = solver.arena.literals(idx);
            lits.contains(&x0) && lits.contains(&z)
        }
    });
    assert!(
        rewritten_exists,
        "decompose should rewrite (x1 | y | z) into an active binary (x0 | z)"
    );
}

/// Verify decompose rewrites a clause via a transitive 3-variable equivalence
/// chain: x0 -> x1 -> x2 -> x0 forms a 3-variable SCC. Clause (x2 | y)
/// rewrites to (x0 | y).
///
/// Reference: CaDiCaL decompose.cpp:436-676, #4606.
#[test]
fn test_decompose_transitive_chain_rewrites_clause() {
    let mut solver: Solver = Solver::new(4);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let y = Literal::positive(Variable(3));

    // Transitive chain: x0 -> x1 -> x2 -> x0 (all equivalent).
    solver.add_clause(vec![x0.negated(), x1]);
    solver.add_clause(vec![x1.negated(), x2]);
    solver.add_clause(vec![x2.negated(), x0]);
    // Reverse direction to complete the SCC:
    solver.add_clause(vec![x1.negated(), x0]);
    solver.add_clause(vec![x2.negated(), x1]);
    solver.add_clause(vec![x0.negated(), x2]);

    // Target clause to be rewritten: (x2 | y) -> (x0 | y)
    solver.add_clause(vec![x2, y]);

    solver.initialize_watches();
    assert!(
        solver.process_initial_clauses().is_none(),
        "no initial conflicts expected"
    );

    solver.decompose();

    // Verify the rewritten clause (x0 | y) exists in the clause DB.
    let rewritten = solver.arena.indices().any(|idx| {
        solver.arena.is_active(idx) && solver.arena.len_of(idx) == 2 && {
            let lits = solver.arena.literals(idx);
            lits.contains(&x0) && lits.contains(&y)
        }
    });
    assert!(rewritten, "decompose should rewrite (x2 | y) into (x0 | y)");
}

/// Verify that decompose rewrites a ternary clause to a binary via
/// transitive substitution and duplicate removal.
///
/// Setup: x0 equiv x1. Clause (x0 | x1 | y) rewrites to (x0 | x0 | y)
/// after substitution, then deduplicates to (x0 | y).
///
/// Reference: CaDiCaL decompose.cpp:596-639 (shrinking path), #4606.
#[test]
fn test_decompose_duplicate_removal_after_substitution() {
    let mut solver: Solver = Solver::new(3);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let y = Literal::positive(Variable(2));

    // x0 equiv x1 via binary implications.
    solver.add_clause(vec![x0.negated(), x1]); // x0 -> x1
    solver.add_clause(vec![x1.negated(), x0]); // x1 -> x0

    // Clause containing both x0 and x1: after substitution x1->x0,
    // becomes (x0 | x0 | y) which should deduplicate to (x0 | y).
    solver.add_clause(vec![x0, x1, y]);

    solver.initialize_watches();
    assert!(
        solver.process_initial_clauses().is_none(),
        "no initial conflicts expected"
    );

    solver.decompose();

    // Verify the shortened clause (x0 | y) exists.
    let shortened = solver.arena.indices().any(|idx| {
        solver.arena.is_active(idx) && solver.arena.len_of(idx) == 2 && {
            let lits = solver.arena.literals(idx);
            lits.contains(&x0) && lits.contains(&y)
        }
    });
    assert!(
        shortened,
        "decompose should produce (x0 | y) from (x0 | x1 | y) after          substitution x1->x0 and duplicate removal"
    );
}

/// Verify that SCC-UNSAT detection marks the solver as having an empty
/// clause when a variable and its negation are in the same SCC.
///
/// Setup: x0 -> x1 -> not-x0 and not-x0 -> not-x1 -> x0 form a conflicting
/// SCC (x0 and not-x0 in the same SCC). Decompose derives a contradiction.
///
/// Reference: CaDiCaL decompose.cpp:47-66
/// (decompose_conflicting_scc_lrat), #4606.
#[test]
fn test_decompose_scc_unsat_detects_conflict() {
    let mut solver: Solver = Solver::new(2);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));

    // Build conflicting SCC: x0 and not-x0 reachable from each other.
    // x0 -> x1 -> not-x0 -> not-x1 -> x0
    solver.add_clause(vec![x0.negated(), x1]); // x0 -> x1
    solver.add_clause(vec![x1.negated(), x0.negated()]); // x1 -> not-x0
    solver.add_clause(vec![x0, x1.negated()]); // not-x0 -> not-x1
    solver.add_clause(vec![x1, x0]); // not-x1 -> x0

    solver.initialize_watches();
    assert!(
        solver.process_initial_clauses().is_none(),
        "no initial conflicts expected"
    );

    solver.decompose();

    // Decompose should detect UNSAT from conflicting SCC.
    assert!(
        solver.has_empty_clause,
        "decompose must detect UNSAT when x0 and not-x0 are in the same SCC"
    );
}
