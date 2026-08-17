// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for 1UIP conflict analysis and clause learning.

use super::*;
use crate::decompose::{DecomposeProofEmitContext, FmlaGuardedEquivSupportCoverLratSidecar};
use crate::fmla_runtime_ledger::{
    FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
    FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_PATH_ENV,
    FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA,
    FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV,
    FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT,
    FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_SCHEMA,
    FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_SCHEMA,
};
use crate::literal::Variable;
use crate::proof_manager::{
    LearnedLratAuthorityStatus, LearnedLratMaterializationStatus, LearnedLratReplayRowKind,
    ProofAddKind, LEARNED_LRAT_AUTHORITY_EXTERNAL_CHECKER_REQUIRED,
    LEARNED_LRAT_AUTHORITY_FAIL_CLOSED,
};
use crate::ClauseTrace;
use crate::ProofOutput;
use ay_test_support::env::{lock_env, ScopedEnvVar};
use sha2::{Digest, Sha256};

fn lock_fmla_learned_lrat_env_test() -> std::sync::MutexGuard<'static, ()> {
    lock_env()
}

/// Add `n` original clauses to satisfy ProofManager's embedded ForwardChecker
/// and LRAT hint validation. Uses binary clauses on variables `base..base+n`
/// so they don't interfere with test variables 0..base. Also adds `[+x0]`
/// as the first clause to make any derived clause containing +x0 trivially
/// RUP-valid (the checker propagates x0=true, so +x0 is satisfied).
fn add_padding_original_clauses(solver: &mut Solver, n: usize) {
    // First clause: [+x0] — its negation under RUP causes conflict.
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    // Remaining clauses: [+x0, +x_i] — each becomes a unit clause under
    // the RUP assumption (x0=false), propagating a fresh variable. This
    // makes all padding clauses valid LRAT hints (unit or conflict),
    // satisfying the non-unit hint rejection check (#5236 Gap 3).
    for i in 1..n {
        let v = (i * 2) as u32;
        solver.add_clause(vec![
            Literal::positive(Variable(0)),
            Literal::positive(Variable(v)),
        ]);
    }
}

fn setup_retained_fmla_learned_lrat_dry_run_fixture() -> (Solver, u64, u64) {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    add_padding_original_clauses(&mut solver, 8);

    let materializer_context = DecomposeProofEmitContext {
        transaction_id: 42,
        sidecar_context_token: "fmla-guarded-equiv-support-cover-lrat-42".to_string(),
        sidecar_row_index: 0,
        source_row_id: "fmla-guarded-equiv-support-cover-source-1".to_string(),
        obligation_id: "fmla-guarded-equiv-support-cover-42-0".to_string(),
    };
    let materializer_clause = vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(4)),
    ];
    let materializer_source_ids = vec![1, 6, 3];
    let materializer_id = solver
        .proof_manager
        .as_mut()
        .expect("proof manager")
        .emit_add_with_decompose_context(
            &materializer_clause,
            &materializer_source_ids,
            ProofAddKind::Derived,
            &materializer_context,
        )
        .expect("emit materializer proof row");

    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_attempt(1, 1);
    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_fail_closed(false);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;

    let a = Literal::positive(Variable(0));
    let b = Literal::negative(Variable(1));
    let learned_ref =
        solver.add_conflict_learned_clause(vec![a, b], 1, vec![1, materializer_id, 6]);
    let learned_id = solver.clause_id(learned_ref);

    (solver, materializer_id, learned_id)
}

fn setup_missing_materializer_fmla_learned_lrat_dry_run_fixture() -> (Solver, u64) {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    add_padding_original_clauses(&mut solver, 8);
    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_attempt(1, 1);
    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_fail_closed(false);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;

    let a = Literal::positive(Variable(0));
    let b = Literal::negative(Variable(1));
    let learned_ref =
        solver.add_conflict_learned_clause(vec![a, b], 1, vec![1, 6, 3, 6, 2, 3, 8, 7, 8]);
    let learned_id = solver.clause_id(learned_ref);

    (solver, learned_id)
}

fn emit_test_lrat_materializer_row(
    solver: &mut Solver,
    context: &DecomposeProofEmitContext,
) -> u64 {
    let materializer_clause = vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(4)),
    ];
    solver
        .proof_manager
        .as_mut()
        .expect("proof manager")
        .emit_add_with_decompose_context(
            &materializer_clause,
            &[1, 6, 3],
            ProofAddKind::Derived,
            context,
        )
        .expect("emit materializer proof row")
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut hex = String::with_capacity(64);
    for byte in digest {
        use std::fmt::Write as _;
        let _ = write!(&mut hex, "{byte:02x}");
    }
    hex
}

fn solve_latched_lrat_unit_contradiction_to_file(path: &std::path::Path) -> SatResult {
    let proof_file = std::fs::File::create(path).expect("create proof.out fixture");
    let proof = ProofOutput::lrat_text(proof_file, 2);
    let mut solver: Solver = Solver::with_proof_output(1, proof);
    let x = Literal::positive(Variable(0));
    solver.add_clause(vec![x]);
    solver.add_clause(vec![x.negated()]);
    solver
        .proof_manager
        .as_mut()
        .expect("proof manager")
        .mark_lrat_authority_fail_closed();
    solver.solve().into_inner()
}

fn write_fmla_main_lrat_authority_replay(
    path: &std::path::Path,
    proof_out_path: &std::path::Path,
    proof_out_sha256: &str,
    authorized: bool,
) {
    let status = if authorized {
        "authorized"
    } else {
        "fail_closed"
    };
    let proof_dir = proof_out_path.parent().expect("proof.out parent");
    let checker_artifact_path =
        proof_dir.join(FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT.artifact_file_name);
    std::fs::write(&checker_artifact_path, b"checker verdict")
        .expect("write retained checker verdict artifact");
    let checker_path = proof_dir.join("ay-test-lrat-check");
    let checked_dimacs_path = proof_dir.join("input.cnf");
    let checker_path = checker_path.display().to_string();
    let checker_artifact_path = checker_artifact_path.display().to_string();
    let checked_dimacs_path = checked_dimacs_path.display().to_string();
    let proof_out_path_str = proof_out_path.display().to_string();
    let checker_command = format!("{checker_path} {checked_dimacs_path} {proof_out_path_str}");
    let payload = serde_json::json!({
        "schema": FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_SCHEMA,
        "status": "committed_checker_backed_admission",
        "proof_obligation_rows": 1,
        "external_proof_checker_verdict_artifact_rows": 1,
        "external_proof_checker_verdict_artifact": checker_artifact_path,
        "external_proof_checker_verdict_artifact_sha256": sha256_hex(b"checker verdict"),
        "external_proof_checker_verdict_artifact_schema": FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_SCHEMA,
        "external_proof_checker_verdict_artifact_runtime_field": FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT.runtime_field,
        "external_proof_checker_verdict": "VERIFIED_UNSAT",
        "external_proof_checker_path": checker_path,
        "external_proof_checker_sha256": sha256_hex(b"checker"),
        "external_proof_checker_command": checker_command,
        "external_proof_checker_argv": [checker_path, checked_dimacs_path, proof_out_path_str],
        "external_proof_checker_dimacs_path": checked_dimacs_path,
        "external_proof_checker_dimacs_sha256": sha256_hex(b"p cnf 1 2\n1 0\n-1 0\n"),
        "checker_exit_code": 0,
        "learned_lrat_main_proof_authority_status": status,
        "learned_lrat_main_proof_authority_reason": if authorized { serde_json::Value::Null } else { serde_json::json!("fail_closed_diagnostic") },
        "learned_lrat_main_proof_authority_checker_visible_id": 10,
        "learned_lrat_main_proof_authority_proof_out_path": proof_out_path_str,
        "learned_lrat_main_proof_authority_proof_out_sha256": proof_out_sha256,
        "learned_lrat_main_proof_authority_external_checker_verified": authorized,
        "learned_lrat_main_proof_authority_proof_out_contains_lrat_fragment": authorized,
        "learned_lrat_main_proof_authority_authorizes_main_proof_out": authorized,
    });
    let mut bytes = serde_json::to_vec_pretty(&payload).expect("serialize replay");
    bytes.push(b'\n');
    std::fs::write(path, bytes).expect("write authority replay");
}

fn assign_test_lit(solver: &mut Solver, lit: Literal) {
    solver.vals[lit.index()] = 1;
    solver.vals[lit.negated().index()] = -1;
}

#[test]
fn test_analyze_conflict_bails_on_non_uip_decision_reason() {
    let mut solver: Solver = Solver::new(2);
    solver.decision_level = 1;

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let conflict_idx = solver.add_clause_db(&[a.negated(), b.negated()], false);
    let conflict_ref = ClauseRef(conflict_idx as u32);

    solver.trail = vec![a, b];
    solver.trail_lim = vec![0];
    for (trail_pos, lit) in [a, b].into_iter().enumerate() {
        let var = lit.variable().index();
        solver.var_data[var].level = 1;
        solver.var_data[var].trail_pos = trail_pos as u32;
        solver.var_data[var].reason = NO_REASON;
        assign_test_lit(&mut solver, lit);
    }

    let result = solver.analyze_conflict(conflict_ref);

    assert!(
        result.is_none(),
        "non-UIP NO_REASON must fail closed instead of learning a non-asserting clause"
    );
    assert_eq!(solver.stats.trail_exhaustion_bailouts, 1);
    assert_eq!(solver.conflict.learned_count(), 0);
    assert!(
        solver.var_data.iter().all(|var_data| !var_data.is_seen()),
        "bailout must clear transient conflict-analysis seen marks"
    );
}

fn setup_lrat_unit_chain_window_fixture() -> (Solver, Vec<Literal>) {
    let mut solver: Solver = Solver::new(8);
    solver.enable_lrat();

    let lits: Vec<Literal> = (0..8)
        .map(|i| Literal::positive(Variable(i as u32)))
        .collect();
    solver.trail = lits.clone();
    solver.trail_lim.clear();

    for (i, &lit) in lits.iter().enumerate() {
        solver.var_data[i].level = 0;
        solver.var_data[i].trail_pos = i as u32;
        solver.var_data[i].reason = NO_REASON;
        assign_test_lit(&mut solver, lit);
        solver.record_unit_proof_id_for_lit(lit, 100 + i as u64);
    }

    (solver, lits)
}

fn seed_lrat_unit_chain_vars(solver: &mut Solver, vars: &[usize]) {
    for &var_idx in vars {
        if solver.min.minimize_flags[var_idx] & LRAT_A == 0 {
            solver.min.minimize_flags[var_idx] |= LRAT_A;
            solver.min.lrat_to_clear.push(var_idx);
        }
    }
}

#[test]
fn test_add_learned_clause_reorders_second_literal_to_highest_level() {
    let mut solver: Solver = Solver::new(4);
    solver.var_data[0].level = 7; // UIP level (ignored for reorder)
    solver.var_data[1].level = 1;
    solver.var_data[2].level = 5; // highest non-UIP level
    solver.var_data[3].level = 3;

    let uip = Literal::positive(Variable(0));
    let low = Literal::positive(Variable(1));
    let high = Literal::positive(Variable(2));
    let mid = Literal::positive(Variable(3));

    let learned = solver.add_learned_clause(vec![uip, low, high, mid], 3, &[]);
    let idx = learned.0 as usize;

    assert_eq!(solver.arena.literal(idx, 0), uip);
    assert_eq!(solver.arena.literal(idx, 1), high);
}

#[test]
fn test_add_learned_clause_keeps_binary_order() {
    let mut solver: Solver = Solver::new(2);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;

    let first = Literal::positive(Variable(0));
    let second = Literal::negative(Variable(1));
    let learned = solver.add_learned_clause(vec![first, second], 1, &[]);
    let idx = learned.0 as usize;

    assert_eq!(solver.arena.literal(idx, 0), first);
    assert_eq!(solver.arena.literal(idx, 1), second);
}

fn learned_tail_reorder_fixture(clause_len: usize) -> (Solver, Vec<Literal>) {
    let mut solver: Solver = Solver::new(clause_len);
    for i in 0..clause_len {
        solver.var_data[i].level = 0;
        solver.var_data[i].trail_pos = 0;
    }
    solver.var_data[0].level = 99;
    solver.var_data[0].trail_pos = 99;
    solver.var_data[1].level = 10;
    solver.var_data[1].trail_pos = 10;
    if clause_len > 4 {
        solver.var_data[2].level = 1;
        solver.var_data[3].level = 3;
        solver.var_data[4].level = 2;
    }

    let lits = (0..clause_len)
        .map(|i| Literal::positive(Variable(i as u32)))
        .collect();
    (solver, lits)
}

fn arena_clause_literals(solver: &Solver, idx: usize) -> Vec<Literal> {
    (0..solver.arena.len_of(idx))
        .map(|slot| solver.arena.literal(idx, slot))
        .collect()
}

fn sorted_literal_words(lits: &[Literal]) -> Vec<u32> {
    let mut words = lits.iter().map(|lit| lit.0).collect::<Vec<_>>();
    words.sort_unstable();
    words
}

fn assert_tail_reordered_by_assignment_recency(
    solver: &Solver,
    idx: usize,
    original_lits: &[Literal],
    lbd: u32,
) {
    let arena_lits = arena_clause_literals(solver, idx);

    assert_eq!(
        arena_lits[0], original_lits[0],
        "UIP watch must stay at position 0"
    );
    assert_eq!(
        arena_lits[1], original_lits[1],
        "highest non-UIP watch must stay at position 1"
    );
    assert_eq!(
        &arena_lits[2..5],
        &[original_lits[3], original_lits[4], original_lits[2]],
        "tail should sort by descending (decision level, trail position)"
    );
    assert_eq!(
        &arena_lits[5..],
        &original_lits[5..],
        "equal-key tail literals should keep their relative order"
    );
    assert_eq!(
        sorted_literal_words(&arena_lits),
        sorted_literal_words(original_lits),
        "tail reorder must preserve the literal multiset"
    );
    assert_eq!(solver.arena.lbd(idx), lbd, "LBD must be preserved");
    assert_eq!(
        solver.arena.saved_pos(idx),
        2,
        "saved_pos must stay initialized"
    );
}

#[test]
fn test_bcp_learned_1963_tail_reorder_default_off_keeps_tail_order() {
    let (mut solver, lits) = learned_tail_reorder_fixture(32);

    let learned = solver.add_learned_clause(lits.clone(), 7, &[]);
    let idx = learned.0 as usize;

    assert_eq!(
        arena_clause_literals(&solver, idx),
        lits,
        "default-off creation-time tail reorder must preserve learned clause order"
    );
    let stats = solver.bcp_long_scan_stats();
    assert!(!stats.learned_1963_tail_reorder_enabled);
    assert_eq!(stats.learned_1963_tail_reorder_candidates, 0);
    assert_eq!(stats.learned_1963_tail_reorder_changed, 0);
    assert_eq!(stats.learned_1963_tail_reorder_swaps, 0);
}

#[test]
fn test_bcp_learned_617_and_18_tail_reorder_default_off_keeps_tail_order() {
    for clause_len in [6usize, 18usize] {
        let (mut solver, lits) = learned_tail_reorder_fixture(clause_len);

        let learned = solver.add_learned_clause(lits.clone(), 7, &[]);
        let idx = learned.0 as usize;

        assert_eq!(
            arena_clause_literals(&solver, idx),
            lits,
            "default-off len-{clause_len} creation-time tail reorder must preserve learned clause order"
        );
        let stats = solver.bcp_long_scan_stats();
        assert!(!stats.learned_617_tail_reorder_enabled);
        assert_eq!(stats.learned_617_tail_reorder_candidates, 0);
        assert_eq!(stats.learned_617_tail_reorder_exercised, 0);
        assert_eq!(stats.learned_617_tail_reorder_changed, 0);
        assert_eq!(stats.learned_617_tail_reorder_swaps, 0);
        assert!(!stats.learned_18_tail_reorder_enabled);
        assert_eq!(stats.learned_18_tail_reorder_candidates, 0);
        assert_eq!(stats.learned_18_tail_reorder_exercised, 0);
        assert_eq!(stats.learned_18_tail_reorder_changed, 0);
        assert_eq!(stats.learned_18_tail_reorder_swaps, 0);
    }
}

#[test]
fn test_bcp_learned_617_tail_reorder_enabled_reorders_len6_and_len17_tail_only() {
    for clause_len in [6usize, 17usize] {
        let (mut solver, lits) = learned_tail_reorder_fixture(clause_len);
        solver.set_bcp_learned_617_tail_reorder_enabled(true);

        let learned = solver.add_learned_clause(lits.clone(), 9, &[]);
        let idx = learned.0 as usize;

        assert_tail_reordered_by_assignment_recency(&solver, idx, &lits, 9);
        let stats = solver.bcp_long_scan_stats();
        assert!(stats.learned_617_tail_reorder_enabled);
        assert_eq!(stats.learned_617_tail_reorder_candidates, 1);
        assert_eq!(stats.learned_617_tail_reorder_exercised, 1);
        assert_eq!(stats.learned_617_tail_reorder_changed, 1);
        assert_eq!(stats.learned_617_tail_reorder_swaps, 2);
        assert_eq!(stats.learned_18_tail_reorder_candidates, 0);
        assert_eq!(stats.learned_1963_tail_reorder_candidates, 0);
    }
}

#[test]
fn test_bcp_learned_18_tail_reorder_enabled_reorders_tail_only() {
    let (mut solver, lits) = learned_tail_reorder_fixture(18);
    solver.set_bcp_learned_18_tail_reorder_enabled(true);

    let learned = solver.add_learned_clause(lits.clone(), 9, &[]);
    let idx = learned.0 as usize;

    assert_tail_reordered_by_assignment_recency(&solver, idx, &lits, 9);
    let stats = solver.bcp_long_scan_stats();
    assert!(stats.learned_18_tail_reorder_enabled);
    assert_eq!(stats.learned_18_tail_reorder_candidates, 1);
    assert_eq!(stats.learned_18_tail_reorder_exercised, 1);
    assert_eq!(stats.learned_18_tail_reorder_changed, 1);
    assert_eq!(stats.learned_18_tail_reorder_swaps, 2);
    assert_eq!(stats.learned_617_tail_reorder_candidates, 0);
    assert_eq!(stats.learned_1963_tail_reorder_candidates, 0);
}

#[test]
fn test_bcp_learned_617_and_18_tail_reorder_do_not_cross_buckets() {
    let (mut len18_solver, len18_lits) = learned_tail_reorder_fixture(18);
    len18_solver.set_bcp_learned_617_tail_reorder_enabled(true);
    let len18_learned = len18_solver.add_learned_clause(len18_lits.clone(), 5, &[]);
    assert_eq!(
        arena_clause_literals(&len18_solver, len18_learned.0 as usize),
        len18_lits,
        "6-17 gate must not reorder length-18 learned clauses"
    );
    let len18_stats = len18_solver.bcp_long_scan_stats();
    assert!(len18_stats.learned_617_tail_reorder_enabled);
    assert_eq!(len18_stats.learned_617_tail_reorder_candidates, 0);
    assert_eq!(len18_stats.learned_617_tail_reorder_exercised, 0);

    let (mut len17_solver, len17_lits) = learned_tail_reorder_fixture(17);
    len17_solver.set_bcp_learned_18_tail_reorder_enabled(true);
    let len17_learned = len17_solver.add_learned_clause(len17_lits.clone(), 5, &[]);
    assert_eq!(
        arena_clause_literals(&len17_solver, len17_learned.0 as usize),
        len17_lits,
        "length-18 gate must not reorder 6-17 learned clauses"
    );
    let len17_stats = len17_solver.bcp_long_scan_stats();
    assert!(len17_stats.learned_18_tail_reorder_enabled);
    assert_eq!(len17_stats.learned_18_tail_reorder_candidates, 0);
    assert_eq!(len17_stats.learned_18_tail_reorder_exercised, 0);
}

#[test]
fn test_bcp_learned_1963_tail_reorder_enabled_reorders_len32_tail_only() {
    let (mut solver, lits) = learned_tail_reorder_fixture(32);
    solver.set_bcp_learned_1963_tail_reorder_enabled(true);

    let learned = solver.add_learned_clause(lits.clone(), 9, &[]);
    let idx = learned.0 as usize;

    assert_tail_reordered_by_assignment_recency(&solver, idx, &lits, 9);

    let stats = solver.bcp_long_scan_stats();
    assert!(stats.learned_1963_tail_reorder_enabled);
    assert_eq!(stats.learned_1963_tail_reorder_candidates, 1);
    assert_eq!(stats.learned_1963_tail_reorder_changed, 1);
    assert_eq!(stats.learned_1963_tail_reorder_swaps, 2);
}

#[test]
fn test_bcp_learned_1963_tail_reorder_budget_applies_within_budget() {
    let (mut solver, lits) = learned_tail_reorder_fixture(32);
    solver.set_bcp_learned_1963_tail_reorder_swap_budget(Some(2));

    let learned = solver.add_learned_clause(lits.clone(), 9, &[]);
    let idx = learned.0 as usize;

    assert_tail_reordered_by_assignment_recency(&solver, idx, &lits, 9);

    let stats = solver.bcp_long_scan_stats();
    assert!(stats.learned_1963_tail_reorder_enabled);
    assert_eq!(stats.learned_1963_tail_reorder_swap_budget, Some(2));
    assert_eq!(stats.learned_1963_tail_reorder_candidates, 1);
    assert_eq!(stats.learned_1963_tail_reorder_changed, 1);
    assert_eq!(stats.learned_1963_tail_reorder_swaps, 2);
    assert_eq!(stats.learned_1963_tail_reorder_budget_candidates, 1);
    assert_eq!(stats.learned_1963_tail_reorder_budget_applied, 1);
    assert_eq!(
        stats.learned_1963_tail_reorder_budget_skipped_over_budget,
        0
    );
    assert_eq!(stats.learned_1963_tail_reorder_budget_swaps_applied, 2);
    assert_eq!(stats.learned_1963_tail_reorder_budget_swaps_skipped, 0);
}

#[test]
fn test_bcp_learned_1963_tail_reorder_budget_skips_high_swap_clause() {
    let clause_len = 32usize;
    let (mut solver, lits) = learned_tail_reorder_fixture(clause_len);
    for i in 2..clause_len {
        solver.var_data[i].level = i as u32;
        solver.var_data[i].trail_pos = i as u32;
    }
    solver.set_bcp_learned_1963_tail_reorder_swap_budget(Some(256));

    let learned = solver.add_learned_clause(lits.clone(), 9, &[]);
    let idx = learned.0 as usize;

    let mut expected_lits = Vec::with_capacity(clause_len);
    expected_lits.push(lits[0]);
    expected_lits.push(lits[clause_len - 1]);
    expected_lits.extend_from_slice(&lits[2..clause_len - 1]);
    expected_lits.push(lits[1]);
    assert_eq!(
        arena_clause_literals(&solver, idx),
        expected_lits,
        "budgeted tail reorder must leave over-budget clauses untouched"
    );

    let expected_swaps = 414;
    let stats = solver.bcp_long_scan_stats();
    assert!(stats.learned_1963_tail_reorder_enabled);
    assert_eq!(stats.learned_1963_tail_reorder_swap_budget, Some(256));
    assert_eq!(stats.learned_1963_tail_reorder_candidates, 1);
    assert_eq!(stats.learned_1963_tail_reorder_changed, 0);
    assert_eq!(stats.learned_1963_tail_reorder_swaps, 0);
    assert_eq!(stats.learned_1963_tail_reorder_budget_candidates, 1);
    assert_eq!(stats.learned_1963_tail_reorder_budget_applied, 0);
    assert_eq!(
        stats.learned_1963_tail_reorder_budget_skipped_over_budget,
        1
    );
    assert_eq!(stats.learned_1963_tail_reorder_budget_swaps_applied, 0);
    assert_eq!(
        stats.learned_1963_tail_reorder_budget_swaps_skipped,
        expected_swaps
    );
}

#[test]
fn test_bcp_learned_1963_tail_reorder_ignores_len18_and_len64() {
    for clause_len in [18usize, 64usize] {
        let (mut solver, lits) = learned_tail_reorder_fixture(clause_len);
        solver.set_bcp_learned_1963_tail_reorder_enabled(true);

        let learned = solver.add_learned_clause(lits.clone(), 5, &[]);
        let idx = learned.0 as usize;

        assert_eq!(
            arena_clause_literals(&solver, idx),
            lits,
            "len-{clause_len} should not reorder outside the learned 19-63 gate"
        );
        let stats = solver.bcp_long_scan_stats();
        assert!(stats.learned_1963_tail_reorder_enabled);
        assert_eq!(stats.learned_1963_tail_reorder_candidates, 0);
        assert_eq!(stats.learned_1963_tail_reorder_changed, 0);
        assert_eq!(stats.learned_1963_tail_reorder_swaps, 0);
    }
}

#[test]
fn test_add_learned_clause_reverses_lrat_hint_order() {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    // Add 8 original clauses so LRAT hint IDs 1-8 are registered
    add_padding_original_clauses(&mut solver, 8);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;

    let a = Literal::positive(Variable(0));
    let b = Literal::negative(Variable(1));
    // Include clause 1 ([+x0]) in hints — required for RUP derivation
    // of [+x0, -x1]: negating gives x0=false, then hint 1 ({+x0}) is
    // falsified → contradiction.
    let _ = solver.add_learned_clause(vec![a, b], 1, &[1, 6, 3, 2, 8, 7]);

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be available");
    let proof_text = String::from_utf8(writer.into_vec().expect("proof flush"))
        .expect("proof bytes should be valid UTF-8");

    // Derived clause ID = 9 (8 originals + 1), hints reversed
    assert_eq!(proof_text, "9 1 -2 0 7 8 2 3 6 1 0\n");
}

#[test]
fn test_add_conflict_learned_clause_returns_owned_buffers_to_analyzer() {
    let mut solver: Solver = Solver::new(4);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;
    solver
        .conflict
        .set_asserting_literal(Literal::positive(Variable(0)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(1)));
    solver.conflict.add_to_chain(5);
    solver.conflict.add_to_chain(9);

    let result = solver.conflict.get_result(1, 1);
    let learned_cap = result.learned_clause.capacity();
    let chain_cap = result.resolution_chain.capacity();

    let learned_ref =
        solver.add_conflict_learned_clause(result.learned_clause, 1, result.resolution_chain);

    assert_eq!(
        solver.arena.literal(learned_ref.0 as usize, 0),
        Literal::positive(Variable(0))
    );
    assert_eq!(solver.conflict.learned_capacity(), learned_cap);
    assert_eq!(solver.conflict.resolution_chain_capacity(), chain_cap);
}

#[test]
fn test_bump_analyzed_variables_uses_persistent_sort_buf() {
    let mut solver: Solver = Solver::new(4);
    solver.stable_mode = false;
    solver.bump_order_sort_buf = Vec::with_capacity(8);
    solver.conflict.mark_seen(0, &mut solver.var_data);
    solver.conflict.mark_seen(2, &mut solver.var_data);
    solver.conflict.mark_seen(1, &mut solver.var_data);

    solver.bump_analyzed_variables();

    // Initial bump_order for Solver::new(4) is [4, 3, 2, 1]; analyzed order
    // is [0, 2, 1], so ascending bump_order yields indices [2, 1, 0].
    let sorted_indices: Vec<usize> = solver
        .bump_order_sort_buf
        .iter()
        .map(|&(_, idx)| idx)
        .collect();
    assert_eq!(sorted_indices, vec![2, 1, 0]);
    assert!(solver.bump_order_sort_buf.capacity() >= 8);
}

/// Verify lrat_reverse_hints reverses and filters zeros.
/// Dedup is NOT done here — it's handled at construction time by
/// `ConflictAnalyzer::add_to_chain` (#5248). Post-hoc dedup here would
/// break multi-stage ordering (#5194).
#[test]
fn test_lrat_reverse_dedup_handles_large_chains() {
    let mut hints: Vec<u64> = Vec::new();
    for i in 1..=100 {
        hints.push(i);
        hints.push(i); // duplicate — preserved by lrat_reverse_hints
    }
    for i in (1..=50).rev() {
        hints.push(i);
    }

    let result = Solver::lrat_reverse_hints(&hints);

    // All 250 non-zero entries preserved (no dedup at this level), zeros filtered.
    assert_eq!(result.len(), 250, "should preserve all non-zero hints");
    assert!(!result.contains(&0), "sentinel 0 must not appear in hints");
    assert_eq!(result[0], 1, "first hint after reversal should be 1");
}

/// Verify LRAT chain helpers and reusable work arrays exist and are sized
/// correctly. The LRAT bits (LRAT_A, LRAT_B in minimize_flags, plus lrat_to_clear)
/// replaced per-conflict vec![false; num_vars] allocations (#4579).
#[test]
fn test_lrat_chain_functions_exist_and_are_callable() {
    // Verify the LRAT chain helper functions compile and don't panic on empty input.
    // This is a minimal smoke test; correctness is validated by LRAT proof checking.
    let solver: Solver = Solver::new(10);

    // lrat_reverse_hints: static method, no allocation concern
    let empty_result = Solver::lrat_reverse_hints(&[]);
    assert!(empty_result.is_empty());

    // Verify the solver has packed minimize_flags array (#5089)
    assert_eq!(solver.min.minimize_flags.len(), 10);

    // Verify LRAT bits are packed into minimize_flags (#5089, #4579)
    assert_eq!(solver.min.minimize_flags.len(), 10);
    assert!(solver.min.lrat_to_clear.is_empty());
}

#[test]
fn test_collect_level0_unit_chain_no_filter_matches_empty_filter() {
    let (mut no_filter_solver, _) = setup_lrat_unit_chain_window_fixture();
    seed_lrat_unit_chain_vars(&mut no_filter_solver, &[5, 7]);
    let no_filter_chain = no_filter_solver.collect_level0_unit_chain();

    let (mut empty_filter_solver, _) = setup_lrat_unit_chain_window_fixture();
    seed_lrat_unit_chain_vars(&mut empty_filter_solver, &[5, 7]);
    let empty_filter = det_hash_set_new();
    let empty_filter_chain = empty_filter_solver.collect_level0_unit_chain_filtered(&empty_filter);

    assert_eq!(no_filter_chain, empty_filter_chain);
    assert_eq!(
        no_filter_chain,
        vec![107, 105],
        "no-filter collection must preserve reverse-trail hint order"
    );
}

#[test]
fn test_lrat_no_filter_collectors_do_not_construct_empty_filter() {
    let unit_chain_src = include_str!("conflict_analysis_lrat_unit_chain.rs");
    let specialized_src = include_str!("conflict_analysis_lrat_specialized.rs");

    assert!(
        unit_chain_src.contains("emit_level0_unit_chain_filtered(None"),
        "collect_level0_unit_chain should route no-filter collection through None"
    );
    assert!(
        !unit_chain_src.contains("collect_level0_unit_chain_filtered(&det_hash_set_new())"),
        "collect_level0_unit_chain must not allocate an empty DetHashSet"
    );
    assert!(
        !specialized_src.contains("collect_level0_unit_chain_filtered(&det_hash_set_new())"),
        "specialized no-filter callers must use collect_level0_unit_chain"
    );
}

#[test]
fn test_add_learned_clause_deduplicates_reversed_lrat_hints() {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    add_padding_original_clauses(&mut solver, 8);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;

    let a = Literal::positive(Variable(0));
    let b = Literal::negative(Variable(1));
    // lrat_reverse_hints reverses and filters zeros.
    // ProofManager::emit_add deduplicates hint IDs at the output boundary
    // (#5248) so external LRAT checkers do not reject duplicate hints.
    let _ = solver.add_learned_clause(vec![a, b], 1, &[1, 6, 3, 6, 2, 3, 8, 7, 8]);

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be available");
    let proof_text = String::from_utf8(writer.into_vec().expect("proof flush"))
        .expect("proof bytes should be valid UTF-8");

    // Derived clause ID = 9 (8 originals + 1), reversed and deduped:
    // Input [1,6,3,6,2,3,8,7,8] → reverse [8,7,8,3,2,6,3,6,1]
    // → dedup (first-occurrence order) [8,7,3,2,6,1]
    assert_eq!(proof_text, "9 1 -2 0 8 7 3 2 6 1 0\n");
}

#[test]
fn test_add_learned_clause_filters_deleted_lrat_hint_ids() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(8, proof);

    let live_lit = Literal::positive(Variable(0));
    let deleted_lits = [live_lit, Literal::positive(Variable(2))];
    let live_idx = solver.add_clause_db(&[live_lit], false);
    let deleted_idx = solver.add_clause_db(&deleted_lits, false);
    let live_id = solver.clause_id(ClauseRef(live_idx as u32));
    let deleted_id = solver.clause_id(ClauseRef(deleted_idx as u32));
    assert_ne!(live_id, 0, "live padding clause must have an LRAT ID");
    assert_ne!(deleted_id, 0, "deleted padding clause must have an LRAT ID");
    assert!(solver.lrat_hint_id_visible(deleted_id));

    solver
        .proof_emit_delete(&deleted_lits, deleted_id)
        .expect("proof delete should succeed");
    assert!(
        !solver.lrat_hint_id_visible(deleted_id),
        "deleted LRAT IDs must not be eligible as external hints"
    );

    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;
    let learned_ref = solver.add_learned_clause(
        vec![
            Literal::positive(Variable(0)),
            Literal::negative(Variable(1)),
        ],
        1,
        &[live_id, deleted_id],
    );
    let learned_id = solver.clause_id(learned_ref);
    assert!(
        solver
            .proof_manager
            .as_ref()
            .expect("proof manager")
            .has_io_error(),
        "deleted derived LRAT hints must trip the proof-error latch"
    );

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be available");
    let proof_text = String::from_utf8(writer.into_vec().expect("proof flush"))
        .expect("proof bytes should be valid UTF-8");
    assert!(
        proof_text
            .lines()
            .all(|line| !line.starts_with(&format!("{learned_id} "))),
        "derived learned clause with deleted hint ID {deleted_id} must not be written with stripped hints\nproof:\n{proof_text}"
    );
}

#[test]
fn test_add_conflict_learned_clause_reuses_owned_chain_for_lrat_emit() {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    add_padding_original_clauses(&mut solver, 8);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;

    let a = Literal::positive(Variable(0));
    let b = Literal::negative(Variable(1));
    let mut chain = Vec::with_capacity(16);
    chain.extend_from_slice(&[1, 6, 3, 6, 2, 3, 8, 7, 8]);
    let chain_cap = chain.capacity();

    let _ = solver.add_conflict_learned_clause(vec![a, b], 1, chain);

    assert_eq!(
        solver.conflict.resolution_chain_capacity(),
        chain_cap,
        "owned conflict chain buffer should be returned for reuse"
    );
    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be available");
    let proof_text = String::from_utf8(writer.into_vec().expect("proof flush"))
        .expect("proof bytes should be valid UTF-8");

    assert_eq!(proof_text, "9 1 -2 0 8 7 3 2 6 1 0\n");
}

#[test]
fn test_add_conflict_learned_clause_fmla_fail_closed_reserves_without_forward_emit() {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    add_padding_original_clauses(&mut solver, 8);
    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_attempt(1, 1);
    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_fail_closed(false);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;

    let a = Literal::positive(Variable(0));
    let b = Literal::negative(Variable(1));
    let learned_chain = vec![1, 6, 3, 6, 2, 3, 8, 7, 8];
    let mut chain = Vec::with_capacity(16);
    chain.extend_from_slice(&learned_chain);
    let chain_cap = chain.capacity();

    let learned_ref = solver.add_conflict_learned_clause(vec![a, b], 1, chain);
    let learned_id = solver.clause_id(learned_ref);

    assert_ne!(
        learned_id, 0,
        "fail-closed learned clause should still reserve a stable LRAT ID"
    );
    assert_eq!(
        solver.conflict.resolution_chain_capacity(),
        chain_cap,
        "owned conflict chain buffer should still be returned for reuse"
    );
    {
        let proof_manager = solver.proof_manager.as_ref().expect("proof manager");
        assert!(
            !proof_manager.has_inprocessing_boundary_error(),
            "Fmla authority fail-closed must not trip inprocessing boundary guards"
        );
        assert!(
            proof_manager.has_lrat_authority_fail_closed(),
            "Fmla fail-closed materializer must downgrade downstream learned LRAT authority"
        );
        let authority_records = proof_manager.learned_lrat_authority_records();
        assert_eq!(
            authority_records.len(),
            1,
            "Fmla fail-closed learned LRAT row must retain an authority observation"
        );
        let record = &authority_records[0];
        assert_eq!(record.checker_visible_id, learned_id);
        assert_eq!(record.clause_lits_dimacs, vec![1, -2]);
        assert_eq!(record.raw_resolution_chain, learned_chain);
        assert_eq!(record.lrat_hints, vec![8, 7, 8, 3, 2, 6, 3, 6, 1]);
        assert!(
            record.materializer_dependency_ids.is_empty(),
            "missing materializer record must not fabricate learned authority"
        );
        assert!(
            record.source_clause_dependency_ids.is_empty(),
            "missing materializer dependency must leave source authority empty"
        );
        assert_eq!(record.proof_manager_mode, "lrat");
        assert!(!record.proof_out_emitted);
        assert!(!record.proof_writer_io_error);
        assert_eq!(
            record.authority_status,
            LearnedLratAuthorityStatus::FailClosedMaterializer
        );
        let exports = proof_manager.materialize_fmla_learned_lrat_authority_exports();
        assert_eq!(exports.len(), 1);
        let export = &exports[0];
        assert_eq!(export.checker_visible_id, learned_id);
        assert_eq!(export.checker_visible_lrat_hints, vec![8, 7, 3, 2, 6, 1]);
        assert!(export.materializer_rows.is_empty());
        assert!(!export.proof_out_emitted);
        assert_eq!(
            export.materialization_status,
            LearnedLratMaterializationStatus::FailClosedMissingMaterializerDependency
        );
        let replays = proof_manager.checked_fmla_learned_lrat_materialization_replays();
        assert_eq!(replays.len(), 1);
        let replay = &replays[0];
        assert_eq!(replay.checker_visible_id, learned_id);
        assert_eq!(
            replay.materialization_status,
            LearnedLratMaterializationStatus::FailClosedMissingMaterializerDependency
        );
        assert!(
            replay.rows.is_empty(),
            "missing materializer dependency must not replay learned LRAT rows"
        );
        assert!(!replay.proof_out_emitted);
        assert!(!replay.proof_writer_io_error);
        let artifacts = proof_manager.dry_run_fmla_learned_lrat_materialization_fragments();
        assert_eq!(artifacts.len(), 1);
        let artifact = &artifacts[0];
        assert_eq!(artifact.checker_visible_id, learned_id);
        assert_eq!(
            artifact.materialization_status,
            LearnedLratMaterializationStatus::FailClosedMissingMaterializerDependency
        );
        assert!(
            artifact.rows.is_empty(),
            "missing materializer dependency must not serialize LRAT dry-run rows"
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
    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be available");
    let proof_text = String::from_utf8(writer.into_vec().expect("proof flush"))
        .expect("proof bytes should be valid UTF-8");
    assert!(
        proof_text
            .lines()
            .all(|line| !line.starts_with(&format!("{learned_id} "))),
        "Fmla fail-closed learned clause {learned_id} must not be forward-emitted\nproof:\n{proof_text}"
    );
}

#[test]
fn test_fmla_fail_closed_learned_lrat_record_captures_materializer_dependency() {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    add_padding_original_clauses(&mut solver, 8);

    let materializer_context = DecomposeProofEmitContext {
        transaction_id: 42,
        sidecar_context_token: "fmla-guarded-equiv-support-cover-lrat-42".to_string(),
        sidecar_row_index: 0,
        source_row_id: "fmla-guarded-equiv-support-cover-source-1".to_string(),
        obligation_id: "fmla-guarded-equiv-support-cover-42-0".to_string(),
    };
    let materializer_clause = vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(4)),
    ];
    let materializer_source_ids = vec![1, 6, 3];
    let materializer_id = solver
        .proof_manager
        .as_mut()
        .expect("proof manager")
        .emit_add_with_decompose_context(
            &materializer_clause,
            &materializer_source_ids,
            ProofAddKind::Derived,
            &materializer_context,
        )
        .expect("emit materializer proof row");

    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_attempt(1, 1);
    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_fail_closed(false);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;

    let a = Literal::positive(Variable(0));
    let b = Literal::negative(Variable(1));
    let learned_chain = vec![1, materializer_id, 6];
    let learned_ref = solver.add_conflict_learned_clause(vec![a, b], 1, learned_chain.clone());
    let learned_id = solver.clause_id(learned_ref);

    let proof_manager = solver.proof_manager.as_ref().expect("proof manager");
    assert!(proof_manager.has_lrat_authority_fail_closed());
    let authority_records = proof_manager.learned_lrat_authority_records();
    assert_eq!(authority_records.len(), 1);
    let record = &authority_records[0];
    assert_eq!(record.checker_visible_id, learned_id);
    assert_eq!(record.clause_lits_dimacs, vec![1, -2]);
    assert_eq!(record.raw_resolution_chain, learned_chain);
    assert_eq!(record.lrat_hints, vec![6, materializer_id, 1]);
    assert_eq!(record.materializer_dependency_ids, vec![materializer_id]);
    assert_eq!(record.source_clause_dependency_ids, materializer_source_ids);
    assert!(!record.proof_out_emitted);
    assert_eq!(
        record.authority_status,
        LearnedLratAuthorityStatus::FailClosedMaterializer
    );
    let exports = proof_manager.materialize_fmla_learned_lrat_authority_exports();
    assert_eq!(exports.len(), 1);
    let export = &exports[0];
    assert_eq!(export.checker_visible_id, learned_id);
    assert_eq!(export.clause_lits_dimacs, vec![1, -2]);
    assert_eq!(export.raw_resolution_chain, learned_chain);
    assert_eq!(
        export.checker_visible_lrat_hints,
        vec![6, materializer_id, 1]
    );
    assert_eq!(export.materializer_rows.len(), 1);
    let materializer_row = &export.materializer_rows[0];
    assert_eq!(materializer_row.context, materializer_context);
    assert_eq!(materializer_row.checker_visible_id, materializer_id);
    assert_eq!(materializer_row.clause_lits_dimacs, vec![1, 5]);
    assert_eq!(
        materializer_row.checker_visible_lrat_hints,
        materializer_source_ids
    );
    assert!(materializer_row.solver_runtime_emitted);
    assert!(!materializer_row.proof_writer_io_error);
    assert!(!export.proof_out_emitted);
    assert_eq!(
        export.authority_status,
        LearnedLratAuthorityStatus::FailClosedMaterializer
    );
    assert_eq!(
        export.materialization_status,
        LearnedLratMaterializationStatus::RetainedDependenciesComplete
    );
    let replays = proof_manager.checked_fmla_learned_lrat_materialization_replays();
    assert_eq!(replays.len(), 1);
    let replay = &replays[0];
    assert_eq!(replay.checker_visible_id, learned_id);
    assert_eq!(
        replay.materialization_status,
        LearnedLratMaterializationStatus::RetainedDependenciesComplete
    );
    assert_eq!(replay.rows.len(), 2);
    assert_eq!(
        replay.rows[0].kind,
        LearnedLratReplayRowKind::MaterializerAdd
    );
    assert_eq!(replay.rows[0].checker_visible_id, materializer_id);
    assert_eq!(replay.rows[0].clause_lits_dimacs, vec![1, 5]);
    assert_eq!(
        replay.rows[0].checker_visible_lrat_hints,
        materializer_source_ids
    );
    assert_eq!(replay.rows[1].kind, LearnedLratReplayRowKind::LearnedAdd);
    assert_eq!(replay.rows[1].checker_visible_id, learned_id);
    assert_eq!(replay.rows[1].clause_lits_dimacs, vec![1, -2]);
    assert_eq!(
        replay.rows[1].checker_visible_lrat_hints,
        vec![6, materializer_id, 1]
    );
    assert!(!replay.proof_out_emitted);
    assert!(!replay.proof_writer_io_error);
    let artifacts = proof_manager.dry_run_fmla_learned_lrat_materialization_fragments();
    assert_eq!(artifacts.len(), 1);
    let artifact = &artifacts[0];
    assert_eq!(artifact.checker_visible_id, learned_id);
    assert_eq!(
        artifact.materialization_status,
        LearnedLratMaterializationStatus::RetainedDependenciesComplete
    );
    assert_eq!(artifact.rows.len(), 2);
    assert_eq!(
        artifact.rows[0].kind,
        LearnedLratReplayRowKind::MaterializerAdd
    );
    assert_eq!(artifact.rows[0].checker_visible_id, materializer_id);
    assert_eq!(
        artifact.rows[0].lrat_line,
        format!("{materializer_id} 1 5 0 1 6 3 0\n")
    );
    assert_eq!(artifact.rows[1].kind, LearnedLratReplayRowKind::LearnedAdd);
    assert_eq!(artifact.rows[1].checker_visible_id, learned_id);
    assert_eq!(
        artifact.rows[1].lrat_line,
        format!("{learned_id} 1 -2 0 6 {materializer_id} 1 0\n")
    );
    assert_eq!(
        artifact.lrat_fragment,
        format!("{materializer_id} 1 5 0 1 6 3 0\n{learned_id} 1 -2 0 6 {materializer_id} 1 0\n")
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
        "dry-run fragment is not Main proof.out authority"
    );

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be available");
    let proof_text = String::from_utf8(writer.into_vec().expect("proof flush"))
        .expect("proof bytes should be valid UTF-8");
    assert!(
        proof_text
            .lines()
            .all(|line| !line.starts_with(&format!("{learned_id} "))),
        "Fmla fail-closed learned clause {learned_id} must not be forward-emitted\nproof:\n{proof_text}"
    );
}

#[test]
fn test_fmla_fail_closed_learned_lrat_record_retains_available_materializer_dependency() {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    add_padding_original_clauses(&mut solver, 8);

    let materializer_context = DecomposeProofEmitContext {
        transaction_id: 45,
        sidecar_context_token: "fmla-guarded-equiv-support-cover-lrat-45".to_string(),
        sidecar_row_index: 0,
        source_row_id: "fmla-guarded-equiv-support-cover-source-1".to_string(),
        obligation_id: "fmla-guarded-equiv-support-cover-45-0".to_string(),
    };
    let materializer_clause = vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(4)),
    ];
    let materializer_source_ids = vec![1, 6, 3];
    let materializer_id = solver
        .proof_manager
        .as_mut()
        .expect("proof manager")
        .emit_add_with_decompose_context(
            &materializer_clause,
            &materializer_source_ids,
            ProofAddKind::Derived,
            &materializer_context,
        )
        .expect("emit materializer proof row");

    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_attempt(1, 1);
    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_fail_closed(false);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;

    let a = Literal::positive(Variable(0));
    let b = Literal::negative(Variable(1));
    let learned_chain = vec![0, 1, 6, 3, 6, 2, 3, 8, 7, 8, 0];
    let learned_ref = solver.add_conflict_learned_clause(vec![a, b], 1, learned_chain.clone());
    let learned_id = solver.clause_id(learned_ref);

    let proof_manager = solver.proof_manager.as_ref().expect("proof manager");
    assert!(proof_manager.has_lrat_authority_fail_closed());
    let authority_records = proof_manager.learned_lrat_authority_records();
    assert_eq!(authority_records.len(), 1);
    let record = &authority_records[0];
    assert_eq!(record.checker_visible_id, learned_id);
    assert_eq!(record.raw_resolution_chain, learned_chain);
    assert_eq!(
        record.lrat_hints,
        vec![8, 7, 8, 3, 2, 6, 3, 6, 1, 0, materializer_id],
        "synthetic materializer dependency must retain a zero marker so learned replay stays fail-closed"
    );
    assert_eq!(record.materializer_dependency_ids, vec![materializer_id]);
    assert_eq!(record.source_clause_dependency_ids, materializer_source_ids);
    assert!(!record.proof_out_emitted);
    assert!(!record.proof_writer_io_error);
    assert_eq!(
        record.authority_status,
        LearnedLratAuthorityStatus::FailClosedMaterializer
    );

    let exports = proof_manager.materialize_fmla_learned_lrat_authority_exports();
    assert_eq!(exports.len(), 1);
    let export = &exports[0];
    assert_eq!(
        export.checker_visible_lrat_hints,
        vec![8, 7, 3, 2, 6, 1, materializer_id],
        "proof-manager export should deduplicate checker-visible hints only at the boundary"
    );
    assert_eq!(export.materializer_rows.len(), 1);
    assert_eq!(
        export.materialization_status,
        LearnedLratMaterializationStatus::FailClosedIncompleteLearnedDependency
    );

    let replays = proof_manager.checked_fmla_learned_lrat_materialization_replays();
    assert_eq!(replays.len(), 1);
    let replay = &replays[0];
    assert_eq!(
        replay.materialization_status,
        LearnedLratMaterializationStatus::FailClosedIncompleteLearnedDependency
    );
    assert_eq!(replay.rows.len(), 1);
    assert_eq!(
        replay.rows[0].kind,
        LearnedLratReplayRowKind::MaterializerAdd
    );
    assert_eq!(replay.rows[0].checker_visible_id, materializer_id);

    let artifacts = proof_manager.dry_run_fmla_learned_lrat_materialization_fragments();
    assert_eq!(artifacts.len(), 1);
    let artifact = &artifacts[0];
    assert_eq!(
        artifact.materialization_status,
        LearnedLratMaterializationStatus::FailClosedIncompleteLearnedDependency
    );
    assert_eq!(artifact.rows.len(), 1);
    assert_eq!(
        artifact.rows[0].kind,
        LearnedLratReplayRowKind::MaterializerAdd
    );
    assert_eq!(artifact.rows[0].checker_visible_id, materializer_id);
    assert!(!artifact.external_checker_required);
    assert!(!artifact.external_checker_verified);
    assert_eq!(
        artifact.main_proof_authority_reason,
        LEARNED_LRAT_AUTHORITY_FAIL_CLOSED
    );
    assert!(
        !artifact.authorizes_main_proof_out,
        "retained dry-run rows are not Main proof.out authority without checker validation"
    );

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be available");
    let proof_text = String::from_utf8(writer.into_vec().expect("proof flush"))
        .expect("proof bytes should be valid UTF-8");
    assert!(
        proof_text
            .lines()
            .all(|line| !line.starts_with(&format!("{learned_id} "))),
        "retained learned authority evidence must not forward-emit {learned_id}\nproof:\n{proof_text}"
    );
}

#[test]
fn test_fmla_fail_closed_empty_learned_chain_retains_materializer_diagnostic() {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    add_padding_original_clauses(&mut solver, 8);

    let materializer_context = DecomposeProofEmitContext {
        transaction_id: 46,
        sidecar_context_token: "fmla-guarded-equiv-support-cover-lrat-46".to_string(),
        sidecar_row_index: 0,
        source_row_id: "fmla-guarded-equiv-support-cover-source-1".to_string(),
        obligation_id: "fmla-guarded-equiv-support-cover-46-0".to_string(),
    };
    let materializer_clause = vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(4)),
    ];
    let materializer_id = solver
        .proof_manager
        .as_mut()
        .expect("proof manager")
        .emit_add_with_decompose_context(
            &materializer_clause,
            &[1, 6, 3],
            ProofAddKind::Derived,
            &materializer_context,
        )
        .expect("emit materializer proof row");

    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_attempt(1, 1);
    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_fail_closed(false);

    let learned_ref = solver.add_conflict_learned_clause(
        vec![
            Literal::positive(Variable(0)),
            Literal::negative(Variable(1)),
        ],
        1,
        Vec::new(),
    );
    let learned_id = solver.clause_id(learned_ref);
    let proof_manager = solver.proof_manager.as_ref().expect("proof manager");
    let authority_records = proof_manager.learned_lrat_authority_records();
    assert_eq!(authority_records.len(), 1);
    assert_eq!(authority_records[0].checker_visible_id, learned_id);
    assert!(authority_records[0].raw_resolution_chain.is_empty());
    assert_eq!(authority_records[0].lrat_hints, vec![0, materializer_id]);
    assert_eq!(
        authority_records[0].materializer_dependency_ids,
        vec![materializer_id]
    );

    let artifacts = proof_manager.dry_run_fmla_learned_lrat_materialization_fragments();
    assert_eq!(artifacts.len(), 1);
    assert_eq!(
        artifacts[0].materialization_status,
        LearnedLratMaterializationStatus::FailClosedIncompleteLearnedDependency
    );
    assert_eq!(artifacts[0].rows.len(), 1);
    assert_eq!(artifacts[0].rows[0].checker_visible_id, materializer_id);
    assert!(!artifacts[0].external_checker_required);
    assert!(!artifacts[0].authorizes_main_proof_out);
}

#[test]
fn test_fmla_unchecked_materializer_learned_chain_records_authority_without_forward_emit() {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    add_padding_original_clauses(&mut solver, 8);

    let materializer_context = DecomposeProofEmitContext {
        transaction_id: 48,
        sidecar_context_token: "fmla-guarded-equiv-support-cover-lrat-48".to_string(),
        sidecar_row_index: 0,
        source_row_id: "fmla-guarded-equiv-support-cover-source-1".to_string(),
        obligation_id: "fmla-guarded-equiv-support-cover-48-0".to_string(),
    };
    let materializer_id = emit_test_lrat_materializer_row(&mut solver, &materializer_context);
    let stats_before = solver.inproc.decompose_engine.lrat_preflight_stats();
    assert_eq!(stats_before.main_rewrite_materializer_fail_closed, 0);

    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;
    let a = Literal::positive(Variable(0));
    let b = Literal::negative(Variable(1));
    let learned_chain = vec![1, materializer_id, 6];
    let learned_ref = solver.add_conflict_learned_clause(vec![a, b], 1, learned_chain.clone());
    let learned_id = solver.clause_id(learned_ref);

    let proof_manager = solver.proof_manager.as_ref().expect("proof manager");
    assert!(
        proof_manager.has_lrat_authority_fail_closed(),
        "unchecked Fmla materializer rows must keep learned LRAT authority fail-closed"
    );
    let authority_records = proof_manager.learned_lrat_authority_records();
    assert_eq!(authority_records.len(), 1);
    let record = &authority_records[0];
    assert_eq!(record.checker_visible_id, learned_id);
    assert_eq!(record.raw_resolution_chain, learned_chain);
    assert_eq!(record.lrat_hints, vec![6, materializer_id, 1]);
    assert_eq!(record.materializer_dependency_ids, vec![materializer_id]);
    assert_eq!(record.source_clause_dependency_ids, vec![1, 6, 3]);
    assert!(!record.proof_out_emitted);
    assert_eq!(
        record.authority_status,
        LearnedLratAuthorityStatus::FailClosedMaterializer
    );

    let artifacts = proof_manager.dry_run_fmla_learned_lrat_materialization_fragments();
    assert_eq!(artifacts.len(), 1);
    assert_eq!(
        artifacts[0].materialization_status,
        LearnedLratMaterializationStatus::RetainedDependenciesComplete
    );
    assert!(artifacts[0].external_checker_required);
    assert!(!artifacts[0].external_checker_verified);
    assert!(!artifacts[0].authorizes_main_proof_out);

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be available");
    let proof_text = String::from_utf8(writer.into_vec().expect("proof flush"))
        .expect("proof bytes should be valid UTF-8");
    assert!(
        proof_text.contains(&format!("{materializer_id} 1 5 0 1 6 3 0\n")),
        "Fmla materializer row should remain in proof output\nproof:\n{proof_text}"
    );
    assert!(
        proof_text
            .lines()
            .all(|line| !line.starts_with(&format!("{learned_id} "))),
        "unchecked Fmla learned clause {learned_id} must not be forward-emitted\nproof:\n{proof_text}"
    );
}

#[test]
fn test_fmla_unchecked_empty_learned_chain_retains_materializer_diagnostic() {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    add_padding_original_clauses(&mut solver, 8);

    let materializer_context = DecomposeProofEmitContext {
        transaction_id: 49,
        sidecar_context_token: "fmla-guarded-equiv-support-cover-lrat-49".to_string(),
        sidecar_row_index: 0,
        source_row_id: "fmla-guarded-equiv-support-cover-source-1".to_string(),
        obligation_id: "fmla-guarded-equiv-support-cover-49-0".to_string(),
    };
    let materializer_id = emit_test_lrat_materializer_row(&mut solver, &materializer_context);
    assert_eq!(
        solver
            .inproc
            .decompose_engine
            .lrat_preflight_stats()
            .main_rewrite_materializer_fail_closed,
        0
    );

    let learned_ref = solver.add_conflict_learned_clause(
        vec![
            Literal::positive(Variable(0)),
            Literal::negative(Variable(1)),
        ],
        1,
        Vec::new(),
    );
    let learned_id = solver.clause_id(learned_ref);
    let proof_manager = solver.proof_manager.as_ref().expect("proof manager");
    assert!(proof_manager.has_lrat_authority_fail_closed());
    let authority_records = proof_manager.learned_lrat_authority_records();
    assert_eq!(authority_records.len(), 1);
    assert_eq!(authority_records[0].checker_visible_id, learned_id);
    assert!(authority_records[0].raw_resolution_chain.is_empty());
    assert_eq!(authority_records[0].lrat_hints, vec![0, materializer_id]);
    assert_eq!(
        authority_records[0].materializer_dependency_ids,
        vec![materializer_id]
    );

    let artifacts = proof_manager.dry_run_fmla_learned_lrat_materialization_fragments();
    assert_eq!(artifacts.len(), 1);
    assert_eq!(
        artifacts[0].materialization_status,
        LearnedLratMaterializationStatus::FailClosedIncompleteLearnedDependency
    );
    assert_eq!(artifacts[0].rows.len(), 1);
    assert_eq!(artifacts[0].rows[0].checker_visible_id, materializer_id);
    assert!(!artifacts[0].external_checker_required);
    assert!(!artifacts[0].authorizes_main_proof_out);

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be available");
    let proof_text = String::from_utf8(writer.into_vec().expect("proof flush"))
        .expect("proof bytes should be valid UTF-8");
    assert!(
        proof_text
            .lines()
            .all(|line| !line.starts_with(&format!("{learned_id} "))),
        "empty-chain Fmla learned clause {learned_id} must not be forward-emitted\nproof:\n{proof_text}"
    );
}

#[test]
fn test_non_fmla_decompose_materializer_does_not_block_forward_learned_lrat_emit() {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    add_padding_original_clauses(&mut solver, 8);

    let materializer_context = DecomposeProofEmitContext {
        transaction_id: 50,
        sidecar_context_token: String::from(concat!("decompose-lrat-", "50")),
        sidecar_row_index: 0,
        source_row_id: "decompose-lrat-source-1".to_string(),
        obligation_id: "decompose-lrat-50-0".to_string(),
    };
    let materializer_id = emit_test_lrat_materializer_row(&mut solver, &materializer_context);

    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;
    let a = Literal::positive(Variable(0));
    let b = Literal::negative(Variable(1));
    let learned_ref =
        solver.add_conflict_learned_clause(vec![a, b], 1, vec![1, materializer_id, 6]);
    let learned_id = solver.clause_id(learned_ref);

    let proof_manager = solver.proof_manager.as_ref().expect("proof manager");
    assert!(!proof_manager.has_lrat_authority_fail_closed());
    assert!(proof_manager.learned_lrat_authority_records().is_empty());

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be available");
    let proof_text = String::from_utf8(writer.into_vec().expect("proof flush"))
        .expect("proof bytes should be valid UTF-8");
    assert_eq!(
        proof_text,
        format!("{materializer_id} 1 5 0 1 6 3 0\n{learned_id} 1 -2 0 6 {materializer_id} 1 0\n")
    );
}

#[test]
fn test_fmla_learned_lrat_dry_run_artifact_export_writes_retained_json() {
    let (mut solver, materializer_id, learned_id) =
        setup_retained_fmla_learned_lrat_dry_run_fixture();
    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_fail_closed_detail(true, 0, 440_513);
    let dir = tempfile::tempdir().expect("tempdir");
    let artifact_path = dir
        .path()
        .join("fmla-learned-lrat-dry-run-proof-artifact.json");

    let written = solver
        .write_fmla_learned_lrat_dry_run_proof_artifact_json(&artifact_path)
        .expect("write dry-run artifact");
    assert_eq!(written.as_deref(), Some(artifact_path.as_path()));

    let artifact_bytes = std::fs::read(&artifact_path).expect("artifact bytes");
    let artifact_json: serde_json::Value =
        serde_json::from_slice(&artifact_bytes).expect("artifact json");
    assert_eq!(
        artifact_json["schema"].as_str(),
        Some(FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA)
    );
    assert_eq!(
        artifact_json["materialization_status"].as_str(),
        Some("retained_dependencies_complete")
    );
    assert_eq!(
        artifact_json["checker_visible_id"].as_u64(),
        Some(learned_id),
        "complete learned artifact must outrank bounded missing-materializer fallback"
    );
    assert_eq!(
        artifact_json["external_checker_required"].as_bool(),
        Some(true)
    );
    assert_eq!(
        artifact_json["external_checker_verified"].as_bool(),
        Some(false)
    );
    assert_eq!(
        artifact_json["authorizes_main_proof_out"].as_bool(),
        Some(false),
        "solver-side export must remain evidence-only until postcheck replay"
    );
    let fragment = artifact_json["lrat_fragment"]
        .as_str()
        .expect("lrat fragment");
    assert!(
        fragment.contains(&format!("{materializer_id} 1 5 0 1 6 3 0\n")),
        "artifact must retain checker-visible materializer row\n{fragment}"
    );
    assert!(
        fragment.contains(&format!("{learned_id} 1 -2 0 6 {materializer_id} 1 0\n")),
        "artifact must retain checker-visible learned row\n{fragment}"
    );
}

#[test]
fn test_fmla_learned_lrat_dry_run_artifact_export_prefers_learned_diagnostic_over_bounded_fallback()
{
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    add_padding_original_clauses(&mut solver, 8);

    let materializer_context = DecomposeProofEmitContext {
        transaction_id: 44,
        sidecar_context_token: "fmla-guarded-equiv-support-cover-lrat-44".to_string(),
        sidecar_row_index: 0,
        source_row_id: "fmla-guarded-equiv-support-cover-source-1".to_string(),
        obligation_id: "fmla-guarded-equiv-support-cover-44-0".to_string(),
    };
    let materializer_clause = vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(4)),
    ];
    let learned_clause = vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
    ];
    let learned_id = {
        let proof_manager = solver.proof_manager.as_mut().expect("proof manager");
        let materializer_id = proof_manager
            .emit_add_with_decompose_context(
                &materializer_clause,
                &[1, 6, 3],
                ProofAddKind::Derived,
                &materializer_context,
            )
            .expect("emit materializer proof row");
        proof_manager.mark_lrat_authority_fail_closed();
        let learned_id = proof_manager.reserve_lrat_id_for_backward();
        proof_manager.record_fmla_learned_lrat_authority_fail_closed(
            learned_id,
            &learned_clause,
            &[1, materializer_id, 99],
            &[6, materializer_id, 99, 1],
        );
        learned_id
    };
    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_fail_closed_detail(true, 0, 440_513);

    let dir = tempfile::tempdir().expect("tempdir");
    let artifact_path = dir
        .path()
        .join("fmla-learned-lrat-dry-run-proof-artifact.json");

    let written = solver
        .write_fmla_learned_lrat_dry_run_proof_artifact_json(&artifact_path)
        .expect("write dry-run artifact");
    assert_eq!(written.as_deref(), Some(artifact_path.as_path()));
    let artifact_json: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&artifact_path).expect("artifact bytes"))
            .expect("artifact json");
    assert_eq!(
        artifact_json["checker_visible_id"].as_u64(),
        Some(learned_id),
        "learned-authority diagnostic must not be replaced by bounded materializer fallback"
    );
    assert_eq!(
        artifact_json["materialization_status"].as_str(),
        Some("fail_closed_incomplete_learned_dependency")
    );
    assert_eq!(artifact_json["rows"].as_array().map(Vec::len), Some(1));
    assert_eq!(
        artifact_json["rows"][0]["kind"].as_str(),
        Some("materializer_add")
    );
    assert_eq!(
        artifact_json["authorizes_main_proof_out"].as_bool(),
        Some(false)
    );
}

#[test]
fn test_fmla_learned_lrat_dry_run_artifact_export_writes_fail_closed_diagnostic() {
    let (solver, learned_id) = setup_missing_materializer_fmla_learned_lrat_dry_run_fixture();
    let dir = tempfile::tempdir().expect("tempdir");
    let artifact_path = dir
        .path()
        .join("fmla-learned-lrat-dry-run-proof-artifact.json");

    let written = solver
        .write_fmla_learned_lrat_dry_run_proof_artifact_json(&artifact_path)
        .expect("write dry-run artifact");
    assert_eq!(written.as_deref(), Some(artifact_path.as_path()));

    let artifact_bytes = std::fs::read(&artifact_path).expect("artifact bytes");
    let artifact_json: serde_json::Value =
        serde_json::from_slice(&artifact_bytes).expect("artifact json");
    assert_eq!(
        artifact_json["schema"].as_str(),
        Some(FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA)
    );
    assert_eq!(
        artifact_json["checker_visible_id"].as_u64(),
        Some(learned_id)
    );
    assert_eq!(
        artifact_json["materialization_status"].as_str(),
        Some("fail_closed_missing_materializer_dependency")
    );
    assert_eq!(artifact_json["rows"].as_array().map(Vec::len), Some(0));
    assert_eq!(artifact_json["lrat_fragment"].as_str(), Some(""));
    assert_eq!(
        artifact_json["external_checker_required"].as_bool(),
        Some(false)
    );
    assert_eq!(
        artifact_json["main_proof_authority_reason"].as_str(),
        Some(LEARNED_LRAT_AUTHORITY_FAIL_CLOSED)
    );
    assert_eq!(
        artifact_json["authorizes_main_proof_out"].as_bool(),
        Some(false)
    );
}

#[test]
fn test_fmla_learned_lrat_dry_run_artifact_export_runs_before_take_proof_writer() {
    let _lock = lock_fmla_learned_lrat_env_test();
    let (mut solver, materializer_id, learned_id) =
        setup_retained_fmla_learned_lrat_dry_run_fixture();
    let dir = tempfile::tempdir().expect("tempdir");
    let artifact_path = dir
        .path()
        .join("fmla-learned-lrat-dry-run-proof-artifact.json");
    let _dry_run = ScopedEnvVar::set(
        FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_PATH_ENV,
        artifact_path.to_str().expect("temp path is UTF-8"),
    );

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be returned");
    drop(writer);
    assert!(
        solver.proof_writer().is_none(),
        "take_proof_writer must still consume the proof manager"
    );
    assert!(
        artifact_path.is_file(),
        "timeout cleanup path must retain dry-run artifact before consuming proof writer"
    );
    let artifact_json: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&artifact_path).expect("artifact bytes"))
            .expect("artifact json");
    assert_eq!(
        artifact_json["schema"].as_str(),
        Some(FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA)
    );
    assert_eq!(
        artifact_json["authorizes_main_proof_out"].as_bool(),
        Some(false),
        "pre-timeout export remains evidence-only"
    );
    let fragment = artifact_json["lrat_fragment"]
        .as_str()
        .expect("lrat fragment");
    assert!(fragment.contains(&format!("{materializer_id} 1 5 0 1 6 3 0\n")));
    assert!(fragment.contains(&format!("{learned_id} 1 -2 0 6 {materializer_id} 1 0\n")));
}

#[test]
fn test_fmla_learned_lrat_dry_run_artifact_take_proof_writer_replaces_stale_artifact() {
    let _lock = lock_fmla_learned_lrat_env_test();
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    let dir = tempfile::tempdir().expect("tempdir");
    let artifact_path = dir
        .path()
        .join("fmla-learned-lrat-dry-run-proof-artifact.json");
    std::fs::write(&artifact_path, b"stale artifact").expect("seed stale artifact");
    let _dry_run = ScopedEnvVar::set(
        FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_PATH_ENV,
        artifact_path.to_str().expect("temp path is UTF-8"),
    );

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be returned");
    drop(writer);
    assert!(
        artifact_path.exists(),
        "timeout cleanup path must replace stale dry-run artifact with a fail-closed diagnostic"
    );
    let artifact_json: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&artifact_path).expect("artifact bytes"))
            .expect("artifact json");
    assert_eq!(
        artifact_json["schema"].as_str(),
        Some(FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA)
    );
    let status = artifact_json["materialization_status"]
        .as_str()
        .expect("materialization status");
    assert!(
        status == "retained_dependencies_complete" || status.starts_with("fail_closed_"),
        "timeout cleanup path must write a recognized non-authorizing diagnostic, got {status}"
    );
    if status.starts_with("fail_closed_") {
        assert_eq!(
            artifact_json["main_proof_authority_reason"].as_str(),
            Some(LEARNED_LRAT_AUTHORITY_FAIL_CLOSED)
        );
    }
    assert_eq!(
        artifact_json["authorizes_main_proof_out"].as_bool(),
        Some(false)
    );
}

#[test]
fn test_fmla_learned_lrat_dry_run_artifact_export_writes_no_records_diagnostic() {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let solver: Solver = Solver::with_proof_output(20, proof);
    let dir = tempfile::tempdir().expect("tempdir");
    let artifact_path = dir
        .path()
        .join("fmla-learned-lrat-dry-run-proof-artifact.json");
    std::fs::write(&artifact_path, b"stale artifact").expect("seed stale artifact");

    let written = solver
        .write_fmla_learned_lrat_dry_run_proof_artifact_json(&artifact_path)
        .expect("write fail-closed diagnostic");
    assert_eq!(written.as_deref(), Some(artifact_path.as_path()));
    let artifact_json: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&artifact_path).expect("artifact bytes"))
            .expect("artifact json");
    assert_eq!(artifact_json["checker_visible_id"].as_u64(), Some(0));
    assert_eq!(
        artifact_json["materialization_status"].as_str(),
        Some("fail_closed_no_learned_lrat_authority_records")
    );
    assert_eq!(artifact_json["rows"].as_array().map(Vec::len), Some(0));
    assert_eq!(artifact_json["lrat_fragment"].as_str(), Some(""));
    assert_eq!(
        artifact_json["external_checker_required"].as_bool(),
        Some(false)
    );
    assert_eq!(
        artifact_json["main_proof_authority_reason"].as_str(),
        Some(LEARNED_LRAT_AUTHORITY_FAIL_CLOSED)
    );
    assert_eq!(
        artifact_json["authorizes_main_proof_out"].as_bool(),
        Some(false)
    );
}

#[test]
fn test_fmla_learned_lrat_dry_run_artifact_reports_materializer_reject_without_learned_records() {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    let missing_checker_visible_id = 173_569;
    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_attempt(2560, 0);
    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_fail_closed_detail(
            true,
            0,
            missing_checker_visible_id,
        );

    let dir = tempfile::tempdir().expect("tempdir");
    let artifact_path = dir
        .path()
        .join("fmla-learned-lrat-dry-run-proof-artifact.json");

    let written = solver
        .write_fmla_learned_lrat_dry_run_proof_artifact_json(&artifact_path)
        .expect("write fail-closed materializer diagnostic");
    assert_eq!(written.as_deref(), Some(artifact_path.as_path()));
    let artifact_json: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&artifact_path).expect("artifact bytes"))
            .expect("artifact json");
    assert_eq!(
        artifact_json["checker_visible_id"].as_u64(),
        Some(missing_checker_visible_id)
    );
    assert_eq!(
        artifact_json["materialization_status"].as_str(),
        Some("fail_closed_missing_materializer_dependency")
    );
    assert_eq!(artifact_json["rows"].as_array().map(Vec::len), Some(0));
    assert_eq!(
        artifact_json["external_checker_required"].as_bool(),
        Some(false)
    );
    assert_eq!(
        artifact_json["authorizes_main_proof_out"].as_bool(),
        Some(false)
    );
}

#[test]
fn test_fmla_learned_lrat_dry_run_artifact_export_retains_sidecar_rows_when_records_zero() {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    let planned_add_id = 440_513;
    solver
        .inproc
        .decompose_engine
        .set_fmla_guarded_equiv_support_cover_lrat_sidecars(vec![
            FmlaGuardedEquivSupportCoverLratSidecar {
                planned_add_id,
                support_clause_id: 3,
                support_guard_lits_dimacs: vec![4],
                source_lit_dimacs: 1,
                destination_lits_dimacs: vec![5],
                clause_lits_dimacs: vec![1, 5],
                directional_ternary_source_ids: vec![1, 6],
                lrat_hints: vec![1, 6, 3],
            },
        ]);
    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_attempt(2560, 0);
    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_fail_closed_detail(true, 0, planned_add_id);

    let dir = tempfile::tempdir().expect("tempdir");
    let artifact_path = dir
        .path()
        .join("fmla-learned-lrat-dry-run-proof-artifact.json");

    let written = solver
        .write_fmla_learned_lrat_dry_run_proof_artifact_json(&artifact_path)
        .expect("write dry-run artifact");
    assert_eq!(written.as_deref(), Some(artifact_path.as_path()));
    let artifact_json: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&artifact_path).expect("artifact bytes"))
            .expect("artifact json");
    assert_eq!(
        artifact_json["checker_visible_id"].as_u64(),
        Some(planned_add_id)
    );
    assert_eq!(
        artifact_json["materialization_status"].as_str(),
        Some("fail_closed_no_learned_lrat_authority_records")
    );
    assert_eq!(artifact_json["rows"].as_array().map(Vec::len), Some(1));
    assert_eq!(
        artifact_json["rows"][0]["kind"].as_str(),
        Some("materializer_add")
    );
    assert_eq!(
        artifact_json["rows"][0]["checker_visible_id"].as_u64(),
        Some(planned_add_id)
    );
    let expected_lrat_line = format!("{planned_add_id} 1 5 0 1 6 3 0\n");
    assert_eq!(
        artifact_json["rows"][0]["lrat_line"].as_str(),
        Some(expected_lrat_line.as_str())
    );
    assert_eq!(
        artifact_json["lrat_fragment"].as_str(),
        Some(expected_lrat_line.as_str())
    );
    assert_eq!(
        artifact_json["authorizes_main_proof_out"].as_bool(),
        Some(false)
    );
}

#[test]
fn test_fmla_learned_lrat_dry_run_artifact_retains_materializer_rows_without_learned_records() {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    add_padding_original_clauses(&mut solver, 8);
    let materializer_context = DecomposeProofEmitContext {
        transaction_id: 47,
        sidecar_context_token: "fmla-guarded-equiv-support-cover-lrat-47".to_string(),
        sidecar_row_index: 0,
        source_row_id: "fmla-guarded-equiv-support-cover-source-1".to_string(),
        obligation_id: "fmla-guarded-equiv-support-cover-47-0".to_string(),
    };
    let materializer_id = solver
        .proof_manager
        .as_mut()
        .expect("proof manager")
        .emit_add_with_decompose_context(
            &[
                Literal::positive(Variable(0)),
                Literal::positive(Variable(4)),
            ],
            &[1, 6, 3],
            ProofAddKind::Derived,
            &materializer_context,
        )
        .expect("emit materializer proof row");
    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_attempt(1, 1);
    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_fail_closed_detail(true, 0, materializer_id);

    let dir = tempfile::tempdir().expect("tempdir");
    let artifact_path = dir
        .path()
        .join("fmla-learned-lrat-dry-run-proof-artifact.json");

    solver
        .write_fmla_learned_lrat_dry_run_proof_artifact_json(&artifact_path)
        .expect("write fail-closed materializer row diagnostic");
    let artifact_json: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&artifact_path).expect("artifact bytes"))
            .expect("artifact json");
    assert_eq!(
        artifact_json["materialization_status"].as_str(),
        Some("fail_closed_no_learned_lrat_authority_records")
    );
    assert_eq!(artifact_json["rows"].as_array().map(Vec::len), Some(1));
    assert_eq!(
        artifact_json["rows"][0]["checker_visible_id"].as_u64(),
        Some(materializer_id)
    );
    assert_eq!(
        artifact_json["authorizes_main_proof_out"].as_bool(),
        Some(false)
    );
}

#[test]
fn test_fmla_learned_lrat_dry_run_artifact_export_writes_no_records_without_proof_manager() {
    let solver: Solver = Solver::new(2);
    let dir = tempfile::tempdir().expect("tempdir");
    let artifact_path = dir
        .path()
        .join("fmla-learned-lrat-dry-run-proof-artifact.json");
    std::fs::write(&artifact_path, b"stale artifact").expect("seed stale artifact");

    let written = solver
        .write_fmla_learned_lrat_dry_run_proof_artifact_json(&artifact_path)
        .expect("write fail-closed diagnostic");
    assert_eq!(written.as_deref(), Some(artifact_path.as_path()));
    let artifact_json: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&artifact_path).expect("artifact bytes"))
            .expect("artifact json");
    assert_eq!(
        artifact_json["materialization_status"].as_str(),
        Some("fail_closed_no_learned_lrat_authority_records")
    );
    assert_eq!(
        artifact_json["authorizes_main_proof_out"].as_bool(),
        Some(false)
    );
}

#[test]
fn test_fmla_fail_closed_learned_lrat_replay_rejects_incomplete_learned_dependency() {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(20, proof);
    add_padding_original_clauses(&mut solver, 8);

    let materializer_context = DecomposeProofEmitContext {
        transaction_id: 43,
        sidecar_context_token: "fmla-guarded-equiv-support-cover-lrat-43".to_string(),
        sidecar_row_index: 0,
        source_row_id: "fmla-guarded-equiv-support-cover-source-1".to_string(),
        obligation_id: "fmla-guarded-equiv-support-cover-43-0".to_string(),
    };
    let materializer_clause = vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(4)),
    ];
    let materializer_source_ids = vec![1, 6, 3];
    let learned_clause = vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
    ];
    let missing_dependency_id = 99;
    let (learned_id, materializer_id) = {
        let proof_manager = solver.proof_manager.as_mut().expect("proof manager");
        let materializer_id = proof_manager
            .emit_add_with_decompose_context(
                &materializer_clause,
                &materializer_source_ids,
                ProofAddKind::Derived,
                &materializer_context,
            )
            .expect("emit materializer proof row");
        proof_manager.mark_lrat_authority_fail_closed();
        let learned_id = proof_manager.reserve_lrat_id_for_backward();
        proof_manager.record_fmla_learned_lrat_authority_fail_closed(
            learned_id,
            &learned_clause,
            &[1, materializer_id, missing_dependency_id],
            &[6, materializer_id, missing_dependency_id, 1],
        );
        (learned_id, materializer_id)
    };

    let proof_manager = solver.proof_manager.as_ref().expect("proof manager");
    assert!(proof_manager.has_lrat_authority_fail_closed());
    let exports = proof_manager.materialize_fmla_learned_lrat_authority_exports();
    assert_eq!(exports.len(), 1);
    let export = &exports[0];
    assert_eq!(export.checker_visible_id, learned_id);
    assert_eq!(
        export.checker_visible_lrat_hints,
        vec![6, materializer_id, 1],
        "unknown learned dependency must be omitted from checker-visible replay hints"
    );
    assert_eq!(export.materializer_rows.len(), 1);
    assert_eq!(
        export.materialization_status,
        LearnedLratMaterializationStatus::FailClosedIncompleteLearnedDependency
    );
    let replays = proof_manager.checked_fmla_learned_lrat_materialization_replays();
    assert_eq!(replays.len(), 1);
    let replay = &replays[0];
    assert_eq!(replay.checker_visible_id, learned_id);
    assert_eq!(
        replay.materialization_status,
        LearnedLratMaterializationStatus::FailClosedIncompleteLearnedDependency
    );
    assert_eq!(
        replay.rows.len(),
        1,
        "incomplete learned dependency should retain materializer-only diagnostic rows"
    );
    assert_eq!(
        replay.rows[0].kind,
        LearnedLratReplayRowKind::MaterializerAdd
    );
    assert_eq!(
        replay.rows[0].checker_visible_id, materializer_id,
        "diagnostic replay must keep the concrete materializer dependency"
    );
    assert!(!replay.proof_out_emitted);
    assert!(!replay.proof_writer_io_error);
    let artifacts = proof_manager.dry_run_fmla_learned_lrat_materialization_fragments();
    assert_eq!(artifacts.len(), 1);
    let artifact = &artifacts[0];
    assert_eq!(artifact.checker_visible_id, learned_id);
    assert_eq!(
        artifact.materialization_status,
        LearnedLratMaterializationStatus::FailClosedIncompleteLearnedDependency
    );
    assert_eq!(
        artifact.rows.len(),
        1,
        "incomplete learned dependency should serialize materializer-only diagnostic rows"
    );
    assert_eq!(
        artifact.rows[0].kind,
        LearnedLratReplayRowKind::MaterializerAdd
    );
    assert_eq!(artifact.rows[0].checker_visible_id, materializer_id);
    assert_eq!(artifact.rows[0].lrat_line, artifact.lrat_fragment);
    assert!(!artifact.proof_out_emitted);
    assert!(!artifact.proof_writer_io_error);
    assert!(!artifact.external_checker_required);
    assert!(!artifact.external_checker_verified);
    assert_eq!(
        artifact.main_proof_authority_reason,
        LEARNED_LRAT_AUTHORITY_FAIL_CLOSED
    );
    assert!(!artifact.authorizes_main_proof_out);

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be available");
    let proof_text = String::from_utf8(writer.into_vec().expect("proof flush"))
        .expect("proof bytes should be valid UTF-8");
    assert!(
        proof_text
            .lines()
            .all(|line| !line.starts_with(&format!("{learned_id} "))),
        "incomplete learned dependency must not emit learned clause {learned_id}\nproof:\n{proof_text}"
    );
}

#[test]
fn test_fmla_fail_closed_learned_lrat_chain_final_solve_returns_unknown() {
    let proof = ProofOutput::lrat_text(Vec::new(), 8);
    let mut solver: Solver = Solver::with_proof_output(24, proof);
    add_padding_original_clauses(&mut solver, 8);
    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_attempt(1, 1);
    solver
        .inproc
        .decompose_engine
        .record_lrat_main_rewrite_materializer_fail_closed(false);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;

    let a = Literal::positive(Variable(0));
    let b = Literal::negative(Variable(1));
    let learned_ref =
        solver.add_conflict_learned_clause(vec![a, b], 1, vec![1, 6, 3, 6, 2, 3, 8, 7, 8]);
    let learned_id = solver.clause_id(learned_ref);
    let stats = solver.inproc.decompose_engine.lrat_preflight_stats();
    assert_eq!(stats.main_rewrite_materializer_records, 1);
    assert_eq!(stats.main_rewrite_materializer_fail_closed, 1);

    let contradiction = Literal::positive(Variable(10));
    solver.add_clause(vec![contradiction]);
    solver.add_clause(vec![contradiction.negated()]);

    let result = solver.solve().into_inner();

    assert!(
        result.is_unknown(),
        "Fmla fail-closed learned LRAT authority must not return UNSAT: {result:?}"
    );
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::ProofFinalizationFailure)
    );
    let detail = solver
        .last_unknown_detail()
        .expect("proof finalization failure should explain the downgrade");
    assert!(
        detail.contains("LRAT authority fail-closed"),
        "unexpected proof finalization detail: {detail}"
    );
    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be available");
    let proof_text = String::from_utf8(writer.into_vec().expect("proof flush"))
        .expect("proof bytes should be valid UTF-8");
    assert!(
        proof_text
            .lines()
            .all(|line| !line.starts_with(&format!("{learned_id} "))),
        "Fmla fail-closed learned clause {learned_id} must not be forward-emitted\nproof:\n{proof_text}"
    );
}

#[test]
fn test_lrat_authority_fail_closed_replay_diagnostic_still_downgrades_unsat() {
    let _lock = lock_fmla_learned_lrat_env_test();
    let _dry_run = ScopedEnvVar::unset(FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_PATH_ENV);
    let dir = tempfile::tempdir().expect("tempdir");
    let seed_proof = dir.path().join("seed-proof.out");

    let seed_result = solve_latched_lrat_unit_contradiction_to_file(&seed_proof);
    assert!(seed_result.is_unknown());
    let seed_proof_bytes = std::fs::read(&seed_proof).expect("seed proof bytes");
    assert!(
        !seed_proof_bytes.is_empty(),
        "fail-closed finalization should still flush diagnostic proof bytes"
    );

    let proof_out = dir.path().join("proof.out");
    let replay = dir
        .path()
        .join("fmla-main-lrat-postcheck-admission-replay.json");
    write_fmla_main_lrat_authority_replay(
        &replay,
        &proof_out,
        &sha256_hex(&seed_proof_bytes),
        false,
    );
    let _replay = ScopedEnvVar::set(
        FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV,
        replay.to_str().expect("temp path is UTF-8"),
    );
    let _proof_out = ScopedEnvVar::set(
        FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
        proof_out.to_str().expect("temp path is UTF-8"),
    );

    let result = solve_latched_lrat_unit_contradiction_to_file(&proof_out);
    assert!(
        result.is_unknown(),
        "fail-closed authority replay must not admit UNSAT: {result:?}"
    );
}

#[test]
fn test_lrat_authority_fail_closed_complete_verified_replay_admits_unsat() {
    let _lock = lock_fmla_learned_lrat_env_test();
    let _dry_run = ScopedEnvVar::unset(FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_PATH_ENV);
    let dir = tempfile::tempdir().expect("tempdir");
    let seed_proof = dir.path().join("seed-proof.out");

    let seed_result = solve_latched_lrat_unit_contradiction_to_file(&seed_proof);
    assert!(seed_result.is_unknown());
    let seed_proof_bytes = std::fs::read(&seed_proof).expect("seed proof bytes");
    assert!(
        !seed_proof_bytes.is_empty(),
        "seed run should write the proof bytes later bound by authority replay"
    );

    let proof_out = dir.path().join("proof.out");
    let replay = dir
        .path()
        .join("fmla-main-lrat-postcheck-admission-replay.json");
    write_fmla_main_lrat_authority_replay(
        &replay,
        &proof_out,
        &sha256_hex(&seed_proof_bytes),
        true,
    );
    let _replay = ScopedEnvVar::set(
        FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV,
        replay.to_str().expect("temp path is UTF-8"),
    );
    let _proof_out = ScopedEnvVar::set(
        FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
        proof_out.to_str().expect("temp path is UTF-8"),
    );

    let result = solve_latched_lrat_unit_contradiction_to_file(&proof_out);
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "complete verified authority replay should admit UNSAT: {result:?}"
    );
    let admitted_proof_bytes = std::fs::read(&proof_out).expect("admitted proof bytes");
    assert_eq!(
        sha256_hex(&admitted_proof_bytes),
        sha256_hex(&seed_proof_bytes),
        "authority replay should bind to the exact proof.out bytes"
    );
}

#[test]
fn test_add_conflict_learned_clause_trace_keeps_raw_hints() {
    let proof = ProofOutput::lrat_text(Vec::new(), 10);
    let mut solver: Solver = Solver::with_proof_output(24, proof);
    add_padding_original_clauses(&mut solver, 10);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;
    solver.cold.clause_trace = Some(ClauseTrace::new());

    let a = Literal::positive(Variable(0));
    let b = Literal::negative(Variable(1));
    let chain = vec![1, 6, 3, 2, 8, 7];
    let clause_ref = solver.add_conflict_learned_clause(vec![a, b], 1, chain);

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be available");
    let proof_text = String::from_utf8(writer.into_vec().expect("proof flush"))
        .expect("proof bytes should be valid UTF-8");
    assert_eq!(proof_text, "11 1 -2 0 7 8 2 3 6 1 0\n");

    let trace = solver.clause_trace().expect("clause trace should exist");
    let clause_id = solver.clause_id(clause_ref);
    let entry = trace
        .entries()
        .iter()
        .find(|e| e.id == clause_id)
        .expect("trace should contain the learned clause");
    assert_eq!(
        entry.resolution_hints,
        vec![1, 6, 3, 2, 8, 7],
        "clause trace should receive raw (non-reversed) hints"
    );
}

#[test]
fn test_add_learned_clause_truncates_trail_to_recent_suffix() {
    const TRAIL_CAPACITY: usize = 1024;
    const RETAINED_AFTER_TRUNCATION: usize = TRAIL_CAPACITY / 2;
    const EAGER_SUBSUME_LIMIT: usize = 20;
    const TOTAL_LEARNED: usize = TRAIL_CAPACITY + 1;

    let mut solver: Solver = Solver::new(TOTAL_LEARNED + 1);
    let uip = Literal::positive(Variable(0));
    let mut learned_offsets = Vec::with_capacity(TOTAL_LEARNED);

    for i in 0..TOTAL_LEARNED {
        let other = Literal::positive(Variable((i + 1) as u32));
        let learned = solver.add_learned_clause(vec![uip, other], 1, &[]);
        learned_offsets.push(learned.0 as usize);
    }

    let retained_start = TOTAL_LEARNED - RETAINED_AFTER_TRUNCATION;
    assert_eq!(
        solver.cold.learned_clause_trail.len(),
        RETAINED_AFTER_TRUNCATION
    );
    assert_eq!(
        solver.cold.learned_clause_trail.as_slice(),
        &learned_offsets[retained_start..],
        "trail truncation should keep the newest learned clauses"
    );
    assert_eq!(
        &solver.cold.learned_clause_trail
            [solver.cold.learned_clause_trail.len() - EAGER_SUBSUME_LIMIT..],
        &learned_offsets[TOTAL_LEARNED - EAGER_SUBSUME_LIMIT..],
        "truncation must preserve the full eager-subsumption window"
    );
}

/// Verify that clause trace receives raw (non-reversed) resolution hints.
///
/// LRAT proof output receives reversed+deduped hints (for sequential RUP
/// checking), but the clause trace receives raw hints in analysis order.
/// The SatProofManager consumes the raw order and resolves iteratively,
/// finding pivots dynamically. This test documents that the two outputs
/// receive DIFFERENT hint orderings from the same add_learned_clause call.
#[test]
fn test_add_learned_clause_trace_receives_raw_hints() {
    use crate::ClauseTrace;

    // 10 original clauses so hints [1..8] are in valid range [1, 11)
    let proof = ProofOutput::lrat_text(Vec::new(), 10);
    let mut solver: Solver = Solver::with_proof_output(24, proof);
    // Add 10 original clauses to register IDs 1-10 in ProofManager
    add_padding_original_clauses(&mut solver, 10);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;
    // Enable clause trace
    solver.cold.clause_trace = Some(ClauseTrace::new());

    let a = Literal::positive(Variable(0));
    let b = Literal::negative(Variable(1));
    // Include clause 1 ([+x0]) — required for RUP derivation of [+x0, -x1]
    let chain = &[1, 6, 3, 2, 8, 7];
    let clause_ref = solver.add_learned_clause(vec![a, b], 1, chain);

    // Verify LRAT gets reversed order (clause ID 11 = 10 original + 1)
    let writer = solver
        .take_proof_writer()
        .expect("proof writer should still be available");
    let proof_text = String::from_utf8(writer.into_vec().expect("proof flush"))
        .expect("proof bytes should be valid UTF-8");
    assert_eq!(proof_text, "11 1 -2 0 7 8 2 3 6 1 0\n");

    // Verify clause trace gets raw (non-reversed) order
    let trace = solver.clause_trace().expect("clause trace should exist");
    let clause_id = solver.clause_id(clause_ref);
    let entry = trace
        .entries()
        .iter()
        .find(|e| e.id == clause_id)
        .expect("trace should contain the learned clause");
    assert_eq!(
        entry.resolution_hints,
        vec![1, 6, 3, 2, 8, 7],
        "clause trace should receive raw (non-reversed) hints"
    );
}

/// Verify that clause IDs are always assigned even without LRAT, but
/// clause trace entries are only recorded when lrat_enabled is true.
///
/// After #8069 (Phase 2a), clause IDs are assigned unconditionally.
/// However, when `lrat_enabled` is false, `add_clause_db_checked` still
/// skips `clause_trace.add_clause_with_hints()` — callers that depend
/// on the trace must enable LRAT.
#[test]
fn test_add_learned_clause_has_id_but_no_trace_without_lrat() {
    use crate::ClauseTrace;

    // No proof output -> lrat_enabled is false, but clause_ids ARE populated
    let mut solver: Solver = Solver::new(2);
    solver.var_data[0].level = 2;
    solver.var_data[1].level = 1;
    solver.cold.clause_trace = Some(ClauseTrace::new());

    let a = Literal::positive(Variable(0));
    let b = Literal::negative(Variable(1));
    let clause_ref = solver.add_learned_clause(vec![a, b], 1, &[6, 3, 2]);

    // Clause ID is always assigned now (#8069: Phase 2a)
    let id = solver.clause_id(clause_ref);
    assert_ne!(id, 0, "clause IDs are always assigned after #8069");

    // When LRAT is disabled, add_clause_db_checked does not record trace
    // entries at all — the trace must be empty.
    let trace = solver
        .cold
        .clause_trace
        .as_ref()
        .expect("clause trace exists");
    assert!(
        trace.is_empty(),
        "clause trace must have no entries when LRAT is disabled (was: {} entries)",
        trace.len(),
    );
}

#[test]
fn test_append_lrat_unit_chain_uses_unit_proof_id_for_dynamic_var() {
    let mut solver: Solver = Solver::new(1);
    solver.enable_lrat(); // enables LRAT hint construction (unit_proof_id always allocated since #8069)
    let fresh = solver.new_var();
    let fresh_idx = fresh.index();
    let fresh_lit = Literal::positive(fresh);

    solver.var_data[fresh_idx].level = 0;
    solver.var_data[fresh_idx].trail_pos = 0;
    solver.var_data[fresh_idx].reason = NO_REASON;
    solver.trail = vec![fresh_lit];
    assign_test_lit(&mut solver, fresh_lit);
    solver.record_unit_proof_id_for_lit(fresh_lit, 77);

    solver.append_lrat_unit_chain(&[fresh_idx], &det_hash_set_new());
    // get_result requires asserting_literal to be set (debug invariant).
    solver.conflict.set_asserting_literal(fresh_lit);
    let result = solver.conflict.get_result(0, 0);

    assert_eq!(result.resolution_chain, vec![77]);
    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.unit_chain_calls, 1);
    assert_eq!(stats.unit_chain_root_trail_entries, 0);
    assert_eq!(stats.unit_chain_hints, 1);
    assert_eq!(stats.unit_chain_max_hints, 1);
    assert_eq!(stats.unit_chain_missing_hints, 0);
}

#[test]
fn test_append_lrat_unit_chain_counts_missing_visible_hint() {
    let mut solver: Solver = Solver::new(1);
    solver.enable_lrat();
    let lit = Literal::positive(Variable(0));

    solver.var_data[0].level = 0;
    solver.var_data[0].reason = NO_REASON;
    solver.trail = vec![lit];
    assign_test_lit(&mut solver, lit);

    solver.append_lrat_unit_chain(&[0], &det_hash_set_new());

    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.unit_chain_calls, 1);
    assert_eq!(stats.unit_chain_root_trail_entries, 1);
    assert_eq!(stats.unit_chain_hints, 0);
    assert_eq!(stats.unit_chain_max_hints, 0);
    assert_eq!(stats.unit_chain_missing_hints, 1);
}

#[test]
fn test_append_lrat_unit_chain_fast_path_emits_seed_units_in_reverse_trail_order() {
    let (mut solver, lits) = setup_lrat_unit_chain_window_fixture();

    solver.append_lrat_unit_chain(&[5, 7], &det_hash_set_new());
    solver.conflict.set_asserting_literal(lits[7]);
    let result = solver.conflict.get_result(0, 0);

    assert_eq!(
        result.resolution_chain,
        vec![107, 105],
        "windowed scan must preserve reverse-trail hint order"
    );
    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.unit_chain_calls, 1);
    assert_eq!(
        stats.unit_chain_root_trail_entries, 0,
        "standalone visible seed units should bypass the root-trail scan"
    );
    assert_eq!(stats.unit_chain_hints, 2);
    assert_eq!(stats.unit_chain_max_hints, 2);
    assert_eq!(stats.unit_chain_missing_hints, 0);
}

#[test]
fn test_append_lrat_unit_chain_fast_path_honors_rup_satisfied() {
    let (mut solver, lits) = setup_lrat_unit_chain_window_fixture();
    let mut rup_satisfied = det_hash_set_new();
    rup_satisfied.insert(lits[7]);

    solver.append_lrat_unit_chain(&[5, 7], &rup_satisfied);
    solver.conflict.set_asserting_literal(lits[7]);
    let result = solver.conflict.get_result(0, 0);

    assert_eq!(
        result.resolution_chain,
        vec![105],
        "unit already satisfied by the RUP assumption must be skipped"
    );
    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.unit_chain_calls, 1);
    assert_eq!(stats.unit_chain_root_trail_entries, 0);
    assert_eq!(stats.unit_chain_hints, 1);
    assert_eq!(stats.unit_chain_max_hints, 1);
    assert_eq!(stats.unit_chain_missing_hints, 0);
}

#[test]
fn test_append_lrat_unit_chain_falls_back_on_stale_trail_pos() {
    let (mut solver, lits) = setup_lrat_unit_chain_window_fixture();
    solver.var_data[7].trail_pos = 0;

    solver.append_lrat_unit_chain(&[5, 7], &det_hash_set_new());
    solver.conflict.set_asserting_literal(lits[7]);
    let result = solver.conflict.get_result(0, 0);

    assert_eq!(
        result.resolution_chain,
        vec![107, 105],
        "fallback full scan must preserve reverse-trail hint order"
    );
    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.unit_chain_calls, 1);
    assert_eq!(
        stats.unit_chain_root_trail_entries, 8,
        "stale trail_pos should fall back to scanning the full level-0 prefix"
    );
    assert_eq!(stats.unit_chain_hints, 2);
    assert_eq!(stats.unit_chain_max_hints, 2);
    assert_eq!(stats.unit_chain_missing_hints, 0);
}

#[test]
fn test_visible_unit_proof_id_requires_matching_literal_sign() {
    let mut solver: Solver = Solver::new(1);
    solver.enable_lrat();

    let lit = Literal::positive(Variable(0));
    solver.record_unit_proof_id_for_lit(lit, 77);

    assert_eq!(solver.visible_unit_proof_id_for_lit(lit), Some(77));
    assert_eq!(solver.visible_unit_proof_id_for_lit(lit.negated()), None);
}

/// Verify that after level-0 unit materialization, `append_lrat_unit_chain`
/// uses the seed's standalone visible unit proof directly instead of BFS-ing
/// through its reason dependencies.
///
/// Scenario: two level-0 variables a and b. Variable b's reason was
/// cleared by ClearLevel0 (BVE deleted the clause) but its proof ID
/// is preserved in `level0_proof_id[b]`. Variable a's reason clause
/// contains b. Materialization first derives a standalone visible unit proof
/// for a using b's preserved ID; append can then emit only a's unit ID.
#[test]
fn test_append_lrat_unit_chain_after_materialization_skips_bfs_dependencies() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));

    // c0 = {a, ¬b}: with b=true, this is a's reason clause.
    solver.add_clause(vec![a, b.negated()]);
    let c0_ref = ClauseRef(0);
    let c0_id = solver.clause_id(c0_ref);
    assert_ne!(c0_id, 0, "c0 must have a non-zero LRAT ID");

    // c1 = {b}: visible proof ID preserved across ClearLevel0.
    let b_unit_idx = solver.add_clause_db(&[b], false);
    let b_unit_ref = ClauseRef(b_unit_idx as u32);
    let b_unit_id = solver.clause_id(b_unit_ref);
    assert_ne!(b_unit_id, 0, "b unit must have a non-zero LRAT ID");

    // Set up trail: b propagated first, then a
    solver.trail = vec![b, a];
    solver.trail_lim = vec![]; // all at level 0 (no decisions)
    solver.var_data[0].level = 0;
    solver.var_data[0].trail_pos = 1;
    solver.var_data[1].level = 0;
    solver.var_data[1].trail_pos = 0;
    assign_test_lit(&mut solver, b);
    assign_test_lit(&mut solver, a);

    // a's reason is c0 (a normal reason clause)
    solver.var_data[0].reason = c0_ref.0;

    // b's reason cleared by ClearLevel0: reason=None, level0_proof_id set
    solver.var_data[1].reason = NO_REASON;
    solver.unit_proof_id[1] = 0; // ensure unit_proof_id doesn't mask level0
    solver.record_level0_proof_id_for_lit(b, b_unit_id); // ClearLevel0 saved this visible ID

    solver.materialize_level0_unit_proofs();
    let a_unit_id = solver
        .visible_unit_proof_id_for_lit(a)
        .expect("a should have a materialized visible unit proof");
    solver.append_lrat_unit_chain(&[0], &det_hash_set_new());

    solver.conflict.set_asserting_literal(a);
    let result = solver.conflict.get_result(0, 0);

    assert_eq!(
        result.resolution_chain,
        vec![a_unit_id],
        "materialized seed unit should make BFS dependencies unnecessary"
    );
    assert_ne!(
        a_unit_id, b_unit_id,
        "derived seed unit should be distinct from its ClearLevel0 antecedent"
    );

    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.materialize_calls, 1);
    assert_eq!(stats.materialize_root_trail_entries, 2);
    assert_eq!(stats.materialize_emitted_unit_lines, 1);
    assert_eq!(stats.materialize_unit_hints, 2);
    assert_eq!(stats.materialize_unit_max_hints, 2);
    assert_eq!(stats.materialize_incomplete_chains, 0);
    assert_eq!(stats.materialize_hidden_trusted_units, 0);
    assert_eq!(stats.unit_chain_calls, 1);
    assert_eq!(stats.unit_chain_root_trail_entries, 0);
    assert_eq!(stats.unit_chain_hints, 1);
    assert_eq!(stats.unit_chain_max_hints, 1);
    assert_eq!(stats.unit_chain_missing_hints, 0);
}

#[test]
fn materialize_level0_unit_proofs_honors_expired_solve_deadline() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    let support = Literal::positive(Variable(0));
    let target = Literal::positive(Variable(1));

    let support_idx = solver.add_clause_db(&[support], false);
    let support_ref = ClauseRef(support_idx as u32);
    let support_id = solver.clause_id(support_ref);
    let reason_idx = solver.add_clause_db(&[target, support.negated()], false);
    let reason_ref = ClauseRef(reason_idx as u32);

    solver.trail = vec![support, target];
    solver.trail_lim.clear();
    solver.var_data[support.variable().index()].level = 0;
    solver.var_data[support.variable().index()].trail_pos = 0;
    solver.var_data[support.variable().index()].reason = support_ref.0;
    solver.var_data[target.variable().index()].level = 0;
    solver.var_data[target.variable().index()].trail_pos = 1;
    solver.var_data[target.variable().index()].reason = reason_ref.0;
    assign_test_lit(&mut solver, support);
    assign_test_lit(&mut solver, target);
    solver.record_unit_proof_id_for_lit(support, support_id);

    solver.set_solve_deadline(Some(ay_core::time::Instant::now()));
    let started = std::time::Instant::now();
    assert!(!solver.materialize_level0_unit_proofs_interruptible());

    assert!(
        started.elapsed() < std::time::Duration::from_millis(500),
        "expired deadline must stop LRAT unit materialization promptly"
    );
    assert_eq!(solver.cold.lrat_level0_unit_materialize_cursor, 0);
    assert_eq!(solver.cold.level0_proof_id[target.variable().index()], 0);
    assert_eq!(solver.unit_proof_id[target.variable().index()], 0);
}

#[test]
fn test_append_lrat_unit_chain_strict_fast_path_ignores_level0_proof_id() {
    let mut solver: Solver = Solver::new(2);
    solver.enable_lrat();

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));

    let reason_idx = solver.add_clause_db(&[a, b.negated()], false);
    let reason_ref = ClauseRef(reason_idx as u32);

    solver.trail = vec![b, a];
    solver.trail_lim.clear();
    solver.var_data[0].level = 0;
    solver.var_data[0].trail_pos = 1;
    solver.var_data[0].reason = reason_ref.0;
    solver.var_data[1].level = 0;
    solver.var_data[1].trail_pos = 0;
    solver.var_data[1].reason = NO_REASON;
    assign_test_lit(&mut solver, b);
    assign_test_lit(&mut solver, a);

    solver.record_level0_proof_id_for_lit(a, 501);
    solver.record_unit_proof_id_for_lit(b, 502);
    assert_eq!(solver.visible_unit_proof_id_for_lit(a), None);
    assert_eq!(solver.level0_var_proof_id(a.variable().index()), Some(501));

    solver.append_lrat_unit_chain(&[a.variable().index()], &det_hash_set_new());
    solver.conflict.set_asserting_literal(a);
    let result = solver.conflict.get_result(0, 0);

    assert_eq!(
        result.resolution_chain,
        vec![501, 502],
        "level0_var_proof_id alone must fall back to BFS and include dependencies"
    );
    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.unit_chain_calls, 1);
    assert_eq!(stats.unit_chain_root_trail_entries, 2);
    assert_eq!(stats.unit_chain_hints, 2);
    assert_eq!(stats.unit_chain_max_hints, 2);
    assert_eq!(stats.unit_chain_missing_hints, 0);
}

#[test]
fn test_compute_lrat_chain_for_removed_literals_uses_unit_proof_id_for_level0_reason() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(3, proof);

    let uip = Literal::positive(Variable(0));
    let removed = Literal::positive(Variable(1));
    let level0 = Literal::positive(Variable(2));

    // c0 = {level0}: explicit unit proof for the level-0 antecedent.
    let c0_idx = solver.add_clause_db(&[level0], false);
    let c0_ref = ClauseRef(c0_idx as u32);
    let c0_id = solver.clause_id(c0_ref);
    assert_ne!(c0_id, 0, "level-0 unit clause must have a proof ID");

    // c1 = {removed, level0}: removed literal's reason clause.
    let c1_idx = solver.add_clause_db(&[removed, level0], false);
    let c1_ref = ClauseRef(c1_idx as u32);
    let c1_id = solver.clause_id(c1_ref);
    assert_ne!(
        c1_id, 0,
        "removed literal reason clause must have a proof ID"
    );

    // c2 = {uip, removed}: original learned clause before minimize removes `removed`.
    let c2_idx = solver.add_clause_db(&[uip, removed], false);
    let c2_ref = ClauseRef(c2_idx as u32);
    let c2_id = solver.clause_id(c2_ref);
    assert_ne!(c2_id, 0, "original learned clause must have a proof ID");

    solver.conflict.set_asserting_literal(uip);
    solver.var_data[removed.variable().index()].level = 1;
    solver.var_data[removed.variable().index()].reason = c1_ref.0;
    solver.var_data[level0.variable().index()].level = 0;
    solver.var_data[level0.variable().index()].reason = c0_ref.0;
    assign_test_lit(&mut solver, level0);
    solver.record_unit_proof_id_for_lit(level0, c0_id);

    // Final learned clause keeps only the UIP; `removed` was eliminated by minimize.
    let minimize_level0 = solver.compute_lrat_chain_for_removed_literals(&[uip, removed]);

    let result = solver.conflict.get_result(0, 0);

    // After #7108 fix: level-0 units are routed to the returned Vec, not
    // the resolution chain. The chain should only contain non-level-0
    // reason clause IDs (c1_id for the removed literal's reason).
    assert_eq!(
        result.resolution_chain,
        vec![c1_id],
        "removed-literal minimize chain must contain only non-level-0 reason IDs"
    );
    assert_eq!(
        minimize_level0,
        vec![level0.variable().index()],
        "level-0 variable from minimize DFS must be returned for unit chain routing"
    );

    // Sanity: the removed literal's original clause is not part of the minimize chain.
    assert!(
        !result.resolution_chain.contains(&c2_id),
        "minimize chain should only contain the removed literal's reason graph"
    );
}

#[test]
fn test_compute_lrat_chain_for_removed_literals_skips_minimize_materialization_without_removed_literals(
) {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(3, proof);

    let uip = Literal::positive(Variable(0));
    let leaf = Literal::positive(Variable(1));
    let mid = Literal::positive(Variable(2));

    let leaf_idx = solver.add_clause_db(&[leaf], false);
    let leaf_ref = ClauseRef(leaf_idx as u32);
    let leaf_id = solver.clause_id(leaf_ref);
    assert_ne!(leaf_id, 0, "leaf unit must have a proof ID");

    let mid_idx = solver.add_clause_db(&[mid, leaf.negated()], false);
    let mid_ref = ClauseRef(mid_idx as u32);
    assert_ne!(
        solver.clause_id(mid_ref),
        0,
        "mid reason must have a proof ID"
    );

    solver.conflict.set_asserting_literal(uip);
    solver.trail = vec![leaf, mid];
    solver.trail_lim = vec![];
    solver.var_data[leaf.variable().index()].level = 0;
    solver.var_data[leaf.variable().index()].trail_pos = 0;
    solver.var_data[leaf.variable().index()].reason = leaf_ref.0;
    solver.var_data[mid.variable().index()].level = 0;
    solver.var_data[mid.variable().index()].trail_pos = 1;
    solver.var_data[mid.variable().index()].reason = mid_ref.0;
    assign_test_lit(&mut solver, leaf);
    assign_test_lit(&mut solver, mid);
    solver.record_unit_proof_id_for_lit(leaf, leaf_id);

    let minimize_level0 = solver.compute_lrat_chain_for_removed_literals(&[uip]);

    assert!(
        minimize_level0.is_empty(),
        "no removed learned literal should produce no minimize unit-chain seeds"
    );
    assert_eq!(
        solver.cold.level0_proof_id[mid.variable().index()],
        0,
        "no-removed minimize path must not materialize unrelated root units"
    );

    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.materialize_minimize_calls, 0);
    assert_eq!(stats.materialize_minimize_root_trail_entries, 0);
    assert_eq!(stats.materialize_minimize_emitted_unit_lines, 0);
}

#[test]
fn test_level0_var_proof_id_uses_unit_reason_clause_in_lrat_mode() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(1, proof);

    let unit = Literal::positive(Variable(0));
    let unit_idx = solver.add_clause_db(&[unit], false);
    let unit_ref = ClauseRef(unit_idx as u32);
    let unit_id = solver.clause_id(unit_ref);
    assert_ne!(unit_id, 0, "unit reason clause must have a proof ID");

    solver.var_data[unit.variable().index()].level = 0;
    solver.var_data[unit.variable().index()].reason = unit_ref.0;
    solver.unit_proof_id[unit.variable().index()] = 0;
    solver.cold.level0_proof_id[unit.variable().index()] = 0;
    assign_test_lit(&mut solver, unit);

    assert_eq!(
        solver.level0_var_proof_id(unit.variable().index()),
        Some(unit_id),
        "LRAT mode must accept a unit reason clause when no materialized unit proof exists yet"
    );
}

#[test]
fn test_compute_lrat_chain_for_removed_literals_materializes_nested_level0_units() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(4, proof);

    let uip = Literal::positive(Variable(0));
    let removed = Literal::positive(Variable(1));
    let mid = Literal::positive(Variable(2));
    let leaf = Literal::positive(Variable(3));

    // c0 = {leaf}: explicit unit proof for the deepest level-0 antecedent.
    let c0_idx = solver.add_clause_db(&[leaf], false);
    let c0_ref = ClauseRef(c0_idx as u32);
    let c0_id = solver.clause_id(c0_ref);
    assert_ne!(c0_id, 0, "deepest level-0 unit must have a proof ID");

    // c1 = {mid, ¬leaf}: leaf=true forces mid=true at level 0.
    let c1_idx = solver.add_clause_db(&[mid, leaf.negated()], false);
    let c1_ref = ClauseRef(c1_idx as u32);
    let c1_id = solver.clause_id(c1_ref);
    assert_ne!(
        c1_id, 0,
        "nested level-0 reason clause must have a proof ID"
    );

    // c2 = {removed, ¬mid}: mid=true forces removed=true.
    let c2_idx = solver.add_clause_db(&[removed, mid.negated()], false);
    let c2_ref = ClauseRef(c2_idx as u32);
    let c2_id = solver.clause_id(c2_ref);
    assert_ne!(
        c2_id, 0,
        "removed literal reason clause must have a proof ID"
    );

    solver.conflict.set_asserting_literal(uip);
    solver.trail = vec![leaf, mid];
    solver.trail_lim = vec![];
    solver.var_data[leaf.variable().index()].level = 0;
    solver.var_data[leaf.variable().index()].trail_pos = 0;
    solver.var_data[leaf.variable().index()].reason = c0_ref.0;
    solver.var_data[mid.variable().index()].level = 0;
    solver.var_data[mid.variable().index()].trail_pos = 1;
    solver.var_data[mid.variable().index()].reason = c1_ref.0;
    solver.var_data[removed.variable().index()].level = 1;
    solver.var_data[removed.variable().index()].reason = c2_ref.0;
    assign_test_lit(&mut solver, leaf);
    assign_test_lit(&mut solver, mid);
    solver.record_unit_proof_id_for_lit(leaf, c0_id);

    // Final learned clause keeps only the UIP; `removed` was eliminated by minimize.
    let minimize_level0 = solver.compute_lrat_chain_for_removed_literals(&[uip, removed]);

    let mid_unit_id = solver.cold.level0_proof_id[mid.variable().index()];
    assert_ne!(
        mid_unit_id, 0,
        "nested level-0 antecedent must be materialized as a derived unit proof"
    );
    assert_ne!(
        mid_unit_id, c1_id,
        "minimize chain must not reuse the raw multi-literal level-0 reason clause"
    );

    let result = solver.conflict.get_result(0, 0);
    // After #7108 fix: level-0 units are routed to the returned Vec, not
    // the resolution chain. Only the non-level-0 reason (c2_id) remains.
    assert_eq!(
        result.resolution_chain,
        vec![c2_id],
        "removed-literal minimize chain must contain only non-level-0 reason IDs"
    );
    assert_eq!(
        minimize_level0,
        vec![mid.variable().index()],
        "nested level-0 variable from minimize DFS must be returned for unit chain routing"
    );

    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.materialize_minimize_calls, 1);
    assert_eq!(stats.materialize_minimize_root_trail_entries, 2);
    assert_eq!(stats.materialize_minimize_emitted_unit_lines, 1);
    assert_eq!(stats.materialize_minimize_unit_hints, 2);
    assert_eq!(stats.materialize_minimize_unit_max_hints, 2);
    assert_eq!(stats.materialize_minimize_incomplete_chains, 0);
}

#[test]
fn test_materialize_level0_unit_proofs_rederives_hidden_trusted_unit_as_visible() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(3, proof);

    let support = Literal::positive(Variable(1));
    let target = Literal::positive(Variable(2));

    let support_idx = solver.add_clause_db(&[support], false);
    let support_ref = ClauseRef(support_idx as u32);
    let support_id = solver.clause_id(support_ref);
    assert_ne!(support_id, 0, "support unit must have a proof ID");

    let reason_idx = solver.add_clause_db(&[target, support.negated()], false);
    let reason_ref = ClauseRef(reason_idx as u32);
    let reason_id = solver.clause_id(reason_ref);
    assert_ne!(reason_id, 0, "target reason must have a proof ID");

    solver.trail = vec![support, target];
    solver.trail_lim = vec![];

    solver.var_data[support.variable().index()].level = 0;
    solver.var_data[support.variable().index()].trail_pos = 0;
    solver.var_data[support.variable().index()].reason = support_ref.0;

    solver.var_data[target.variable().index()].level = 0;
    solver.var_data[target.variable().index()].trail_pos = 1;
    solver.var_data[target.variable().index()].reason = reason_ref.0;

    assign_test_lit(&mut solver, support);
    assign_test_lit(&mut solver, target);
    solver.record_unit_proof_id_for_lit(support, support_id);

    let hidden_id = solver.proof_emit_unit(target, &[], ProofAddKind::TrustedTransform);
    assert_ne!(
        hidden_id, 0,
        "trusted-transform unit must reserve an LRAT ID"
    );
    assert!(
        !solver.lrat_hint_id_visible(hidden_id),
        "trusted-transform unit must stay hidden from the external LRAT file"
    );
    solver.record_unit_proof_id_for_lit(target, hidden_id);

    solver.materialize_level0_unit_proofs();

    let visible_id = solver.cold.level0_proof_id[target.variable().index()];
    assert_ne!(
        visible_id, 0,
        "target must be rederived as a visible LRAT unit"
    );
    assert_ne!(
        visible_id, hidden_id,
        "materialization must not reuse the hidden trusted-transform proof ID"
    );
    assert!(
        solver.lrat_hint_id_visible(visible_id),
        "materialized level-0 unit must be eligible for external LRAT hints"
    );
    assert_eq!(
        solver.level0_var_proof_id(target.variable().index()),
        Some(visible_id),
        "LRAT hint lookup must prefer the visible rederived unit"
    );

    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.materialize_calls, 1);
    assert_eq!(stats.materialize_root_trail_entries, 2);
    assert_eq!(stats.materialize_emitted_unit_lines, 1);
    assert_eq!(stats.materialize_unit_hints, 2);
    assert_eq!(stats.materialize_unit_max_hints, 2);
    assert_eq!(stats.materialize_incomplete_chains, 0);
    assert_eq!(stats.materialize_hidden_trusted_units, 0);

    solver.materialize_level0_unit_proofs();

    let stats = solver.lrat_materialization_stats();
    assert_eq!(
        solver.cold.level0_proof_id[target.variable().index()],
        visible_id,
        "repeated materialization must not emit a duplicate visible unit"
    );
    assert_eq!(stats.materialize_calls, 2);
    assert_eq!(
        stats.materialize_root_trail_entries, 2,
        "idempotent cursor pass should scan no already-materialized root entries"
    );
    assert_eq!(stats.materialize_emitted_unit_lines, 1);
    assert_eq!(stats.materialize_unit_hints, 2);
    assert_eq!(stats.materialize_unit_max_hints, 2);
    assert_eq!(stats.materialize_incomplete_chains, 0);
    assert_eq!(stats.materialize_hidden_trusted_units, 0);
}

#[test]
fn test_materialize_level0_unit_proofs_counts_incomplete_hidden_fallback() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);

    let support = Literal::positive(Variable(0));
    let target = Literal::positive(Variable(1));

    let reason_idx = solver.add_clause_db(&[target, support.negated()], false);
    let reason_ref = ClauseRef(reason_idx as u32);
    assert_ne!(solver.clause_id(reason_ref), 0);

    solver.trail = vec![support, target];
    solver.trail_lim = vec![];
    solver.var_data[support.variable().index()].level = 0;
    solver.var_data[support.variable().index()].trail_pos = 0;
    solver.var_data[support.variable().index()].reason = NO_REASON;
    solver.var_data[target.variable().index()].level = 0;
    solver.var_data[target.variable().index()].trail_pos = 1;
    solver.var_data[target.variable().index()].reason = reason_ref.0;
    assign_test_lit(&mut solver, support);
    assign_test_lit(&mut solver, target);

    solver.materialize_level0_unit_proofs();

    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.materialize_calls, 1);
    assert_eq!(stats.materialize_root_trail_entries, 2);
    assert_eq!(stats.materialize_emitted_unit_lines, 0);
    assert_eq!(stats.materialize_incomplete_chains, 1);
    assert_eq!(stats.materialize_hidden_trusted_units, 1);
    assert_ne!(
        solver.cold.level0_proof_id[target.variable().index()],
        0,
        "target should still receive a hidden fallback proof ID"
    );
    let hidden_id = solver.cold.level0_proof_id[target.variable().index()];
    assert!(
        !solver.lrat_hint_id_visible(hidden_id),
        "incomplete fallback must stay hidden from external LRAT output"
    );

    solver.materialize_level0_unit_proofs();

    let stats = solver.lrat_materialization_stats();
    assert_eq!(
        solver.cold.level0_proof_id[target.variable().index()],
        hidden_id,
        "hidden fallback cursor retry must not emit a duplicate hidden unit"
    );
    assert_eq!(solver.unit_proof_id[target.variable().index()], hidden_id);
    assert_eq!(stats.materialize_calls, 2);
    assert_eq!(
        stats.materialize_root_trail_entries, 3,
        "hidden fallback should pin the cursor at the unresolved trail slot"
    );
    assert_eq!(stats.materialize_emitted_unit_lines, 0);
    assert_eq!(stats.materialize_incomplete_chains, 2);
    assert_eq!(stats.materialize_hidden_trusted_units, 1);
    assert_eq!(stats.materialize_unit_hints, 0);
}

/// #A5: a pinned slot low in the root trail must not force re-walking the
/// materialized suffix behind it. Pre-#A5 the scalar cursor restarted at the
/// oldest pin, so every later call re-scanned (level0_end - pin) entries;
/// with (cursor, pinned) the retry costs exactly |pinned| entries while the
/// emitted unit lines (and the LRAT stream) stay identical.
#[test]
fn test_materialize_level0_unit_proofs_depinned_retry_skips_materialized_suffix() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(5, proof);

    let support = Literal::positive(Variable(0));
    let target = Literal::positive(Variable(1));
    let base = Literal::positive(Variable(2));
    let t1 = Literal::positive(Variable(3));
    let t2 = Literal::positive(Variable(4));

    // target's reason contains an antecedent (support) with no provenance:
    // target pins its slot with a hidden TrustedTransform fallback.
    let target_reason_idx = solver.add_clause_db(&[target, support.negated()], false);
    let target_reason_ref = ClauseRef(target_reason_idx as u32);
    assert_ne!(solver.clause_id(target_reason_ref), 0);

    // base -> t1 -> t2 is a fully materializable chain behind the pin.
    let base_idx = solver.add_clause_db(&[base], false);
    let base_ref = ClauseRef(base_idx as u32);
    let base_id = solver.clause_id(base_ref);
    assert_ne!(base_id, 0);
    let t1_reason_idx = solver.add_clause_db(&[t1, base.negated()], false);
    let t1_reason_ref = ClauseRef(t1_reason_idx as u32);
    assert_ne!(solver.clause_id(t1_reason_ref), 0);
    let t2_reason_idx = solver.add_clause_db(&[t2, t1.negated()], false);
    let t2_reason_ref = ClauseRef(t2_reason_idx as u32);
    assert_ne!(solver.clause_id(t2_reason_ref), 0);

    solver.trail = vec![support, target, base, t1, t2];
    solver.trail_lim = vec![];
    for (lit, reason) in [
        (support, NO_REASON),
        (target, target_reason_ref.0),
        (base, base_ref.0),
        (t1, t1_reason_ref.0),
        (t2, t2_reason_ref.0),
    ] {
        let vi = lit.variable().index();
        solver.var_data[vi].level = 0;
        solver.var_data[vi].reason = reason;
    }
    for (pos, lit) in [support, target, base, t1, t2].into_iter().enumerate() {
        solver.var_data[lit.variable().index()].trail_pos = pos as u32;
        assign_test_lit(&mut solver, lit);
    }
    solver.record_unit_proof_id_for_lit(base, base_id);

    solver.materialize_level0_unit_proofs();

    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.materialize_calls, 1);
    assert_eq!(stats.materialize_root_trail_entries, 5);
    assert_eq!(stats.materialize_emitted_unit_lines, 2, "t1 and t2");
    assert_eq!(stats.materialize_incomplete_chains, 1, "target pins");
    assert_eq!(stats.materialize_hidden_trusted_units, 1);
    assert_eq!(
        solver.cold.lrat_level0_unit_materialize_pinned,
        vec![1],
        "only target's slot stays pinned"
    );
    assert_eq!(solver.cold.lrat_level0_unit_materialize_cursor, 5);

    solver.materialize_level0_unit_proofs();

    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.materialize_calls, 2);
    assert_eq!(
        stats.materialize_root_trail_entries, 6,
        "retry must cost one pinned slot, not the 4-entry suffix the \
         pre-#A5 scalar cursor re-walked"
    );
    assert_eq!(
        stats.materialize_emitted_unit_lines, 2,
        "no duplicate unit lines on retry"
    );
    assert_eq!(stats.materialize_incomplete_chains, 2);
    assert_eq!(
        stats.materialize_hidden_trusted_units, 1,
        "fallback emitted once"
    );
    assert_eq!(solver.cold.lrat_level0_unit_materialize_pinned, vec![1]);
}

#[test]
fn test_materialize_level0_unit_proofs_rejects_hidden_trusted_antecedent() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);

    let support = Literal::positive(Variable(0));
    let target = Literal::positive(Variable(1));

    let reason_idx = solver.add_clause_db(&[target, support.negated()], false);
    let reason_ref = ClauseRef(reason_idx as u32);
    let reason_id = solver.clause_id(reason_ref);
    assert_ne!(reason_id, 0, "target reason must have a proof ID");

    solver.trail = vec![support, target];
    solver.trail_lim = vec![];
    solver.var_data[support.variable().index()].level = 0;
    solver.var_data[support.variable().index()].trail_pos = 0;
    solver.var_data[support.variable().index()].reason = NO_REASON;
    solver.var_data[target.variable().index()].level = 0;
    solver.var_data[target.variable().index()].trail_pos = 1;
    solver.var_data[target.variable().index()].reason = reason_ref.0;
    assign_test_lit(&mut solver, support);
    assign_test_lit(&mut solver, target);

    let hidden_support_id = solver.proof_emit_unit(support, &[], ProofAddKind::TrustedTransform);
    assert_ne!(
        hidden_support_id, 0,
        "trusted-transform support unit must reserve an LRAT ID"
    );
    assert!(
        !solver.lrat_hint_id_visible(hidden_support_id),
        "trusted-transform support unit must stay hidden from external LRAT output"
    );
    assert_eq!(
        solver.visible_unit_proof_id_for_lit(support),
        None,
        "hidden trusted-transform unit IDs must not be visible unit hints"
    );
    assert_eq!(
        solver.level0_unit_chain_proof_id_for_lit(support),
        None,
        "hidden trusted-transform unit IDs must not satisfy level-0 materialization"
    );

    solver.materialize_level0_unit_proofs();

    let target_id = solver.cold.level0_proof_id[target.variable().index()];
    assert_ne!(
        target_id, 0,
        "target should receive only a hidden fallback when its antecedent is hidden"
    );
    assert!(
        !solver.lrat_hint_id_visible(target_id),
        "materialization must not derive a visible unit from hidden antecedent ID {hidden_support_id}"
    );
    assert_eq!(
        solver.level0_var_proof_id(target.variable().index()),
        None,
        "hidden fallback must not become an externally usable level-0 proof"
    );

    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.materialize_calls, 1);
    assert_eq!(stats.materialize_root_trail_entries, 2);
    assert_eq!(stats.materialize_emitted_unit_lines, 0);
    assert_eq!(stats.materialize_unit_hints, 0);
    assert_eq!(stats.materialize_incomplete_chains, 1);
    assert_eq!(stats.materialize_hidden_trusted_units, 1);
}

#[test]
fn test_materialize_level0_unit_proofs_rejects_stale_reason_without_unit_literal() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(3, proof);

    let support = Literal::positive(Variable(0));
    let target = Literal::positive(Variable(1));
    let unrelated = Literal::positive(Variable(2));

    let support_idx = solver.add_clause_db(&[support], false);
    let support_ref = ClauseRef(support_idx as u32);
    let support_id = solver.clause_id(support_ref);
    assert_ne!(support_id, 0);

    let stale_idx = solver.add_clause_db(&[unrelated, support.negated()], false);
    let stale_ref = ClauseRef(stale_idx as u32);
    assert_ne!(solver.clause_id(stale_ref), 0);

    solver.trail = vec![support, target];
    solver.trail_lim = vec![];
    solver.var_data[support.variable().index()].level = 0;
    solver.var_data[support.variable().index()].trail_pos = 0;
    solver.var_data[support.variable().index()].reason = support_ref.0;
    solver.var_data[target.variable().index()].level = 0;
    solver.var_data[target.variable().index()].trail_pos = 1;
    solver.var_data[target.variable().index()].reason = stale_ref.0;
    assign_test_lit(&mut solver, support);
    assign_test_lit(&mut solver, target);

    solver.materialize_level0_unit_proofs();

    assert_eq!(
        solver.cold.level0_proof_id[target.variable().index()],
        0,
        "stale reason clauses that do not contain the implied literal must not derive a visible unit"
    );
    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.materialize_incomplete_chains, 1);
    assert_eq!(stats.materialize_emitted_unit_lines, 0);
    assert_eq!(stats.materialize_hidden_trusted_units, 0);
}

#[test]
fn test_materialize_level0_minimize_unit_proofs_rejects_stale_reason_without_unit_literal() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(3, proof);

    let support = Literal::positive(Variable(0));
    let target = Literal::positive(Variable(1));
    let unrelated = Literal::positive(Variable(2));

    let support_idx = solver.add_clause_db(&[support], false);
    let support_ref = ClauseRef(support_idx as u32);
    let support_id = solver.clause_id(support_ref);
    assert_ne!(support_id, 0);

    let stale_idx = solver.add_clause_db(&[unrelated, support.negated()], false);
    let stale_ref = ClauseRef(stale_idx as u32);
    assert_ne!(solver.clause_id(stale_ref), 0);

    solver.trail = vec![support, target];
    solver.trail_lim = vec![];
    solver.var_data[support.variable().index()].level = 0;
    solver.var_data[support.variable().index()].trail_pos = 0;
    solver.var_data[support.variable().index()].reason = support_ref.0;
    solver.var_data[target.variable().index()].level = 0;
    solver.var_data[target.variable().index()].trail_pos = 1;
    solver.var_data[target.variable().index()].reason = stale_ref.0;
    assign_test_lit(&mut solver, support);
    assign_test_lit(&mut solver, target);

    solver.materialize_level0_minimize_unit_proofs();

    assert_eq!(
        solver.cold.level0_proof_id[target.variable().index()],
        0,
        "stale minimize reasons must not derive a visible unit for a missing literal"
    );
    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.materialize_minimize_incomplete_chains, 1);
    assert_eq!(stats.materialize_minimize_emitted_unit_lines, 0);
}

#[test]
fn test_materialize_level0_minimize_unit_proofs_cursor_scans_new_suffix_only() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(3, proof);

    let leaf = Literal::positive(Variable(0));
    let mid = Literal::positive(Variable(1));
    let tail = Literal::positive(Variable(2));

    let leaf_idx = solver.add_clause_db(&[leaf], false);
    let leaf_ref = ClauseRef(leaf_idx as u32);
    let leaf_id = solver.clause_id(leaf_ref);
    assert_ne!(leaf_id, 0, "leaf unit must have a proof ID");

    let mid_idx = solver.add_clause_db(&[mid, leaf.negated()], false);
    let mid_ref = ClauseRef(mid_idx as u32);
    assert_ne!(
        solver.clause_id(mid_ref),
        0,
        "mid reason must have a proof ID"
    );

    let tail_idx = solver.add_clause_db(&[tail, mid.negated()], false);
    let tail_ref = ClauseRef(tail_idx as u32);
    assert_ne!(
        solver.clause_id(tail_ref),
        0,
        "tail reason must have a proof ID"
    );

    solver.trail = vec![leaf, mid];
    solver.trail_lim = vec![];
    solver.var_data[leaf.variable().index()].level = 0;
    solver.var_data[leaf.variable().index()].trail_pos = 0;
    solver.var_data[leaf.variable().index()].reason = leaf_ref.0;
    solver.var_data[mid.variable().index()].level = 0;
    solver.var_data[mid.variable().index()].trail_pos = 1;
    solver.var_data[mid.variable().index()].reason = mid_ref.0;
    assign_test_lit(&mut solver, leaf);
    assign_test_lit(&mut solver, mid);
    solver.record_unit_proof_id_for_lit(leaf, leaf_id);
    solver.cold.lrat_materialize_hints_buf = Vec::with_capacity(8);
    solver.cold.lrat_materialize_hints_buf.push(999);
    let initial_hint_capacity = solver.cold.lrat_materialize_hints_buf.capacity();

    solver.materialize_level0_minimize_unit_proofs();
    let mid_id = solver.cold.level0_proof_id[mid.variable().index()];
    assert_ne!(mid_id, 0, "mid unit should be materialized");
    assert!(
        solver.lrat_hint_id_visible(mid_id),
        "mid unit should be visible to LRAT"
    );

    solver.trail.push(tail);
    solver.var_data[tail.variable().index()].level = 0;
    solver.var_data[tail.variable().index()].trail_pos = 2;
    solver.var_data[tail.variable().index()].reason = tail_ref.0;
    assign_test_lit(&mut solver, tail);

    solver.materialize_level0_minimize_unit_proofs();

    assert_eq!(
        solver.cold.level0_proof_id[mid.variable().index()],
        mid_id,
        "suffix scan must leave the already-materialized mid unit unchanged"
    );
    let tail_id = solver.cold.level0_proof_id[tail.variable().index()];
    assert_ne!(tail_id, 0, "tail unit should be materialized");
    assert!(
        solver.lrat_hint_id_visible(tail_id),
        "tail unit should be visible to LRAT"
    );

    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.materialize_minimize_calls, 2);
    assert_eq!(
        stats.materialize_minimize_root_trail_entries, 3,
        "first pass scans two roots; second pass should scan only the new suffix"
    );
    assert_eq!(stats.materialize_minimize_emitted_unit_lines, 2);
    assert_eq!(stats.materialize_minimize_unit_hints, 4);
    assert_eq!(stats.materialize_minimize_unit_max_hints, 2);
    assert_eq!(stats.materialize_minimize_incomplete_chains, 0);
    assert!(
        solver.cold.lrat_materialize_hints_buf.is_empty(),
        "materialization scratch must not retain stale hint IDs"
    );
    assert!(
        solver.cold.lrat_materialize_hints_buf.capacity() >= initial_hint_capacity,
        "materialization scratch should retain capacity for reuse"
    );
}

#[test]
fn test_materialize_level0_unit_proofs_cursor_scans_new_suffix_only() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(3, proof);

    let leaf = Literal::positive(Variable(0));
    let mid = Literal::positive(Variable(1));
    let tail = Literal::positive(Variable(2));

    let leaf_idx = solver.add_clause_db(&[leaf], false);
    let leaf_ref = ClauseRef(leaf_idx as u32);
    let leaf_id = solver.clause_id(leaf_ref);
    assert_ne!(leaf_id, 0, "leaf unit must have a proof ID");

    let mid_idx = solver.add_clause_db(&[mid, leaf.negated()], false);
    let mid_ref = ClauseRef(mid_idx as u32);
    assert_ne!(
        solver.clause_id(mid_ref),
        0,
        "mid reason must have a proof ID"
    );

    let tail_idx = solver.add_clause_db(&[tail, mid.negated()], false);
    let tail_ref = ClauseRef(tail_idx as u32);
    assert_ne!(
        solver.clause_id(tail_ref),
        0,
        "tail reason must have a proof ID"
    );

    solver.trail = vec![leaf, mid];
    solver.trail_lim = vec![];
    solver.var_data[leaf.variable().index()].level = 0;
    solver.var_data[leaf.variable().index()].trail_pos = 0;
    solver.var_data[leaf.variable().index()].reason = leaf_ref.0;
    solver.var_data[mid.variable().index()].level = 0;
    solver.var_data[mid.variable().index()].trail_pos = 1;
    solver.var_data[mid.variable().index()].reason = mid_ref.0;
    assign_test_lit(&mut solver, leaf);
    assign_test_lit(&mut solver, mid);
    solver.record_unit_proof_id_for_lit(leaf, leaf_id);
    solver.cold.lrat_materialize_hints_buf = Vec::with_capacity(8);
    solver.cold.lrat_materialize_hints_buf.push(999);
    let initial_hint_capacity = solver.cold.lrat_materialize_hints_buf.capacity();

    solver.materialize_level0_unit_proofs();
    let mid_id = solver.cold.level0_proof_id[mid.variable().index()];
    assert_ne!(mid_id, 0, "mid unit should be materialized");
    assert!(
        solver.lrat_hint_id_visible(mid_id),
        "mid unit should be visible to LRAT"
    );

    solver.trail.push(tail);
    solver.var_data[tail.variable().index()].level = 0;
    solver.var_data[tail.variable().index()].trail_pos = 2;
    solver.var_data[tail.variable().index()].reason = tail_ref.0;
    assign_test_lit(&mut solver, tail);

    solver.materialize_level0_unit_proofs();

    assert_eq!(
        solver.cold.level0_proof_id[mid.variable().index()],
        mid_id,
        "suffix scan must leave the already-materialized mid unit unchanged"
    );
    let tail_id = solver.cold.level0_proof_id[tail.variable().index()];
    assert_ne!(tail_id, 0, "tail unit should be materialized");
    assert!(
        solver.lrat_hint_id_visible(tail_id),
        "tail unit should be visible to LRAT"
    );

    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.materialize_calls, 2);
    assert_eq!(
        stats.materialize_root_trail_entries, 3,
        "first pass scans two roots; second pass should scan only the new suffix"
    );
    assert_eq!(stats.materialize_emitted_unit_lines, 2);
    assert_eq!(stats.materialize_unit_hints, 4);
    assert_eq!(stats.materialize_unit_max_hints, 2);
    assert_eq!(stats.materialize_incomplete_chains, 0);
    assert_eq!(stats.materialize_hidden_trusted_units, 0);
    assert!(
        solver.cold.lrat_materialize_hints_buf.is_empty(),
        "materialization scratch must not retain stale hint IDs"
    );
    assert!(
        solver.cold.lrat_materialize_hints_buf.capacity() >= initial_hint_capacity,
        "materialization scratch should retain capacity for reuse"
    );
}

#[test]
fn test_collect_empty_clause_hints_for_unit_contradiction_skips_hidden_unit_id() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(1, proof);

    let existing = Literal::positive(Variable(0));
    let existing_idx = solver.add_clause_db(&[existing], false);
    let existing_ref = ClauseRef(existing_idx as u32);
    let existing_id = solver.clause_id(existing_ref);
    assert_ne!(existing_id, 0, "existing unit must have a proof ID");

    solver.trail = vec![existing];
    solver.trail_lim = vec![];
    solver.var_data[existing.variable().index()].level = 0;
    solver.var_data[existing.variable().index()].trail_pos = 0;
    solver.var_data[existing.variable().index()].reason = existing_ref.0;
    assign_test_lit(&mut solver, existing);
    solver.record_unit_proof_id_for_lit(existing, existing_id);

    let hidden_id = solver.proof_emit_unit(existing.negated(), &[], ProofAddKind::TrustedTransform);
    assert_ne!(
        hidden_id, 0,
        "trusted-transform unit must reserve an LRAT ID"
    );
    assert!(
        !solver.lrat_hint_id_visible(hidden_id),
        "trusted-transform unit must stay hidden from external LRAT output"
    );

    let hints =
        solver.collect_empty_clause_hints_for_unit_contradiction(hidden_id, existing.negated());
    assert!(
        hints.is_empty(),
        "hidden contradictory unit must not produce an external LRAT empty-clause hint chain"
    );
}

#[test]
fn test_compute_lrat_chain_for_removed_literals_falls_back_to_raw_level0_reason() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(5, proof);

    let uip = Literal::positive(Variable(0));
    let removed = Literal::positive(Variable(1));
    let level0_mid = Literal::positive(Variable(2));
    let leaf_a = Literal::positive(Variable(3));
    let leaf_b = Literal::positive(Variable(4));

    // c0 = {level0_mid, ¬leaf_a, ¬leaf_b}: root-level implication whose own
    // unit proof cannot be materialized because its antecedents have no proof IDs.
    let c0_idx = solver.add_clause_db(&[level0_mid, leaf_a.negated(), leaf_b.negated()], false);
    let c0_ref = ClauseRef(c0_idx as u32);
    let c0_id = solver.clause_id(c0_ref);
    assert_ne!(c0_id, 0, "level-0 fallback reason must have a proof ID");

    // c1 = {removed, ¬level0_mid}: removed literal depends on that level-0 node.
    let c1_idx = solver.add_clause_db(&[removed, level0_mid.negated()], false);
    let c1_ref = ClauseRef(c1_idx as u32);
    let c1_id = solver.clause_id(c1_ref);
    assert_ne!(c1_id, 0, "removed literal reason must have a proof ID");

    solver.conflict.set_asserting_literal(uip);
    solver.trail = vec![leaf_a, leaf_b, level0_mid];
    solver.trail_lim = vec![];

    solver.var_data[level0_mid.variable().index()].level = 0;
    solver.var_data[level0_mid.variable().index()].trail_pos = 2;
    solver.var_data[level0_mid.variable().index()].reason = c0_ref.0;

    solver.var_data[leaf_a.variable().index()].level = 0;
    solver.var_data[leaf_a.variable().index()].trail_pos = 0;
    solver.var_data[leaf_a.variable().index()].reason = NO_REASON;

    solver.var_data[leaf_b.variable().index()].level = 0;
    solver.var_data[leaf_b.variable().index()].trail_pos = 1;
    solver.var_data[leaf_b.variable().index()].reason = NO_REASON;

    solver.var_data[removed.variable().index()].level = 1;
    solver.var_data[removed.variable().index()].reason = c1_ref.0;

    let minimize_level0 = solver.compute_lrat_chain_for_removed_literals(&[uip, removed]);
    let result = solver.conflict.get_result(0, 0);

    assert!(
        minimize_level0.is_empty(),
        "fallback path must keep the raw level-0 reason in mini_chain when no unit proof exists"
    );
    assert_eq!(
        result.resolution_chain,
        vec![c1_id, c0_id],
        "removed-literal minimize chain must retain the raw level-0 reason when unit proof materialization is unavailable"
    );
}

fn setup_level0_conflict_chain_fixture() -> (Solver, ClauseRef) {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    solver.cold.clause_trace = Some(ClauseTrace::new());
    solver.decision_level = 0;

    let a = Literal::positive(Variable(0));
    let c = Literal::positive(Variable(1));
    let idx_c1 = solver.add_clause_db(&[a], false);
    let idx_c2 = solver.add_clause_db(&[a.negated(), c], false);
    let idx_c3 = solver.add_clause_db(&[a.negated(), c.negated()], false);
    let ref_c1 = ClauseRef(idx_c1 as u32);
    let ref_c3 = ClauseRef(idx_c3 as u32);

    solver.trail = vec![a, c];
    solver.var_data[0].reason = ref_c1.0;
    solver.var_data[1].reason = idx_c2 as u32;
    solver.vals[a.index()] = 1;
    solver.vals[a.negated().index()] = -1;
    solver.vals[c.index()] = 1;
    solver.vals[c.negated().index()] = -1;
    (solver, ref_c3)
}

/// Verify that record_level0_conflict_chain populates resolution hints in clause trace.
///
/// At decision level 0, 1UIP conflict analysis cannot run (it assumes
/// decision_level > 0). Instead, record_level0_conflict_chain walks the trail
/// backward and collects all reason clause IDs. This test verifies that:
/// 1. The empty-clause trace entry gets the correct resolution chain
/// 2. set_resolution_hints succeeds (the debug_assert contract is satisfied)
#[test]
fn test_record_level0_conflict_chain_sets_resolution_hints() {
    // Scenario:
    // c1={a} propagates a=true, c2={¬a,c} propagates c=true, c3={¬a,¬c}
    // conflicts at level 0. Expected chain: c3(3) -> c2(2) -> c1(1).
    let (mut solver, ref_c3) = setup_level0_conflict_chain_fixture();
    solver.record_level0_conflict_chain(ref_c3);

    let trace = solver
        .cold
        .clause_trace
        .as_ref()
        .expect("clause trace exists");
    assert_eq!(trace.len(), 5);
    let empty_entry = trace.entries().last().expect("has entries");
    assert!(
        empty_entry.clause.is_empty(),
        "level-0 chain stores empty clause"
    );
    assert!(!empty_entry.is_original, "level-0 chain clause is learned");
    assert_eq!(
        empty_entry.resolution_hints,
        vec![1, 2, 3],
        "positive-RUP chain: root fact, implication, then conflict"
    );
    crate::validate_clause_trace_resolution(
        trace,
        2,
        &crate::ResolutionValidationLimits::unbounded(),
    )
    .expect("forward level-0 hints must pass independent positive-RUP replay");
}

/// Regression test for #4617: ClearLevel0 must preserve LRAT chain provenance.
///
/// When a level-0 reason clause is deleted via ReasonPolicy::ClearLevel0,
/// reason[vi] is set to None. Without the level0_proof_id fallback, the
/// chain collector silently skips the variable and produces an incomplete
/// LRAT derivation chain.
#[test]
fn test_level0_conflict_chain_after_clearlevel0_includes_saved_proof_id() {
    use crate::ClauseTrace;

    // 3 variables: a=0, b=1, c=2; LRAT enabled for clause IDs.
    //
    // Scenario:
    //   c1: {a}         -> unit, propagates a=true (reason for var 0). ID=1
    //   c2: {¬a, b}     -> binary, ¬a=false → b=true (reason for var 1). ID=2
    //   c3: {¬b, c}     -> binary, ¬b=false → c=true (reason for var 2). ID=3
    //
    // After propagation, delete c2 via ClearLevel0:
    //   reason[1] = None, but level0_proof_id[1] = 2 (saved by fix).
    //
    // Then add conflict clause:
    //   c4: {¬a, ¬c}    -> conflict: ¬a=false, ¬c=false. ID=4
    //
    // Chain should include c2's ID (2) via the fallback.
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(3, proof);
    solver.cold.clause_trace = Some(ClauseTrace::new());
    solver.decision_level = 0;

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));

    let _idx_c1 = solver.add_clause_db(&[a], false);
    let idx_c2 = solver.add_clause_db(&[a.negated(), b], false);
    let _idx_c3 = solver.add_clause_db(&[b.negated(), c], false);
    let idx_c4 = solver.add_clause_db(&[a.negated(), c.negated()], false);

    let ref_c2 = ClauseRef(idx_c2 as u32);
    let ref_c4 = ClauseRef(idx_c4 as u32);

    // Simulate level-0 propagation: a, b, c
    solver.trail = vec![a, b, c];
    solver.var_data[0].reason = _idx_c1 as u32;
    solver.var_data[1].reason = ref_c2.0;
    solver.var_data[2].reason = _idx_c3 as u32;
    solver.vals[a.index()] = 1;
    solver.vals[a.negated().index()] = -1;
    solver.vals[b.index()] = 1;
    solver.vals[b.negated().index()] = -1;
    solver.vals[c.index()] = 1;
    solver.vals[c.negated().index()] = -1;

    // Simulate ClearLevel0: the real delete_clause_checked calls
    // materialize_level0_unit_proofs() first, then emits a derived unit proof
    // for the variable whose reason is being cleared, then sets the reason to
    // NO_REASON. Simulate this sequence correctly (#7108).
    solver.materialize_level0_unit_proofs();
    // After materialization, var 1 should have a unit proof ID.
    let b_proof_id = solver.unit_proof_id_of_var_index(1).unwrap_or(0);
    assert_ne!(
        b_proof_id, 0,
        "var 1 (b) should have a materialized unit proof ID"
    );
    // Now clear the reason (simulating ClearLevel0 after materialization).
    solver.var_data[1].reason = NO_REASON;

    // Now trigger level-0 conflict chain collection.
    solver.record_level0_conflict_chain(ref_c4);

    // Verify: the chain includes the proof ID for var 1 (b). In the clause
    // trace, this is recorded via collect_resolution_chain which uses the
    // resolution chain format. The key requirement is that the empty clause
    // is properly derived.
    let trace = solver
        .cold
        .clause_trace
        .as_ref()
        .expect("clause trace exists");
    let empty_entry = trace.entries().last().expect("has entries");
    assert!(
        empty_entry.clause.is_empty(),
        "level-0 chain stores empty clause"
    );
    // The clause trace should contain a proof ID for var 1 (b) — either the
    // original c2_id (from collect_resolution_chain's level0_proof_id fallback)
    // or the materialized unit proof ID.
    let c2_id = solver.clause_id(ref_c2);
    let has_b_proof = empty_entry.resolution_hints.contains(&c2_id)
        || empty_entry.resolution_hints.contains(&b_proof_id);
    assert!(
        has_b_proof,
        "chain must include proof for var 1 (b): c2_id={c2_id}, b_proof_id={b_proof_id}, \
         but got: {:?}",
        empty_entry.resolution_hints,
    );
    crate::validate_clause_trace_resolution(
        trace,
        3,
        &crate::ResolutionValidationLimits::unbounded(),
    )
    .expect("ClearLevel0 provenance must remain a complete positive-RUP trace");
}

/// Re-entering level-0 materialization must reuse the saved standalone unit
/// provenance rather than append a duplicate clause-ID row to `ClauseTrace`.
#[test]
fn test_materialize_level0_unit_proofs_traces_each_id_once() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver = Solver::with_proof_output(2, proof);
    solver.cold.clause_trace = Some(ClauseTrace::new());

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c1 = solver.add_clause_db(&[a], false);
    let c2 = solver.add_clause_db(&[a.negated(), b], false);

    solver.trail = vec![a, b];
    solver.var_data[0].reason = c1 as u32;
    solver.var_data[1].reason = c2 as u32;
    solver.var_data[0].level = 0;
    solver.var_data[1].level = 0;
    solver.var_data[0].trail_pos = 0;
    solver.var_data[1].trail_pos = 1;
    assign_test_lit(&mut solver, a);
    assign_test_lit(&mut solver, b);

    solver.materialize_level0_unit_proofs();
    let b_unit_id = solver
        .visible_unit_proof_id_for_lit(b)
        .expect("b must receive standalone unit provenance");
    let first_count = solver
        .cold
        .clause_trace
        .as_ref()
        .expect("clause trace")
        .entries()
        .iter()
        .filter(|entry| entry.id == b_unit_id)
        .count();
    assert_eq!(first_count, 1);

    solver.materialize_level0_unit_proofs();
    let second_count = solver
        .cold
        .clause_trace
        .as_ref()
        .expect("clause trace")
        .entries()
        .iter()
        .filter(|entry| entry.id == b_unit_id)
        .count();
    assert_eq!(second_count, 1, "saved proof IDs must not be traced twice");
}

#[test]
fn test_record_level0_conflict_chain_uses_unit_proof_id_when_reason_absent() {
    use crate::ClauseTrace;

    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    solver.cold.clause_trace = Some(ClauseTrace::new());
    solver.decision_level = 0;

    let a = Literal::positive(Variable(0));
    let c = Literal::positive(Variable(1));

    let idx_c1 = solver.add_clause_db(&[a], false);
    let idx_c2 = solver.add_clause_db(&[a.negated(), c], false);
    let idx_c3 = solver.add_clause_db(&[a.negated(), c.negated()], false);
    let c1_ref = ClauseRef(idx_c1 as u32);
    let c3_ref = ClauseRef(idx_c3 as u32);

    solver.trail = vec![a, c];
    solver.var_data[0].reason = NO_REASON;
    solver.var_data[1].reason = idx_c2 as u32;
    solver.record_unit_proof_id_for_lit(a, solver.clause_id(c1_ref));
    assign_test_lit(&mut solver, a);
    assign_test_lit(&mut solver, c);

    solver.record_level0_conflict_chain(c3_ref);

    let trace = solver
        .cold
        .clause_trace
        .as_ref()
        .expect("clause trace exists");
    let empty_entry = trace.entries().last().expect("empty clause entry");
    assert_eq!(
        empty_entry.resolution_hints,
        vec![1, 2, 3],
        "level-0 chain should replay unit provenance before the conflict"
    );
    crate::validate_clause_trace_resolution(
        trace,
        2,
        &crate::ResolutionValidationLimits::unbounded(),
    )
    .expect("unit-provenance fallback must pass independent positive-RUP replay");
}

/// Regression guard: collect_resolution_chain reuses persistent work arrays
/// and clears only touched entries after each call.
///
/// References: #4172 (sat-debuggability tracking), CaDiCaL uses
/// reusable stamp arrays (reference/cadical/src/analyze.cpp).
#[test]
fn test_collect_resolution_chain_reuses_persistent_marks() {
    // Setup: 3 variables, LRAT enabled, level-0 propagation with conflict.
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(3, proof);
    solver.decision_level = 0;

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));

    let idx_c1 = solver.add_clause_db(&[a], false);
    let idx_c2 = solver.add_clause_db(&[a.negated(), b], false);
    let _idx_c3 = solver.add_clause_db(&[b.negated(), c], false);

    solver.trail = vec![a, b, c];
    solver.var_data[0].reason = idx_c1 as u32;
    solver.var_data[1].reason = idx_c2 as u32;
    solver.vals[a.index()] = 1;
    solver.vals[a.negated().index()] = -1;
    solver.vals[b.index()] = 1;
    solver.vals[b.negated().index()] = -1;
    solver.vals[c.index()] = 1;
    solver.vals[c.negated().index()] = -1;

    assert!(solver.min.lrat_to_clear.is_empty(), "worklist starts empty");
    assert!(
        solver.min.minimize_flags.iter().all(|&f| f & LRAT_A == 0),
        "LRAT_A bits start clear"
    );

    // collect_resolution_chain must reuse persistent marks and clean up.
    let chain =
        solver.collect_resolution_chain(ClauseRef(idx_c2 as u32), None, &det_hash_set_new());
    assert!(!chain.is_empty(), "chain should contain reason clause IDs");
    assert_eq!(
        solver.min.minimize_flags.len(),
        3,
        "packed flags array is sized by num_vars"
    );
    assert!(
        solver.min.lrat_to_clear.is_empty(),
        "sparse cleanup list must be empty after collection"
    );
    assert!(
        solver.min.minimize_flags.iter().all(|&f| f & LRAT_A == 0),
        "all touched LRAT_A marks must be cleared after collection"
    );
}

/// Verify lrat_reverse_hints reverses, filters zeros, and preserves
/// duplicates at scale. Dedup is at construction time (#5248), not here.
#[test]
fn test_lrat_hint_dedup_correctness_at_scale() {
    // Build: 500 entries + 200 duplicates + 2 zeros = 702 total
    let mut hints: Vec<u64> = Vec::new();
    for cycle in 0..5 {
        for i in 1..=100u64 {
            hints.push(i + cycle * 100);
        }
    }
    let dup = hints[..200].to_vec();
    hints.extend(dup);
    hints.push(0);
    hints.push(0);

    let result = Solver::lrat_reverse_hints(&hints);

    // All 700 non-zero entries preserved (no dedup at this level), zeros filtered
    assert_eq!(result.len(), 700, "700 non-zero hint entries expected");
    assert!(!result.contains(&0), "sentinel 0 must not appear");
    assert_eq!(
        result[0], 200,
        "first after reversal should be last dup entry"
    );
}

#[test]
fn test_collect_probe_conflict_lrat_hints_valid_level1_conflict() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    solver.decision_level = 1;

    let probe = Literal::positive(Variable(0));
    let conflict_idx = solver.add_clause_db(&[probe.negated()], false);
    let conflict_ref = ClauseRef(conflict_idx as u32);

    solver.trail = vec![probe];
    solver.vals[probe.index()] = 1;
    solver.vals[probe.negated().index()] = -1;

    let hints = solver.collect_probe_conflict_lrat_hints(conflict_ref, probe, None);
    assert_eq!(
        hints,
        vec![1],
        "single conflict clause should produce one hint"
    );
}

#[test]
fn test_collect_probe_conflict_lrat_hints_uses_unit_proof_id_when_reason_absent() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    solver.decision_level = 1;

    let probe = Literal::positive(Variable(0));
    let implied = Literal::positive(Variable(1));
    let unit_idx = solver.add_clause_db(&[implied], false);
    let conflict_idx = solver.add_clause_db(&[probe.negated(), implied.negated()], false);
    let conflict_ref = ClauseRef(conflict_idx as u32);

    solver.trail = vec![implied, probe];
    solver.var_data[implied.variable().index()].reason = NO_REASON;
    solver.record_unit_proof_id_for_lit(implied, solver.clause_id(ClauseRef(unit_idx as u32)));
    assign_test_lit(&mut solver, implied);
    assign_test_lit(&mut solver, probe);

    let hints = solver.collect_probe_conflict_lrat_hints(conflict_ref, probe, None);
    // collect_resolution_chain builds [conflict_id, unit_id] = [2, 1],
    // then lrat_reverse_hints reverses to [1, 2].
    assert_eq!(
        hints,
        vec![1, 2],
        "probe hints after reversal: unit provenance then conflict clause"
    );
}

#[test]
fn test_collect_probe_conflict_lrat_hints_uses_cached_conflict_clause_id() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    solver.decision_level = 1;

    let probe = Literal::positive(Variable(0));

    // Real active conflict clause with a valid proof ID.
    let real_conflict_idx = solver.add_clause_db(&[probe.negated()], false);
    let real_conflict_id = solver.clause_id(ClauseRef(real_conflict_idx as u32));
    assert_ne!(
        real_conflict_id, 0,
        "test setup requires a real conflict ID"
    );

    // Simulate an internal/shortened conflict_ref without a direct proof ID.
    // In production this cache is populated by propagate_bcp::conflict_finalize
    // before LRAT hint collection runs.
    let internal_conflict_idx = solver.add_clause_db(&[probe.negated()], false);
    solver.cold.clause_ids[internal_conflict_idx] = 0;
    let conflict_ref = ClauseRef(internal_conflict_idx as u32);
    solver.last_conflict_clause_ref = Some(conflict_ref);
    solver.last_conflict_clause_id = real_conflict_id;

    solver.trail = vec![probe];
    solver.trail_lim = vec![0];
    solver.vals[probe.index()] = 1;
    solver.vals[probe.negated().index()] = -1;

    let hints = solver.collect_probe_conflict_lrat_hints(conflict_ref, probe, None);
    assert_eq!(
        hints,
        vec![real_conflict_id],
        "probe hint collection must reuse the cached conflict clause ID \
         when conflict_ref has no direct mapping (#7262)"
    );
}

#[test]
fn test_reset_search_state_rebuild_preserves_original_clause_ids_in_lrat_mode() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    assert!(solver.add_clause(vec![x0, x1]));
    assert!(solver.add_clause(vec![x0.negated()]));

    let original_offsets: Vec<usize> = solver.arena.active_indices().collect();
    assert_eq!(original_offsets.len(), 2, "test setup requires 2 originals");

    let original_ids: Vec<u64> = original_offsets
        .iter()
        .map(|&idx| solver.clause_id(ClauseRef(idx as u32)))
        .collect();
    assert!(
        original_ids.iter().all(|&id| id != 0),
        "original clauses must start with LRAT IDs"
    );

    solver.arena.delete(original_offsets[0]);
    solver.reset_search_state();

    let rebuilt_offsets: Vec<usize> = solver.arena.active_indices().collect();
    assert_eq!(
        rebuilt_offsets.len(),
        2,
        "rebuild must restore both originals"
    );

    let rebuilt_ids: Vec<u64> = rebuilt_offsets
        .iter()
        .map(|&idx| solver.clause_id(ClauseRef(idx as u32)))
        .collect();
    assert_eq!(
        rebuilt_ids, original_ids,
        "reset_search_state rebuild must preserve original LRAT clause IDs"
    );
}

#[test]
fn test_collect_probe_conflict_lrat_hints_filters_forced_unit_rup_literal() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(3, proof);
    solver.decision_level = 1;

    let probe = Literal::positive(Variable(0));
    let forced_unit = Literal::negative(Variable(1));
    let implied = Literal::positive(Variable(2));

    // Reason clause contains forced_unit.negated() and would be satisfied
    // under the RUP assumption for the derived unit [forced_unit].
    let reason_idx = solver.add_clause_db(&[forced_unit.negated(), implied], false);
    let conflict_idx = solver.add_clause_db(&[probe.negated(), implied.negated()], false);
    let conflict_ref = ClauseRef(conflict_idx as u32);

    solver.trail = vec![probe, implied];
    solver.trail_lim = vec![0];
    solver.var_data[implied.variable().index()].reason = reason_idx as u32;
    solver.vals[probe.index()] = 1;
    solver.vals[probe.negated().index()] = -1;
    solver.vals[implied.index()] = 1;
    solver.vals[implied.negated().index()] = -1;

    let hints = solver.collect_probe_conflict_lrat_hints(conflict_ref, probe, Some(forced_unit));
    assert_eq!(
        hints,
        vec![2],
        "reason clause satisfied by forced-unit RUP assumption must be filtered"
    );
}

#[test]
fn test_collect_probe_parent_chain_lrat_hints_starts_at_parent_assumption() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(3, proof);
    solver.decision_level = 1;

    let probe = Literal::positive(Variable(0));
    let parent = Literal::positive(Variable(1));
    let leaf = Literal::positive(Variable(2));

    let probe_to_parent = solver.add_clause_db(&[probe.negated(), parent], false);
    let parent_to_leaf = solver.add_clause_db(&[parent.negated(), leaf], false);
    let conflict_idx = solver.add_clause_db(&[leaf.negated()], false);
    let conflict_ref = ClauseRef(conflict_idx as u32);

    solver.trail = vec![probe, parent, leaf];
    solver.trail_lim = vec![0];
    for (pos, lit) in solver.trail.clone().into_iter().enumerate() {
        let var_idx = lit.variable().index();
        solver.var_data[var_idx].level = 1;
        solver.var_data[var_idx].trail_pos = pos as u32;
        assign_test_lit(&mut solver, lit);
    }
    solver.var_data[parent.variable().index()].reason = probe_to_parent as u32;
    solver.var_data[leaf.variable().index()].reason = parent_to_leaf as u32;
    solver.probe_parent[probe.variable().index()] = None;
    solver.probe_parent[parent.variable().index()] = Some(probe);
    solver.probe_parent[leaf.variable().index()] = Some(parent);

    let hints = solver
        .collect_probe_parent_chain_lrat_hints(conflict_ref, parent)
        .expect("parent-dominated trail suffix should produce LRAT hints");

    assert_eq!(
        hints,
        vec![
            solver.clause_id(ClauseRef(parent_to_leaf as u32)),
            solver.clause_id(conflict_ref),
        ],
        "parent-chain proof must skip the decision-to-parent prefix and replay only the dominated suffix"
    );
}

#[test]
fn test_collect_probe_parent_chain_lrat_hints_rejects_nondominated_conflict() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(4, proof);
    solver.decision_level = 1;

    let probe = Literal::positive(Variable(0));
    let parent = Literal::positive(Variable(1));
    let leaf = Literal::positive(Variable(2));
    let sibling = Literal::positive(Variable(3));

    let probe_to_parent = solver.add_clause_db(&[probe.negated(), parent], false);
    let parent_to_leaf = solver.add_clause_db(&[parent.negated(), leaf], false);
    let probe_to_sibling = solver.add_clause_db(&[probe.negated(), sibling], false);
    let conflict_idx = solver.add_clause_db(&[leaf.negated(), sibling.negated()], false);
    let conflict_ref = ClauseRef(conflict_idx as u32);

    solver.trail = vec![probe, parent, leaf, sibling];
    solver.trail_lim = vec![0];
    for (pos, lit) in solver.trail.clone().into_iter().enumerate() {
        let var_idx = lit.variable().index();
        solver.var_data[var_idx].level = 1;
        solver.var_data[var_idx].trail_pos = pos as u32;
        assign_test_lit(&mut solver, lit);
    }
    solver.var_data[parent.variable().index()].reason = probe_to_parent as u32;
    solver.var_data[leaf.variable().index()].reason = parent_to_leaf as u32;
    solver.var_data[sibling.variable().index()].reason = probe_to_sibling as u32;
    solver.probe_parent[probe.variable().index()] = None;
    solver.probe_parent[parent.variable().index()] = Some(probe);
    solver.probe_parent[leaf.variable().index()] = Some(parent);
    solver.probe_parent[sibling.variable().index()] = Some(probe);

    assert!(
        solver
            .collect_probe_parent_chain_lrat_hints(conflict_ref, parent)
            .is_none(),
        "conflict proof must fail closed when a required conflict literal is outside the parent subtree"
    );
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "must be called at decision level 1")]
fn test_collect_probe_conflict_lrat_hints_panics_when_level_not_one() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    solver.decision_level = 0;

    let probe = Literal::positive(Variable(0));
    let conflict_idx = solver.add_clause_db(&[probe.negated()], false);
    let conflict_ref = ClauseRef(conflict_idx as u32);

    let _ = solver.collect_probe_conflict_lrat_hints(conflict_ref, probe, None);
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "probe literal")]
fn test_collect_probe_conflict_lrat_hints_panics_when_probe_unassigned() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    solver.decision_level = 1;

    let probe = Literal::positive(Variable(0));
    let conflict_idx = solver.add_clause_db(&[probe.negated()], false);
    let conflict_ref = ClauseRef(conflict_idx as u32);

    let _ = solver.collect_probe_conflict_lrat_hints(conflict_ref, probe, None);
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "probe conflict clause")]
fn test_collect_probe_conflict_lrat_hints_panics_when_conflict_clause_not_false() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    solver.decision_level = 1;

    let probe = Literal::positive(Variable(0));
    let conflict_idx = solver.add_clause_db(&[probe], false);
    let conflict_ref = ClauseRef(conflict_idx as u32);

    solver.vals[probe.index()] = 1;
    solver.vals[probe.negated().index()] = -1;

    let _ = solver.collect_probe_conflict_lrat_hints(conflict_ref, probe, None);
}

/// Verify that CHB score updates are skipped in LegacyCoupled mode (#8091).
///
/// In the default single-thread configuration (EVSIDS+VMTF only), CHB
/// score updates on every conflict are pure overhead. The fix gates CHB
/// updates behind a check on `branch_selector_mode`.
#[test]
fn test_chb_scores_not_updated_in_legacy_coupled_mode() {
    use crate::mab::BranchSelectorMode;

    let mut solver: Solver = Solver::new(4);
    // Default should already be LegacyCoupled
    assert_eq!(
        solver.cold.branch_selector_mode,
        BranchSelectorMode::LegacyCoupled,
        "default branch_selector_mode must be LegacyCoupled"
    );

    // Mark some variables as analyzed (simulating a conflict)
    solver.conflict.mark_seen(0, &mut solver.var_data);
    solver.conflict.mark_seen(2, &mut solver.var_data);

    let alpha_before = solver.vsids.chb_alpha;
    let conflicts_before = solver.vsids.chb_conflicts;

    solver.bump_analyzed_variables();

    // CHB alpha and conflict counter must NOT have changed
    assert_eq!(
        solver.vsids.chb_alpha, alpha_before,
        "CHB alpha must not change in LegacyCoupled mode"
    );
    assert_eq!(
        solver.vsids.chb_conflicts, conflicts_before,
        "CHB conflict counter must not advance in LegacyCoupled mode"
    );
}

/// Verify that CHB score updates are skipped in focused MAB mode.
#[test]
fn test_chb_scores_not_updated_in_focused_mab_ucb1_mode() {
    use crate::mab::BranchSelectorMode;

    let mut solver: Solver = Solver::new(4);
    solver.cold.branch_selector_mode = BranchSelectorMode::MabUcb1;
    solver.stable_mode = false;

    solver.conflict.mark_seen(0, &mut solver.var_data);
    solver.conflict.mark_seen(2, &mut solver.var_data);

    let alpha_before = solver.vsids.chb_alpha;
    let conflicts_before = solver.vsids.chb_conflicts;

    solver.bump_analyzed_variables();

    assert_eq!(
        solver.vsids.chb_alpha, alpha_before,
        "focused MAB mode must not update dormant CHB scores"
    );
    assert_eq!(
        solver.vsids.chb_conflicts, conflicts_before,
        "focused MAB mode must not advance CHB conflict counter"
    );
}

/// Verify that CHB score updates DO run when stable MAB UCB1 mode is active.
#[test]
fn test_chb_scores_updated_in_stable_mab_ucb1_mode() {
    use crate::mab::BranchSelectorMode;

    let mut solver: Solver = Solver::new(4);
    solver.cold.branch_selector_mode = BranchSelectorMode::MabUcb1;
    solver.stable_mode = true;

    solver.conflict.mark_seen(0, &mut solver.var_data);
    solver.conflict.mark_seen(2, &mut solver.var_data);

    let alpha_before = solver.vsids.chb_alpha;
    let conflicts_before = solver.vsids.chb_conflicts;

    solver.bump_analyzed_variables();

    // CHB alpha and conflict counter MUST have changed
    assert!(
        solver.vsids.chb_alpha < alpha_before,
        "CHB alpha must decay in MabUcb1 mode"
    );
    assert_eq!(
        solver.vsids.chb_conflicts,
        conflicts_before + 1,
        "CHB conflict counter must advance in MabUcb1 mode"
    );
}

/// Verify that set_branch_heuristic(Chb) still works for programmatic callers.
///
/// When a caller explicitly requests CHB, the mode switches to Fixed(Chb)
/// and CHB score updates must run.
#[test]
fn test_set_branch_heuristic_chb_enables_chb_updates() {
    use crate::mab::{BranchHeuristic, BranchSelectorMode};

    let mut solver: Solver = Solver::new(4);
    solver.set_branch_heuristic(BranchHeuristic::Chb);

    assert_eq!(
        solver.cold.branch_selector_mode,
        BranchSelectorMode::Fixed(BranchHeuristic::Chb),
        "set_branch_heuristic(Chb) must set Fixed(Chb) mode"
    );
    assert_eq!(
        solver.active_branch_heuristic,
        BranchHeuristic::Chb,
        "active heuristic must be Chb after set_branch_heuristic"
    );

    // Simulate a conflict and verify CHB updates run
    solver.conflict.mark_seen(1, &mut solver.var_data);
    let conflicts_before = solver.vsids.chb_conflicts;

    solver.bump_analyzed_variables();

    assert_eq!(
        solver.vsids.chb_conflicts,
        conflicts_before + 1,
        "CHB conflict counter must advance when Fixed(Chb) is active"
    );
}

fn analyze_lrat_two_var_conflict(prune_conflict_experiments: bool) -> Solver {
    let proof = ProofOutput::lrat_text(Vec::new(), 4);
    let mut solver: Solver = Solver::with_proof_output(2, proof);
    solver.set_sat_comp_main_conflict_pruning(prune_conflict_experiments);

    let x = Variable(0);
    let y = Variable(1);
    solver.add_clause(vec![Literal::positive(x), Literal::positive(y)]);
    solver.add_clause(vec![Literal::positive(x), Literal::negative(y)]);
    solver.add_clause(vec![Literal::negative(x), Literal::positive(y)]);
    solver.add_clause(vec![Literal::negative(x), Literal::negative(y)]);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(solver.propagate().is_none());

    solver.decide(Literal::positive(x));
    let conflict_ref = solver
        .propagate()
        .expect("decision x=true should produce a conflict");
    solver.analyze_and_backtrack(conflict_ref, "ibcl-pruning-test", |_, _| {});
    solver
}

fn analyze_lrat_pivot_ready_conflict() -> Solver {
    let proof = ProofOutput::lrat_text(Vec::new(), 4);
    let mut solver: Solver = Solver::with_proof_output(6, proof);

    let x = Variable(0);
    let y = Variable(1);
    let z = Variable(2);
    let a = Variable(3);
    let b = Variable(4);
    let c = Variable(5);

    // y=true, z=true, x=true imply a, b, c and then conflict with (not c or
    // not x). The 1UIP core chain has a conflict seed plus multiple reason
    // clauses, and the learned clause keeps lower-level literals y and z.
    solver.add_clause(vec![
        Literal::negative(x),
        Literal::positive(a),
        Literal::negative(y),
        Literal::negative(z),
    ]);
    solver.add_clause(vec![Literal::negative(a), Literal::positive(b)]);
    solver.add_clause(vec![Literal::negative(b), Literal::positive(c)]);
    solver.add_clause(vec![Literal::negative(c), Literal::negative(x)]);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(solver.propagate().is_none());

    solver.decide(Literal::positive(y));
    assert!(solver.propagate().is_none());
    solver.decide(Literal::positive(z));
    assert!(solver.propagate().is_none());
    solver.decide(Literal::positive(x));
    let conflict_ref = solver
        .propagate()
        .expect("x=true with y,z=true should produce the c/x conflict");
    solver.analyze_and_backtrack(conflict_ref, "ibcl-pivot-ready-test", |_, _| {});
    solver
}

#[test]
fn test_sat_comp_main_pruning_suppresses_lrat_ibcl_stats() {
    let baseline = analyze_lrat_two_var_conflict(false);
    assert!(
        baseline.stats.ibcl_attempts + baseline.stats.ibcl_skipped_short_chain > 0,
        "baseline LRAT conflict analysis should update IBCL stats"
    );
    assert_eq!(baseline.stats.ibcl_skipped_missing_pivots, 0);

    let pruned = analyze_lrat_two_var_conflict(true);
    assert_eq!(pruned.stats.ibcl_attempts, 0);
    assert_eq!(pruned.stats.ibcl_skipped_short_chain, 0);
    assert_eq!(pruned.stats.ibcl_skipped_missing_pivots, 0);
    assert_eq!(pruned.stats.ibcl_improvements, 0);
}

#[test]
fn test_lrat_ibcl_attempt_requires_pivot_ready_core_chain() {
    let solver = analyze_lrat_pivot_ready_conflict();

    assert_eq!(
        solver.stats.ibcl_skipped_missing_pivots, 0,
        "direct 1UIP reason clauses should carry pivot metadata for IBCL"
    );
    assert_eq!(
        solver.stats.ibcl_skipped_short_chain, 0,
        "the crafted conflict has a long core chain and a non-binary learned clause"
    );
    assert_eq!(
        solver.stats.ibcl_attempts, 1,
        "IBCL should count exactly one pivot-ready proof skeleton"
    );
}
