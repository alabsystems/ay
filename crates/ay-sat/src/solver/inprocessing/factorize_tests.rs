// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn ternary_factor_matrix() -> Vec<Vec<Literal>> {
    let pos = |i: u32| Literal::positive(Variable(i));
    vec![
        vec![pos(0), pos(2), pos(3)],
        vec![pos(1), pos(2), pos(3)],
        vec![pos(0), pos(2), pos(4)],
        vec![pos(1), pos(2), pos(4)],
        vec![pos(0), pos(3), pos(4)],
        vec![pos(1), pos(3), pos(4)],
    ]
}

fn factor_application(
    fresh_var: Variable,
    factors: Vec<Literal>,
    quotient_tails: Vec<Vec<Literal>>,
    to_delete: Vec<usize>,
) -> crate::factor::FactorApplication {
    let fresh_pos = Literal::positive(fresh_var);
    let fresh_neg = Literal::negative(fresh_var);
    let divider_clauses = factors
        .iter()
        .map(|&factor| vec![fresh_pos, factor])
        .collect();
    let quotient_clauses = quotient_tails
        .into_iter()
        .map(|tail| {
            let mut clause = Vec::with_capacity(tail.len() + 1);
            clause.push(fresh_neg);
            clause.extend(tail);
            clause
        })
        .collect();
    let mut blocked_clause = Vec::with_capacity(factors.len() + 1);
    blocked_clause.push(fresh_neg);
    blocked_clause.extend(factors.iter().map(|lit| lit.negated()));

    crate::factor::FactorApplication {
        fresh_var,
        factors,
        divider_clauses,
        quotient_clauses,
        blocked_clause,
        to_delete,
    }
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

fn render_factor_lrat_dry_run_replay(
    sidecar: &FactorLratDryRunSidecar,
    final_empty_hints: &[u64],
) -> String {
    let factor_count = sidecar.factors.len();
    assert!(
        sidecar.has_checker_visible_transaction_contract(),
        "dry-run sidecar must retain the signed checker-visible transaction contract"
    );
    assert_eq!(
        sidecar.planned_add_ids.len(),
        factor_count + 1 + sidecar.quotient_clauses.len()
    );
    let divider_ids = &sidecar.divider_clause_ids;
    let blocked_id = sidecar.blocked_clause_id;
    let quotient_ids = &sidecar.quotient_clause_ids;

    let mut proof = String::new();
    for (&divider_id, &factor) in divider_ids.iter().zip(&sidecar.factors) {
        proof.push_str(&format!(
            "{divider_id} {} {factor} 0 0\n",
            sidecar.fresh_lit
        ));
    }
    proof.push_str(&format!("{blocked_id} {}", -sidecar.fresh_lit));
    for &factor in &sidecar.factors {
        proof.push_str(&format!(" {}", -factor));
    }
    proof.push_str(" 0");
    for &hint in &sidecar.blocked_signed_lrat_hints {
        proof.push_str(&format!(" {hint}"));
    }
    proof.push_str(" 0\n");

    for (quotient_idx, (&quotient_id, quotient_clause)) in quotient_ids
        .iter()
        .zip(&sidecar.quotient_clauses)
        .enumerate()
    {
        proof.push_str(&format!("{quotient_id}"));
        for &lit in quotient_clause {
            proof.push_str(&format!(" {lit}"));
        }
        proof.push_str(" 0");
        for &hint in &sidecar.quotient_lrat_hints[quotient_idx] {
            proof.push_str(&format!(" {hint}"));
        }
        proof.push_str(" 0\n");
    }

    if !final_empty_hints.is_empty() {
        let empty_id = sidecar
            .planned_add_ids
            .iter()
            .chain(final_empty_hints)
            .copied()
            .max()
            .expect("planned add or final empty hint IDs")
            + 1;
        proof.push_str(&format!("{empty_id} 0"));
        for &hint in final_empty_hints {
            proof.push_str(&format!(" {hint}"));
        }
        proof.push_str(" 0\n");
    }

    proof
}

fn verify_lrat_fixture(dimacs: &str, proof: &str) {
    let cnf = ay_lrat_check::dimacs::parse_cnf_with_ids(dimacs.as_bytes())
        .expect("bounded sidecar CNF must parse");
    let steps =
        ay_lrat_check::lrat_parser::parse_text_lrat(proof).expect("sidecar LRAT must parse");
    let mut checker = ay_lrat_check::checker::LratChecker::new(cnf.num_vars);
    for (id, clause) in &cnf.clauses {
        assert!(checker.add_original(*id, clause));
    }
    assert!(
        checker.verify_proof(&steps),
        "retained dry-run sidecar should replay as a checker-visible LRAT transaction"
    );
}

fn repo_root_for_factor_artifacts() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(std::path::Path::parent)
        .expect("crate should live under repo/crates/ay-sat")
        .to_path_buf()
}

fn producer_revision_for_factor_artifact() -> String {
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
fn test_build_factor_occ_filters_nonproductive_large_clauses() {
    let mut solver = Solver::new(8);
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));
    let e = Literal::positive(Variable(4));
    let f = Literal::positive(Variable(5));
    let g = Literal::positive(Variable(6));
    let h = Literal::positive(Variable(7));

    solver.add_clause(vec![a, b]);
    solver.add_clause(vec![a, c, d]);
    solver.add_clause(vec![b, c, d]);
    solver.add_clause(vec![a, c, e]);
    solver.add_clause(vec![b, c, e]);
    solver.add_clause(vec![f, g, h]);

    let occ = solver.build_factor_occ();

    assert_eq!(
        occ.count(a),
        3,
        "productive clauses should stay in occ lists"
    );
    assert_eq!(
        occ.count(b),
        3,
        "productive clauses should stay in occ lists"
    );
    assert_eq!(
        occ.count(c),
        4,
        "shared quotient literal should stay in occ lists"
    );
    assert_eq!(
        occ.count(d),
        2,
        "shared quotient literal should stay in occ lists"
    );
    assert_eq!(
        occ.count(e),
        2,
        "shared quotient literal should stay in occ lists"
    );
    assert_eq!(
        occ.count(f),
        0,
        "unique large clause should be filtered out"
    );
    assert_eq!(
        occ.count(g),
        0,
        "unique large clause should be filtered out"
    );
    assert_eq!(
        occ.count(h),
        0,
        "unique large clause should be filtered out"
    );
}

#[test]
fn test_factorize_records_er_extension_definition_log() {
    let clauses = ternary_factor_matrix();

    let mut solver = Solver::new(5);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    solver.factorize();

    assert_eq!(
        solver.er_extension_definition_count(),
        1,
        "one factorization extension variable must have one ER definition artifact"
    );
    let def = &solver.er_extension_proof_log().definitions()[0];
    assert_eq!(def.producer(), crate::er_proof::ErProducer::Factor);
    assert_eq!(def.definition_clauses().len(), 2);
    assert_eq!(def.derived_clauses().len(), 3);
    assert_eq!(def.proof_only_clauses().len(), 1);
    assert_eq!(def.source_clause_ids(), &[1, 2, 3, 4, 5, 6]);
    assert!(
        def.obligations()
            .contains(&crate::er_proof::ErObligationKind::OriginalModelProjection),
        "factor ER log must carry the original-DIMACS model projection obligation"
    );

    let mut buf = Vec::new();
    solver
        .write_er_extension_log_proof_replay(&mut buf)
        .expect("write ER log");
    let source = String::from_utf8(buf).expect("utf8");
    assert!(source.contains("Producer.factor"));
    assert!(source.contains("Obligation.freshRatDefinition"));
    assert!(source.contains("Obligation.derivedClauseRup"));
    assert!(source.contains("Obligation.originalModelProjection"));
    assert!(
        !source.contains("heuristicScore") && !source.contains("candidate"),
        "ER artifact must not include heuristic selection data"
    );
}

#[test]
fn test_factorize_missing_er_source_id_skips_before_mutation() {
    let clauses = ternary_factor_matrix();

    let mut solver = Solver::new(5);
    for clause in &clauses {
        assert!(solver.add_clause(clause.clone()));
    }

    let missing_source = 0usize;
    assert_ne!(
        solver.cold.clause_ids[missing_source], 0,
        "source clause should start with a tracked clause ID"
    );
    solver.cold.clause_ids[missing_source] = 0;

    let num_vars_before = solver.num_vars;
    let active_before = solver.arena.active_clause_count();
    let er_defs_before = solver.er_extension_definition_count();
    let factor_stats_before = solver.factor_stats();
    let factor_preflight_stats_before = solver.factor_lrat_preflight_stats();
    let factor_marks_before = solver.cold.factor_candidate_marks.clone();
    let factor_rounds_before = solver.cold.factor_rounds;
    let factor_extension_vars_before = solver.cold.factor_extension_vars_total;

    solver.factorize();

    assert_eq!(
        solver.num_vars, num_vars_before,
        "missing ER source ID must reject before extension-variable allocation"
    );
    assert_eq!(
        solver.arena.active_clause_count(),
        active_before,
        "missing ER source ID must reject before clause DB mutation"
    );
    assert_eq!(
        solver.er_extension_definition_count(),
        er_defs_before,
        "missing ER source ID must reject before recording reconstruction artifacts"
    );
    let factor_stats_after = solver.factor_stats();
    assert_eq!(
        factor_stats_after.rounds, factor_stats_before.rounds,
        "missing ER source ID must reject before factor stats advance"
    );
    assert_eq!(
        factor_stats_after.factored_count, factor_stats_before.factored_count,
        "missing ER source ID must reject before factor count advances"
    );
    assert_eq!(
        factor_stats_after.extension_vars, factor_stats_before.extension_vars,
        "missing ER source ID must reject before extension-var stats advance"
    );
    assert_eq!(
        solver.cold.factor_candidate_marks, factor_marks_before,
        "missing ER source ID must reject before consuming factor candidate marks"
    );
    assert_eq!(solver.cold.factor_rounds, factor_rounds_before);
    assert_eq!(
        solver.cold.factor_extension_vars_total,
        factor_extension_vars_before
    );
    assert_eq!(
        solver.factor_lrat_preflight_stats().er_obligation_missing,
        factor_preflight_stats_before.er_obligation_missing + 1,
        "missing source IDs must be counted as missing ER/model obligations"
    );
}

#[test]
fn test_factorize_lrat_missing_source_id_skips_before_mutation() {
    use crate::proof::ProofOutput;

    let clauses = ternary_factor_matrix();
    let mut solver =
        Solver::with_proof_output(5, ProofOutput::lrat_text(Vec::new(), clauses.len() as u64));
    for clause in &clauses {
        assert!(solver.add_clause(clause.clone()));
    }

    let occ = solver.build_factor_occ();
    let planned = solver.inproc.factor_engine.clone().run(
        &solver.arena,
        &occ,
        &solver.vals,
        solver.var_lifecycle.as_slice(),
        &crate::factor::FactorConfig {
            next_var_id: solver.num_vars,
            effort_limit: u64::MAX,
            elim_bound: 0,
        },
    );
    assert_eq!(
        planned.factored_count, 1,
        "test matrix must produce one factor transaction"
    );
    assert!(solver.factor_result_has_lrat_transaction_contract(&planned));
    let plan = solver
        .preflight_factor_lrat_transaction(&planned)
        .expect("structural planning succeeds before checker-obligation validation");
    assert_eq!(plan.planned_add_ids, vec![7, 8, 9, 10, 11, 12]);
    assert_eq!(plan.live_add_ids, vec![7, 8, 10, 11, 12]);
    assert_eq!(plan.source_delete_ids, vec![1, 2, 3, 4, 5, 6]);
    assert_eq!(plan.proof_only_delete_ids, vec![9]);

    let missing_source = planned.applications[0].to_delete[0];
    assert_ne!(
        solver.cold.clause_ids[missing_source], 0,
        "source clause should start with a real LRAT ID"
    );
    solver.cold.clause_ids[missing_source] = 0;
    assert!(
        !solver.factor_result_has_lrat_transaction_contract(&planned),
        "missing source ID must reject before any factor mutation"
    );
    assert!(matches!(
        solver.preflight_factor_lrat_transaction(&planned),
        Err(FactorLratTransactionReject::MissingOrHiddenSourceId {
            clause_idx,
            clause_id: 0,
        }) if clause_idx == missing_source
    ));

    let num_vars_before = solver.num_vars;
    let active_before = solver.arena.active_clause_count();
    let er_defs_before = solver.er_extension_definition_count();
    let factor_stats_before = solver.factor_stats();
    let factor_marks_before = solver.cold.factor_candidate_marks.clone();
    let factor_completed_epoch_before = solver.cold.factor_last_completed_epoch;
    let last_factor_ticks_before = solver.cold.last_factor_ticks;
    let next_factor_conflict_before = solver.inproc_ctrl.factor.next_conflict;
    let proof_added_before = solver
        .proof_manager
        .as_ref()
        .expect("proof manager")
        .added_count();
    let proof_deleted_before = solver
        .proof_manager
        .as_ref()
        .expect("proof manager")
        .deleted_count();
    solver.search_ticks[0] = 12345;

    solver.factorize();

    assert_eq!(
        solver.num_vars, num_vars_before,
        "failed LRAT preflight must not allocate extension variables"
    );
    assert_eq!(
        solver.arena.active_clause_count(),
        active_before,
        "failed LRAT preflight must not add or delete clauses"
    );
    assert_eq!(
        solver.er_extension_definition_count(),
        er_defs_before,
        "failed LRAT preflight must not record reconstruction witnesses"
    );
    assert_eq!(
        solver.factor_stats().rounds,
        factor_stats_before.rounds,
        "failed LRAT preflight must not count as an applied factor round"
    );
    assert_eq!(
        solver.factor_stats().factored_count,
        factor_stats_before.factored_count,
        "failed LRAT preflight must not count factored transactions"
    );
    assert_eq!(
        solver.cold.factor_candidate_marks, factor_marks_before,
        "failed LRAT preflight must not consume factor candidate marks"
    );
    assert_eq!(
        solver.cold.factor_last_completed_epoch, factor_completed_epoch_before,
        "failed LRAT preflight must not advance the completed factor epoch"
    );
    assert_eq!(
        solver.cold.last_factor_ticks, last_factor_ticks_before,
        "failed LRAT preflight must not update factor scheduler tick state"
    );
    assert_eq!(
        solver.inproc_ctrl.factor.next_conflict, next_factor_conflict_before,
        "failed LRAT preflight must not reschedule factor"
    );
    assert_eq!(
        solver
            .proof_manager
            .as_ref()
            .expect("proof manager")
            .added_count(),
        proof_added_before,
        "failed LRAT preflight must not emit proof additions"
    );
    assert_eq!(
        solver
            .proof_manager
            .as_ref()
            .expect("proof manager")
            .deleted_count(),
        proof_deleted_before,
        "failed LRAT preflight must not emit proof deletions"
    );
}

#[test]
fn test_factorize_lrat_preflight_flushes_pending_delete_batch() {
    use crate::proof::ProofOutput;

    let clauses = ternary_factor_matrix();
    let mut solver =
        Solver::with_proof_output(7, ProofOutput::lrat_text(Vec::new(), clauses.len() as u64));
    for clause in &clauses {
        assert!(solver.add_clause(clause.clone()));
    }

    let occ = solver.build_factor_occ();
    let planned = solver.inproc.factor_engine.clone().run(
        &solver.arena,
        &occ,
        &solver.vals,
        solver.var_lifecycle.as_slice(),
        &crate::factor::FactorConfig {
            next_var_id: solver.num_vars,
            effort_limit: u64::MAX,
            elim_bound: 0,
        },
    );
    assert_eq!(
        planned.factored_count, 1,
        "test matrix must produce one factor transaction"
    );

    let proof_only_clause = clauses[0].clone();
    let proof_only_id = solver
        .proof_emit_add(&proof_only_clause, &[1], ProofAddKind::Derived)
        .expect("emit proof-only LRAT addition");
    solver
        .proof_emit_delete(&proof_only_clause, proof_only_id)
        .expect("emit pending proof-only LRAT deletion");

    assert!(solver
        .proof_manager
        .as_ref()
        .expect("proof manager")
        .output()
        .has_pending_lrat_deletions());
    let plan = solver
        .preflight_factor_lrat_transaction(&planned)
        .expect("structural planning flushes prior deletion state");
    assert_eq!(plan.planned_add_ids, vec![9, 10, 11, 12, 13, 14]);
    assert_eq!(plan.live_add_ids, vec![9, 10, 12, 13, 14]);
    assert!(
        !solver
            .proof_manager
            .as_ref()
            .expect("proof manager")
            .output()
            .has_pending_lrat_deletions(),
        "planning must flush the pre-existing deletion before assigning IDs"
    );
}

#[test]
fn test_factorize_lrat_unproved_dividers_reject_before_mutation() {
    use crate::proof::ProofOutput;

    let clauses = ternary_factor_matrix();
    let mut solver =
        Solver::with_proof_output(5, ProofOutput::lrat_text(Vec::new(), clauses.len() as u64));
    for clause in &clauses {
        assert!(solver.add_clause(clause.clone()));
    }

    let num_vars_before = solver.num_vars;
    let active_before = solver.arena.active_clause_count();
    let er_defs_before = solver.er_extension_definition_count();
    let factor_stats_before = solver.factor_stats();
    let proof_added_before = solver
        .proof_manager
        .as_ref()
        .expect("proof manager")
        .added_count();
    let proof_deleted_before = solver
        .proof_manager
        .as_ref()
        .expect("proof manager")
        .deleted_count();
    let preflight_stats_before = solver.factor_lrat_preflight_stats();

    solver.factorize();

    assert_eq!(
        solver.num_vars, num_vars_before,
        "unproved dividers must reject before allocating an extension variable"
    );
    assert_eq!(
        solver.arena.active_clause_count(),
        active_before,
        "unproved dividers must reject before clause mutation"
    );
    assert_eq!(
        solver.er_extension_definition_count(),
        er_defs_before,
        "rejected transaction must not retain an ER reconstruction witness"
    );
    let factor_stats = solver.factor_stats();
    assert_eq!(factor_stats.rounds, factor_stats_before.rounds);
    assert_eq!(
        factor_stats.factored_count,
        factor_stats_before.factored_count
    );
    assert_eq!(
        factor_stats.extension_vars,
        factor_stats_before.extension_vars
    );
    assert_eq!(
        solver
            .proof_manager
            .as_ref()
            .expect("proof manager")
            .added_count(),
        proof_added_before,
        "rejected factor transaction must not emit LRAT additions"
    );
    assert_eq!(
        solver
            .proof_manager
            .as_ref()
            .expect("proof manager")
            .deleted_count(),
        proof_deleted_before,
        "rejected factor transaction must not emit LRAT deletions"
    );
    assert_eq!(
        solver
            .factor_lrat_preflight_stats()
            .checker_obligation_missing,
        preflight_stats_before.checker_obligation_missing + 1,
        "missing divider hints must trip the checker-obligation gate"
    );
    assert_eq!(
        solver.factor_lrat_dry_run_sidecars().len(),
        1,
        "diagnostic sidecar may be retained without applying the transformation"
    );
}

#[test]
fn test_factorize_lrat_retains_diagnostic_sidecar_but_rejects_mutation() {
    use crate::proof::ProofOutput;

    let clauses = ternary_factor_matrix();
    let mut solver =
        Solver::with_proof_output(5, ProofOutput::lrat_text(Vec::new(), clauses.len() as u64));
    for clause in &clauses {
        assert!(solver.add_clause(clause.clone()));
    }

    let num_vars_before = solver.num_vars;
    let active_before = solver.arena.active_clause_count();
    let er_defs_before = solver.er_extension_definition_count();
    let factor_stats_before = solver.factor_stats();
    let preflight_stats_before = solver.factor_lrat_preflight_stats();
    let proof_added_before = solver
        .proof_manager
        .as_ref()
        .expect("proof manager")
        .added_count();
    let proof_deleted_before = solver
        .proof_manager
        .as_ref()
        .expect("proof manager")
        .deleted_count();

    solver.factorize();

    assert_eq!(
        solver.factor_lrat_dry_run_sidecars().len(),
        1,
        "dry-run evidence remains available for diagnostics without authorizing mutation"
    );
    let preflight_stats = solver.factor_lrat_preflight_stats();
    assert_eq!(
        preflight_stats.transaction_candidates,
        preflight_stats_before.transaction_candidates + 1
    );
    assert_eq!(
        preflight_stats.dry_run_emitted,
        preflight_stats_before.dry_run_emitted + 1
    );
    assert_eq!(
        preflight_stats.dry_run_rejected,
        preflight_stats_before.dry_run_rejected
    );
    assert_eq!(
        preflight_stats.checker_obligation_missing,
        preflight_stats_before.checker_obligation_missing + 1
    );
    assert_eq!(
        solver.num_vars, num_vars_before,
        "rejected LRAT factor preflight must not allocate an extension variable"
    );
    assert_eq!(
        solver.arena.active_clause_count(),
        active_before,
        "rejected LRAT factor preflight must not mutate clauses"
    );
    assert_eq!(
        solver.er_extension_definition_count(),
        er_defs_before,
        "rejected LRAT factor preflight must not retain reconstruction witnesses"
    );
    let factor_stats = solver.factor_stats();
    assert_eq!(factor_stats.rounds, factor_stats_before.rounds);
    assert_eq!(
        factor_stats.factored_count,
        factor_stats_before.factored_count
    );
    assert_eq!(
        factor_stats.extension_vars,
        factor_stats_before.extension_vars
    );
    assert_eq!(
        solver
            .proof_manager
            .as_ref()
            .expect("proof manager")
            .added_count(),
        proof_added_before,
        "rejected LRAT factor transaction must not emit additions"
    );
    assert_eq!(
        solver
            .proof_manager
            .as_ref()
            .expect("proof manager")
            .deleted_count(),
        proof_deleted_before,
        "rejected LRAT factor transaction must not emit deletions"
    );
}

#[test]
fn test_factor_lrat_dry_run_sidecar_replays_with_external_checker_fixture() {
    use crate::proof::ProofOutput;

    let pos = |i: u32| Literal::positive(Variable(i));
    let neg = |i: u32| Literal::negative(Variable(i));
    let mut clauses = ternary_factor_matrix();
    clauses.push(vec![pos(6)]);
    clauses.push(vec![neg(6)]);

    let mut solver =
        Solver::with_proof_output(7, ProofOutput::lrat_text(Vec::new(), clauses.len() as u64));
    for clause in &clauses {
        assert!(solver.add_clause(clause.clone()));
    }

    solver.factorize();

    let sidecars = solver.factor_lrat_dry_run_sidecars();
    assert_eq!(sidecars.len(), 1);
    assert_eq!(
        solver
            .factor_lrat_preflight_stats()
            .checker_obligation_missing,
        1,
        "live route rejects the sidecar's zero-hint divider additions"
    );
    assert_eq!(
        solver.num_vars, 7,
        "diagnostic replay must not authorize live extension-variable mutation"
    );

    let sidecar = &sidecars[0];
    let factor_count = sidecar.factors.len();
    assert_eq!(factor_count, 2);
    let proof = render_factor_lrat_dry_run_replay(sidecar, &[7, 8]);
    let dimacs = render_dimacs_fixture(7, &clauses);
    verify_lrat_fixture(&dimacs, &proof);
}

#[test]
fn test_factor_lrat_dry_run_sidecar_persists_export_artifacts_for_checker() {
    use crate::proof::ProofOutput;

    let pos = |i: u32| Literal::positive(Variable(i));
    let neg = |i: u32| Literal::negative(Variable(i));
    let mut clauses = ternary_factor_matrix();
    clauses.push(vec![pos(6)]);
    clauses.push(vec![neg(6)]);

    let mut solver =
        Solver::with_proof_output(7, ProofOutput::lrat_text(Vec::new(), clauses.len() as u64));
    for clause in &clauses {
        assert!(solver.add_clause(clause.clone()));
    }

    solver.factorize();

    let sidecars = solver.factor_lrat_dry_run_sidecars();
    assert_eq!(sidecars.len(), 1);
    assert_eq!(
        solver
            .factor_lrat_preflight_stats()
            .checker_obligation_missing,
        1,
        "persisted dry-run records the checker-obligation rejection"
    );
    assert_eq!(
        solver.num_vars, 7,
        "persisting diagnostics must not apply the extension-variable mutation"
    );

    let sidecar = &sidecars[0];
    let dimacs = render_dimacs_fixture(7, &clauses);
    let proof = render_factor_lrat_dry_run_replay(sidecar, &[7, 8]);
    verify_lrat_fixture(&dimacs, &proof);

    let artifact_dir = repo_root_for_factor_artifacts().join("target/9285");
    std::fs::create_dir_all(&artifact_dir).expect("create factor sidecar artifact dir");
    let cnf_path = artifact_dir.join("minimal-factor-unsat-core.cnf");
    let lrat_path = artifact_dir.join("factor-dry-run-with-unsat-core.lrat");
    let sidecar_path = artifact_dir.join("factor-dry-run-sidecar.json");
    std::fs::write(&cnf_path, dimacs).expect("write factor dry-run source CNF");
    std::fs::write(&lrat_path, proof).expect("write factor dry-run LRAT replay");

    let cnf_uri = cnf_path.display().to_string();
    let lrat_uri = lrat_path.display().to_string();
    let sidecar_uri = sidecar_path.display().to_string();
    let producer_revision = producer_revision_for_factor_artifact();
    let export = crate::factor::FactorLratDryRunExport {
        source_dimacs_uri: &cnf_uri,
        lrat_proof_uri: &lrat_uri,
        transform_transaction_uri: &sidecar_uri,
        benchmark_id: "minimal_factor_unsat_core",
        family: "factor-lrat-dry-run-fixture",
        num_vars: 7,
        num_clauses: clauses.len() as u64,
        producer_revision: Some(&producer_revision),
    };
    let sidecar_json = sidecar.to_factor_extension_lrat_dry_run_json(&export);
    std::fs::write(
        &sidecar_path,
        format!(
            "{}\n",
            serde_json::to_string_pretty(&sidecar_json).expect("serialize factor sidecar JSON")
        ),
    )
    .expect("write factor dry-run JSON sidecar");

    let persisted: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(&sidecar_path).expect("read factor dry-run JSON sidecar"),
    )
    .expect("parse persisted factor dry-run JSON sidecar");
    assert_eq!(persisted["source_dimacs_uri"], serde_json::json!(cnf_uri));
    assert_eq!(persisted["lrat_proof_uri"], serde_json::json!(lrat_uri));
    assert_eq!(
        persisted["transform_transaction_uri"],
        serde_json::json!(sidecar_uri)
    );
    assert_eq!(persisted["fresh_lit"], serde_json::json!(sidecar.fresh_lit));
    assert_eq!(persisted["factors"], serde_json::json!(sidecar.factors));
    assert_eq!(
        persisted["quotient_clauses"],
        serde_json::json!(sidecar.quotient_clauses)
    );
    assert_eq!(
        persisted["planned_add_ids"],
        serde_json::json!(sidecar.planned_add_ids)
    );
    assert_eq!(
        persisted["source_clause_ids_quotient_major"],
        serde_json::json!(sidecar.source_clause_ids_quotient_major)
    );
    assert_eq!(
        persisted["source_clause_lits_quotient_major"],
        serde_json::json!(sidecar.source_clause_lits_quotient_major)
    );
    assert_eq!(
        persisted["source_delete_ids_quotient_major"],
        serde_json::json!(sidecar.source_delete_ids_quotient_major)
    );
    assert_eq!(
        persisted["producer_revision"],
        serde_json::json!(producer_revision)
    );

    eprintln!("factor_dry_run_source_cnf={}", cnf_path.display());
    eprintln!("factor_dry_run_lrat={}", lrat_path.display());
    eprintln!("factor_dry_run_sidecar_json={}", sidecar_path.display());
}

#[test]
fn test_factor_lrat_transaction_artifact_persists_signed_checker_obligations() {
    use crate::proof::ProofOutput;

    let pos = |i: u32| Literal::positive(Variable(i));
    let neg = |i: u32| Literal::negative(Variable(i));
    let mut clauses = ternary_factor_matrix();
    clauses.push(vec![pos(6)]);
    clauses.push(vec![neg(6)]);

    let mut solver =
        Solver::with_proof_output(7, ProofOutput::lrat_text(Vec::new(), clauses.len() as u64));
    for clause in &clauses {
        assert!(solver.add_clause(clause.clone()));
    }

    solver.factorize();

    let sidecars = solver.factor_lrat_dry_run_sidecars();
    assert_eq!(sidecars.len(), 1);
    assert_eq!(
        solver
            .factor_lrat_preflight_stats()
            .checker_obligation_missing,
        1,
        "transaction artifact remains diagnostic after the live gate rejects it"
    );
    assert_eq!(
        solver.num_vars, 7,
        "transaction artifact export must not mutate the live solver"
    );

    let sidecar = &sidecars[0];
    assert!(
        sidecar.has_checker_visible_transaction_contract(),
        "sidecar must retain signed LRAT/RAT obligations before export"
    );
    let dimacs = render_dimacs_fixture(7, &clauses);
    let proof = render_factor_lrat_dry_run_replay(sidecar, &[7, 8]);
    verify_lrat_fixture(&dimacs, &proof);

    let artifact_dir = repo_root_for_factor_artifacts().join("target/9108");
    std::fs::create_dir_all(&artifact_dir).expect("create factor transaction artifact dir");
    let cnf_path = artifact_dir.join("minimal-factor-unsat-core.cnf");
    let lrat_path = artifact_dir.join("factor-transaction-with-unsat-core.lrat");
    let transaction_path = artifact_dir.join("factor-lrat-transaction.json");
    std::fs::write(&cnf_path, dimacs).expect("write factor transaction source CNF");
    std::fs::write(&lrat_path, proof).expect("write factor transaction LRAT replay");

    let cnf_uri = cnf_path.display().to_string();
    let lrat_uri = lrat_path.display().to_string();
    let transaction_uri = transaction_path.display().to_string();
    let producer_revision = producer_revision_for_factor_artifact();
    let export = crate::factor::FactorLratDryRunExport {
        source_dimacs_uri: &cnf_uri,
        lrat_proof_uri: &lrat_uri,
        transform_transaction_uri: &transaction_uri,
        benchmark_id: "minimal_factor_signed_transaction",
        family: "factor-lrat-transaction-fixture",
        num_vars: 7,
        num_clauses: clauses.len() as u64,
        producer_revision: Some(&producer_revision),
    };
    let transaction_json = sidecar
        .to_factor_extension_lrat_transaction_json(&export)
        .expect("signed transaction export must be checker-visible");
    std::fs::write(
        &transaction_path,
        format!(
            "{}\n",
            serde_json::to_string_pretty(&transaction_json)
                .expect("serialize factor transaction JSON")
        ),
    )
    .expect("write factor transaction JSON sidecar");

    let persisted: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(&transaction_path).expect("read factor transaction JSON"),
    )
    .expect("parse persisted factor transaction JSON");
    assert_eq!(persisted["source_dimacs_uri"], serde_json::json!(cnf_uri));
    assert_eq!(persisted["lrat_proof_uri"], serde_json::json!(lrat_uri));
    assert_eq!(
        persisted["transform_transaction_uri"],
        serde_json::json!(transaction_uri)
    );
    assert_eq!(persisted["fresh_lit"], serde_json::json!(8));
    // Pin update (live-score schedule, CaDiCaL `factor_occs_size` tie
    // order): tied first-factor candidates pop in DESCENDING literal order,
    // so the tied pair applies as [2, 1]. Identical matrix; factor-minor
    // order swaps in the ids/hints below.
    assert_eq!(persisted["factors"], serde_json::json!([2, 1]));
    assert_eq!(
        persisted["quotient_tails"],
        serde_json::json!([[3, 4], [3, 5], [4, 5]])
    );
    assert_eq!(
        persisted["source_clause_ids_quotient_major"],
        serde_json::json!([2, 1, 4, 3, 6, 5])
    );
    assert_eq!(persisted["divider_clause_ids"], serde_json::json!([9, 10]));
    assert_eq!(persisted["divider_rat_pivots"], serde_json::json!([8, 8]));
    assert_eq!(persisted["blocked_clause_id"], serde_json::json!(11));
    assert_eq!(
        persisted["blocked_signed_lrat_hints"],
        serde_json::json!([-9, -10])
    );
    assert_eq!(
        persisted["quotient_clause_ids"],
        serde_json::json!([12, 13, 14])
    );
    assert_eq!(
        persisted["quotient_lrat_hints"],
        serde_json::json!([[2, 1, 11], [4, 3, 11], [6, 5, 11]])
    );
    assert_eq!(persisted["proof_only_delete_id"], serde_json::json!(11));
    assert_eq!(
        persisted["source_delete_ids"],
        serde_json::json!([2, 1, 4, 3, 6, 5])
    );
    assert_eq!(
        persisted["producer_revision"],
        serde_json::json!(producer_revision)
    );
    assert!(
        persisted.get("planned_add_ids").is_none() && persisted.get("quotient_clauses").is_none(),
        "transaction export must carry the signed checker contract, not only the replay dry-run"
    );

    eprintln!("factor_transaction_source_cnf={}", cnf_path.display());
    eprintln!("factor_transaction_lrat={}", lrat_path.display());
    eprintln!("factor_transaction_json={}", transaction_path.display());
}

#[test]
fn test_factor_lrat_rejected_live_output_still_checks_original_fixture() {
    use crate::proof::ProofOutput;

    let pos = |i: u32| Literal::positive(Variable(i));
    let neg = |i: u32| Literal::negative(Variable(i));
    let mut clauses = ternary_factor_matrix();
    clauses.push(vec![pos(6)]);
    clauses.push(vec![neg(6)]);

    let mut solver =
        Solver::with_proof_output(7, ProofOutput::lrat_text(Vec::new(), clauses.len() as u64));
    for clause in &clauses {
        assert!(solver.add_clause(clause.clone()));
    }

    solver.factorize();
    assert_eq!(
        solver.factor_stats().factored_count,
        0,
        "fixture must reject the live factor LRAT transaction"
    );
    assert_eq!(solver.factor_lrat_dry_run_sidecars().len(), 1);
    assert!(
        solver.solve().into_inner().is_unsat(),
        "contradictory units should finish the live LRAT proof"
    );

    let dimacs = render_dimacs_fixture(7, &clauses);
    let proof = String::from_utf8(
        solver
            .take_proof_writer()
            .expect("proof writer")
            .into_vec()
            .expect("flush live factor proof"),
    )
    .expect("UTF-8");
    assert!(
        !proof.contains("11 -8 -2 -1 0 -9 -10 0"),
        "diagnostic factor transaction must not leak into live proof output: {proof}"
    );
    verify_lrat_fixture(&dimacs, &proof);

    let artifact_dir = repo_root_for_factor_artifacts().join("target/9305");
    std::fs::create_dir_all(&artifact_dir).expect("create factor live artifact dir");
    let cnf_path = artifact_dir.join("minimal-factor-live.cnf");
    let lrat_path = artifact_dir.join("factor-live-proof.lrat");
    std::fs::write(&cnf_path, dimacs).expect("write live factor source CNF");
    std::fs::write(&lrat_path, proof).expect("write live factor LRAT proof");
    eprintln!("factor_live_source_cnf={}", cnf_path.display());
    eprintln!("factor_live_lrat={}", lrat_path.display());
}

#[test]
fn test_factor_lrat_rejection_preserves_original_dimacs_sat_model() {
    use crate::proof::ProofOutput;

    let clauses = ternary_factor_matrix();
    let mut solver =
        Solver::with_proof_output(5, ProofOutput::lrat_text(Vec::new(), clauses.len() as u64));
    for clause in &clauses {
        assert!(solver.add_clause(clause.clone()));
    }

    solver.factorize();
    assert_eq!(
        solver.factor_stats().factored_count,
        0,
        "SAT fixture must reject unproved factor before solving"
    );
    assert_eq!(solver.num_vars, 5);

    match solver.solve().into_inner() {
        SatResult::Sat(model) => {
            assert_eq!(
                solver.verify_against_original(&model),
                None,
                "factor SAT model must satisfy the original DIMACS ledger"
            );
            for clause in &clauses {
                assert!(
                    clause.iter().any(|lit| {
                        let vi = lit.variable().index();
                        vi < model.len() && model[vi] == lit.is_positive()
                    }),
                    "returned SAT model must satisfy original clause {:?}",
                    clause.iter().map(|lit| lit.to_dimacs()).collect::<Vec<_>>()
                );
            }
        }
        other => panic!("expected SAT after rejected factor transaction, got {other:?}"),
    }
}

#[test]
fn test_factor_lrat_dry_run_slices_multiple_applications() {
    use crate::proof::ProofOutput;

    let pos = |i: u32| Literal::positive(Variable(i));
    let first_clauses = ternary_factor_matrix();
    let second_clauses = vec![
        vec![pos(5), pos(7), pos(8)],
        vec![pos(6), pos(7), pos(8)],
        vec![pos(5), pos(7), pos(9)],
        vec![pos(6), pos(7), pos(9)],
        vec![pos(5), pos(8), pos(9)],
        vec![pos(6), pos(8), pos(9)],
    ];
    let mut clauses = first_clauses;
    clauses.extend(second_clauses);

    let mut solver =
        Solver::with_proof_output(10, ProofOutput::lrat_text(Vec::new(), clauses.len() as u64));
    for clause in &clauses {
        assert!(solver.add_clause(clause.clone()));
    }
    let active_indices = solver.arena.active_indices().collect::<Vec<_>>();
    assert_eq!(active_indices.len(), 12);

    let app0 = factor_application(
        Variable(10),
        vec![pos(0), pos(1)],
        vec![
            vec![pos(2), pos(3)],
            vec![pos(2), pos(4)],
            vec![pos(3), pos(4)],
        ],
        active_indices[..6].to_vec(),
    );
    let app1 = factor_application(
        Variable(11),
        vec![pos(5), pos(6)],
        vec![
            vec![pos(7), pos(8)],
            vec![pos(7), pos(9)],
            vec![pos(8), pos(9)],
        ],
        active_indices[6..].to_vec(),
    );
    let mut result = FactorResult {
        to_delete: active_indices,
        extension_vars_needed: 2,
        factored_count: 2,
        applications: vec![app0, app1],
        ..FactorResult::default()
    };
    for app in &result.applications {
        result.new_clauses.extend(app.divider_clauses.clone());
        result.new_clauses.extend(app.quotient_clauses.clone());
    }

    let plan = solver
        .preflight_factor_lrat_transaction(&result)
        .expect("two planned factor applications should preflight");
    assert_eq!(plan.planned_add_ids, (13..=24).collect::<Vec<_>>());

    let sidecars = solver
        .factor_lrat_dry_run_obligations(&result, &plan)
        .expect("dry-run sidecars should slice the strict LRAT plan");
    assert_eq!(sidecars.len(), 2);
    assert_eq!(sidecars[0].planned_add_ids, vec![13, 14, 15, 16, 17, 18]);
    assert_eq!(sidecars[1].planned_add_ids, vec![19, 20, 21, 22, 23, 24]);
    assert_eq!(
        sidecars[0].source_clause_ids_quotient_major,
        vec![1, 2, 3, 4, 5, 6]
    );
    assert_eq!(
        sidecars[1].source_clause_ids_quotient_major,
        vec![7, 8, 9, 10, 11, 12]
    );
    assert_eq!(sidecars[0].fresh_lit, 11);
    assert_eq!(sidecars[1].fresh_lit, 12);
}

#[test]
fn test_factor_lrat_dry_run_fails_closed_on_self_subsuming_factor() {
    let solver = Solver::new(2);
    let result = FactorResult {
        factored_count: 1,
        self_subsuming: vec![crate::factor::SelfSubsumingApplication {
            resolvents: vec![vec![Literal::positive(Variable(0))]],
            to_delete: vec![0, 1],
            proof_pairs: vec![(0, 1)],
        }],
        ..FactorResult::default()
    };
    let plan = FactorLratTransactionPlan {
        planned_add_ids: Vec::new(),
        live_add_ids: Vec::new(),
        source_delete_ids: Vec::new(),
        proof_only_delete_ids: Vec::new(),
    };

    assert_eq!(
        solver.factor_lrat_dry_run_obligations(&result, &plan),
        Err(FactorLratTransactionReject::SelfSubsumingUnsupported),
        "self-subsuming factor results need a separate checker-visible LRAT contract"
    );
}
