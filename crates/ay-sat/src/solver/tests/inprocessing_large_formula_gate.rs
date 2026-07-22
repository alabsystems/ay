// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn hyper_unary_round_solver() -> (Solver, Variable) {
    let mut solver = Solver::new(2);
    let a = Variable(0);
    let b = Variable(1);
    let a_pos = Literal::positive(a);

    // (a v b) and (a v !b) let the inprocessing binary-dedup pass derive unit a.
    solver.add_clause_db(&[a_pos, Literal::positive(b)], false);
    solver.add_clause_db(&[a_pos, Literal::negative(b)], false);
    solver.initialize_watches();

    (solver, a)
}

fn subsume_due_solver(num_vars: usize) -> (Solver, usize) {
    let mut solver = Solver::new(num_vars);
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));

    solver.add_clause_db(&[a, b], false);
    let learned_off = solver.add_clause_db(&[a, b, c], true);
    solver.initialize_watches();
    solver.disable_all_inprocessing();
    solver.set_subsume_enabled(true);
    solver.cold.next_inprobe_conflict = 0;
    solver.num_conflicts = SUBSUME_INTERVAL;
    solver.inproc_ctrl.subsume.next_conflict = 0;

    (solver, learned_off)
}

fn subsume_noop_due_solver(num_vars: usize) -> Solver {
    let mut solver = Solver::new(num_vars);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
            Literal::positive(Variable(2)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::negative(Variable(1)),
            Literal::positive(Variable(3)),
        ],
        false,
    );
    solver.initialize_watches();
    solver.disable_all_inprocessing();
    solver.set_subsume_enabled(true);
    solver.cold.next_inprobe_conflict = 0;
    solver.num_conflicts = SUBSUME_INTERVAL;
    solver.inproc_ctrl.subsume.next_conflict = 0;

    solver
}

fn post_vivify_subsume_due_solver(num_vars: usize) -> Solver {
    let mut solver = Solver::new(num_vars);
    solver.initialize_watches();
    solver.disable_all_inprocessing();
    solver.set_vivify_enabled(true);
    solver.set_subsume_enabled(true);
    solver.cold.next_inprobe_conflict = 0;
    solver.num_conflicts = VIVIFY_INTERVAL;
    solver.inproc_ctrl.vivify.next_conflict = 0;
    solver.inproc_ctrl.vivify_irred.next_conflict = 0;
    solver.inproc_ctrl.subsume.next_conflict = u64::MAX;
    solver
}

fn subsume_accounting(solver: &Solver) -> (u64, u64, u64) {
    solver
        .inprocessing_pass_accounting()
        .into_iter()
        .find_map(|(label, accounting)| {
            (label == "inproc_subsume_ms").then_some((
                accounting.attempts,
                accounting.runs,
                accounting.yields,
            ))
        })
        .expect("subsumption accounting should be present")
}

#[test]
fn test_inprocessing_gates_pass_uses_base_interval_on_small_formulas() {
    let (mut solver, _) = hyper_unary_round_solver();

    // With next_inprobe_conflict=0 (default), any num_conflicts>0 passes.
    solver.num_conflicts = 500;
    assert!(
        solver.inprocessing_gates_pass(),
        "small formulas should pass inprocessing gate when conflicts >= limit",
    );
}

#[test]
fn test_inprocessing_gates_pass_respects_conflict_limit() {
    let (mut solver, _) = hyper_unary_round_solver();

    // Set a conflict limit — gate should block until reached.
    solver.cold.next_inprobe_conflict = 2000;
    solver.num_conflicts = 500;
    assert!(
        !solver.inprocessing_gates_pass(),
        "conflicts below next_inprobe_conflict should be blocked",
    );

    solver.num_conflicts = 1999;
    assert!(
        !solver.inprocessing_gates_pass(),
        "conflicts just below limit should be blocked",
    );

    solver.num_conflicts = 2000;
    assert!(
        solver.inprocessing_gates_pass(),
        "conflicts at limit should pass",
    );
}

#[test]
fn test_run_restart_inprocessing_respects_conflict_limit_on_large_formulas() {
    let (mut solver, a) = hyper_unary_round_solver();
    solver
        .arena
        .spoof_num_clauses_for_test(PREPROCESS_EXPENSIVE_MAX_CLAUSES + 1);

    // Simulate init_search_limits setting a high conflict limit.
    solver.cold.next_inprobe_conflict = 2000;

    solver.num_conflicts = 500;
    assert!(
        !solver.run_restart_inprocessing(),
        "500 conflicts should not enter inprocessing when limit is 2000",
    );
    assert_eq!(
        solver.get_var_assignment(a.index()),
        None,
        "the conflict limit should prevent binary dedup from firing at 500 conflicts",
    );

    solver.num_conflicts = 2000;
    assert!(
        !solver.run_restart_inprocessing(),
        "the inprocessing round should complete without deriving UNSAT",
    );
    assert_eq!(
        solver.get_var_assignment(a.index()),
        Some(true),
        "once the limit is reached, the inprocessing round should derive the hyper-unary unit",
    );
}

#[test]
fn test_subsume_large_var_gate_skips_spg_200_316_size() {
    let (mut solver, learned_off) = subsume_due_solver(365_895);

    assert!(
        !solver.run_restart_inprocessing(),
        "restart inprocessing should not derive UNSAT while skipping large-formula subsumption"
    );

    assert!(
        solver.arena.is_active(learned_off),
        "large-var subsumption gate should leave the learned clause untouched"
    );
    assert_eq!(
        subsume_accounting(&solver),
        (1, 0, 0),
        "subsumption should be considered but not entered on spg_200_316-sized formulas"
    );
    assert_eq!(
        solver.inproc_ctrl.subsume.next_conflict,
        SUBSUME_INTERVAL + SUBSUME_INTERVAL * 4,
        "skipped large-formula subsumption should use the large idle cooldown"
    );
}

#[test]
fn test_subsume_large_sparse_noop_uses_extended_cooldown() {
    let mut solver = subsume_noop_due_solver(25_000);
    solver
        .arena
        .spoof_active_clause_count_for_test(SUBSUME_LARGE_SPARSE_MIN_ACTIVE_CLAUSES);

    assert!(
        !solver.run_restart_inprocessing(),
        "restart inprocessing should not derive UNSAT on a no-op large sparse formula"
    );

    assert_eq!(
        subsume_accounting(&solver),
        (1, 1, 0),
        "no-op large sparse subsumption should run once before cooling down"
    );
    assert_eq!(
        solver.inproc_ctrl.subsume.next_conflict,
        SUBSUME_INTERVAL + SUBSUME_INTERVAL * 4,
        "no-op large sparse subsumption should use the extended idle cooldown"
    );
}

#[test]
fn test_subsume_large_active_clause_gate_skips_above_threshold() {
    let (mut solver, learned_off) = subsume_due_solver(54_411);
    solver
        .arena
        .spoof_active_clause_count_for_test(PREPROCESS_EXPENSIVE_MAX_CLAUSES + 1);

    assert!(
        !solver.run_restart_inprocessing(),
        "restart inprocessing should not derive UNSAT while skipping huge active-clause subsumption"
    );

    assert!(
        solver.arena.is_active(learned_off),
        "active-clause subsumption gate should leave the learned clause untouched"
    );
    assert_eq!(
        subsume_accounting(&solver),
        (1, 0, 0),
        "subsumption should be considered but not entered above the active-clause threshold"
    );
    assert!(
        solver.inproc_ctrl.subsume.next_conflict > solver.num_conflicts,
        "skipped huge active-clause subsumption should back off the interval"
    );
    assert_eq!(
        solver.inproc_ctrl.subsume.next_conflict,
        SUBSUME_INTERVAL + SUBSUME_INTERVAL * 4,
        "skipped huge active-clause subsumption should use the large idle cooldown"
    );
}

#[test]
fn test_subsume_large_var_gate_allows_fmla_equiv_chain_size() {
    let (mut solver, learned_off) = subsume_due_solver(54_411);

    assert!(
        !solver.run_restart_inprocessing(),
        "restart inprocessing should not derive UNSAT on the Fmla-sized fixture"
    );

    assert!(
        !solver.arena.is_active(learned_off),
        "FmlaEquivChain-sized formulas must keep ordinary subsumption enabled"
    );
    assert_eq!(
        subsume_accounting(&solver),
        (1, 1, 1),
        "ordinary subsumption should still run and yield below the large-var gate"
    );
}

#[test]
fn test_subsume_large_var_gate_allows_clique_n2_k10_size() {
    let (mut solver, learned_off) = subsume_due_solver(180);

    assert!(
        !solver.run_restart_inprocessing(),
        "restart inprocessing should not derive UNSAT on the clique-sized fixture"
    );

    assert!(
        !solver.arena.is_active(learned_off),
        "small dense clique-sized formulas must keep ordinary subsumption enabled"
    );
    assert_eq!(
        subsume_accounting(&solver),
        (1, 1, 1),
        "ordinary subsumption should still run and yield on small formulas"
    );
}

#[test]
fn test_post_vivify_subsume_large_var_gate_skips_spg_200_316_size() {
    let mut solver = post_vivify_subsume_due_solver(365_895);

    assert!(
        !solver.run_restart_inprocessing(),
        "post-vivify subsumption should not derive UNSAT on an empty large-var formula"
    );
    assert_eq!(
        subsume_accounting(&solver),
        (0, 0, 0),
        "large-var gate should suppress post-vivify subsumption"
    );
}

#[test]
fn test_post_vivify_subsume_large_sparse_honors_cooldown() {
    let mut solver = post_vivify_subsume_due_solver(25_000);
    solver
        .arena
        .spoof_active_clause_count_for_test(SUBSUME_LARGE_SPARSE_MIN_ACTIVE_CLAUSES);

    assert!(
        !solver.run_restart_inprocessing(),
        "post-vivify subsumption should not derive UNSAT on a large sparse formula"
    );
    assert_eq!(
        subsume_accounting(&solver),
        (0, 0, 0),
        "large sparse post-vivify subsumption should honor an active cooldown when vivify made no progress"
    );
}

#[test]
fn test_post_vivify_subsume_large_sparse_runs_when_due() {
    let mut solver = post_vivify_subsume_due_solver(25_000);
    solver
        .arena
        .spoof_active_clause_count_for_test(SUBSUME_LARGE_SPARSE_MIN_ACTIVE_CLAUSES);
    solver.inproc_ctrl.subsume.next_conflict = 0;

    assert!(
        !solver.run_restart_inprocessing(),
        "post-vivify subsumption should not derive UNSAT on a due large sparse formula"
    );
    assert_eq!(
        subsume_accounting(&solver),
        (1, 1, 0),
        "due large sparse post-vivify subsumption should still run"
    );
}

#[test]
fn test_post_vivify_subsume_large_var_gate_allows_fmla_equiv_chain_size() {
    let mut solver = post_vivify_subsume_due_solver(54_411);

    assert!(
        !solver.run_restart_inprocessing(),
        "post-vivify subsumption should not derive UNSAT on an empty medium formula"
    );
    assert_eq!(
        subsume_accounting(&solver),
        (1, 1, 0),
        "post-vivify subsumption should still enter below the large-var gate"
    );
}

#[test]
fn test_run_restart_inprocessing_allows_bve_above_former_large_clause_cap() {
    let mut solver = Solver::new(3);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);

    // x0 is a trivial BVE candidate: eliminating it replaces the pair with (x1 v x2).
    solver.add_clause_db(&[Literal::positive(x0), Literal::positive(x1)], false);
    solver.add_clause_db(&[Literal::negative(x0), Literal::positive(x2)], false);

    // Keep auxiliaries from being pure-eliminated before x0.
    solver.freeze(x1);
    solver.freeze(x2);

    solver.initialize_watches();
    solver.set_bve_enabled(true);
    solver.set_congruence_enabled(false);
    solver.set_decompose_enabled(false);
    solver.set_htr_enabled(false);
    solver.set_subsume_enabled(false);
    solver.set_probe_enabled(false);
    solver.set_backbone_enabled(false);
    solver.set_factor_enabled(false);
    solver.set_bce_enabled(false);
    solver.set_cce_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_transred_enabled(false);
    solver.set_sweep_enabled(false);
    solver.set_vivify_enabled(false);

    // Reproduce the old scheduler condition: active_clauses > 5_000_000.
    solver.arena.spoof_num_clauses_for_test(5_000_001);
    solver.cold.next_inprobe_conflict = 1;
    solver.num_conflicts = 1;

    assert!(
        !solver.run_restart_inprocessing(),
        "the inprocessing round should complete without deriving UNSAT",
    );
    assert_eq!(
        solver.bve_stats().vars_eliminated,
        1,
        "BVE should still run above the former 5M-clause inprocessing cap",
    );
    assert!(
        solver.inproc.bve.is_eliminated(x0),
        "x0 should be eliminated by inprocessing BVE",
    );
}
