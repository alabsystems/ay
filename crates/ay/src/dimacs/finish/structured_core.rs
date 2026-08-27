// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

fn insert_dimacs_structured_solver_core(
    solver: &mut SatSolver,
    proof: Option<&ProofConfig>,
    proof_writer_telemetry: Option<DimacsProofWriterTelemetry>,
    stats: &mut stats_output::RunStatistics,
) {
    let (mli_detected, mli_reimplied, mli_used) = solver.mli_stats();
    stats.insert("conflicts", solver.num_conflicts());
    stats.insert("decisions", solver.num_decisions());
    stats.insert("propagations", solver.num_propagations());
    stats.insert("search_propagations", solver.num_search_propagations());
    stats.insert("restarts", solver.num_restarts());
    stats.insert("sat.cold_restarts", solver.num_cold_restarts());
    stats.insert("sat.chrono_bt", solver.num_chrono_backtracks());
    stats.insert(
        "sat.approx_bcp_noop_matched",
        solver.approx_bcp_noop_matched(),
    );
    stats.insert(
        "sat.approx_bcp_conflict_matched",
        solver.approx_bcp_conflict_matched(),
    );
    stats.insert(
        "sat.approx_bcp_mismatch_detected",
        solver.approx_bcp_mismatch_detected(),
    );
    stats.insert("sat.forced_bt", solver.num_forced_backtracks());
    stats.insert("sat.mli_detected", mli_detected);
    stats.insert("sat.mli_reimplied", mli_reimplied);
    stats.insert("sat.mli_used_in_analysis", mli_used);
    stats.insert("sat.random_decisions", solver.num_random_decisions());
    stats.insert("sat.fixed_vars", solver.num_fixed() as u64);
    stats.insert("sat.original_clauses", solver.num_original_clauses() as u64);
    stats.insert("sat.learned_clauses", solver.num_learned_clauses());
    insert_dimacs_proof_telemetry(stats, solver, proof, proof_writer_telemetry);
    insert_preprocessing_transaction_telemetry(stats, solver.preprocessing_transaction_stats());
}

fn insert_guard_cover_structured_stats(
    sidecar: Option<&GuardCoverSidecarRunStats>,
    stats: &mut stats_output::RunStatistics,
) {
    stats.insert(
        "sat.guard_cover_sidecar_checked",
        u64::from(sidecar.is_some()),
    );
    stats.insert(
        "sat.guard_cover_sidecar_accepted",
        u64::from(sidecar.is_some_and(|value| value.accepted)),
    );
    stats.insert(
        "sat.guard_cover_sidecar_empty_cut",
        u64::from(sidecar.is_some_and(|value| value.injected_empty_cut)),
    );
    stats.insert(
        "sat.guard_cover_sidecar_cuts",
        sidecar.map_or(0, |value| value.cuts),
    );
    stats.insert(
        "sat.guard_cover_sidecar_guards",
        sidecar.map_or(0, |value| value.guards),
    );
    stats.insert(
        "sat.guard_cover_sidecar_budget_rhs",
        sidecar.map_or(0, |value| value.budget_rhs),
    );
    stats.insert(
        "sat.guard_cover_sidecar_packed_deficit",
        sidecar.map_or(0, |value| value.packed_deficit),
    );
}

fn insert_separator_cover_structured_stats(
    sidecar: Option<&SeparatorCoverSidecarRunStats>,
    stats: &mut stats_output::RunStatistics,
) {
    stats.insert(
        "sat.separator_cover_sidecar_checked",
        sidecar.is_some() as u64,
    );
    stats.insert(
        "sat.separator_cover_sidecar_accepted",
        sidecar.is_some_and(|value| value.accepted) as u64,
    );
    stats.insert(
        "sat.separator_cover_sidecar_empty_cut",
        sidecar.is_some_and(|value| value.injected_empty_cut) as u64,
    );
    stats.insert(
        "sat.separator_cover_sidecar_separator_vars",
        sidecar.map_or(0, |value| value.separator_vars),
    );
    stats.insert(
        "sat.separator_cover_sidecar_cubes",
        sidecar.map_or(0, |value| value.cubes),
    );
    stats.insert(
        "sat.separator_cover_sidecar_covered_assignments",
        sidecar.map_or(0, |value| value.covered_assignments),
    );
}

fn insert_structural_sidecar_totals(
    guard: Option<&GuardCoverSidecarRunStats>,
    separator: Option<&SeparatorCoverSidecarRunStats>,
    stats: &mut stats_output::RunStatistics,
) {
    stats.insert(
        "sat.structural_sidecar_checked_count",
        guard.is_some() as u64 + separator.is_some() as u64,
    );
    stats.insert(
        "sat.structural_sidecar_accepted_count",
        guard.is_some_and(|value| value.accepted) as u64
            + separator.is_some_and(|value| value.accepted) as u64,
    );
    stats.insert(
        "sat.structural_sidecar_empty_cut_count",
        guard.is_some_and(|value| value.injected_empty_cut) as u64
            + separator.is_some_and(|value| value.injected_empty_cut) as u64,
    );
}

fn insert_dimacs_structured_timing(solver: &SatSolver, stats: &mut stats_output::RunStatistics) {
    let props = solver.num_propagations();
    let confs = solver.num_conflicts();
    let decs = solver.num_decisions();
    let preprocess_ns = solver.preprocess_time_ns();
    let search_ns = solver.search_time_ns();
    let lucky_ns = solver.lucky_time_ns();
    let walk_ns = solver.walk_time_ns();
    let total_ns = preprocess_ns + search_ns + lucky_ns + walk_ns;
    let inproc_ns: u64 = solver
        .inprocessing_pass_times_ns()
        .iter()
        .map(|&(_, v)| v)
        .sum();
    stats.insert("sat.preprocess_ms", preprocess_ns / 1_000_000);
    stats.insert("sat.search_ms", search_ns / 1_000_000);
    stats.insert("sat.lucky_ms", lucky_ns / 1_000_000);
    stats.insert("sat.walk_ms", walk_ns / 1_000_000);
    // `sat.walk_ms` is the STARTUP walk only; the in-search rephase walk is
    // reported separately so a zero there cannot be read as "walk never ran".
    let (rw_runs, rw_skips, rw_ns) = solver.rephase_walk_report();
    stats.insert("sat.rephase_walks", rw_runs);
    stats.insert("sat.rephase_walk_gated", rw_skips);
    stats.insert("sat.rephase_walk_ms", rw_ns / 1_000_000);
    stats.insert("sat.inprocessing_ms", inproc_ns / 1_000_000);
    if let Some(value) = (preprocess_ns * 10000).checked_div(total_ns) {
        stats.insert("sat.preprocess_pct_x100", value);
    }
    if let Some(value) = (search_ns * 10000).checked_div(total_ns) {
        stats.insert("sat.search_pct_x100", value);
    }
    if let Some(value) = (inproc_ns * 10000).checked_div(total_ns) {
        stats.insert("sat.inprocessing_pct_x100", value);
    }
    let search_secs = search_ns as f64 / 1_000_000_000.0;
    if search_secs > 0.001 {
        stats.insert("sat.props_per_sec", (props as f64 / search_secs) as u64);
        stats.insert("sat.conflicts_per_sec", (confs as f64 / search_secs) as u64);
    }
    if let Some(value) = (decs * 100).checked_div(confs) {
        stats.insert("sat.decs_per_conflict_x100", value);
    }
}

fn insert_dimacs_structured_lbd(solver: &SatSolver, stats: &mut stats_output::RunStatistics) {
    let (lbd_sum, lbd_count) = solver.lbd_sum_count();
    if let Some(value) = (lbd_sum * 100).checked_div(lbd_count) {
        stats.insert("sat.avg_lbd_x100", value);
    }
    let buckets = solver.lbd_buckets();
    stats.insert("sat.lbd_1", buckets[0]);
    stats.insert("sat.lbd_2", buckets[1]);
    stats.insert("sat.lbd_3to5", buckets[2]);
    stats.insert("sat.lbd_6to10", buckets[3]);
    stats.insert("sat.lbd_11plus", buckets[4]);
    stats.insert(
        "sat.peak_decision_level",
        u64::from(solver.peak_decision_level()),
    );
    stats.insert(
        "sat.avg_decision_level_x100",
        (solver.avg_decision_level() * 100.0) as u64,
    );
}

fn insert_dimacs_structured_restart_routes(
    solver: &SatSolver,
    stats: &mut stats_output::RunStatistics,
) {
    stats.insert(
        SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_REQUESTED_KEY,
        u64::from(ay_core::sat_ab_switches().dense_mutex_focused_restart_gate),
    );
    stats.insert(
        SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_ENABLED_KEY,
        u64::from(solver.dense_mutex_focused_restart_gate_experiment_enabled()),
    );
    stats.insert(
        SAT_FOCUSED_RESTART_GATE_FINAL_KEY,
        solver.focused_restart_gate(),
    );
    stats.insert(
        SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_UPDATES_KEY,
        solver.dense_mutex_focused_restart_gate_updates(),
    );
    stats.insert(
        SAT_DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CHECKED_KEY,
        solver.dense_mutex_focused_restart_runtime_checked(),
    );
    stats.insert(
        SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_VARS_KEY,
        solver.dense_mutex_focused_restart_active_vars(),
    );
    stats.insert(
        SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_CLAUSES_KEY,
        solver.dense_mutex_focused_restart_active_clauses(),
    );
    stats.insert(
        SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_BINARY_CLAUSES_KEY,
        solver.dense_mutex_focused_restart_active_binary_clauses(),
    );
    stats.insert(
        SAT_DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CANDIDATE_KEY,
        u64::from(solver.dense_mutex_focused_restart_runtime_candidate()),
    );
    stats.insert(
        SAT_DENSE_MUTEX_FOCUSED_RESTART_PREVIOUS_GATE_KEY,
        solver.dense_mutex_focused_restart_previous_gate(),
    );
    stats.insert(
        SAT_DENSE_MUTEX_FOCUSED_RESTART_COMPUTED_GATE_KEY,
        solver.dense_mutex_focused_restart_computed_gate(),
    );
    stats.insert(
        SAT_DENSE_CLIQUE_MAB_BRANCH_REQUESTED_KEY,
        u64::from(ay_core::sat_ab_switches().dense_clique_mab_branch),
    );
    stats.insert(
        SAT_DENSE_CLIQUE_MAB_BRANCH_ENABLED_KEY,
        u64::from(solver.dense_clique_mab_branch_route_enabled()),
    );
    stats.insert(
        SAT_DENSE_CLIQUE_MAB_BRANCH_EXERCISED_KEY,
        u64::from(solver.dense_clique_mab_branch_route_exercised()),
    );
    stats.insert(
        SAT_DENSE_CLIQUE_MAB_BRANCH_EXERCISE_COUNT_KEY,
        solver.dense_clique_mab_branch_route_exercise_count(),
    );
}

fn insert_dimacs_structured_core(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    insert_dimacs_structured_solver_core(
        context.solver,
        context.proof,
        context.proof_writer_telemetry,
        context.run_stats,
    );
    insert_guard_cover_structured_stats(context.guard_cover, context.run_stats);
    insert_separator_cover_structured_stats(context.separator_cover, context.run_stats);
    insert_structural_sidecar_totals(
        context.guard_cover,
        context.separator_cover,
        context.run_stats,
    );
    insert_dimacs_structured_timing(context.solver, context.run_stats);
    insert_dimacs_structured_lbd(context.solver, context.run_stats);
    insert_dimacs_structured_restart_routes(context.solver, context.run_stats);
    insert_dense_clique_scout_stats(context.run_stats, context.source);
    insert_multiplier_equiv_conservation_scout_stats(context.run_stats, context.source);
}
