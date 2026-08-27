// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

fn insert_dimacs_otfs_ibcl_and_fixpoint(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let solver = &*context.solver;
    let stats = &mut *context.run_stats;
    let (otfs_candidates, otfs_subsumed, otfs_strengthened) = solver.otfs_stats();
    stats.insert("sat.otfs_candidates", otfs_candidates);
    stats.insert("sat.otfs_subsumed", otfs_subsumed);
    stats.insert("sat.otfs_strengthened", otfs_strengthened);
    stats.insert("sat.otfs_branch_b", solver.otfs_branch_b());
    stats.insert("sat.otfs_branch_c", solver.otfs_branch_c());
    stats.insert("sat.otfs_clause_subsumed", solver.otfs_clause_subsumed());
    let (ibcl_attempts, ibcl_improvements, ibcl_skipped) = solver.ibcl_stats();
    stats.insert("sat.ibcl_attempts", ibcl_attempts);
    stats.insert("sat.ibcl_improvements", ibcl_improvements);
    stats.insert("sat.ibcl_skipped_short_chain", ibcl_skipped);
    stats.insert(
        "sat.ibcl_skipped_missing_pivots",
        solver.ibcl_skipped_missing_pivots(),
    );
    let (entries, iterations, max_depth, saturated) = solver.bcp_theory_fixpoint_stats();
    stats.insert("sat.bcp_theory_fixpoint_entries", entries);
    stats.insert("sat.bcp_theory_fixpoint_iterations", iterations);
    stats.insert("sat.bcp_theory_fixpoint_max_depth", u64::from(max_depth));
    stats.insert("sat.bcp_theory_fixpoint_saturated", saturated);
}

fn insert_dimacs_shrink_and_snapshot_stats(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let solver = &*context.solver;
    let stats = &mut *context.run_stats;
    let (
        singleton_skips,
        snapshot_copies,
        snapshot_literals,
        snapshot_singleton_skips,
        chain_calls,
    ) = solver.learned_lrat_snapshot_stats();
    stats.insert("sat.shrink_attempts", solver.shrink_block_attempts());
    stats.insert("sat.shrink_successes", solver.shrink_block_successes());
    stats.insert("sat.shrink_singleton_fast_path_skips", singleton_skips);
    stats.insert("sat.lrat_original_learned_snapshot_copies", snapshot_copies);
    stats.insert(
        "sat.lrat_original_learned_snapshot_literals",
        snapshot_literals,
    );
    stats.insert(
        "sat.lrat_original_learned_snapshot_singleton_skips",
        snapshot_singleton_skips,
    );
    stats.insert("sat.lrat_removed_literal_chain_calls", chain_calls);
}

fn insert_dimacs_mode_and_inprocessing_stats(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let solver = &*context.solver;
    let stats = &mut *context.run_stats;
    let (focused_decisions, stable_decisions) = solver.mode_decisions();
    let (_, focused_ema_fires) = solver.focused_ema_stats();
    stats.insert("sat.mode_switches", solver.mode_switch_count());
    stats.insert("sat.focused_ema_fires", focused_ema_fires);
    stats.insert(
        "sat.stable_reluctant_fires",
        solver.stable_reluctant_fires(),
    );
    stats.insert("sat.stable_ema_fires", solver.stable_ema_fires());
    stats.insert("sat.focused_decisions", focused_decisions);
    stats.insert("sat.stable_decisions", stable_decisions);
    stats.insert("sat.mab_switches", solver.mab_arm_switches());
    let search_ticks = solver.total_search_ticks();
    stats.insert("sat.search_ticks", search_ticks);
    // Per-mode ticks: the stabilization share the schedule actually budgets.
    let (focused_ticks, stable_ticks) = solver.mode_search_ticks();
    stats.insert("sat.search_ticks_focused", focused_ticks);
    stats.insert("sat.search_ticks_stable", stable_ticks);
    if let Some(value) = search_ticks.checked_div(solver.num_conflicts()) {
        stats.insert("sat.ticks_per_conflict", value);
    }
    stats.insert("sat.inproc_rounds", solver.inprocessing_rounds());
    stats.insert(
        "sat.incr_inproc_rounds",
        solver.incremental_inprocessing_rounds(),
    );
    stats.insert(
        "sat.inproc_simplifications",
        solver.inprocessing_simplifications(),
    );
    stats.insert("sat.rebuild_watches_us", solver.rebuild_watches_us());
    stats.insert("sat.rebuild_watches_calls", solver.rebuild_watches_calls());
    stats.insert(
        "sat.full_rebuild_watches_us",
        solver.full_rebuild_watches_us(),
    );
    stats.insert(
        "sat.full_rebuild_watches_calls",
        solver.full_rebuild_watches_calls(),
    );
    stats.insert(
        "sat.incremental_reconnect_watches_us",
        solver.incremental_reconnect_watches_us(),
    );
    stats.insert(
        "sat.incremental_reconnect_watches_calls",
        solver.incremental_reconnect_watches_calls(),
    );
}

fn insert_dimacs_rebuild_bcp_stats(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let solver = &*context.solver;
    let stats = &mut *context.run_stats;
    let (post_ns, post_props) = solver.post_rebuild_bcp_stats();
    stats.insert("sat.post_rebuild_bcp_ns", post_ns);
    stats.insert("sat.post_rebuild_bcp_propagations", post_props);
    if post_props > 0 && post_ns > 0 {
        stats.insert(
            "sat.post_rebuild_mpps_x1000",
            post_props * 1000 / post_ns.max(1),
        );
    }
    let (full_ns, full_props) = solver.post_full_rebuild_bcp_stats();
    stats.insert("sat.post_full_rebuild_bcp_ns", full_ns);
    stats.insert("sat.post_full_rebuild_bcp_propagations", full_props);
    if full_props > 0 && full_ns > 0 {
        stats.insert(
            "sat.post_full_rebuild_mpps_x1000",
            full_props * 1000 / full_ns.max(1),
        );
    }
    let (incremental_ns, incremental_props) = solver.post_incremental_reconnect_bcp_stats();
    stats.insert("sat.post_incr_reconnect_bcp_ns", incremental_ns);
    stats.insert(
        "sat.post_incr_reconnect_bcp_propagations",
        incremental_props,
    );
    if incremental_props > 0 && incremental_ns > 0 {
        stats.insert(
            "sat.post_incr_reconnect_mpps_x1000",
            incremental_props * 1000 / incremental_ns.max(1),
        );
    }
    let props = solver.num_propagations();
    let search_ns = solver.search_time_ns();
    if props > 0 && search_ns > 0 {
        stats.insert("sat.overall_mpps_x1000", props * 1000 / search_ns.max(1));
    }
}

fn insert_dimacs_reduction_core(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let solver = &*context.solver;
    let stats = &mut *context.run_stats;
    let (occ_scans, full_scans, no_occ_skips, satisfied_deleted) =
        solver.reduction_l0_satisfied_prepass_stats();
    stats.insert("sat.reductions", solver.num_reductions());
    stats.insert("sat.flushes", solver.num_flushes());
    stats.insert("sat.arena_compactions", solver.num_arena_compactions());
    stats.insert("sat.reduction_l0_satisfied_occ_scans", occ_scans);
    stats.insert("sat.reduction_l0_satisfied_full_scans", full_scans);
    stats.insert("sat.reduction_l0_satisfied_no_occ_skips", no_occ_skips);
    stats.insert("sat.reduction_l0_satisfied_deleted", satisfied_deleted);
}

fn insert_dimacs_learned_reduction_stats(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let (
        considered,
        deleted,
        reason_protected,
        ic3_protected,
        low_lbd_protected,
        usage_protected,
        target_kept,
        lrat_retained_delete_skips,
        hyper_deleted,
        hyper_kept,
    ) = context.solver.learned_reduction_telemetry_stats();
    let stats = &mut *context.run_stats;
    stats.insert("sat.learned_reduction_considered", considered);
    stats.insert("sat.learned_reduction_deleted", deleted);
    stats.insert("sat.learned_reduction_reason_protected", reason_protected);
    stats.insert("sat.learned_reduction_ic3_protected", ic3_protected);
    stats.insert("sat.learned_reduction_low_lbd_protected", low_lbd_protected);
    stats.insert("sat.learned_reduction_usage_protected", usage_protected);
    stats.insert("sat.learned_reduction_target_kept", target_kept);
    stats.insert(
        "sat.learned_reduction_lrat_retained_delete_skips",
        lrat_retained_delete_skips,
    );
    stats.insert("sat.learned_reduction_hyper_deleted", hyper_deleted);
    stats.insert("sat.learned_reduction_hyper_kept", hyper_kept);
    insert_dimacs_two_stage_clause_management_stats(context);
}

/// Two-stage clause management telemetry (arXiv:2602.20829).
///
/// Emitted unconditionally so the key shape is stable, but only the two-stage
/// code paths can make any of these non-zero. `sat.two_stage_enabled` plus a
/// zero `sat.two_stage_reduce_rounds` is the signature of a flag that was
/// accepted and never reached.
fn insert_dimacs_two_stage_clause_management_stats(
    context: &mut DimacsStructuredStatistics<'_, '_, '_>,
) {
    let two_stage = context.solver.two_stage_clause_management_stats();
    let stats = &mut *context.run_stats;
    stats.insert("sat.two_stage_enabled", u64::from(two_stage.enabled));
    stats.insert("sat.two_stage_learned_inits", two_stage.learned_inits);
    stats.insert("sat.two_stage_bcp_bumps", two_stage.bcp_bumps);
    stats.insert("sat.two_stage_analysis_bumps", two_stage.analysis_bumps);
    stats.insert(
        "sat.two_stage_score_saturations",
        two_stage.score_saturations,
    );
    stats.insert("sat.two_stage_decay_rounds", two_stage.decay_rounds);
    stats.insert("sat.two_stage_decay_clauses", two_stage.decay_clauses);
    stats.insert("sat.two_stage_reduce_rounds", two_stage.reduce_rounds);
    stats.insert("sat.two_stage_stage1_kept", two_stage.stage1_kept);
    stats.insert(
        "sat.two_stage_stage2_candidates",
        two_stage.stage2_candidates,
    );
    stats.insert("sat.two_stage_stage2_deleted", two_stage.stage2_deleted);
    stats.insert("sat.two_stage_flushes_absorbed", two_stage.flushes_absorbed);
    stats.insert("sat.two_stage_score_total", two_stage.score_total);
    stats.insert("sat.two_stage_score_max", two_stage.score_max);
    for (bucket, label) in ["0", "1", "2_3", "4_7", "8_15", "16_31", "32_255", "256_up"]
        .iter()
        .enumerate()
    {
        stats.insert(
            &format!("sat.two_stage_score_hist_{label}"),
            two_stage.score_histogram[bucket],
        );
    }
}

fn insert_dimacs_inprocessing_accounting(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let solver = &*context.solver;
    let stats = &mut *context.run_stats;
    for (label, value) in solver.inprocessing_pass_times_ms() {
        stats.insert(&format!("sat.{label}"), value);
    }
    for (label, accounting) in solver.inprocessing_pass_accounting() {
        let stem = match label.strip_suffix("_ms") {
            Some(value) => value,
            None => label,
        };
        stats.insert(&format!("sat.{stem}_attempts"), accounting.attempts);
        stats.insert(&format!("sat.{stem}_runs"), accounting.runs);
        stats.insert(&format!("sat.{stem}_yields"), accounting.yields);
    }
}

fn insert_dimacs_structured_search(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    insert_dimacs_otfs_ibcl_and_fixpoint(context);
    insert_dimacs_shrink_and_snapshot_stats(context);
    insert_dimacs_mode_and_inprocessing_stats(context);
    insert_dimacs_rebuild_bcp_stats(context);
    insert_dimacs_reduction_core(context);
    insert_dimacs_learned_reduction_stats(context);
    insert_dimacs_inprocessing_accounting(context);
}
