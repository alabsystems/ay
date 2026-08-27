// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

fn insert_dimacs_backbone_admission(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let solver = &*context.solver;
    let stats = &mut *context.run_stats;
    stats.insert("sat.backbone_binary_units", solver.backbone_binary_units());
    stats.insert(
        "sat.inprocessing_yield_productivity_rescue_enabled",
        u64::from(solver.inprocessing_yield_productivity_rescue_enabled()),
    );
    stats.insert(
        SAT_LRAT_PROOF_CLAMP_PROBE_RESCUE_ENABLED_KEY,
        u64::from(solver.lrat_proof_clamp_probe_rescue_enabled()),
    );
    let (bve_due, factor_due, probe_rescue) = solver.inprocessing_lrat_clamp_stats();
    stats.insert(SAT_INPROCESSING_LRAT_CLAMPED_BVE_DUE_ROUNDS_KEY, bve_due);
    stats.insert(
        SAT_INPROCESSING_LRAT_CLAMPED_FACTOR_DUE_ROUNDS_KEY,
        factor_due,
    );
    stats.insert(SAT_INPROCESSING_LRAT_PROBE_RESCUE_ROUNDS_KEY, probe_rescue);
    stats.insert(
        SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION_ENABLED_KEY,
        u64::from(solver.backbone_post_vivify_binary_admission_enabled()),
    );
}

fn insert_dimacs_backbone_rescue_schedule(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let schedule = context.solver.backbone_schedule_stats();
    let stats = &mut *context.run_stats;
    stats.insert(
        SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_ENABLED_KEY,
        u64::from(schedule.yield_rescue_cooldown_enabled),
    );
    stats.insert(
        SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_ROUNDS_KEY,
        schedule.yield_rescue_cooldown_rounds,
    );
    stats.insert(
        SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_INTERVAL_KEY,
        schedule.yield_rescue_cooldown_interval,
    );
    stats.insert(
        SAT_BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF_ENABLED_KEY,
        u64::from(schedule.bounded_zero_decompose_backoff_enabled),
    );
    stats.insert(
        SAT_BOUNDED_BACKBONE_BACKOFF_TRIGGERS_KEY,
        schedule.bounded_backoff_triggers,
    );
    stats.insert(SAT_BOUNDED_BACKBONE_RUNS_KEY, schedule.bounded_runs);
    stats.insert(SAT_BOUNDED_BACKBONE_YIELDS_KEY, schedule.bounded_yields);
    stats.insert(SAT_BOUNDED_BACKBONE_MS_KEY, schedule.bounded_ms);
    stats.insert(
        SAT_BOUNDED_BACKBONE_BINARY_SUPPRESSED_KEY,
        schedule.bounded_binary_suppressed,
    );
}

fn insert_dimacs_backbone_schedule(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let schedule = context.solver.backbone_schedule_stats();
    let stats = &mut *context.run_stats;
    stats.insert("sat.backbone_schedule_enabled", u64::from(schedule.enabled));
    stats.insert("sat.backbone_due", u64::from(schedule.due));
    stats.insert("sat.backbone_phases", u64::from(schedule.phases));
    stats.insert("sat.backbone_max_rounds", u64::from(schedule.max_rounds));
    stats.insert(
        "sat.backbone_consecutive_empty",
        u64::from(schedule.consecutive_empty),
    );
    stats.insert("sat.backbone_stall_limit", u64::from(schedule.stall_limit));
    stats.insert(
        "sat.backbone_stalled_by_empty",
        u64::from(schedule.stalled_by_empty),
    );
    stats.insert(
        "sat.backbone_rounds_exhausted",
        u64::from(schedule.rounds_exhausted),
    );
    stats.insert("sat.backbone_next_conflict", schedule.next_conflict);
    stats.insert(
        "sat.backbone_conflicts_until_next",
        schedule.conflicts_until_next,
    );
    stats.insert("sat.backbone_backoff_interval", schedule.backoff_interval);
    stats.insert("sat.backbone_base_interval", schedule.base_interval);
    stats.insert("sat.backbone_max_interval", schedule.max_interval);
}

fn insert_dimacs_backbone_misc(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let solver = &*context.solver;
    let stats = &mut *context.run_stats;
    stats.insert(
        "sat.occ_incremental_refreshes",
        solver.occ_incremental_refreshes(),
    );
    stats.insert("sat.occ_full_rebuilds", solver.occ_full_rebuilds());
    let (reductions, deleted, decays) = solver.between_solve_stats();
    stats.insert("sat.between_solve_reductions", reductions);
    stats.insert("sat.between_solve_clauses_deleted", deleted);
    stats.insert("sat.between_solve_used_decays", decays);
    let (domain_skips, domain_calls) = solver.domain_bcp_stats();
    stats.insert("sat.domain_bcp_skips", domain_skips);
    stats.insert("sat.domain_bcp_calls", domain_calls);
    stats.insert("sat.stale_enqueue_skips", solver.stale_enqueue_skips());
    stats.insert("sat.stale_bcp_watch_skips", solver.stale_bcp_watch_skips());
    stats.insert("sat.eager_subsumed", solver.num_eager_subsumptions());
    let (lookahead_rounds, failed_literals, decisions_used) = solver.lookahead_stats();
    stats.insert("sat.lookahead_rounds", lookahead_rounds);
    stats.insert("sat.lookahead_failed_literals", failed_literals);
    stats.insert("sat.lookahead_decisions_used", decisions_used);
    let search_secs = solver.search_time_ns() as f64 / 1_000_000_000.0;
    if search_secs > 0.001 {
        stats.insert(
            "sat.decisions_per_sec",
            (solver.num_decisions() as f64 / search_secs) as u64,
        );
    }
}

fn insert_dimacs_resource_stats(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let stats = &mut *context.run_stats;
    stats.insert(
        "resource.rss_peak_bytes",
        ay_sys::current_rss_bytes() as u64,
    );
    stats.insert(
        "resource.memory_limit_bytes",
        ay_sys::get_process_memory_limit() as u64,
    );
    stats.insert(
        "resource.term_bytes",
        ay_core::TermStore::global_term_bytes() as u64,
    );
    stats.insert("time.total_ms", global_elapsed().as_millis() as u64);
}

fn insert_dimacs_structured_backbone(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    insert_dimacs_backbone_admission(context);
    insert_dimacs_backbone_rescue_schedule(context);
    insert_dimacs_backbone_schedule(context);
    insert_dimacs_backbone_misc(context);
    insert_dimacs_resource_stats(context);
}
