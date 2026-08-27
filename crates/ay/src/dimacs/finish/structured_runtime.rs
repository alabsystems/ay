// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

fn insert_dimacs_runtime_core(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let solver = &*context.solver;
    let stats = &mut *context.run_stats;
    stats.insert("sat.dense_propagations", solver.dense_propagations());
    stats.insert("sat.dense_conflicts", solver.dense_conflicts());
    stats.insert(
        "sat.dense_satisfied_deleted",
        solver.dense_satisfied_deleted(),
    );
    stats.insert("sat.flush_dirty_lits", solver.flush_dirty_lits());
    stats.insert("sat.flush_watches_removed", solver.flush_watches_removed());
    stats.insert("sat.watches_shrunk", solver.watches_shrunk());
    stats.insert("sat.trail_rewind_skipped", solver.trail_rewind_skipped());
    stats.insert("sat.trail_rewind_partial", solver.trail_rewind_partial());
    stats.insert("sat.trail_rewind_full", solver.trail_rewind_full());
    stats.insert(
        "sat.trail_rewind_saved_entries",
        solver.trail_rewind_saved_entries(),
    );
}

fn insert_dimacs_competition_jit(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let solver = &*context.solver;
    let stats = &mut *context.run_stats;
    let learned_applications = solver.sat_learned_clause_candidate_applications();
    let native_applications = solver.sat_native_code_helper_applications();
    let guard_installs = solver.sat_whole_loop_guard_installs();
    let guard_applications = solver.sat_whole_loop_guard_applications();
    stats.insert(
        "sat_learned_clause_candidate_applications",
        learned_applications,
    );
    stats.insert("sat_native_code_helper_applications", native_applications);
    stats.insert(SAT_WHOLE_LOOP_GUARD_INSTALL_COUNTER, guard_installs);
    stats.insert(SAT_WHOLE_LOOP_GUARD_APPLICATION_COUNTER, guard_applications);
    let metadata = sat_native_helper_competition_jit_metadata();
    let application_count =
        if metadata.application_counter == SAT_WHOLE_LOOP_GUARD_APPLICATION_COUNTER {
            guard_applications
        } else {
            native_applications
        };
    stats.competition_jit = Some(sat_native_helper_competition_jit_evidence(
        &metadata,
        application_count,
    ));
    stats.insert(
        "sat.subsumption_native_applications",
        solver.sat_subsumption_native_applications(),
    );
    stats.insert(
        "sat.conflict_analysis_native_applications",
        solver.sat_conflict_analysis_native_applications(),
    );
}

fn insert_dimacs_code_cache_and_native(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let solver = &*context.solver;
    let stats = &mut *context.run_stats;
    stats.insert(
        "sat.code_cache_total_bytes",
        solver.code_cache_total_bytes() as u64,
    );
    stats.insert(
        "sat.code_cache_peak_bytes",
        solver.code_cache_peak_bytes() as u64,
    );
    stats.insert("sat.code_cache_evictions", solver.code_cache_evictions());
    stats.insert(
        "sat.code_cache_bytes_evicted",
        solver.code_cache_bytes_evicted(),
    );
    stats.insert(
        "sat.native_code_helpers_enabled",
        u64::from(solver.native_code_helpers_enabled()),
    );
    stats.insert(
        "sat.tier_controller_promotions",
        solver.tier_controller_promotions(),
    );
    stats.insert(
        "sat.propagation_native_active",
        u64::from(solver.sat_propagation_native_active()),
    );
    stats.insert(
        "sat.propagation_native_clauses",
        solver.sat_propagation_native_clauses(),
    );
    stats.insert(
        "sat.propagation_native_rounds",
        solver.sat_propagation_native_rounds(),
    );
    stats.insert(
        "sat.propagation_native_propagations",
        solver.sat_propagation_native_propagations(),
    );
    stats.insert(
        "sat.propagation_native_conflicts",
        solver.sat_propagation_native_conflicts(),
    );
    stats.insert(
        "sat.propagation_native_compile_time_us",
        solver.sat_propagation_native_compile_time_us(),
    );
    stats.insert("sat.arena_words", solver.arena_words() as u64);
    stats.insert("sat.arena_dead_words", solver.arena_dead_words() as u64);
    stats.insert("sat.arena_clause_slots", solver.arena_clause_slots() as u64);
    stats.insert("sat.active_clauses", solver.active_clause_count() as u64);
}

fn insert_dimacs_structured_runtime(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    insert_dimacs_runtime_core(context);
    insert_dimacs_competition_jit(context);
    insert_dimacs_code_cache_and_native(context);
}
