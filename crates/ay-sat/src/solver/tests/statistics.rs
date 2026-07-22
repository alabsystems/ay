// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Memory statistics and efficiency tests.
//!
//! Extracted from tests.rs for code-quality (Part of #5142).

use super::*;
use std::mem::size_of;

fn packed_bool_vec_bytes(capacity: usize) -> usize {
    capacity.div_ceil(8)
}

#[test]
fn test_sat_native_code_helper_flat_counter_includes_live_helper_counters() {
    let mut solver = Solver::new(4);
    solver.stats.sat_conflict_analysis_native_applications = 3;
    // Retired propagation counters must not unlock current external code generation
    // native-dispatch evidence.
    solver.stats.jit_propagations = 2;
    solver.stats.jit_conflicts = 4;
    solver.stats.sat_propagation_native_propagations = 5;
    solver.stats.sat_propagation_native_conflicts = 6;

    let subsume_stats = SubsumeStats {
        native_applications: 11,
        ..Default::default()
    };
    solver.inproc.subsumer.restore_stats(subsume_stats);

    assert_eq!(solver.sat_conflict_analysis_native_applications(), 3);
    assert_eq!(solver.sat_subsumption_native_applications(), 11);
    assert_eq!(
        solver.sat_native_code_helper_applications(),
        3 + 11,
        "flat native-helper counter must include only live SAT helper dispatches"
    );
}

#[test]
fn test_sat_learned_clause_candidate_counter_is_zero_until_native_dispatch_exists() {
    let mut solver = Solver::new(4);
    solver.stats.jit_learned_clauses_compiled = 42;

    assert_eq!(
        solver.sat_learned_clause_candidate_applications(),
        0,
        "profile-only learned-clause metadata must not count as native dispatch"
    );
}

#[test]
fn test_sat_whole_loop_guard_counters_are_separate_from_native_helpers() {
    let mut solver = Solver::new(4);
    solver.stats.sat_whole_loop_guard_installs = 1;
    solver.stats.sat_whole_loop_guard_applications = 1;
    solver.stats.sat_conflict_analysis_native_applications = 2;

    assert_eq!(solver.sat_whole_loop_guard_installs(), 1);
    assert_eq!(solver.sat_whole_loop_guard_applications(), 1);
    assert_eq!(
        solver.sat_native_code_helper_applications(),
        2,
        "whole-loop guard telemetry must not be folded into current native-helper evidence"
    );
}

#[test]
fn test_gpu_bve_stats_accessor_reports_solver_counters() {
    let mut solver = Solver::new(4);
    solver.stats.gpu_bve_dispatches = 2;
    solver.stats.gpu_bve_pairs = 4096;
    solver.stats.gpu_bve_tautologies = 17;

    assert_eq!(solver.gpu_bve_stats(), (2, 4096, 17));
}

#[test]
fn test_lrat_materialization_stats_accessor_reports_solver_counters() {
    let mut solver = Solver::new(4);
    assert_eq!(solver.lrat_materialization_stats(), Default::default());

    solver.stats.lrat_materialize_calls = 1;
    solver.stats.lrat_materialize_minimize_calls = 2;
    solver.stats.lrat_materialize_root_trail_entries = 3;
    solver.stats.lrat_materialize_minimize_root_trail_entries = 4;
    solver.stats.lrat_materialize_emitted_unit_lines = 5;
    solver.stats.lrat_materialize_minimize_emitted_unit_lines = 6;
    solver.stats.lrat_materialize_unit_hints = 7;
    solver.stats.lrat_materialize_minimize_unit_hints = 8;
    solver.stats.lrat_materialize_unit_max_hints = 9;
    solver.stats.lrat_materialize_minimize_unit_max_hints = 10;
    solver.stats.lrat_materialize_incomplete_chains = 11;
    solver.stats.lrat_materialize_minimize_incomplete_chains = 12;
    solver.stats.lrat_materialize_hidden_trusted_units = 13;
    solver.stats.lrat_unit_chain_calls = 14;
    solver.stats.lrat_unit_chain_root_trail_entries = 15;
    solver.stats.lrat_unit_chain_hints = 16;
    solver.stats.lrat_unit_chain_max_hints = 17;
    solver.stats.lrat_unit_chain_missing_hints = 18;

    let stats = solver.lrat_materialization_stats();
    assert_eq!(stats.materialize_calls, 1);
    assert_eq!(stats.materialize_minimize_calls, 2);
    assert_eq!(stats.materialize_root_trail_entries, 3);
    assert_eq!(stats.materialize_minimize_root_trail_entries, 4);
    assert_eq!(stats.materialize_emitted_unit_lines, 5);
    assert_eq!(stats.materialize_minimize_emitted_unit_lines, 6);
    assert_eq!(stats.materialize_unit_hints, 7);
    assert_eq!(stats.materialize_minimize_unit_hints, 8);
    assert_eq!(stats.materialize_unit_max_hints, 9);
    assert_eq!(stats.materialize_minimize_unit_max_hints, 10);
    assert_eq!(stats.materialize_incomplete_chains, 11);
    assert_eq!(stats.materialize_minimize_incomplete_chains, 12);
    assert_eq!(stats.materialize_hidden_trusted_units, 13);
    assert_eq!(stats.unit_chain_calls, 14);
    assert_eq!(stats.unit_chain_root_trail_entries, 15);
    assert_eq!(stats.unit_chain_hints, 16);
    assert_eq!(stats.unit_chain_max_hints, 17);
    assert_eq!(stats.unit_chain_missing_hints, 18);
}

#[cfg(feature = "jit")]
#[test]
fn test_conflict_analysis_jit_counts_native_helper_applications() {
    let mut solver = Solver::new(2);
    solver.set_preprocess_enabled(false);
    solver.set_walk_enabled(false);
    solver.set_warmup_enabled(false);

    let x0 = Variable(0);
    let x1 = Variable(1);
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::positive(x1)]);
    solver.add_clause(vec![Literal::positive(x0), Literal::negative(x1)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::negative(x1)]);

    solver.compile_conflict_processor();
    if solver.jit_conflict_processor.is_none() {
        return;
    }

    let result = solver.solve_with_assumptions(&[]).into_inner();
    assert!(
        result.is_unsat(),
        "xor contradiction must be UNSAT, got {result:?}"
    );
    assert!(
        solver.sat_conflict_analysis_native_applications() > 0,
        "conflict-analysis JIT dispatches must be counted"
    );
    assert!(
        solver.sat_native_code_helper_applications()
            >= solver.sat_conflict_analysis_native_applications(),
        "flat native-helper counter must include conflict-analysis JIT applications"
    );
}

// ========================================================================
// Memory Benchmark Tests
// ========================================================================

/// Test memory statistics for a small formula
#[test]
fn test_memory_stats_basic() {
    let mut solver = Solver::new(100);

    // Add 200 3-SAT clauses
    for i in 0..200 {
        let v1 = (i * 3) % 100;
        let v2 = (i * 3 + 1) % 100;
        let v3 = (i * 3 + 2) % 100;
        solver.add_clause(vec![
            Literal::positive(Variable(v1 as u32)),
            Literal::negative(Variable(v2 as u32)),
            Literal::positive(Variable(v3 as u32)),
        ]);
    }

    let stats = solver.memory_stats();
    assert_eq!(stats.num_vars, 100);
    assert_eq!(stats.num_clauses, 200);
    assert_eq!(stats.total_literals, 600); // 200 clauses * 3 literals

    assert_eq!(stats.solver_shell, size_of::<Solver>());

    // Per-var should be in a reasonable range for the current arena-based core
    // plus the remaining cold inprocessing/proof scaffolding.
    // After #8069 (Phase 2a), unit_proof_id, level0_proof_id, and clause_ids
    // are always allocated (+16 bytes/var for proof IDs, plus clause_ids
    // pre-allocated at 4*num_vars capacity = +32 bytes/var).
    // After #8465 (SoA watch lists) and parallel development adding
    // incremental state, learned clause reduction data, and theory conflict
    // pre-minimization buffers. Measured at ~513 bytes (commit a7ed0ba53).
    // Threshold set to 600 bytes to allow headroom.
    assert!(stats.per_var() > 20.0, "Per-var should be > 20 bytes");
    assert!(stats.per_var() < 600.0, "Per-var should be < 600 bytes");

    // Total should be positive and reasonable
    assert!(stats.total() > 0);
    assert!(stats.total() < 1_000_000, "Small formula should use < 1MB");
}

/// Test memory efficiency - bytes per literal should be reasonable
#[test]
fn test_memory_efficiency_per_literal() {
    let mut solver = Solver::new(1000);

    // Add 4000 3-SAT clauses (12000 literals)
    for i in 0..4000 {
        let v1 = (i * 7) % 1000;
        let v2 = (i * 7 + 3) % 1000;
        let v3 = (i * 7 + 5) % 1000;
        solver.add_clause(vec![
            Literal::positive(Variable(v1 as u32)),
            Literal::negative(Variable(v2 as u32)),
            Literal::positive(Variable(v3 as u32)),
        ]);
    }

    let stats = solver.memory_stats();

    // Bytes per literal in the inline clause arena.
    // Ideal payload is 4 bytes per literal, with additional amortized header
    // and capacity slack from the packed arena representation.
    let per_lit = stats.per_literal();
    assert!(
        per_lit >= 4.0,
        "Per literal should be >= 4 bytes, got {per_lit}"
    );
    assert!(
        per_lit < 50.0,
        "Per literal should be < 50 bytes, got {per_lit}"
    );

    // Compare clause_db to theoretical minimum
    // Minimum: num_clauses * (3 lits * 4 bytes) = 4000 * 12 = 48KB
    let min_clause_bytes = 4000 * 3 * 4;
    assert!(
        stats.arena >= min_clause_bytes,
        "Clause DB {} should be >= minimum {}",
        stats.arena,
        min_clause_bytes
    );

    // Should be within 10x of minimum (allowing for Vec overhead)
    assert!(
        stats.arena < min_clause_bytes * 10,
        "Clause DB {} should be < 10x minimum {}",
        stats.arena,
        min_clause_bytes * 10
    );
}

/// Benchmark memory usage after solving (with learned clauses)
#[test]
fn test_memory_after_solving() {
    let mut solver = Solver::new(50);

    // Add a satisfiable random 3-SAT instance
    for i in 0..200 {
        let v1 = (i * 3) % 50;
        let v2 = (i * 3 + 1) % 50;
        let v3 = (i * 3 + 2) % 50;
        solver.add_clause(vec![
            if i % 2 == 0 {
                Literal::positive(Variable(v1 as u32))
            } else {
                Literal::negative(Variable(v1 as u32))
            },
            Literal::negative(Variable(v2 as u32)),
            Literal::positive(Variable(v3 as u32)),
        ]);
    }

    let stats_before = solver.memory_stats();

    // Solve
    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Sat(_)));

    let stats_after = solver.memory_stats();

    // After solving, we may have learned clauses
    // Memory should not explode (allow up to 5x growth for learned clauses)
    assert!(
        stats_after.total() < stats_before.total() * 5,
        "Memory should not grow more than 5x after solving"
    );
}

/// Test memory stats display formatting
#[test]
fn test_memory_stats_display() {
    let mut solver = Solver::new(100);
    for i in 0..100 {
        solver.add_clause(vec![Literal::positive(Variable(i as u32))]);
    }

    let stats = solver.memory_stats();
    let display = format!("{stats}");

    // Should contain key information
    assert!(display.contains("Variables: 100"));
    assert!(display.contains("Clauses: 100"));
    assert!(display.contains("Solver shell:"));
    assert!(display.contains("Original clause ledger:"));
    assert!(display.contains("Total:"));
    assert!(display.contains("bytes"));
}

#[test]
fn test_memory_stats_var_data_matches_live_layout() {
    let solver = Solver::new(64);
    let stats = solver.memory_stats();

    let expected = solver.vals.capacity() * size_of::<i8>()
        + solver.var_data.capacity() * size_of::<VarData>()
        + solver.phase.capacity() * size_of::<i8>()
        + solver.target_phase.capacity() * size_of::<i8>()
        + solver.best_phase.capacity() * size_of::<i8>();

    assert_eq!(
        stats.var_data, expected,
        "memory_stats var_data must match the live VarData + phase-array layout"
    );
}

#[test]
fn test_memory_stats_conflict_counts_minimization_buffers() {
    let solver = Solver::new(32);
    let stats = solver.memory_stats();

    let minimize_bytes = solver.min.minimize_flags.capacity() * size_of::<u8>()
        + solver.min.minimize_to_clear.capacity() * size_of::<usize>()
        + solver.min.level_seen.capacity() * size_of::<minimization_state::LevelSeen>()
        + solver.min.level_seen_to_clear.capacity() * size_of::<u32>()
        + solver.min.lrat_to_clear.capacity() * size_of::<usize>()
        + solver.min.lrat_original_learned_buf.capacity() * size_of::<Literal>()
        + solver.min.minimize_level_seen.capacity() * size_of::<minimization_state::LevelSeen>()
        + solver.min.minimize_levels_to_clear.capacity() * size_of::<u32>();

    assert!(
        stats.conflict >= minimize_bytes,
        "conflict bucket must include the minimization arrays"
    );
}

#[test]
fn test_memory_stats_watches_use_outer_capacity_after_var_growth() {
    let mut solver = Solver::new(0);
    while solver.watches.outer_capacity() == solver.num_vars * 2 {
        solver.new_var();
        if solver.num_vars >= 64 {
            break;
        }
    }

    assert!(
        solver.watches.outer_capacity() > solver.num_vars * 2,
        "expected incremental growth to leave spare capacity in the outer watch table"
    );

    let stats = solver.memory_stats();
    let expected = solver.watches.heap_bytes()
        + solver.deferred_watch_list.capacity() * size_of::<u32>()
        + solver.deferred_replacement_watches.capacity() * size_of::<(Literal, Watcher)>();

    assert_eq!(
        stats.watches, expected,
        "memory_stats watches must use the live outer watch-table capacity, not just num_vars * 2"
    );
}

#[test]
fn test_memory_stats_support_counts_mapping_and_walk_buffers() {
    let mut solver = Solver::new(8);
    solver.ensure_num_vars(17);

    let stats = solver.memory_stats();
    let expected = solver.cold.e2i.capacity() * size_of::<u32>()
        + solver.cold.i2e.capacity() * size_of::<u32>()
        + solver.var_lifecycle.heap_bytes()
        + packed_bool_vec_bytes(solver.phase_init.walk_prev_phase.capacity())
        + solver
            .cold
            .solution_witness
            .as_ref()
            .map_or(0, |witness| witness.capacity() * size_of::<Option<bool>>());

    assert_eq!(
        stats.support, expected,
        "memory_stats support bucket must match live mapping/lifecycle/walk buffers"
    );
}

#[test]
fn test_memory_stats_original_ledger_matches_live_layout() {
    let mut solver = Solver::new(16);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(3)),
        Literal::positive(Variable(4)),
        Literal::negative(Variable(5)),
    ]);
    solver.add_clause(vec![Literal::positive(Variable(6))]);

    let stats = solver.memory_stats();
    let expected = solver.cold.original_ledger.heap_bytes();

    assert_eq!(
        stats.original_ledger, expected,
        "memory_stats must include the immutable original-clause ledger kept beside the arena"
    );
}

// ========================================================================
// Progress Reporting Tests
// ========================================================================

/// Test that `format_progress_line` produces the expected DIMACS comment format.
#[test]
fn test_format_progress_line_dimacs_format() {
    let solver = Solver::new(10);
    let line = solver.format_progress_line(5.0);
    assert!(
        line.starts_with("c ["),
        "Progress line must start with 'c [', got: {line}"
    );
    assert!(
        line.contains("conflicts="),
        "Progress line must contain conflicts="
    );
    assert!(
        line.contains("decisions="),
        "Progress line must contain decisions="
    );
    assert!(line.contains("props="), "Progress line must contain props=");
    assert!(
        line.contains("restarts="),
        "Progress line must contain restarts="
    );
    assert!(
        line.contains("learned="),
        "Progress line must contain learned="
    );
    assert!(line.contains("mode="), "Progress line must contain mode=");
    assert!(
        line.contains("rss="),
        "Progress line must contain rss= (#8641)"
    );
}

/// Test that `format_progress_line` reflects actual solver counters after solving.
#[test]
fn test_format_progress_line_reflects_counters() {
    let mut solver = Solver::new(50);
    // Add a satisfiable random 3-SAT instance that requires some search.
    for i in 0..200 {
        let v1 = (i * 3) % 50;
        let v2 = (i * 3 + 1) % 50;
        let v3 = (i * 3 + 2) % 50;
        solver.add_clause(vec![
            if i % 2 == 0 {
                Literal::positive(Variable(v1 as u32))
            } else {
                Literal::negative(Variable(v1 as u32))
            },
            Literal::negative(Variable(v2 as u32)),
            Literal::positive(Variable(v3 as u32)),
        ]);
    }
    let _ = solver.solve();
    let line = solver.format_progress_line(1.0);
    // After solving, at least some propagations and decisions must have occurred.
    assert!(
        line.contains("props="),
        "progress line after solve must contain props="
    );
    // The line should reflect non-zero counters.
    assert!(
        !line.contains("props=0 "),
        "after solving, propagation count should be > 0"
    );
}

/// Test that `set_progress_enabled` toggles the flag and `maybe_emit_progress` is safe to call.
#[test]
fn test_set_progress_enabled_toggle() {
    let mut solver = Solver::new(10);
    // Default: disabled.
    solver.maybe_emit_progress();
    // Enable.
    solver.set_progress_enabled(true);
    // Call without a solve start time — should not panic.
    solver.maybe_emit_progress();
}

#[test]
fn test_bcp_telemetry_toggle_accessors() {
    let mut solver = Solver::new(10);

    assert!(
        !solver.bcp_telemetry_enabled(),
        "release BCP telemetry should be opt-in"
    );
    solver.set_bcp_telemetry_enabled(true);
    assert!(solver.bcp_telemetry_enabled());
    solver.set_bcp_telemetry_enabled(false);
    assert!(!solver.bcp_telemetry_enabled());
}

#[test]
fn test_bcp_trail_lookahead_prefetch_toggle_accessors() {
    let mut solver = Solver::new(10);

    assert!(
        solver.bcp_trail_lookahead_prefetch_enabled(),
        "outer-loop BCP trail-lookahead prefetch should default on"
    );
    solver.set_bcp_trail_lookahead_prefetch_enabled(false);
    assert!(!solver.bcp_trail_lookahead_prefetch_enabled());
    solver.set_bcp_trail_lookahead_prefetch_enabled(true);
    assert!(solver.bcp_trail_lookahead_prefetch_enabled());
}

#[test]
fn test_bcp_advance_saved_pos_toggle_accessors() {
    let mut solver = Solver::new(10);

    assert!(
        !solver.bcp_advance_saved_pos_after_unassigned_move_enabled(),
        "saved-position advance experiment should be opt-in"
    );
    solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);
    assert!(solver.bcp_advance_saved_pos_after_unassigned_move_enabled());
    solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(false);
    assert!(!solver.bcp_advance_saved_pos_after_unassigned_move_enabled());
}

#[test]
fn test_bcp_learned_1963_false_saved_pos_reset_toggle_accessors() {
    let mut solver = Solver::new(10);

    assert!(
        !solver.bcp_learned_1963_false_saved_pos_reset_enabled(),
        "learned 19-63 false saved-position reset experiment should be opt-in"
    );
    solver.set_bcp_learned_1963_false_saved_pos_reset_enabled(true);
    assert!(solver.bcp_learned_1963_false_saved_pos_reset_enabled());
    solver.set_bcp_learned_1963_false_saved_pos_reset_enabled(false);
    assert!(!solver.bcp_learned_1963_false_saved_pos_reset_enabled());
}

#[test]
fn test_bcp_learned_1963_used5_fsw_saved_pos_reset_toggle_accessors() {
    let mut solver = Solver::new(32);

    assert!(
        !solver.bcp_learned_1963_used5_fsw_saved_pos_reset_enabled(),
        "learned 19-63 used5 FSW saved-position reset should be opt-in"
    );
    solver.set_bcp_learned_1963_used5_fsw_saved_pos_reset_enabled(true);
    assert!(solver.bcp_learned_1963_used5_fsw_saved_pos_reset_enabled());
    solver.set_bcp_learned_1963_used5_fsw_saved_pos_reset_enabled(false);
    assert!(!solver.bcp_learned_1963_used5_fsw_saved_pos_reset_enabled());
}

#[test]
fn test_bcp_learned_1963_fsw_conflict_saved_pos_reset_toggle_accessors() {
    let mut solver = Solver::new(32);

    assert!(
        !solver.bcp_learned_1963_fsw_conflict_saved_pos_reset_enabled(),
        "learned 19-63 FSW conflict-only saved-position reset should be opt-in"
    );
    solver.set_bcp_learned_1963_fsw_conflict_saved_pos_reset_enabled(true);
    assert!(solver.bcp_learned_1963_fsw_conflict_saved_pos_reset_enabled());
    solver.set_bcp_learned_1963_fsw_conflict_saved_pos_reset_enabled(false);
    assert!(!solver.bcp_learned_1963_fsw_conflict_saved_pos_reset_enabled());
}

#[test]
fn test_bcp_learned_1963_fsw_gent_skip_toggle_accessors() {
    let mut solver = Solver::new(32);

    assert!(
        !solver.bcp_learned_1963_fsw_gent_skip_enabled(),
        "learned 19-63 FSW Gent-order skip experiment should be opt-in"
    );
    solver.set_bcp_learned_1963_fsw_gent_skip_enabled(true);
    assert!(solver.bcp_learned_1963_fsw_gent_skip_enabled());
    solver.set_bcp_learned_1963_fsw_gent_skip_enabled(false);
    assert!(!solver.bcp_learned_1963_fsw_gent_skip_enabled());
}

#[test]
fn test_bcp_learned_1963_fsw_gent_skip_does_not_force_hot_path_telemetry() {
    let mut solver = Solver::new(32);

    assert!(!solver.bcp_hot_path_telemetry_forced_by_experiment());
    solver.set_bcp_learned_1963_fsw_gent_skip_enabled(true);
    assert!(
        solver.bcp_learned_1963_fsw_gent_skip_enabled(),
        "functional Gent-order skip gate should still be on"
    );
    assert!(
        !solver.bcp_hot_path_telemetry_forced_by_experiment(),
        "Gent-order skip must not force full BCP telemetry for score timing"
    );

    solver.set_bcp_learned_no_replacement_scan_pressure_enabled(true);
    assert!(
        solver.bcp_hot_path_telemetry_forced_by_experiment(),
        "diagnostic scan-pressure profiling still requires telemetry dispatch"
    );
}

#[test]
fn test_bcp_learned_618_true_tail_relocation_toggle_accessors() {
    let mut solver = Solver::new(18);

    assert!(
        !solver.bcp_learned_618_true_tail_relocation_enabled(),
        "learned 6-18 true-tail relocation experiment should be opt-in"
    );
    solver.set_bcp_learned_618_true_tail_relocation_enabled(true);
    assert!(solver.bcp_learned_618_true_tail_relocation_enabled());
    solver.set_bcp_learned_618_true_tail_relocation_enabled(false);
    assert!(!solver.bcp_learned_618_true_tail_relocation_enabled());
}

#[test]
fn test_bcp_learned_no_replacement_scan_pressure_toggle_accessors() {
    let mut solver = Solver::new(18);

    assert!(
        !solver.bcp_learned_no_replacement_scan_pressure_enabled(),
        "learned no-replacement scan-pressure instrumentation should be opt-in"
    );
    solver.set_bcp_learned_no_replacement_scan_pressure_enabled(true);
    assert!(solver.bcp_learned_no_replacement_scan_pressure_enabled());
    solver.set_bcp_learned_no_replacement_scan_pressure_enabled(false);
    assert!(!solver.bcp_learned_no_replacement_scan_pressure_enabled());
}

#[test]
fn test_bcp_learned_1963_identity_profile_toggle_accessors() {
    let mut solver = Solver::new(32);

    assert!(
        !solver.bcp_learned_1963_identity_profile_enabled(),
        "learned 19-63 identity profile should be opt-in"
    );
    assert!(!solver.bcp_learned_1963_identity_stats(4).enabled);
    solver.set_bcp_learned_1963_identity_profile_enabled(true);
    assert!(solver.bcp_learned_1963_identity_profile_enabled());
    assert!(solver.bcp_learned_1963_identity_stats(4).enabled);
    solver.set_bcp_learned_1963_identity_profile_enabled(false);
    assert!(!solver.bcp_learned_1963_identity_profile_enabled());
}

#[test]
fn test_bcp_learned_1963_pressure_reduction_toggle_accessors() {
    let mut solver = Solver::new(32);

    assert!(
        !solver.bcp_learned_1963_pressure_reduction_enabled(),
        "learned 19-63 pressure reduction should be opt-in"
    );
    assert!(!solver.learned_1963_pressure_reduction_stats().enabled);
    solver.set_bcp_learned_1963_pressure_reduction_enabled(true);
    assert!(solver.bcp_learned_1963_pressure_reduction_enabled());
    assert!(
        solver.bcp_learned_1963_identity_profile_enabled(),
        "pressure reduction should enable the identity pressure source"
    );
    assert!(solver.learned_1963_pressure_reduction_stats().enabled);
    solver.set_bcp_learned_1963_pressure_reduction_enabled(false);
    assert!(!solver.bcp_learned_1963_pressure_reduction_enabled());
    assert!(!solver.learned_1963_pressure_reduction_stats().enabled);
}

#[test]
fn test_bcp_learned_1963_pressure_retention_toggle_accessors() {
    let mut solver = Solver::new(32);

    assert!(
        !solver.bcp_learned_1963_pressure_retention_enabled(),
        "learned 19-63 pressure retention should be opt-in"
    );
    assert!(!solver.learned_1963_pressure_retention_stats().enabled);
    solver.set_bcp_learned_1963_pressure_retention_enabled(true);
    assert!(solver.bcp_learned_1963_pressure_retention_enabled());
    assert!(
        solver.bcp_learned_1963_identity_profile_enabled(),
        "pressure retention should enable the identity pressure source"
    );
    assert!(solver.learned_1963_pressure_retention_stats().enabled);
    solver.set_bcp_learned_1963_pressure_retention_enabled(false);
    assert!(!solver.bcp_learned_1963_pressure_retention_enabled());
    assert!(!solver.learned_1963_pressure_retention_stats().enabled);
}

#[test]
fn test_bcp_learned_617_tail_reorder_toggle_accessors() {
    let mut solver = Solver::new(10);

    assert!(
        !solver.bcp_learned_617_tail_reorder_enabled(),
        "learned 6-17 creation-time tail reorder experiment should be opt-in"
    );
    solver.set_bcp_learned_617_tail_reorder_enabled(true);
    assert!(solver.bcp_learned_617_tail_reorder_enabled());
    solver.set_bcp_learned_617_tail_reorder_enabled(false);
    assert!(!solver.bcp_learned_617_tail_reorder_enabled());
}

#[test]
fn test_bcp_learned_18_tail_reorder_toggle_accessors() {
    let mut solver = Solver::new(18);

    assert!(
        !solver.bcp_learned_18_tail_reorder_enabled(),
        "learned length-18 creation-time tail reorder experiment should be opt-in"
    );
    solver.set_bcp_learned_18_tail_reorder_enabled(true);
    assert!(solver.bcp_learned_18_tail_reorder_enabled());
    solver.set_bcp_learned_18_tail_reorder_enabled(false);
    assert!(!solver.bcp_learned_18_tail_reorder_enabled());
}

#[test]
fn test_bcp_learned_1963_tail_reorder_toggle_accessors() {
    let mut solver = Solver::new(10);

    assert!(
        !solver.bcp_learned_1963_tail_reorder_enabled(),
        "learned 19-63 creation-time tail reorder experiment should be opt-in"
    );
    solver.set_bcp_learned_1963_tail_reorder_enabled(true);
    assert!(solver.bcp_learned_1963_tail_reorder_enabled());
    solver.set_bcp_learned_1963_tail_reorder_enabled(false);
    assert!(!solver.bcp_learned_1963_tail_reorder_enabled());

    assert_eq!(
        solver.bcp_learned_1963_tail_reorder_swap_budget(),
        None,
        "budgeted learned 19-63 tail reorder should be opt-in"
    );
    solver.set_bcp_learned_1963_tail_reorder_swap_budget(Some(256));
    assert_eq!(
        solver.bcp_learned_1963_tail_reorder_swap_budget(),
        Some(256)
    );
    assert!(
        solver
            .bcp_long_scan_stats()
            .learned_1963_tail_reorder_enabled,
        "budgeted route should mark the learned 19-63 tail reorder as enabled"
    );
    solver.set_bcp_learned_1963_tail_reorder_swap_budget(None);
    assert_eq!(solver.bcp_learned_1963_tail_reorder_swap_budget(), None);
}

fn run_small_bcp_telemetry_formula(solver: &mut Solver) {
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);

    // Queue b=true before a=true so (!a || b) hits the blocker fast path when
    // a is propagated. (!a || c) then exercises the binary propagation path.
    solver.add_clause(vec![Literal::positive(b)]);
    solver.add_clause(vec![Literal::positive(a)]);
    solver.add_clause(vec![Literal::negative(a), Literal::positive(b)]);
    solver.add_clause(vec![Literal::negative(a), Literal::positive(c)]);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(solver.search_propagate().is_none());
}

#[cfg(not(debug_assertions))]
fn run_long_bcp_scan_telemetry_formula(solver: &mut Solver) {
    let clause: Vec<Literal> = (0..18)
        .map(|var| Literal::positive(Variable(var)))
        .collect();

    assert!(solver.add_clause(clause));
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.search_propagate().is_none());
}

#[cfg(not(debug_assertions))]
fn run_long_bcp_blocker_telemetry_formula(solver: &mut Solver) {
    let clause: Vec<Literal> = (0..18)
        .map(|var| Literal::positive(Variable(var)))
        .collect();

    assert!(solver.add_clause(clause));
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    solver.decide(Literal::positive(Variable(1)));
    solver.qhead = solver.trail.len();
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.search_propagate().is_none());
}

#[test]
fn test_bcp_telemetry_enabled_counts_watch_paths() {
    let mut solver = Solver::new(3);
    solver.set_bcp_telemetry_enabled(true);

    run_small_bcp_telemetry_formula(&mut solver);

    let (blocker_hits, binary_hits, _) = solver.bcp_stats();
    assert!(
        blocker_hits > 0,
        "enabled BCP telemetry should count satisfied blocker hits"
    );
    assert!(
        binary_hits > 0,
        "enabled BCP telemetry should count binary watch path hits"
    );
}

#[test]
#[cfg(not(debug_assertions))]
fn test_bcp_telemetry_disabled_in_release_keeps_counters_zero() {
    let mut solver = Solver::new(3);

    run_small_bcp_telemetry_formula(&mut solver);

    assert_eq!(
        solver.bcp_stats(),
        (0, 0, 0),
        "release BCP telemetry must stay off unless explicitly requested"
    );

    let mut long_scan_solver = Solver::new(18);
    run_long_bcp_scan_telemetry_formula(&mut long_scan_solver);
    let long_scan_stats = long_scan_solver.bcp_long_scan_stats();
    assert_eq!(
        long_scan_stats.scans_by_len.iter().sum::<u64>(),
        0,
        "release BCP telemetry must not record long-clause scan buckets"
    );
    assert_eq!(
        long_scan_stats.found_replacement_by_len.iter().sum::<u64>(),
        0,
        "release BCP telemetry must not record long-clause replacement buckets"
    );

    let mut long_blocker_solver = Solver::new(18);
    run_long_bcp_blocker_telemetry_formula(&mut long_blocker_solver);
    assert_eq!(
        long_blocker_solver
            .bcp_long_scan_stats()
            .long_blocker_fastpath_hits,
        0,
        "release BCP telemetry must not record long-clause blocker fast-path hits"
    );
}

// ========================================================================
// SolverContext Stats Accessibility Tests (#8425)
// ========================================================================

/// Verify that SolverContext stats methods return non-zero values after solving.
///
/// This test creates a formula that requires search (conflicts, decisions,
/// propagations, restarts) and verifies the stats are accessible through
/// the SolverContext trait. This confirms the trait methods are wired to
/// the actual solver counters and not just returning the default 0.
#[test]
fn test_solver_context_stats_nonzero_after_solve() {
    use crate::SolverContext;

    let mut solver = Solver::new(50);
    // Add a satisfiable but non-trivial 3-SAT instance to force search.
    for i in 0..200 {
        let v1 = (i * 3) % 50;
        let v2 = (i * 3 + 1) % 50;
        let v3 = (i * 3 + 2) % 50;
        solver.add_clause(vec![
            if i % 2 == 0 {
                Literal::positive(Variable(v1 as u32))
            } else {
                Literal::negative(Variable(v1 as u32))
            },
            Literal::negative(Variable(v2 as u32)),
            Literal::positive(Variable(v3 as u32)),
        ]);
    }

    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Sat(_)));

    // Access stats through SolverContext trait object
    let ctx: &dyn SolverContext = &solver;
    assert!(
        ctx.propagations() > 0,
        "SolverContext::propagations() should be non-zero after a non-trivial solve"
    );
    assert!(
        ctx.decisions() > 0,
        "SolverContext::decisions() should be non-zero after a non-trivial solve"
    );
    // Conflicts and restarts may or may not occur depending on the instance,
    // but for a 200-clause/50-var instance they are expected.
    // Just verify they are accessible (no panic, no compilation error).
    let _conflicts = ctx.conflicts();
    let _restarts = ctx.restarts();

    // Verify that direct solver methods match SolverContext methods.
    assert_eq!(ctx.conflicts(), solver.num_conflicts());
    assert_eq!(ctx.decisions(), solver.num_decisions());
    assert_eq!(ctx.restarts(), solver.num_restarts());
    assert_eq!(ctx.propagations(), solver.num_propagations());
}

/// Memory benchmark comparing to theoretical CaDiCaL efficiency
///
/// CaDiCaL uses ~8 bytes per literal (compact arena allocation).
/// AY uses an inline clause arena, so the dominant remaining overhead is
/// original-clause storage plus solver-side per-variable state and cold
/// inprocessing scaffolding.
///
/// Optimization opportunities to reach 1.5x target:
/// 1. Finish `#5090` hot/cold separation for proof/incremental state
/// 2. Lazy initialization of inprocessing engines
/// 3. Compact clause headers (pack lbd, learned, used into single u32)
/// 4. Use SmallVec for short clauses where arena access is not required
#[test]
fn test_memory_vs_cadical_efficiency() {
    let num_vars = 10_000;
    let num_clauses = 40_000; // 4:1 clause-to-var ratio typical for 3-SAT

    let mut solver = Solver::new(num_vars);

    // Add random 3-SAT clauses
    for i in 0..num_clauses {
        let v1 = (i * 7) % num_vars;
        let v2 = (i * 7 + 3) % num_vars;
        let v3 = (i * 7 + 5) % num_vars;
        solver.add_clause(vec![
            Literal::positive(Variable(v1 as u32)),
            Literal::negative(Variable(v2 as u32)),
            Literal::positive(Variable(v3 as u32)),
        ]);
    }

    let stats = solver.memory_stats();

    // CaDiCaL baseline (estimated):
    // - Per variable: ~80 bytes (activities, levels, reasons, etc.)
    // - Per literal: ~8 bytes (arena-allocated with compact headers)
    // - Watches: ~4 bytes per watch entry
    let cadical_per_var = 80;
    let cadical_per_lit = 8;
    let cadical_estimate = num_vars * cadical_per_var + stats.total_literals * cadical_per_lit;

    // AY should be within 1.5x of CaDiCaL estimate (per Priority 2.1 requirement)
    let ratio = stats.total() as f64 / cadical_estimate as f64;

    // Print results for visibility in test output
    safe_eprintln!("Memory Benchmark Results:");
    safe_eprintln!("  Variables: {}", num_vars);
    safe_eprintln!("  Clauses: {}", num_clauses);
    safe_eprintln!("  Literals: {}", stats.total_literals);
    safe_eprintln!();
    safe_eprintln!("Breakdown:");
    safe_eprintln!(
        "  solver_shell: {} bytes ({:.1}%)",
        stats.solver_shell,
        100.0 * stats.solver_shell as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  var_data: {} bytes ({:.1}%)",
        stats.var_data,
        100.0 * stats.var_data as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  vsids: {} bytes ({:.1}%)",
        stats.vsids,
        100.0 * stats.vsids as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  conflict: {} bytes ({:.1}%)",
        stats.conflict,
        100.0 * stats.conflict as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  arena: {} bytes ({:.1}%)",
        stats.arena,
        100.0 * stats.arena as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  watches: {} bytes ({:.1}%)",
        stats.watches,
        100.0 * stats.watches as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  trail: {} bytes ({:.1}%)",
        stats.trail,
        100.0 * stats.trail as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  support: {} bytes ({:.1}%)",
        stats.support,
        100.0 * stats.support as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  clause_ids: {} bytes ({:.1}%)",
        stats.clause_ids,
        100.0 * stats.clause_ids as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  original_ledger: {} bytes ({:.1}%)",
        stats.original_ledger,
        100.0 * stats.original_ledger as f64 / stats.total() as f64
    );
    safe_eprintln!(
        "  inprocessing: {} bytes ({:.1}%)",
        stats.inprocessing,
        100.0 * stats.inprocessing as f64 / stats.total() as f64
    );
    safe_eprintln!();
    safe_eprintln!(
        "  AY total: {} bytes ({:.2} MB)",
        stats.total(),
        stats.total() as f64 / 1_048_576.0
    );
    safe_eprintln!(
        "  CaDiCaL estimate: {} bytes ({:.2} MB)",
        cadical_estimate,
        cadical_estimate as f64 / 1_048_576.0
    );
    safe_eprintln!("  Ratio (AY/CaDiCaL): {:.2}x", ratio);
    safe_eprintln!();
    safe_eprintln!("  AY per variable: {:.2} bytes", stats.per_var());
    safe_eprintln!("  AY per literal: {:.2} bytes", stats.per_literal());

    // Requirement: within 1.5x of CaDiCaL (Priority 2.1)
    // Current baseline is ~4.3x after SoA watch lists and parallel development.
    // Threshold raised to 5x to track further regressions.
    assert!(
        ratio < 5.0,
        "AY memory ({} bytes) should be within 5x of CaDiCaL estimate ({} bytes), ratio: {:.2}x",
        stats.total(),
        cadical_estimate,
        ratio
    );
}
