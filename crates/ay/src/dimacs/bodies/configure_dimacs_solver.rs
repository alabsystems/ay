// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn configure_dimacs_bcp_routes(solver: &mut SatSolver) {
    // Wire interrupt flag so the solver checks the watchdog directly (#3638).
    if let Some(handle) = INTERRUPT_HANDLE.get() {
        solver.set_interrupt(handle.clone());
    }
    // BCP attribution counters write from the propagation hot path. Keep them
    // release-gated to the explicit profiling opt-in, including stats-json
    // runs where the JSON key shape stays stable with zero counters.
    solver.set_bcp_telemetry_enabled(ay_core::sat_ab_switches().bcp_telemetry);
    solver.set_bcp_lean_route_enabled(ay_core::sat_ab_switches().bcp_lean);
    if ay_core::sat_ab_switches().bcp_disable_trail_lookahead_prefetch {
        solver.set_bcp_trail_lookahead_prefetch_enabled(false);
    }
    // Default-on (cold.rs): the in-place SEARCH BCP route is verified
    // bit-identical to the safe deferred-copy path by the 56 differential cases
    // in `solver/tests/propagation_bcp_unsafe.rs`. The env var is a kill-switch
    // rather than an opt-in: `AY_SAT_BCP_SEARCH_INPLACE_WATCH_SCAN=0` forces the
    // safe route; unset or truthy keeps the default-on route.
    solver.set_bcp_search_inplace_watch_scan_enabled(
        ay_core::sat_ab_switches()
            .bcp_search_inplace_watch_scan
            .unwrap_or(true),
    );
    if ay_core::sat_ab_switches().bcp_advance_saved_pos {
        solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);
    }
    if ay_core::sat_ab_switches().bcp_learned_1963_false_saved_pos_reset {
        solver.set_bcp_learned_1963_false_saved_pos_reset_enabled(true);
    }
    if ay_core::sat_ab_switches().bcp_learned_1963_true_tail_relocation {
        solver.set_bcp_learned_1963_true_tail_relocation_enabled(true);
    }
    if ay_core::sat_ab_switches().bcp_learned_1963_used5_fsw_saved_pos_reset {
        solver.set_bcp_learned_1963_used5_fsw_saved_pos_reset_enabled(true);
    }
    if ay_core::sat_ab_switches().bcp_learned_1963_fsw_conflict_saved_pos_reset {
        solver.set_bcp_learned_1963_fsw_conflict_saved_pos_reset_enabled(true);
    }
    if ay_core::sat_ab_switches().bcp_learned_618_true_tail_relocation {
        solver.set_bcp_learned_618_true_tail_relocation_enabled(true);
    }
    if ay_core::sat_ab_switches().bcp_learned_no_replacement_saved_pos_update {
        solver.set_bcp_learned_no_replacement_saved_pos_update_enabled(true);
    }
    if ay_core::sat_ab_switches().bcp_learned_1963_fsw_gent_skip {
        solver.set_bcp_learned_1963_fsw_gent_skip_enabled(true);
    }
    if ay_core::sat_ab_switches().bcp_learned_no_replacement_scan_pressure {
        solver.set_bcp_learned_no_replacement_scan_pressure_enabled(true);
    }
    if ay_core::sat_ab_switches().bcp_learned_1963_identity {
        solver.set_bcp_learned_1963_identity_profile_enabled(true);
    }
    if ay_core::sat_ab_switches().bcp_learned_1963_pressure_reduction {
        solver.set_bcp_learned_1963_pressure_reduction_enabled(true);
    }
    if ay_core::sat_ab_switches().bcp_learned_1963_pressure_retention {
        solver.set_bcp_learned_1963_pressure_retention_enabled(true);
    }
    // Two-stage (LBD-free) learned clause management (arXiv:2602.20829).
    // Tri-state: None and Some(false) both leave the LBD tier policy in place.
    if ay_core::sat_ab_switches()
        .two_stage_clause_management
        .unwrap_or(false)
    {
        solver.set_two_stage_clause_management_enabled(true);
    }
}

fn configure_dimacs_inprocessing_routes(solver: &mut SatSolver) {
    if ay_core::sat_ab_switches().bcp_disable_learned_1963_no_replacement_unit_blocker_refresh {
        solver.set_bcp_disable_learned_1963_no_replacement_unit_blocker_refresh_enabled(true);
    }
    if ay_core::sat_ab_switches().bcp_learned_617_tail_reorder {
        solver.set_bcp_learned_617_tail_reorder_enabled(true);
    }
    if ay_core::sat_ab_switches().bcp_learned_18_tail_reorder {
        solver.set_bcp_learned_18_tail_reorder_enabled(true);
    }
    if ay_core::sat_ab_switches().bcp_learned_1963_tail_reorder {
        solver.set_bcp_learned_1963_tail_reorder_enabled(true);
    }
    if let Some(budget) = ay_core::sat_ab_switches().bcp_learned_1963_tail_reorder_swap_budget {
        solver.set_bcp_learned_1963_tail_reorder_swap_budget(Some(budget));
    }
    if ay_core::sat_ab_switches().bve_occ_delta_validation {
        solver.set_bve_occ_delta_validation_enabled(true);
    }
    if ay_core::sat_ab_switches().bve_occ_saved_state_reuse {
        solver.set_bve_occ_saved_state_reuse_enabled(true);
    }
    if ay_core::sat_ab_switches().inprocessing_yield_productivity_rescue {
        solver.set_inprocessing_yield_productivity_rescue_enabled(true);
    }
    // M2 default flip (2026-08-19): ON unless opted out — the paired A/B
    // lost nothing and the 900s boundary confirmation was clean.
    if ay_core::sat_ab_switches()
        .lrat_proof_clamp_probe_rescue
        .unwrap_or(true)
    {
        solver.set_lrat_proof_clamp_probe_rescue_enabled(true);
    }
    // M3 default flip (2026-08-19): ON unless opted out — paired A/B lost
    // nothing; the 900s confirmation held the gain.
    if ay_core::sat_ab_switches()
        .yield_rescue_backbone_cooldown
        .unwrap_or(true)
    {
        solver.set_inprocessing_yield_rescue_backbone_cooldown_enabled(true);
    }
    if ay_core::sat_ab_switches().bounded_backbone_zero_decompose_backoff {
        solver.set_bounded_backbone_zero_decompose_backoff_enabled(true);
    }
    solver.set_backbone_post_vivify_binary_admission_enabled(
        ay_core::sat_ab_switches()
            .backbone_post_vivify_binary_admission
            .unwrap_or(true),
    );
}

fn configure_dimacs_solver_body(solver: &mut SatSolver) {
    configure_dimacs_bcp_routes(solver);
    configure_dimacs_inprocessing_routes(solver);
    finish_configure_dimacs_solver(solver);
}
