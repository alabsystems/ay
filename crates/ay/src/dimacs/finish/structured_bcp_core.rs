// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

fn insert_dimacs_bcp_scan_core(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let solver = &*context.solver;
    let stats = &mut *context.run_stats;
    let (blocker, binary, scan_steps) = solver.bcp_stats();
    let scan = solver.bcp_long_scan_stats();
    stats.insert("sat.bcp_blocker_hits", blocker);
    stats.insert("sat.bcp_binary_hits", binary);
    stats.insert("sat.bcp_scan_steps", scan_steps);
    stats.insert("sat.bcp_scan_steps_binary", scan.scan_steps_binary);
    stats.insert("sat.bcp_scan_steps_non_binary", scan.scan_steps_non_binary);
    stats.insert("sat.bcp_scan_steps_learned", scan.scan_steps_learned);
    stats.insert("sat.bcp_scan_steps_original", scan.scan_steps_original);
    stats.insert(
        "sat.bcp_advance_saved_pos_enabled",
        u64::from(solver.bcp_advance_saved_pos_after_unassigned_move_enabled()),
    );
    stats.insert(
        SAT_BCP_TRAIL_LOOKAHEAD_PREFETCH_ENABLED_KEY,
        u64::from(solver.bcp_trail_lookahead_prefetch_enabled()),
    );
    stats.insert(
        SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_REQUESTED_KEY,
        u64::from(solver.bcp_search_inplace_watch_scan_enabled()),
    );
    stats.insert(
        SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_ENABLED_KEY,
        u64::from(solver.bcp_search_inplace_watch_scan_route_enabled()),
    );
    stats.insert(
        SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_EXERCISED_KEY,
        u64::from(solver.bcp_search_inplace_watch_scan_exercised()),
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_ENABLED_KEY,
        u64::from(scan.learned_1963_true_tail_relocation_enabled),
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_ATTEMPTS_KEY,
        scan.learned_1963_true_tail_relocation_attempts,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_MOVES_KEY,
        scan.learned_1963_true_tail_relocation_moves,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ENABLED_KEY,
        u64::from(scan.learned_1963_used5_fsw_saved_pos_reset_enabled),
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ELIGIBLE_KEY,
        scan.learned_1963_used5_fsw_saved_pos_reset_eligible,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_WRITES_KEY,
        scan.learned_1963_used5_fsw_saved_pos_reset_writes,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_UNIT_KEY,
        scan.learned_1963_used5_fsw_saved_pos_reset_unit,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_CONFLICT_KEY,
        scan.learned_1963_used5_fsw_saved_pos_reset_conflict,
    );
}

fn insert_dimacs_bcp_saved_position_routes(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let scan = context.solver.bcp_long_scan_stats();
    let stats = &mut *context.run_stats;
    stats.insert(
        SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ENABLED_KEY,
        u64::from(scan.learned_1963_fsw_conflict_saved_pos_reset_enabled),
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ELIGIBLE_KEY,
        scan.learned_1963_fsw_conflict_saved_pos_reset_eligible,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_WRITES_KEY,
        scan.learned_1963_fsw_conflict_saved_pos_reset_writes,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_CONFLICT_KEY,
        scan.learned_1963_fsw_conflict_saved_pos_reset_conflict,
    );
    stats.insert(
        SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_ENABLED_KEY,
        u64::from(scan.learned_618_true_tail_relocation_enabled),
    );
    stats.insert(
        SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_ATTEMPTS_KEY,
        scan.learned_618_true_tail_relocation_attempts,
    );
    stats.insert(
        SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_MOVES_KEY,
        scan.learned_618_true_tail_relocation_moves,
    );
    stats.insert(
        SAT_BCP_LEARNED_NO_REPLACEMENT_SAVED_POS_UPDATE_ENABLED_KEY,
        u64::from(scan.learned_no_replacement_saved_pos_update_enabled),
    );
}

fn insert_dimacs_bcp_gent_skip_routes(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let scan = context.solver.bcp_long_scan_stats();
    let stats = &mut *context.run_stats;
    stats.insert(
        SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_ENABLED_KEY,
        u64::from(scan.learned_1963_fsw_gent_skip_enabled),
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_CANDIDATES_KEY,
        scan.learned_1963_fsw_gent_skip_candidates,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_APPLIED_KEY,
        scan.learned_1963_fsw_gent_skip_applied,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_SAVED_SLOTS_KEY,
        scan.learned_1963_fsw_gent_skip_saved_slots,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_TRUE_SUFFIX_KEY,
        scan.learned_1963_fsw_gent_skip_found_true_suffix,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_UNASSIGNED_SUFFIX_KEY,
        scan.learned_1963_fsw_gent_skip_found_unassigned_suffix,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_TRUE_PREFIX_KEY,
        scan.learned_1963_fsw_gent_skip_found_true_prefix,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_UNASSIGNED_PREFIX_KEY,
        scan.learned_1963_fsw_gent_skip_found_unassigned_prefix,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_NO_REPLACEMENT_UNIT_KEY,
        scan.learned_1963_fsw_gent_skip_no_replacement_unit,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_NO_REPLACEMENT_CONFLICT_KEY,
        scan.learned_1963_fsw_gent_skip_no_replacement_conflict,
    );
    stats.insert(
        SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE_ENABLED_KEY,
        u64::from(scan.learned_no_replacement_scan_pressure_enabled),
    );
    stats.insert(
        SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH_ENABLED_KEY,
        u64::from(scan.disable_learned_1963_no_replacement_unit_blocker_refresh_enabled),
    );
}

fn insert_dimacs_bcp_blocker_certificate_modes(
    context: &mut DimacsStructuredStatistics<'_, '_, '_>,
) {
    let scan = context.solver.bcp_long_scan_stats();
    let stats = &mut *context.run_stats;
    stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISION_ENABLED_KEY,
        u64::from(scan.learned_1963_blocker_cert_elision_enabled),
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ENABLED_KEY,
        u64::from(scan.learned_1963_blocker_cert_shadow_enabled),
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE_ENABLED_KEY,
        u64::from(scan.learned_1963_blocker_cert_false_reject_demote_enabled),
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_CANDIDATES_KEY,
        scan.learned_1963_blocker_cert_candidates,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISIONS_KEY,
        scan.learned_1963_blocker_cert_elisions,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_HITS_KEY,
        scan.learned_1963_blocker_cert_shadow_hits,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_MISMATCHES_KEY,
        scan.learned_1963_blocker_cert_shadow_mismatches,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_MISMATCH_DEMOTIONS_KEY,
        scan.learned_1963_blocker_cert_mismatch_demotions,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_POPULATES_KEY,
        scan.learned_1963_blocker_cert_populates,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_STALE_REJECTS_KEY,
        scan.learned_1963_blocker_cert_stale_rejects,
    );
}

fn insert_dimacs_bcp_blocker_certificate_outcomes(
    context: &mut DimacsStructuredStatistics<'_, '_, '_>,
) {
    let scan = context.solver.bcp_long_scan_stats();
    let stats = &mut *context.run_stats;
    stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECTS_KEY,
        scan.learned_1963_blocker_cert_false_rejects,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTIONS_KEY,
        scan.learned_1963_blocker_cert_false_reject_demotions,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_REPEAT_REJECTS_KEY,
        scan.learned_1963_blocker_cert_repeat_rejects,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELIDED_SUFFIX_SLOTS_KEY,
        scan.learned_1963_blocker_cert_elided_suffix_slots,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ELIDED_SUFFIX_SLOTS_KEY,
        scan.learned_1963_blocker_cert_shadow_elided_suffix_slots,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_AFFECTED_FSW_ROWS_KEY,
        scan.learned_1963_blocker_cert_affected_fsw_rows,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_AFFECTED_FSW_ROWS_KEY,
        scan.learned_1963_blocker_cert_shadow_affected_fsw_rows,
    );
}

fn insert_dimacs_bcp_tail_reorders(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let scan = context.solver.bcp_long_scan_stats();
    let stats = &mut *context.run_stats;
    stats.insert(
        SAT_BCP_LEARNED_617_TAIL_REORDER_ENABLED_KEY,
        u64::from(scan.learned_617_tail_reorder_enabled),
    );
    stats.insert(
        SAT_BCP_LEARNED_617_TAIL_REORDER_CANDIDATES_KEY,
        scan.learned_617_tail_reorder_candidates,
    );
    stats.insert(
        SAT_BCP_LEARNED_617_TAIL_REORDER_EXERCISED_KEY,
        scan.learned_617_tail_reorder_exercised,
    );
    stats.insert(
        SAT_BCP_LEARNED_617_TAIL_REORDER_CHANGED_KEY,
        scan.learned_617_tail_reorder_changed,
    );
    stats.insert(
        SAT_BCP_LEARNED_617_TAIL_REORDER_SWAPS_KEY,
        scan.learned_617_tail_reorder_swaps,
    );
    stats.insert(
        SAT_BCP_LEARNED_18_TAIL_REORDER_ENABLED_KEY,
        u64::from(scan.learned_18_tail_reorder_enabled),
    );
    stats.insert(
        SAT_BCP_LEARNED_18_TAIL_REORDER_CANDIDATES_KEY,
        scan.learned_18_tail_reorder_candidates,
    );
    stats.insert(
        SAT_BCP_LEARNED_18_TAIL_REORDER_EXERCISED_KEY,
        scan.learned_18_tail_reorder_exercised,
    );
    stats.insert(
        SAT_BCP_LEARNED_18_TAIL_REORDER_CHANGED_KEY,
        scan.learned_18_tail_reorder_changed,
    );
    stats.insert(
        SAT_BCP_LEARNED_18_TAIL_REORDER_SWAPS_KEY,
        scan.learned_18_tail_reorder_swaps,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_TAIL_REORDER_ENABLED_KEY,
        u64::from(scan.learned_1963_tail_reorder_enabled),
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_TAIL_REORDER_CANDIDATES_KEY,
        scan.learned_1963_tail_reorder_candidates,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_TAIL_REORDER_CHANGED_KEY,
        scan.learned_1963_tail_reorder_changed,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAPS_KEY,
        scan.learned_1963_tail_reorder_swaps,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_ENABLED_KEY,
        u64::from(scan.learned_1963_tail_reorder_swap_budget.is_some()),
    );
}

fn insert_dimacs_structured_bcp_core(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    insert_dimacs_bcp_scan_core(context);
    insert_dimacs_bcp_saved_position_routes(context);
    insert_dimacs_bcp_gent_skip_routes(context);
    insert_dimacs_bcp_blocker_certificate_modes(context);
    insert_dimacs_bcp_blocker_certificate_outcomes(context);
    insert_dimacs_bcp_tail_reorders(context);
}
