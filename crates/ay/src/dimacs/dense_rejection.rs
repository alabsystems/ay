// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn fail_closed_dense_clique_php_route_target_rejection(
    solver: &mut SatSolver,
    proof: &ProofConfig,
    reason: &str,
) -> ! {
    let _ = cleanup_dense_clique_php_route_rejection_proof(solver, proof);
    fail_closed_satcomp_proof_setup(&format!(
        "dense clique PHP proof route rejected exact target: {reason}"
    ));
}

const SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_true_tail_relocation_enabled";
const SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_ATTEMPTS_KEY: &str =
    "sat.bcp_learned_1963_true_tail_relocation_attempts";
const SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_MOVES_KEY: &str =
    "sat.bcp_learned_1963_true_tail_relocation_moves";
const SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_used5_fsw_saved_pos_reset_enabled";
const SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ELIGIBLE_KEY: &str =
    "sat.bcp_learned_1963_used5_fsw_saved_pos_reset_eligible";
const SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_WRITES_KEY: &str =
    "sat.bcp_learned_1963_used5_fsw_saved_pos_reset_writes";
const SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_UNIT_KEY: &str =
    "sat.bcp_learned_1963_used5_fsw_saved_pos_reset_unit";
const SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_CONFLICT_KEY: &str =
    "sat.bcp_learned_1963_used5_fsw_saved_pos_reset_conflict";
const SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_fsw_conflict_saved_pos_reset_enabled";
const SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ELIGIBLE_KEY: &str =
    "sat.bcp_learned_1963_fsw_conflict_saved_pos_reset_eligible";
const SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_WRITES_KEY: &str =
    "sat.bcp_learned_1963_fsw_conflict_saved_pos_reset_writes";
const SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_CONFLICT_KEY: &str =
    "sat.bcp_learned_1963_fsw_conflict_saved_pos_reset_conflict";
const SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_ENABLED_KEY: &str =
    "sat.bcp_learned_618_true_tail_relocation_enabled";
const SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_ATTEMPTS_KEY: &str =
    "sat.bcp_learned_618_true_tail_relocation_attempts";
const SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_MOVES_KEY: &str =
    "sat.bcp_learned_618_true_tail_relocation_moves";
const SAT_BCP_LEARNED_NO_REPLACEMENT_SAVED_POS_UPDATE_ENABLED_KEY: &str =
    "sat.bcp_learned_no_replacement_saved_pos_update_enabled";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_enabled";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_CANDIDATES_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_candidates";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_APPLIED_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_applied";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_SAVED_SLOTS_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_saved_slots";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_TRUE_SUFFIX_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_found_true_suffix";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_UNASSIGNED_SUFFIX_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_found_unassigned_suffix";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_TRUE_PREFIX_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_found_true_prefix";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_FOUND_UNASSIGNED_PREFIX_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_found_unassigned_prefix";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_NO_REPLACEMENT_UNIT_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_no_replacement_unit";
const SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_NO_REPLACEMENT_CONFLICT_KEY: &str =
    "sat.bcp_learned_1963_fsw_gent_skip_no_replacement_conflict";
const SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE_ENABLED_KEY: &str =
    "sat.bcp_learned_no_replacement_scan_pressure_enabled";
const SAT_BCP_LEARNED_1963_IDENTITY_ENABLED_KEY: &str = "sat.bcp_learned_1963_identity_enabled";
const SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_pressure_reduction_enabled";
const SAT_BCP_LEARNED_1963_PRESSURE_RETENTION_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_pressure_retention_enabled";
const SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH_ENABLED_KEY: &str =
    "sat.bcp_disable_learned_1963_no_replacement_unit_blocker_refresh_enabled";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISION_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_elision_enabled";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_shadow_enabled";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_false_reject_demote_enabled";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_CANDIDATES_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_candidates";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISIONS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_elisions";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_HITS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_shadow_hits";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_MISMATCHES_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_shadow_mismatches";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_MISMATCH_DEMOTIONS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_mismatch_demotions";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_POPULATES_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_populates";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_STALE_REJECTS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_stale_rejects";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECTS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_false_rejects";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTIONS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_false_reject_demotions";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_REPEAT_REJECTS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_repeat_rejects";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELIDED_SUFFIX_SLOTS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_elided_suffix_slots";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ELIDED_SUFFIX_SLOTS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_shadow_elided_suffix_slots";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_AFFECTED_FSW_ROWS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_affected_fsw_rows";
const SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_AFFECTED_FSW_ROWS_KEY: &str =
    "sat.bcp_learned_1963_blocker_cert_shadow_affected_fsw_rows";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_REQUESTED_KEY: &str =
    "sat.dense_mutex_focused_restart_gate_requested";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_ENABLED_KEY: &str =
    "sat.dense_mutex_focused_restart_gate_enabled";
const SAT_FOCUSED_RESTART_GATE_FINAL_KEY: &str = "sat.focused_restart_gate_final";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_UPDATES_KEY: &str =
    "sat.dense_mutex_focused_restart_gate_updates";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CHECKED_KEY: &str =
    "sat.dense_mutex_focused_restart_runtime_checked";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_VARS_KEY: &str =
    "sat.dense_mutex_focused_restart_active_vars";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_CLAUSES_KEY: &str =
    "sat.dense_mutex_focused_restart_active_clauses";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_BINARY_CLAUSES_KEY: &str =
    "sat.dense_mutex_focused_restart_active_binary_clauses";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CANDIDATE_KEY: &str =
    "sat.dense_mutex_focused_restart_runtime_candidate";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_PREVIOUS_GATE_KEY: &str =
    "sat.dense_mutex_focused_restart_previous_gate";
const SAT_DENSE_MUTEX_FOCUSED_RESTART_COMPUTED_GATE_KEY: &str =
    "sat.dense_mutex_focused_restart_computed_gate";
const SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION_ENABLED_KEY: &str =
    "sat.backbone_post_vivify_binary_admission_enabled";
const SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_ENABLED_KEY: &str =
    "sat.inprocessing_yield_rescue_backbone_cooldown_enabled";
const SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_ROUNDS_KEY: &str =
    "sat.inprocessing_yield_rescue_backbone_cooldown_rounds";
const SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_INTERVAL_KEY: &str =
    "sat.inprocessing_yield_rescue_backbone_cooldown_interval";
const SAT_LRAT_PROOF_CLAMP_PROBE_RESCUE_ENABLED_KEY: &str =
    "sat.inprocessing_lrat_proof_clamp_probe_rescue_enabled";
const SAT_INPROCESSING_LRAT_CLAMPED_BVE_DUE_ROUNDS_KEY: &str =
    "sat.inprocessing_lrat_clamped_bve_due_rounds";
const SAT_INPROCESSING_LRAT_CLAMPED_FACTOR_DUE_ROUNDS_KEY: &str =
    "sat.inprocessing_lrat_clamped_factor_due_rounds";
const SAT_INPROCESSING_LRAT_PROBE_RESCUE_ROUNDS_KEY: &str =
    "sat.inprocessing_lrat_probe_rescue_rounds";
const SAT_BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF_ENABLED_KEY: &str =
    "sat.bounded_backbone_zero_decompose_backoff_enabled";
const SAT_BOUNDED_BACKBONE_BACKOFF_TRIGGERS_KEY: &str = "sat.bounded_backbone_backoff_triggers";
const SAT_BOUNDED_BACKBONE_RUNS_KEY: &str = "sat.bounded_backbone_runs";
const SAT_BOUNDED_BACKBONE_YIELDS_KEY: &str = "sat.bounded_backbone_yields";
const SAT_BOUNDED_BACKBONE_MS_KEY: &str = "sat.bounded_backbone_ms";
const SAT_BOUNDED_BACKBONE_BINARY_SUPPRESSED_KEY: &str = "sat.bounded_backbone_binary_suppressed";
const SAT_DENSE_CLIQUE_MAB_BRANCH_REQUESTED_KEY: &str = "sat.dense_clique_mab_branch_requested";
const SAT_DENSE_CLIQUE_MAB_BRANCH_ENABLED_KEY: &str = "sat.dense_clique_mab_branch_enabled";
const SAT_DENSE_CLIQUE_MAB_BRANCH_EXERCISED_KEY: &str = "sat.dense_clique_mab_branch_exercised";
const SAT_DENSE_CLIQUE_MAB_BRANCH_EXERCISE_COUNT_KEY: &str =
    "sat.dense_clique_mab_branch_exercise_count";
const SAT_DENSE_CLIQUE_SCOUT_REQUESTED_KEY: &str = "sat.dense_clique_scout_requested";
const SAT_DENSE_CLIQUE_SCOUT_ENABLED_KEY: &str = "sat.dense_clique_scout_enabled";
const SAT_DENSE_CLIQUE_SCOUT_EXERCISED_KEY: &str = "sat.dense_clique_scout_exercised";
const SAT_DENSE_CLIQUE_SCOUT_REJECTION_CODE_KEY: &str = "sat.dense_clique_scout_rejection_code";
const SAT_DENSE_CLIQUE_SCOUT_VERTICES_KEY: &str = "sat.dense_clique_scout_vertices";
const SAT_DENSE_CLIQUE_SCOUT_COLORS_KEY: &str = "sat.dense_clique_scout_colors";
const SAT_DENSE_CLIQUE_SCOUT_GRAPH_EDGES_KEY: &str = "sat.dense_clique_scout_graph_edges";
const SAT_DENSE_CLIQUE_SCOUT_GRAPH_NON_EDGES_KEY: &str = "sat.dense_clique_scout_graph_non_edges";
const SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKETS_KEY: &str = "sat.dense_clique_scout_nonedge_buckets";
const SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKET_MIN_KEY: &str =
    "sat.dense_clique_scout_nonedge_bucket_min";
const SAT_DENSE_CLIQUE_SCOUT_NONEDGE_BUCKET_MAX_KEY: &str =
    "sat.dense_clique_scout_nonedge_bucket_max";
const SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MULTIPARTITE_KEY: &str =
    "sat.dense_clique_scout_complete_multipartite";
const SAT_DENSE_CLIQUE_SCOUT_PHP_PIGEONS_KEY: &str = "sat.dense_clique_scout_php_pigeons";
const SAT_DENSE_CLIQUE_SCOUT_PHP_HOLES_KEY: &str = "sat.dense_clique_scout_php_holes";
const SAT_DENSE_CLIQUE_SCOUT_PHP_UNSAT_OBLIGATION_KEY: &str =
    "sat.dense_clique_scout_php_unsat_obligation";
const SAT_DENSE_CLIQUE_SCOUT_MUTEXES_KEY: &str = "sat.dense_clique_scout_mutexes";
const SAT_DENSE_CLIQUE_SCOUT_EXPECTED_MUTEXES_KEY: &str = "sat.dense_clique_scout_expected_mutexes";
const SAT_DENSE_CLIQUE_SCOUT_SUPPORT_CLAUSES_KEY: &str = "sat.dense_clique_scout_support_clauses";
const SAT_DENSE_CLIQUE_SCOUT_SUPPORT_WIDTH_KEY: &str = "sat.dense_clique_scout_support_width";
const SAT_DENSE_CLIQUE_SCOUT_OTHER_CLAUSES_KEY: &str = "sat.dense_clique_scout_other_clauses";
const SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MUTEX_KEY: &str = "sat.dense_clique_scout_complete_mutex";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_REQUESTED_KEY: &str =
    "sat.multiplier_equiv_conservation_scout_requested";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_ENABLED_KEY: &str =
    "sat.multiplier_equiv_conservation_scout_enabled";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_EXERCISED_KEY: &str =
    "sat.multiplier_equiv_conservation_scout_exercised";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCHEMA_VERSION_KEY: &str =
    "sat.multiplier_equiv_conservation_schema_version";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_TARGET_ISSUE_KEY: &str =
    "sat.multiplier_equiv_conservation_target_issue";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_LEAN_ADMISSION_ISSUE_KEY: &str =
    "sat.multiplier_equiv_conservation_lean_admission_issue";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_LEAN_CONSERVATION_ISSUE_KEY: &str =
    "sat.multiplier_equiv_conservation_lean_conservation_issue";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_OFFICIAL_ROW_COUNT_KEY: &str =
    "sat.multiplier_equiv_conservation_official_row_count";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_NUM_VARS_KEY: &str =
    "sat.multiplier_equiv_conservation_num_vars";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_NUM_CLAUSES_KEY: &str =
    "sat.multiplier_equiv_conservation_num_clauses";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_OFFICIAL_SHAPE_KEY: &str =
    "sat.multiplier_equiv_conservation_official_shape";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_STRUCTURAL_CANDIDATE_KEY: &str =
    "sat.multiplier_equiv_conservation_structural_candidate";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_DIAGNOSTIC_CANDIDATE_KEY: &str =
    "sat.multiplier_equiv_conservation_diagnostic_candidate";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_FAIL_CLOSED_KEY: &str =
    "sat.multiplier_equiv_conservation_fail_closed";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_GATE_AND_KEY: &str =
    "sat.multiplier_equiv_conservation_gate_and";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_GATE_XOR_KEY: &str =
    "sat.multiplier_equiv_conservation_gate_xor";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_GATES_TOTAL_KEY: &str =
    "sat.multiplier_equiv_conservation_gates_total";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_PARTIAL_PRODUCT_ROWS_KEY: &str =
    "sat.multiplier_equiv_conservation_partial_product_rows";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_COMPRESSOR_LAYER_ROWS_KEY: &str =
    "sat.multiplier_equiv_conservation_compressor_layer_rows";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_OBLIGATION_ROWS_KEY: &str =
    "sat.multiplier_equiv_conservation_obligation_rows";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_CLAUSE_BOUND_ROWS_KEY: &str =
    "sat.multiplier_equiv_conservation_source_clause_bound_rows";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_CLAUSE_BINDINGS_MISSING_KEY: &str =
    "sat.multiplier_equiv_conservation_source_clause_bindings_missing";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_REFERENCES_KEY: &str =
    "sat.multiplier_equiv_conservation_source_gate_clause_references";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_BOUND_REFERENCES_KEY: &str =
    "sat.multiplier_equiv_conservation_source_gate_clause_bound_references";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_BINDING_MISSING_REFERENCES_KEY: &str =
    "sat.multiplier_equiv_conservation_source_gate_clause_binding_missing_references";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_DUPLICATE_REFERENCES_KEY: &str =
    "sat.multiplier_equiv_conservation_source_gate_clause_duplicate_references";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_OUT_OF_RANGE_REFERENCES_KEY: &str =
    "sat.multiplier_equiv_conservation_source_gate_clause_out_of_range_references";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SOURCE_GATE_CLAUSE_LITERAL_MISMATCH_REFERENCES_KEY: &str =
    "sat.multiplier_equiv_conservation_source_gate_clause_literal_mismatch_references";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_COMMON_PRODUCT_WITNESS_ROWS_KEY: &str =
    "sat.multiplier_equiv_conservation_common_product_witness_rows";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_MITER_DISEQUALITY_ROWS_KEY: &str =
    "sat.multiplier_equiv_conservation_miter_disequality_rows";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_ROUTE_BLOCKER_CODE_KEY: &str =
    "sat.multiplier_equiv_conservation_route_blocker_code";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_REJECTION_CODE_KEY: &str =
    "sat.multiplier_equiv_conservation_scout_rejection_code";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_ROUTE_ADMITTED_KEY: &str =
    "sat.multiplier_equiv_conservation_route_admitted";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_RESULT_AUTHORITY_KEY: &str =
    "sat.multiplier_equiv_conservation_result_authority";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_OUTPUT_AUTHORITY_KEY: &str =
    "sat.multiplier_equiv_conservation_proof_output_authority";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_REPLAY_CHECKED_KEY: &str =
    "sat.multiplier_equiv_conservation_proof_replay_checked";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_EXTERNAL_CHECKER_VERIFIED_KEY: &str =
    "sat.multiplier_equiv_conservation_external_checker_verified";
const SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_ARTIFACT_PRESENT_KEY: &str =
    "sat.multiplier_equiv_conservation_proof_artifact_present";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_REQUESTED_KEY: &str =
    "sat.dense_clique_php_proof_route_requested";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ENABLED_KEY: &str =
    "sat.dense_clique_php_proof_route_enabled";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_EXERCISED_KEY: &str =
    "sat.dense_clique_php_proof_route_exercised";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_FINGERPRINT_KEY: &str =
    "sat.dense_clique_php_proof_route_fingerprint";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ORIGINAL_ORDER_WITNESS_KEY: &str =
    "sat.dense_clique_php_proof_route_original_order_witness";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_OBLIGATION_ROWS_KEY: &str =
    "sat.dense_clique_php_proof_route_obligation_rows";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_BUCKET_ALO_ROWS_KEY: &str =
    "sat.dense_clique_php_proof_route_bucket_alo_rows";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_BUCKET_MUTEX_ROWS_KEY: &str =
    "sat.dense_clique_php_proof_route_bucket_mutex_rows";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_EXTENSION_CLAUSES_KEY: &str =
    "sat.dense_clique_php_proof_route_extension_clauses";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_SOURCE_ROWS_KEY: &str =
    "sat.dense_clique_php_proof_route_source_rows";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_SOURCE_RAW_LITERALS_KEY: &str =
    "sat.dense_clique_php_proof_route_source_raw_literals";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_ROWS_KEY: &str =
    "sat.dense_clique_php_proof_route_audit_rows";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_EXTENSION_ROWS_KEY: &str =
    "sat.dense_clique_php_proof_route_audit_extension_rows";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_BUCKET_ALO_ROWS_KEY: &str =
    "sat.dense_clique_php_proof_route_audit_bucket_alo_rows";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_BUCKET_MUTEX_ROWS_KEY: &str =
    "sat.dense_clique_php_proof_route_audit_bucket_mutex_rows";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_AUDIT_EXTERNAL_CHECKER_VERIFIED_ROWS_KEY: &str =
    "sat.dense_clique_php_proof_route_audit_external_checker_verified_rows";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_PROOF_ASSET_PRESENT_KEY: &str =
    "sat.dense_clique_php_proof_route_proof_asset_present";
const SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_PROOF_ASSET_BYTES_KEY: &str =
    "sat.dense_clique_php_proof_route_proof_asset_bytes";
const SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_REQUESTED_KEY: &str =
    "sat.bcp_search_inplace_watch_scan_requested";
const SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_ENABLED_KEY: &str =
    "sat.bcp_search_inplace_watch_scan_enabled";
const SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_EXERCISED_KEY: &str =
    "sat.bcp_search_inplace_watch_scan_exercised";
const SAT_BCP_TRAIL_LOOKAHEAD_PREFETCH_ENABLED_KEY: &str =
    "sat.bcp_trail_lookahead_prefetch_enabled";
const SAT_BCP_LEARNED_617_TAIL_REORDER_ENABLED_KEY: &str =
    "sat.bcp_learned_617_tail_reorder_enabled";
const SAT_BCP_LEARNED_617_TAIL_REORDER_CANDIDATES_KEY: &str =
    "sat.bcp_learned_617_tail_reorder_candidates";
const SAT_BCP_LEARNED_617_TAIL_REORDER_EXERCISED_KEY: &str =
    "sat.bcp_learned_617_tail_reorder_exercised";
const SAT_BCP_LEARNED_617_TAIL_REORDER_CHANGED_KEY: &str =
    "sat.bcp_learned_617_tail_reorder_changed";
const SAT_BCP_LEARNED_617_TAIL_REORDER_SWAPS_KEY: &str = "sat.bcp_learned_617_tail_reorder_swaps";
const SAT_BCP_LEARNED_18_TAIL_REORDER_ENABLED_KEY: &str = "sat.bcp_learned_18_tail_reorder_enabled";
const SAT_BCP_LEARNED_18_TAIL_REORDER_CANDIDATES_KEY: &str =
    "sat.bcp_learned_18_tail_reorder_candidates";
const SAT_BCP_LEARNED_18_TAIL_REORDER_EXERCISED_KEY: &str =
    "sat.bcp_learned_18_tail_reorder_exercised";
const SAT_BCP_LEARNED_18_TAIL_REORDER_CHANGED_KEY: &str = "sat.bcp_learned_18_tail_reorder_changed";
const SAT_BCP_LEARNED_18_TAIL_REORDER_SWAPS_KEY: &str = "sat.bcp_learned_18_tail_reorder_swaps";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_enabled";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_CANDIDATES_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_candidates";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_CHANGED_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_changed";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAPS_KEY: &str = "sat.bcp_learned_1963_tail_reorder_swaps";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_ENABLED_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_swap_budget_enabled";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_LIMIT_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_swap_budget_limit";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_CANDIDATES_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_budget_candidates";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_APPLIED_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_budget_applied";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SKIPPED_OVER_BUDGET_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_budget_skipped_over_budget";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SWAPS_APPLIED_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_budget_swaps_applied";
const SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SWAPS_SKIPPED_KEY: &str =
    "sat.bcp_learned_1963_tail_reorder_budget_swaps_skipped";
