// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

const DIMACS_BOOLEAN_STATS_KEYS: &[&str] = &[
    SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_REQUESTED_KEY,
    SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE_ENABLED_KEY,
    SAT_DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CANDIDATE_KEY,
    SAT_BACKBONE_POST_VIVIFY_BINARY_ADMISSION_ENABLED_KEY,
    SAT_INPROCESSING_YIELD_RESCUE_BACKBONE_COOLDOWN_ENABLED_KEY,
    SAT_LRAT_PROOF_CLAMP_PROBE_RESCUE_ENABLED_KEY,
    SAT_BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF_ENABLED_KEY,
    SAT_DENSE_CLIQUE_MAB_BRANCH_REQUESTED_KEY,
    SAT_DENSE_CLIQUE_MAB_BRANCH_ENABLED_KEY,
    SAT_DENSE_CLIQUE_MAB_BRANCH_EXERCISED_KEY,
    SAT_DENSE_CLIQUE_SCOUT_REQUESTED_KEY,
    SAT_DENSE_CLIQUE_SCOUT_ENABLED_KEY,
    SAT_DENSE_CLIQUE_SCOUT_EXERCISED_KEY,
    SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MUTEX_KEY,
    SAT_DENSE_CLIQUE_SCOUT_COMPLETE_MULTIPARTITE_KEY,
    SAT_DENSE_CLIQUE_SCOUT_PHP_UNSAT_OBLIGATION_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_REQUESTED_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_ENABLED_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_EXERCISED_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_OFFICIAL_SHAPE_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_STRUCTURAL_CANDIDATE_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_DIAGNOSTIC_CANDIDATE_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_SCOUT_FAIL_CLOSED_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_ROUTE_ADMITTED_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_RESULT_AUTHORITY_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_OUTPUT_AUTHORITY_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_REPLAY_CHECKED_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_EXTERNAL_CHECKER_VERIFIED_KEY,
    SAT_MULTIPLIER_EQUIV_CONSERVATION_PROOF_ARTIFACT_PRESENT_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_REQUESTED_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ENABLED_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_EXERCISED_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_ORIGINAL_ORDER_WITNESS_KEY,
    SAT_DENSE_CLIQUE_PHP_PROOF_ROUTE_PROOF_ASSET_PRESENT_KEY,
    SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_REQUESTED_KEY,
    SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_ENABLED_KEY,
    SAT_BCP_SEARCH_INPLACE_WATCH_SCAN_EXERCISED_KEY,
    SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_USED5_FSW_SAVED_POS_RESET_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_FSW_CONFLICT_SAVED_POS_RESET_ENABLED_KEY,
    SAT_BCP_LEARNED_618_TRUE_TAIL_RELOCATION_ENABLED_KEY,
    SAT_BCP_LEARNED_NO_REPLACEMENT_SAVED_POS_UPDATE_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_FSW_GENT_SKIP_ENABLED_KEY,
    SAT_BCP_LEARNED_NO_REPLACEMENT_SCAN_PRESSURE_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_IDENTITY_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_PRESSURE_RETENTION_ENABLED_KEY,
    SAT_BCP_DISABLE_LEARNED_1963_NO_REPLACEMENT_UNIT_BLOCKER_REFRESH_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_ELISION_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_SHADOW_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_BLOCKER_CERT_FALSE_REJECT_DEMOTE_ENABLED_KEY,
    SAT_BCP_TRAIL_LOOKAHEAD_PREFETCH_ENABLED_KEY,
    SAT_BCP_LEARNED_617_TAIL_REORDER_ENABLED_KEY,
    SAT_BCP_LEARNED_18_TAIL_REORDER_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_TAIL_REORDER_ENABLED_KEY,
    SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_ENABLED_KEY,
];

fn boolify_dimacs_stats(
    map: &mut serde_json::Map<String, serde_json::Value>,
    run_stats: &stats_output::RunStatistics,
) {
    for key in DIMACS_BOOLEAN_STATS_KEYS {
        boolify_stats_counter(map, run_stats, key);
    }
}

fn insert_sat_competition_json(
    map: &mut serde_json::Map<String, serde_json::Value>,
    route_profile: VariantRouteProfile,
    profile: Option<&str>,
    profile_identity: Option<&str>,
    hard_tail_row_id: Option<&str>,
    jit: &SatCompetitionJitMetadata,
    application_count: u64,
) {
    let metadata_present = profile.is_some() && profile_identity.is_some() && jit.mode_present;
    if let Some(row_id) = hard_tail_row_id {
        map.insert("hard_tail_row_id".to_string(), serde_json::json!(row_id));
    }
    map.insert(
        "sat_competition".to_string(),
        serde_json::json!({
            "schema_version": 1,
            "profile": profile.unwrap_or("unavailable"),
            "profile_identity": profile_identity.unwrap_or("unavailable"),
            "hard_tail_row_id": hard_tail_row_id.unwrap_or("unavailable"),
            "fallback": SAT_COMPETITION_FALLBACK,
            "route_profile": route_profile.as_str(),
            "metadata_present": metadata_present,
            "fail_closed": jit.runtime_fail_closed(application_count, metadata_present),
        }),
    );
}

fn dimacs_run_stats_json_body(
    run_stats: &stats_output::RunStatistics,
    route_profile: VariantRouteProfile,
) -> String {
    let json = run_stats.to_json();
    let Ok(mut value) = serde_json::from_str::<serde_json::Value>(&json) else {
        return json;
    };
    let Some(map) = value.as_object_mut() else {
        return json;
    };
    let profile = trimmed_env_value("AY_SAT_COMPETITION_PROFILE");
    let profile_identity = trimmed_env_value("AY_SAT_PROFILE_ID");
    let hard_tail_row_id = trimmed_env_value(SAT_HARD_TAIL_ROW_ID_ENV);
    let jit = sat_native_helper_competition_jit_metadata();
    let application_count = run_stats
        .counters
        .get(jit.application_counter)
        .copied()
        .unwrap_or(0);
    let metadata_present = profile.is_some() && profile_identity.is_some() && jit.mode_present;
    enrich_sat_native_helper_competition_jit_json(map, &jit, application_count, metadata_present);
    boolify_dimacs_stats(map, run_stats);
    insert_sat_competition_json(
        map,
        route_profile,
        profile.as_deref(),
        profile_identity.as_deref(),
        hard_tail_row_id.as_deref(),
        &jit,
        application_count,
    );
    value.to_string()
}
