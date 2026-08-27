// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn insert_decompose_lrat_preflight_core(
    run_stats: &mut stats_output::RunStatistics,
    stats: &ay_sat::DecomposeLratPreflightStats,
) {
    run_stats.insert("sat.decompose_lrat_preflight_attempts", stats.attempts);
    run_stats.insert(
        "sat.decompose_lrat_preflight_candidate_count",
        stats.transaction_candidates,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_no_substitution",
        stats.no_substitution,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_empty_candidates",
        stats.empty_candidates,
    );
    run_stats.insert("sat.decompose_lrat_preflight_slices", stats.dry_run_emitted);
    run_stats.insert(
        "sat.decompose_lrat_preflight_rejected",
        stats.dry_run_rejected,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_missing_source_id",
        stats.missing_source_id,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_missing_chain_edge_id",
        stats.missing_chain_edge_id,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_missing_equiv_chain",
        stats.missing_equiv_chain,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_malformed_rewrite",
        stats.malformed_rewrite,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_contradiction",
        stats.contradiction,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_missing_level0_unit_id",
        stats.missing_level0_unit_id,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_planned_add_rejected",
        stats.planned_add_rejected,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_missing_substitution_hint",
        stats.missing_substitution_hint,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_missing_transient_equiv_id",
        stats.missing_transient_equiv_id,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_proof_obligations",
        stats.proof_obligations,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_reconstruction_witnesses",
        stats.reconstruction_witnesses,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_main_rewrite_materializer_attempts",
        stats.main_rewrite_materializer_attempts,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_main_rewrite_materializer_proof_emit_records_seen",
        stats.main_rewrite_materializer_proof_emit_records_seen,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_main_rewrite_materializer_records",
        stats.main_rewrite_materializer_records,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_main_rewrite_materializer_fail_closed",
        stats.main_rewrite_materializer_fail_closed,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_main_rewrite_materializer_missing_runtime_records",
        stats.main_rewrite_materializer_missing_runtime_records,
    );
}

fn insert_decompose_lrat_preflight_fmla(
    run_stats: &mut stats_output::RunStatistics,
    stats: &ay_sat::DecomposeLratPreflightStats,
) {
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_attempts",
        stats.fmla_lift_attempts,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_detected",
        stats.fmla_lift_detected,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_rejection_code",
        stats.fmla_lift_rejection_code,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_onehot_groups",
        stats.fmla_lift_onehot_groups,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_guarded_equiv_pairs",
        stats.fmla_lift_guarded_equiv_pairs,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_guarded_equiv_guards",
        stats.fmla_lift_guarded_equiv_guards,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_directional_ternary_witnesses",
        stats.fmla_lift_directional_ternary_witnesses,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_touched_vars",
        stats.fmla_lift_touched_vars,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_runtime_records",
        stats.fmla_lift_runtime_records,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_witness_checker_passed",
        stats.fmla_lift_witness_checker_passed,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_all_witness_pairs_checked",
        stats.fmla_lift_all_witness_pairs_checked,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_all_witness_pairs_missing_guard_group",
        stats.fmla_lift_all_witness_pairs_missing_guard_group,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_source_id_refs_checked",
        stats.fmla_lift_source_id_refs_checked,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_unique_source_ids_checked",
        stats.fmla_lift_unique_source_ids_checked,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_source_ids_checked",
        stats.fmla_lift_source_ids_checked,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_source_ids_visible",
        stats.fmla_lift_source_ids_visible,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_source_ids_missing",
        stats.fmla_lift_source_ids_missing,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_first_missing_source_id",
        stats.fmla_lift_first_missing_source_id,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_proof_ready",
        stats.fmla_lift_proof_ready,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_model_ready",
        stats.fmla_lift_model_ready,
    );
    run_stats.insert(
        "sat.decompose_lrat_preflight_fmla_lift_destructive_allowed",
        stats.fmla_lift_destructive_allowed,
    );
}

fn insert_decompose_lrat_preflight_telemetry_body(
    run_stats: &mut stats_output::RunStatistics,
    stats: &ay_sat::DecomposeLratPreflightStats,
) {
    insert_decompose_lrat_preflight_core(run_stats, stats);
    insert_decompose_lrat_preflight_fmla(run_stats, stats);
}
