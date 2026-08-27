// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

fn insert_dimacs_bcp_budget_stats(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let scan = context.solver.bcp_long_scan_stats();
    let stats = &mut *context.run_stats;
    let budget = scan
        .learned_1963_tail_reorder_swap_budget
        .unwrap_or_default();
    stats.insert(
        SAT_BCP_LEARNED_1963_TAIL_REORDER_SWAP_BUDGET_LIMIT_KEY,
        budget,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_CANDIDATES_KEY,
        scan.learned_1963_tail_reorder_budget_candidates,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_APPLIED_KEY,
        scan.learned_1963_tail_reorder_budget_applied,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SKIPPED_OVER_BUDGET_KEY,
        scan.learned_1963_tail_reorder_budget_skipped_over_budget,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SWAPS_APPLIED_KEY,
        scan.learned_1963_tail_reorder_budget_swaps_applied,
    );
    stats.insert(
        SAT_BCP_LEARNED_1963_TAIL_REORDER_BUDGET_SWAPS_SKIPPED_KEY,
        scan.learned_1963_tail_reorder_budget_swaps_skipped,
    );
}

fn insert_dimacs_bcp_pressure_reduction(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let pressure = context.solver.learned_1963_pressure_reduction_stats();
    let stats = &mut *context.run_stats;
    stats.insert(
        SAT_BCP_LEARNED_1963_PRESSURE_REDUCTION_ENABLED_KEY,
        u64::from(pressure.enabled),
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_reduction_candidates",
        pressure.candidates,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_reduction_pressure_candidates",
        pressure.pressure_candidates,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_reduction_ranked",
        pressure.ranked,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_reduction_rank_bias_total",
        pressure.rank_bias_total,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_reduction_selected",
        pressure.selected,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_reduction_selected_steps",
        pressure.selected_steps,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_reduction_deleted",
        pressure.deleted,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_reduction_deleted_steps",
        pressure.deleted_steps,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_reduction_kept",
        pressure.kept,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_reduction_kept_steps",
        pressure.kept_steps,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_reduction_skipped_no_pressure",
        pressure.skipped_no_pressure,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_reduction_lrat_retained_delete_skips",
        pressure.lrat_retained_delete_skips,
    );
}

fn insert_dimacs_bcp_pressure_retention(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let pressure = context.solver.learned_1963_pressure_retention_stats();
    let stats = &mut *context.run_stats;
    stats.insert(
        SAT_BCP_LEARNED_1963_PRESSURE_RETENTION_ENABLED_KEY,
        u64::from(pressure.enabled),
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_retention_candidates",
        pressure.candidates,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_retention_pressure_candidates",
        pressure.pressure_candidates,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_retention_ranked",
        pressure.ranked,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_retention_rank_bias_total",
        pressure.rank_bias_total,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_retention_selected",
        pressure.selected,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_retention_selected_steps",
        pressure.selected_steps,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_retention_deleted",
        pressure.deleted,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_retention_deleted_steps",
        pressure.deleted_steps,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_retention_kept",
        pressure.kept,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_retention_kept_steps",
        pressure.kept_steps,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_retention_skipped_no_pressure",
        pressure.skipped_no_pressure,
    );
    stats.insert(
        "sat.bcp_learned_1963_pressure_retention_lrat_retained_delete_skips",
        pressure.lrat_retained_delete_skips,
    );
}

fn insert_dimacs_bcp_saved_position_stats(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let saved = context.solver.bcp_saved_pos_stats();
    let scan = context.solver.bcp_long_scan_stats();
    let stats = &mut *context.run_stats;
    stats.insert("sat.bcp_long_saved_pos_scans", saved.long_scans);
    stats.insert("sat.bcp_long_saved_pos_start_false", saved.long_start_false);
    stats.insert("sat.bcp_long_saved_pos_found_true", saved.long_found_true);
    stats.insert(
        "sat.bcp_long_saved_pos_found_unassigned",
        saved.long_found_unassigned,
    );
    stats.insert(
        "sat.bcp_long_saved_pos_no_replacement",
        saved.long_no_replacement,
    );
    stats.insert("sat.bcp_len18_saved_pos_scans", saved.len18_scans);
    stats.insert(
        "sat.bcp_len18_saved_pos_start_false",
        saved.len18_start_false,
    );
    stats.insert("sat.bcp_len18_saved_pos_found_true", saved.len18_found_true);
    stats.insert(
        "sat.bcp_len18_saved_pos_found_unassigned",
        saved.len18_found_unassigned,
    );
    stats.insert(
        "sat.bcp_len18_saved_pos_no_replacement",
        saved.len18_no_replacement,
    );
    stats.insert(
        "sat.bcp_long_blocker_fastpath_hits",
        scan.long_blocker_fastpath_hits,
    );
}

fn insert_dimacs_bcp_bucket_value(
    stats: &mut stats_output::RunStatistics,
    bucket: &str,
    prefix: &str,
    metric: &str,
    values: &[u64],
    index: usize,
) {
    stats.insert(&format!("sat.{prefix}_{bucket}_{metric}"), values[index]);
}

fn insert_dimacs_bcp_long_bucket_core(
    context: &mut DimacsStructuredStatistics<'_, '_, '_>,
    bucket: &str,
    index: usize,
) {
    let scan = context.solver.bcp_long_scan_stats();
    let stats = &mut *context.run_stats;
    let values = [
        ("steps", scan.scan_steps_by_len.as_slice()),
        ("learned_steps", scan.learned_scan_steps_by_len.as_slice()),
        ("original_steps", scan.original_scan_steps_by_len.as_slice()),
        ("scans", scan.scans_by_len.as_slice()),
        (
            "found_replacement",
            scan.found_replacement_by_len.as_slice(),
        ),
        ("found_true", scan.found_true_by_len.as_slice()),
        ("found_unassigned", scan.found_unassigned_by_len.as_slice()),
        ("no_replacement", scan.no_replacement_by_len.as_slice()),
        ("unit", scan.unit_by_len.as_slice()),
        ("conflict", scan.conflict_by_len.as_slice()),
    ];
    for (metric, values) in values {
        insert_dimacs_bcp_bucket_value(stats, bucket, "bcp_long_scan", metric, values, index);
    }
}

fn insert_dimacs_bcp_long_bucket_learned(
    context: &mut DimacsStructuredStatistics<'_, '_, '_>,
    bucket: &str,
    index: usize,
) {
    let scan = context.solver.bcp_long_scan_stats();
    let stats = &mut *context.run_stats;
    let values = [
        ("learned", scan.learned_scans_by_len.as_slice()),
        (
            "learned_found_replacement",
            scan.learned_found_replacement_by_len.as_slice(),
        ),
        (
            "learned_no_replacement",
            scan.learned_no_replacement_by_len.as_slice(),
        ),
        ("learned_unit", scan.learned_unit_by_len.as_slice()),
        ("learned_conflict", scan.learned_conflict_by_len.as_slice()),
    ];
    for (metric, values) in values {
        insert_dimacs_bcp_bucket_value(stats, bucket, "bcp_long_scan", metric, values, index);
    }
}

fn insert_dimacs_bcp_saved_position_bucket(
    context: &mut DimacsStructuredStatistics<'_, '_, '_>,
    bucket: &str,
    index: usize,
) {
    let scan = context.solver.bcp_long_scan_stats();
    let stats = &mut *context.run_stats;
    let values = [
        (
            "eligible",
            scan.learned_no_replacement_saved_pos_eligible_by_len
                .as_slice(),
        ),
        (
            "writes",
            scan.learned_no_replacement_saved_pos_writes_by_len
                .as_slice(),
        ),
        (
            "skipped_current",
            scan.learned_no_replacement_saved_pos_skipped_current_by_len
                .as_slice(),
        ),
        (
            "unit",
            scan.learned_no_replacement_saved_pos_unit_by_len.as_slice(),
        ),
        (
            "conflict",
            scan.learned_no_replacement_saved_pos_conflict_by_len
                .as_slice(),
        ),
    ];
    for (metric, values) in values {
        insert_dimacs_bcp_bucket_value(
            stats,
            bucket,
            "bcp_learned_no_replacement_saved_pos",
            metric,
            values,
            index,
        );
    }
}

fn insert_dimacs_bcp_pressure_bucket(
    context: &mut DimacsStructuredStatistics<'_, '_, '_>,
    bucket: &str,
    index: usize,
) {
    let scan = context.solver.bcp_long_scan_stats();
    let stats = &mut *context.run_stats;
    let values = [
        (
            "scans",
            scan.learned_no_replacement_scan_pressure_scans_by_len
                .as_slice(),
        ),
        (
            "steps",
            scan.learned_no_replacement_scan_pressure_steps_by_len
                .as_slice(),
        ),
        (
            "start_false",
            scan.learned_no_replacement_scan_pressure_start_false_by_len
                .as_slice(),
        ),
        (
            "wrapped",
            scan.learned_no_replacement_scan_pressure_wrapped_by_len
                .as_slice(),
        ),
        (
            "unit",
            scan.learned_no_replacement_scan_pressure_unit_by_len
                .as_slice(),
        ),
        (
            "conflict",
            scan.learned_no_replacement_scan_pressure_conflict_by_len
                .as_slice(),
        ),
    ];
    for (metric, values) in values {
        insert_dimacs_bcp_bucket_value(
            stats,
            bucket,
            "bcp_learned_no_replacement_scan_pressure",
            metric,
            values,
            index,
        );
    }
}

fn insert_dimacs_bcp_long_scan_buckets(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    for (index, bucket) in ["6_8", "9_17", "18", "19_63", "64_plus"].iter().enumerate() {
        insert_dimacs_bcp_long_bucket_core(context, bucket, index);
        insert_dimacs_bcp_long_bucket_learned(context, bucket, index);
        insert_dimacs_bcp_saved_position_bucket(context, bucket, index);
        insert_dimacs_bcp_pressure_bucket(context, bucket, index);
    }
}

fn insert_dimacs_structured_bcp_buckets(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    insert_dimacs_bcp_budget_stats(context);
    insert_dimacs_bcp_pressure_reduction(context);
    insert_dimacs_bcp_pressure_retention(context);
    insert_dimacs_bcp_saved_position_stats(context);
    insert_dimacs_bcp_long_scan_buckets(context);
}
