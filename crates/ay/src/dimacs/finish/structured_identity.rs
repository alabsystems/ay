// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

fn insert_dimacs_fsw_identity_buckets(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let scan = context.solver.bcp_long_scan_stats();
    let stats = &mut *context.run_stats;
    let lbd_keys = ["lbd_0_2", "lbd_3_6", "lbd_7_10", "lbd_11_20", "lbd_21_plus"];
    for (index, bucket) in lbd_keys.iter().enumerate() {
        stats.insert(
            &format!("sat.bcp_learned_1963_fsw_unit_{bucket}"),
            scan.learned_1963_fsw_unit_by_lbd[index],
        );
        stats.insert(
            &format!("sat.bcp_learned_1963_fsw_conflict_{bucket}"),
            scan.learned_1963_fsw_conflict_by_lbd[index],
        );
        stats.insert(
            &format!("sat.bcp_learned_1963_fsw_unit_{bucket}_steps"),
            scan.learned_1963_fsw_unit_steps_by_lbd[index],
        );
        stats.insert(
            &format!("sat.bcp_learned_1963_fsw_conflict_{bucket}_steps"),
            scan.learned_1963_fsw_conflict_steps_by_lbd[index],
        );
    }
    let used_keys = ["used_0", "used_1", "used_2_4", "used_5_plus"];
    for (index, bucket) in used_keys.iter().enumerate() {
        stats.insert(
            &format!("sat.bcp_learned_1963_fsw_unit_{bucket}"),
            scan.learned_1963_fsw_unit_by_used[index],
        );
        stats.insert(
            &format!("sat.bcp_learned_1963_fsw_conflict_{bucket}"),
            scan.learned_1963_fsw_conflict_by_used[index],
        );
        stats.insert(
            &format!("sat.bcp_learned_1963_fsw_unit_{bucket}_steps"),
            scan.learned_1963_fsw_unit_steps_by_used[index],
        );
        stats.insert(
            &format!("sat.bcp_learned_1963_fsw_conflict_{bucket}_steps"),
            scan.learned_1963_fsw_conflict_steps_by_used[index],
        );
    }
}

fn insert_dimacs_fsw_repeat_buckets(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let scan = context.solver.bcp_long_scan_stats();
    let stats = &mut *context.run_stats;
    stats.insert(
        "sat.bcp_learned_1963_fsw_repeat_bucket_max",
        scan.learned_1963_fsw_repeat_bucket_max,
    );
    for index in 0..scan.learned_1963_fsw_repeat_by_bucket.len() {
        stats.insert(
            &format!("sat.bcp_learned_1963_fsw_repeat_bucket_{index}_count"),
            scan.learned_1963_fsw_repeat_by_bucket[index],
        );
        stats.insert(
            &format!("sat.bcp_learned_1963_fsw_repeat_bucket_{index}_steps"),
            scan.learned_1963_fsw_repeat_steps_by_bucket[index],
        );
    }
}

fn insert_dimacs_identity_summary(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let identity = context.solver.bcp_learned_1963_identity_stats(16);
    let stats = &mut *context.run_stats;
    stats.insert(
        SAT_BCP_LEARNED_1963_IDENTITY_ENABLED_KEY,
        u64::from(identity.enabled),
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_exact_rows",
        identity.exact_identity_rows,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_row_limit",
        identity.row_limit,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_total_scans",
        identity.total_scans,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_total_steps",
        identity.total_scan_steps,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_replacement_scans",
        identity.replacement_scans,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_replacement_steps",
        identity.replacement_steps,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_true_replacements",
        identity.true_replacements,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_unassigned_replacements",
        identity.unassigned_replacements,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_no_replacement_scans",
        identity.no_replacement_scans,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_no_replacement_steps",
        identity.no_replacement_steps,
    );
    stats.insert("sat.bcp_learned_1963_identity_unit", identity.unit);
    stats.insert("sat.bcp_learned_1963_identity_conflict", identity.conflict);
    stats.insert(
        "sat.bcp_learned_1963_identity_fsw_scans",
        identity.fsw_scans,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_fsw_steps",
        identity.fsw_steps,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_repeat_scans",
        identity.repeat_scans,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_repeat_steps",
        identity.repeat_steps,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_fsw_repeat_steps",
        identity.fsw_repeat_steps,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_topk_steps",
        identity.topk_scan_steps,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_topk_pressure_share_ppm",
        identity.topk_pressure_share_ppm,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_topk_fsw_steps",
        identity.topk_fsw_steps,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_topk_fsw_pressure_share_ppm",
        identity.topk_fsw_pressure_share_ppm,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_scans_per_conflict_x1000",
        identity.scans_per_conflict_x1000,
    );
    stats.insert(
        "sat.bcp_learned_1963_identity_steps_per_conflict_x1000",
        identity.steps_per_conflict_x1000,
    );
}

fn insert_dimacs_identity_distribution(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let identity = context.solver.bcp_learned_1963_identity_stats(16);
    let stats = &mut *context.run_stats;
    let age_keys = [
        "age_0_99",
        "age_100_999",
        "age_1000_9999",
        "age_10000_99999",
        "age_100000_plus",
    ];
    for (index, bucket) in age_keys.iter().enumerate() {
        stats.insert(
            &format!("sat.bcp_learned_1963_identity_{bucket}_steps"),
            identity.age_steps_by_bucket[index],
        );
    }
    for (index, bucket) in age_keys.iter().enumerate() {
        stats.insert(
            &format!("sat.bcp_learned_1963_identity_fsw_{bucket}_steps"),
            identity.fsw_age_steps_by_bucket[index],
        );
    }
    let lbd_keys = ["lbd_0_2", "lbd_3_6", "lbd_7_10", "lbd_11_20", "lbd_21_plus"];
    for (index, bucket) in lbd_keys.iter().enumerate() {
        stats.insert(
            &format!("sat.bcp_learned_1963_identity_{bucket}_steps"),
            identity.lbd_steps_by_bucket[index],
        );
    }
    let used_keys = ["used_0", "used_1", "used_2_4", "used_5_plus"];
    for (index, bucket) in used_keys.iter().enumerate() {
        stats.insert(
            &format!("sat.bcp_learned_1963_identity_{bucket}_steps"),
            identity.used_steps_by_bucket[index],
        );
    }
    let activity_keys = [
        "activity_0",
        "activity_1_999",
        "activity_1000_9999",
        "activity_10000_plus",
    ];
    for (index, bucket) in activity_keys.iter().enumerate() {
        stats.insert(
            &format!("sat.bcp_learned_1963_identity_{bucket}_steps"),
            identity.activity_steps_by_bucket[index],
        );
    }
}

fn insert_dimacs_identity_rows(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let identity = context.solver.bcp_learned_1963_identity_stats(16);
    let stats = &mut *context.run_stats;
    for (index, row) in identity.rows.iter().enumerate() {
        let prefix = format!("sat.bcp_learned_1963_identity_row_{index}");
        stats.insert(&format!("{prefix}_clause_id"), row.clause_id);
        stats.insert(&format!("{prefix}_clause_offset"), row.clause_offset);
        stats.insert(&format!("{prefix}_clause_len"), row.clause_len);
        stats.insert(&format!("{prefix}_birth_conflict"), row.birth_conflict);
        stats.insert(&format!("{prefix}_last_conflict"), row.last_conflict);
        stats.insert(&format!("{prefix}_age"), row.age_conflicts);
        stats.insert(&format!("{prefix}_lbd"), row.lbd);
        stats.insert(&format!("{prefix}_used"), row.used);
        stats.insert(&format!("{prefix}_activity_milli"), row.activity_milli);
        stats.insert(&format!("{prefix}_scans"), row.scans);
        stats.insert(&format!("{prefix}_steps"), row.scan_steps);
        stats.insert(
            &format!("{prefix}_replacement_scans"),
            row.replacement_scans,
        );
        stats.insert(
            &format!("{prefix}_replacement_steps"),
            row.replacement_steps,
        );
        stats.insert(
            &format!("{prefix}_true_replacements"),
            row.true_replacements,
        );
        stats.insert(
            &format!("{prefix}_unassigned_replacements"),
            row.unassigned_replacements,
        );
        stats.insert(
            &format!("{prefix}_no_replacement_scans"),
            row.no_replacement_scans,
        );
        stats.insert(
            &format!("{prefix}_no_replacement_steps"),
            row.no_replacement_steps,
        );
        stats.insert(&format!("{prefix}_unit"), row.unit);
        stats.insert(&format!("{prefix}_conflict"), row.conflict);
        stats.insert(
            &format!("{prefix}_saved_start_false"),
            row.saved_start_false,
        );
        stats.insert(&format!("{prefix}_wrapped"), row.wrapped);
        stats.insert(&format!("{prefix}_fsw"), row.fsw);
        stats.insert(&format!("{prefix}_fsw_steps"), row.fsw_steps);
        stats.insert(&format!("{prefix}_fsw_unit_steps"), row.fsw_unit_steps);
        stats.insert(
            &format!("{prefix}_fsw_conflict_steps"),
            row.fsw_conflict_steps,
        );
        stats.insert(&format!("{prefix}_repeat_scans"), row.repeat_scans);
        stats.insert(&format!("{prefix}_repeat_steps"), row.repeat_steps);
        stats.insert(&format!("{prefix}_fsw_repeat_steps"), row.fsw_repeat_steps);
        stats.insert(&format!("{prefix}_max_scan_steps"), row.max_scan_steps);
    }
}

fn insert_dimacs_structured_identity(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    insert_dimacs_fsw_identity_buckets(context);
    insert_dimacs_fsw_repeat_buckets(context);
    insert_dimacs_identity_summary(context);
    insert_dimacs_identity_distribution(context);
    insert_dimacs_identity_rows(context);
}
