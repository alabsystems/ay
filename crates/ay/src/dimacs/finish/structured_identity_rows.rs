// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

fn insert_dimacs_identity_fsw_rows(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let identity = context.solver.bcp_learned_1963_identity_stats(16);
    let stats = &mut *context.run_stats;
    for (index, row) in identity.fsw_rows.iter().enumerate() {
        let prefix = format!("sat.bcp_learned_1963_identity_fsw_row_{index}");
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

fn insert_dimacs_lrat_materialization_stats(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let materialization = context.solver.lrat_materialization_stats();
    let stats = &mut *context.run_stats;
    stats.insert(
        "sat.lrat_materialize_calls",
        materialization.materialize_calls,
    );
    stats.insert(
        "sat.lrat_materialize_minimize_calls",
        materialization.materialize_minimize_calls,
    );
    stats.insert(
        "sat.lrat_materialize_root_trail_entries",
        materialization.materialize_root_trail_entries,
    );
    stats.insert(
        "sat.lrat_materialize_minimize_root_trail_entries",
        materialization.materialize_minimize_root_trail_entries,
    );
    stats.insert(
        "sat.lrat_materialize_emitted_unit_lines",
        materialization.materialize_emitted_unit_lines,
    );
    stats.insert(
        "sat.lrat_materialize_minimize_emitted_unit_lines",
        materialization.materialize_minimize_emitted_unit_lines,
    );
    stats.insert(
        "sat.lrat_materialize_unit_hints",
        materialization.materialize_unit_hints,
    );
    stats.insert(
        "sat.lrat_materialize_minimize_unit_hints",
        materialization.materialize_minimize_unit_hints,
    );
    stats.insert(
        "sat.lrat_materialize_unit_max_hints",
        materialization.materialize_unit_max_hints,
    );
    stats.insert(
        "sat.lrat_materialize_minimize_unit_max_hints",
        materialization.materialize_minimize_unit_max_hints,
    );
    stats.insert(
        "sat.lrat_materialize_incomplete_chains",
        materialization.materialize_incomplete_chains,
    );
    stats.insert(
        "sat.lrat_materialize_minimize_incomplete_chains",
        materialization.materialize_minimize_incomplete_chains,
    );
    stats.insert(
        "sat.lrat_materialize_hidden_trusted_units",
        materialization.materialize_hidden_trusted_units,
    );
    stats.insert(
        "sat.lrat_unit_chain_calls",
        materialization.unit_chain_calls,
    );
    stats.insert(
        "sat.lrat_unit_chain_root_trail_entries",
        materialization.unit_chain_root_trail_entries,
    );
    stats.insert(
        "sat.lrat_unit_chain_hints",
        materialization.unit_chain_hints,
    );
    stats.insert(
        "sat.lrat_unit_chain_max_hints",
        materialization.unit_chain_max_hints,
    );
    stats.insert(
        "sat.lrat_unit_chain_missing_hints",
        materialization.unit_chain_missing_hints,
    );
    stats.insert("sat.jumped_reasons", context.solver.jumped_reasons());
}

fn insert_dimacs_structured_identity_rows(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    insert_dimacs_identity_fsw_rows(context);
    insert_dimacs_lrat_materialization_stats(context);
}
