// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

fn insert_dimacs_bve_core(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let solver = &*context.solver;
    let bve = solver.bve_stats();
    let stats = &mut *context.run_stats;
    stats.insert(
        "sat.bve_occ_delta_enabled",
        u64::from(solver.is_bve_occ_delta_validation_enabled()),
    );
    stats.insert(
        "sat.bve_occ_saved_state_reuse_enabled",
        u64::from(solver.is_bve_occ_saved_state_reuse_enabled()),
    );
    stats.insert("sat.bve_eliminated", bve.vars_eliminated);
    stats.insert("sat.bve_cls_removed", bve.clauses_removed);
    stats.insert("sat.bve_resolvents", bve.resolvents_added);
    stats.insert("sat.bve_tautologies", bve.tautologies_skipped);
    stats.insert("sat.bve_bw_subsumed", bve.backward_subsumed);
    stats.insert("sat.bve_bw_strengthened", bve.backward_strengthened);
    stats.insert("sat.bve_bw_units", bve.backward_units);
    stats.insert("sat.bve_fast_elim_vars", bve.fast_elim_vars);
    stats.insert("sat.bve_fast_elim_clauses", bve.fast_elim_clauses);
}

fn insert_dimacs_bve_preflight_core(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let bve = context.solver.bve_stats();
    let stats = &mut *context.run_stats;
    stats.insert(
        "sat.bve_lrat_preflight_rejected",
        bve.lrat_preflight_rejected,
    );
    stats.insert(
        "sat.bve_lrat_preflight_missing_proof_manager",
        bve.lrat_preflight_missing_proof_manager,
    );
    stats.insert(
        "sat.bve_lrat_preflight_missing_or_hidden_source_id",
        bve.lrat_preflight_missing_or_hidden_source_id,
    );
    stats.insert(
        "sat.bve_lrat_preflight_deletion_target_not_live",
        bve.lrat_preflight_deletion_target_not_live,
    );
    stats.insert(
        "sat.bve_lrat_preflight_malformed_strengthening",
        bve.lrat_preflight_malformed_strengthening,
    );
    stats.insert(
        "sat.bve_lrat_preflight_malformed_resolvent",
        bve.lrat_preflight_malformed_resolvent,
    );
    stats.insert(
        "sat.bve_lrat_preflight_replacement_cleanup_unit",
        bve.lrat_preflight_replacement_cleanup_unit,
    );
    stats.insert(
        "sat.bve_lrat_preflight_planned_add_rejected",
        bve.lrat_preflight_planned_add_rejected,
    );
    stats.insert(
        "sat.bve_lrat_preflight_planned_not_lrat",
        bve.lrat_preflight_planned_not_lrat,
    );
    stats.insert(
        "sat.bve_lrat_preflight_planned_lrat_blocked",
        bve.lrat_preflight_planned_lrat_blocked,
    );
    stats.insert(
        "sat.bve_lrat_preflight_planned_io_failed",
        bve.lrat_preflight_planned_io_failed,
    );
    stats.insert(
        "sat.bve_lrat_preflight_planned_pending_deletions",
        bve.lrat_preflight_planned_pending_deletions,
    );
    stats.insert(
        "sat.bve_lrat_preflight_planned_output_id_mismatch",
        bve.lrat_preflight_planned_output_id_mismatch,
    );
    stats.insert(
        "sat.bve_lrat_preflight_planned_invalid_clause",
        bve.lrat_preflight_planned_invalid_clause,
    );
}

fn insert_dimacs_bve_preflight_hints(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let bve = context.solver.bve_stats();
    let stats = &mut *context.run_stats;
    stats.insert(
        "sat.bve_lrat_preflight_planned_suppressed_axiom",
        bve.lrat_preflight_planned_suppressed_axiom,
    );
    stats.insert(
        "sat.bve_lrat_preflight_planned_hidden_trusted_unit",
        bve.lrat_preflight_planned_hidden_trusted_unit,
    );
    stats.insert(
        "sat.bve_lrat_preflight_planned_missing_hints",
        bve.lrat_preflight_planned_missing_hints,
    );
    stats.insert(
        "sat.bve_lrat_preflight_planned_zero_hint",
        bve.lrat_preflight_planned_zero_hint,
    );
    stats.insert(
        "sat.bve_lrat_preflight_planned_duplicate_hint",
        bve.lrat_preflight_planned_duplicate_hint,
    );
    stats.insert(
        "sat.bve_lrat_preflight_planned_unknown_hint",
        bve.lrat_preflight_planned_unknown_hint,
    );
    stats.insert(
        "sat.bve_lrat_preflight_planned_trusted_hint",
        bve.lrat_preflight_planned_trusted_hint,
    );
    stats.insert(
        "sat.bve_lrat_preflight_planned_backward_reserved_hint",
        bve.lrat_preflight_planned_backward_reserved_hint,
    );
    stats.insert(
        "sat.bve_lrat_preflight_planned_id_overflow",
        bve.lrat_preflight_planned_id_overflow,
    );
}

fn insert_dimacs_occurrence_stats(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let bve = context.solver.bve_stats();
    let stats = &mut *context.run_stats;
    stats.insert(
        "sat.occ_epoch_fastpath_refreshes",
        bve.occ_epoch_fastpath_refreshes,
    );
    stats.insert(
        "sat.occ_delta_validated_refreshes",
        bve.occ_delta_validated_refreshes,
    );
    stats.insert(
        "sat.occ_delta_validation_fallbacks",
        bve.occ_delta_validation_fallbacks,
    );
    stats.insert(
        "sat.occ_delta_uncertified_fallbacks",
        bve.occ_delta_uncertified_fallbacks,
    );
    stats.insert(
        "sat.occ_delta_oversize_fallbacks",
        bve.occ_delta_oversize_fallbacks,
    );
    stats.insert(
        "sat.occ_delta_touched_clauses",
        bve.occ_delta_touched_clauses,
    );
    stats.insert("sat.occ_delta_touched_lits", bve.occ_delta_touched_lits);
    stats.insert(
        "sat.occ_delta_occ_entries_checked",
        bve.occ_delta_occ_entries_checked,
    );
    stats.insert(
        "sat.occ_delta_missing_entries",
        bve.occ_delta_missing_entries,
    );
    stats.insert(
        "sat.occ_delta_stale_live_entries",
        bve.occ_delta_stale_live_entries,
    );
    stats.insert(
        "sat.occ_delta_live_learned_entries",
        bve.occ_delta_live_learned_entries,
    );
    stats.insert(
        "sat.occ_saved_state_round_end_drops",
        bve.occ_saved_state_round_end_drops,
    );
    stats.insert(
        "sat.occ_saved_state_round_end_retains",
        bve.occ_saved_state_round_end_retains,
    );
}

fn insert_dimacs_simplification_techniques(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let solver = &*context.solver;
    let stats = &mut *context.run_stats;
    let gates = solver.gate_stats();
    stats.insert("sat.gate_and", gates.and_gates);
    stats.insert("sat.gate_xor", gates.xor_gates);
    stats.insert("sat.gate_equiv", gates.equivalences);
    stats.insert("sat.gate_ite", gates.ite_gates);
    stats.insert("sat.probe_failed", solver.probe_stats().failed);
    let congruence = solver.congruence_stats();
    stats.insert("sat.cong_rounds", congruence.rounds);
    stats.insert("sat.cong_equivs", congruence.equivalences_found);
    stats.insert("sat.cong_lits_rwt", congruence.literals_rewritten);
    stats.insert("sat.cong_non_rup_equivs", congruence.non_rup_equivalences);
    stats.insert("sat.cong_xor_ladders", congruence.xor_ladders_emitted);
    stats.insert(
        "sat.cong_xor_ladder_failures",
        congruence.xor_ladder_failures,
    );
    let sweep = solver.sweep_stats();
    stats.insert("sat.sweep_rounds", sweep.rounds);
    stats.insert("sat.sweep_lits_rwt", sweep.literals_rewritten);
    stats.insert("sat.sweep_equivs", sweep.kitten_equivalences);
    stats.insert("sat.sweep_environments", sweep.kitten_environments);
    stats.insert("sat.sweep_backbone", sweep.kitten_backbone);
    stats.insert("sat.sweep_clauses_rwt", sweep.clauses_rewritten);
    stats.insert("sat.sweep_completed_passes", sweep.completed_passes);
    stats.insert("sat.sweep_kitten_solves", sweep.kitten_solves);
    stats.insert("sat.sweep_kitten_propagations", sweep.kitten_propagations);
    let symmetry = solver.symmetry_report();
    stats.insert("sat.symmetry_runs", symmetry.runs);
    stats.insert("sat.symmetry_candidate_pairs", symmetry.candidate_pairs);
    stats.insert("sat.symmetry_pairs", symmetry.pairs_detected);
    stats.insert("sat.symmetry_sb_clauses", symmetry.sb_clauses_added);
    stats.insert("sat.symmetry_groups", symmetry.groups_nontrivial);
    stats.insert(
        "sat.symmetry_groups_over_budget",
        symmetry.groups_over_budget,
    );
    stats.insert("sat.symmetry_largest_group", symmetry.largest_group);
    stats.insert("sat.symmetry_chain_generators", symmetry.chain_generators);
    stats.insert("sat.symmetry_chain_base_len", symmetry.chain_base_len);
    stats.insert("sat.symmetry_chain_orbits", symmetry.chain_orbits);
    stats.insert("sat.symmetry_fixings", symmetry.fixcut_fixings);
    stats.insert("sat.symmetry_cuts", symmetry.fixcut_cuts);
    stats.insert("sat.symmetry_fixcut_levels", symmetry.fixcut_levels);
    stats.insert("sat.symmetry_fixcut_work", symmetry.fixcut_work);
    stats.insert("sat.symmetry_fixcut_budget_hit", symmetry.fixcut_budget_hit);
    stats.insert("sat.symmetry_fixcut_rounds", symmetry.fixcut_rounds);
}

fn insert_dimacs_decomposition_techniques(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let solver = &*context.solver;
    let stats = &mut *context.run_stats;
    let decomposition = solver.decompose_stats();
    stats.insert("sat.decomp_rounds", decomposition.rounds);
    stats.insert("sat.decomp_subst", decomposition.substituted);
    stats.insert(
        "sat.decomp_stale_watches_skipped",
        decomposition.stale_binary_watches_skipped,
    );
    stats.insert(
        "sat.decomp_chained_reprs",
        decomposition.chained_representatives,
    );
    stats.insert(
        "sat.decomp_chain_refusals",
        decomposition.chained_rounds_refused,
    );
    insert_decompose_lrat_preflight_telemetry(stats, &solver.decompose_lrat_preflight_stats());
    let transred = solver.transred_stats();
    stats.insert("sat.transred_rounds", transred.rounds);
    stats.insert("sat.transred_cls_rm", transred.clauses_removed);
    let factor = solver.factor_stats();
    stats.insert("sat.factor_rounds", factor.rounds);
    stats.insert("sat.factor_count", factor.factored_count);
    stats.insert("sat.factor_extension_vars", factor.extension_vars);
    stats.insert("sat.factor_init_calls", factor.init_calls);
    stats.insert("sat.factor_init_ticks", factor.init_ticks);
    stats.insert("sat.factor_init_undrained", factor.init_undrained);
    stats.insert("sat.factor_stops", solver.num_factor_stops());
    for (tag, n) in solver.bve_skip_breakdown() {
        stats.insert(&format!("sat.inproc_bve_skip_{tag}"), n);
    }
    for (tag, n) in solver.bve_gate_skip_breakdown() {
        stats.insert(&format!("sat.inproc_bve_gate_{tag}"), n);
    }
    let (bve_next_conflict, bve_phases, bve_unproductive) = solver.bve_schedule_state();
    stats.insert("sat.bve_next_conflict", bve_next_conflict);
    stats.insert("sat.bve_phases", bve_phases);
    stats.insert("sat.bve_consecutive_unproductive", bve_unproductive);
    stats.insert(
        "sat.bve_ext_cooccur_skips",
        solver.num_bve_ext_cooccur_skips(),
    );
    let [fast, binary_product, over_bound, resolved, max_bound] = solver.bve_rejection_profile();
    stats.insert("sat.bve_rej_fast_limits", fast);
    stats.insert("sat.bve_rej_binary_product", binary_product);
    stats.insert("sat.bve_rej_over_bound", over_bound);
    stats.insert("sat.bve_candidates_resolved", resolved);
    stats.insert("sat.bve_max_growth_bound", max_bound);
    let (gates_proved_mixed, [shape, pairs, incomplete, budget]) = solver.bve_gate_profile();
    stats.insert("sat.bve_gates_proved_mixed", gates_proved_mixed);
    stats.insert(
        "sat.bve_gates_unproved",
        shape + pairs + incomplete + budget,
    );
    stats.insert("sat.bve_gates_unproved_shape", shape);
    stats.insert("sat.bve_gates_unproved_pairs", pairs);
    stats.insert("sat.bve_gates_unproved_incomplete", incomplete);
    stats.insert("sat.bve_gates_unproved_budget", budget);
    let (sbva_rounds, sbva_groups, sbva_extension_vars) = solver.sbva_counts();
    stats.insert("sat.sbva_rounds", sbva_rounds);
    stats.insert("sat.sbva_groups", sbva_groups);
    stats.insert("sat.sbva_extension_vars", sbva_extension_vars);
    let (factor_density_skips, sbva_density_skips) = solver.density_band_skips();
    stats.insert("sat.factor_density_skips", factor_density_skips);
    stats.insert("sat.sbva_density_skips", sbva_density_skips);
    let vivify = solver.vivify_stats();
    stats.insert("sat.vivify_examined", vivify.clauses_examined);
    stats.insert("sat.vivify_generations", vivify.generations);
    stats.insert("sat.vivify_strengthened", vivify.clauses_strengthened);
    stats.insert("sat.vivify_lits_rm", vivify.literals_removed);
    stats.insert("sat.vivify_satisfied", vivify.clauses_satisfied);
    for (i, name) in ["core", "tier2", "other", "irred"].iter().enumerate() {
        stats.insert(
            &format!("sat.vivify_{name}_examined"),
            vivify.tier_examined[i],
        );
        stats.insert(
            &format!("sat.vivify_{name}_vivified"),
            vivify.tier_vivified[i],
        );
    }
    stats.insert("sat.vivify_inline_subsumed", vivify.inline_subsumed);
    stats.insert("sat.vivify_analysis_subsumed", vivify.analysis_subsumed);
    stats.insert("sat.vivify_asym_deleted", vivify.asym_deleted);
    stats.insert("sat.vivify_irred_examined", vivify.irred_examined);
    stats.insert("sat.vivify_irred_strengthened", vivify.irred_strengthened);
    stats.insert("sat.vivify_irred_lits_rm", vivify.irred_literals_removed);
    stats.insert("sat.vivify_irred_deleted", vivify.irred_deleted);
    stats.insert(
        "sat.vivify_irred_calls_preprocess",
        vivify.irred_calls_preprocess,
    );
    stats.insert("sat.vivify_irred_calls_inproc", vivify.irred_calls_inproc);
    stats.insert("sat.vivify_inproc_admitted", vivify.inproc_admitted);
    stats.insert(
        "sat.vivify_inproc_skip_small_dense",
        vivify.inproc_skip_small_dense,
    );
    stats.insert(
        "sat.vivify_inproc_skip_interval",
        vivify.inproc_skip_interval,
    );
    stats.insert(
        "sat.vivify_inproc_skip_threshold",
        vivify.inproc_skip_threshold,
    );
    stats.insert("sat.vivify_preprocess_rounds", vivify.preprocess_rounds);
    stats.insert("sat.vivify_preprocess_ticks", vivify.preprocess_ticks);
    stats.insert(
        "sat.vivify_preprocess_stop_converged",
        vivify.preprocess_stop_converged,
    );
    stats.insert(
        "sat.vivify_preprocess_stop_budget",
        vivify.preprocess_stop_budget,
    );
    stats.insert(
        "sat.vivify_preprocess_stop_rounds",
        vivify.preprocess_stop_rounds,
    );
    stats.insert(
        "sat.vivify_preprocess_stop_deadline",
        vivify.preprocess_stop_deadline,
    );
}

fn insert_dimacs_subsumption_techniques(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let solver = &*context.solver;
    let stats = &mut *context.run_stats;
    let subsumption = solver.subsume_stats();
    stats.insert("sat.subsumed", subsumption.forward_subsumed);
    stats.insert("sat.strengthened", subsumption.strengthened_clauses);
    stats.insert("sat.total_subsumed", solver.total_subsumed());
    stats.insert("sat.bve_bw_subsumed", solver.bve_stats().backward_subsumed);
    stats.insert("sat.otfs_subsumed", solver.otfs_clause_subsumed());
    stats.insert("sat.eager_subsumed", solver.num_eager_subsumptions());
    stats.insert(
        "sat.congruence_subsumed",
        solver.congruence_stats().congruence_subsumed,
    );
    stats.insert("sat.dedup_deleted", solver.dedup_deleted());
    let bce = solver.bce_stats();
    stats.insert("sat.bce_rounds", bce.rounds);
    stats.insert("sat.bce_eliminated", bce.clauses_eliminated);
    let cce = solver.cce_stats();
    stats.insert("sat.cce_rounds", cce.rounds);
    stats.insert("sat.cce_blocked", cce.blocked);
    let htr = solver.htr_stats();
    stats.insert("sat.htr_rounds", htr.rounds);
    stats.insert("sat.htr_ternary", htr.ternary_resolvents);
    stats.insert("sat.htr_binary", htr.binary_resolvents);
    let conditioning = solver.conditioning_stats();
    stats.insert("sat.cond_rounds", conditioning.rounds);
    stats.insert("sat.cond_eliminated", conditioning.clauses_eliminated);
}

fn insert_dimacs_structured_techniques(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    insert_dimacs_bve_core(context);
    insert_dimacs_bve_preflight_core(context);
    insert_dimacs_bve_preflight_hints(context);
    insert_dimacs_occurrence_stats(context);
    insert_dimacs_simplification_techniques(context);
    insert_dimacs_decomposition_techniques(context);
    insert_dimacs_subsumption_techniques(context);
}
