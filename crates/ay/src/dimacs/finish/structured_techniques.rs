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
    let sweep = solver.sweep_stats();
    stats.insert("sat.sweep_rounds", sweep.rounds);
    stats.insert("sat.sweep_lits_rwt", sweep.literals_rewritten);
    stats.insert("sat.sweep_equivs", sweep.kitten_equivalences);
    stats.insert("sat.sweep_environments", sweep.kitten_environments);
    stats.insert("sat.sweep_backbone", sweep.kitten_backbone);
    stats.insert("sat.sweep_clauses_rwt", sweep.clauses_rewritten);
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
}

fn insert_dimacs_decomposition_techniques(context: &mut DimacsStructuredStatistics<'_, '_, '_>) {
    let solver = &*context.solver;
    let stats = &mut *context.run_stats;
    let decomposition = solver.decompose_stats();
    stats.insert("sat.decomp_rounds", decomposition.rounds);
    stats.insert("sat.decomp_subst", decomposition.substituted);
    insert_decompose_lrat_preflight_telemetry(stats, &solver.decompose_lrat_preflight_stats());
    let transred = solver.transred_stats();
    stats.insert("sat.transred_rounds", transred.rounds);
    stats.insert("sat.transred_cls_rm", transred.clauses_removed);
    let factor = solver.factor_stats();
    stats.insert("sat.factor_rounds", factor.rounds);
    stats.insert("sat.factor_count", factor.factored_count);
    let vivify = solver.vivify_stats();
    stats.insert("sat.vivify_examined", vivify.clauses_examined);
    stats.insert("sat.vivify_strengthened", vivify.clauses_strengthened);
    stats.insert("sat.vivify_lits_rm", vivify.literals_removed);
    stats.insert("sat.vivify_irred_examined", vivify.irred_examined);
    stats.insert("sat.vivify_irred_strengthened", vivify.irred_strengthened);
    stats.insert("sat.vivify_irred_lits_rm", vivify.irred_literals_removed);
    stats.insert("sat.vivify_irred_deleted", vivify.irred_deleted);
    stats.insert(
        "sat.vivify_irred_calls_preprocess",
        vivify.irred_calls_preprocess,
    );
    stats.insert("sat.vivify_irred_calls_inproc", vivify.irred_calls_inproc);
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
