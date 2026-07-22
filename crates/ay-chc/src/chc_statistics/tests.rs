// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_merge_additive_fields() {
    let mut a = ChcStatistics {
        iterations: 10,
        lemmas_learned: 5,
        max_frame: 3,
        restarts: 1,
        smt_unknowns: 2,
        cache_hits: 4,
        cache_model_rejections: 3,
        cache_solver_calls: 20,
        trust_proof_fallbacks: 1,
        native_code_helper_compile_attempts: 3,
        native_code_helper_compile_successes: 2,
        native_code_helper_compile_failures: 1,
        native_code_helper_evaluations: 7,
        native_code_helper_deopts: 1,
        native_code_helper_fallbacks: 4,
        native_code_helper_missing_var_fallbacks: 2,
        native_code_helper_interpreter_confirmations: 3,
        native_code_helper_trusted_true_results: 2,
        native_code_helper_applications: 5,
        tla_transition_cluster_applications: 2,
        symbolic_scalarization_projected_cells: 3,
        symbolic_scalarization_multi_cell_args: 1,
        lra_affine_original_clause_validation_attempts: 3,
        lra_affine_original_clause_validation_queries: 9,
        lra_affine_original_clause_validation_successes: 1,
        lra_affine_original_clause_validation_failures: 1,
        lra_affine_original_clause_validation_unknowns: 1,
        deterministic_bv_bool_transition_attempts: 3,
        deterministic_bv_bool_transition_recognized: 2,
        deterministic_bv_bool_transition_bmc_unsafe_validated: 1,
        deterministic_bv_bool_transition_kind_safe_validated: 1,
        deterministic_bv_bool_transition_kind_unsafe_validated: 0,
        deterministic_bv_bool_transition_bool_control_safe_validated: 1,
        deterministic_bv_bool_transition_validation_rejections: 2,
        accelerated_summary_modular_chain_summary_candidates: 2,
        accelerated_summary_modular_chain_family_summary_candidates: 2,
        accelerated_summary_trp_family_summary_candidates: 3,
        accelerated_summary_trp_affine_constant_delta_family_summaries: 1,
        accelerated_summary_trp_polynomial_closed_form_family_summaries: 1,
        accelerated_summary_trp_affine_preserved_difference_family_summaries: 1,
    };
    let b = ChcStatistics {
        iterations: 20,
        lemmas_learned: 15,
        max_frame: 7,
        restarts: 2,
        smt_unknowns: 1,
        cache_hits: 6,
        cache_model_rejections: 2,
        cache_solver_calls: 30,
        trust_proof_fallbacks: 2,
        native_code_helper_compile_attempts: 5,
        native_code_helper_compile_successes: 4,
        native_code_helper_compile_failures: 1,
        native_code_helper_evaluations: 11,
        native_code_helper_deopts: 2,
        native_code_helper_fallbacks: 6,
        native_code_helper_missing_var_fallbacks: 1,
        native_code_helper_interpreter_confirmations: 4,
        native_code_helper_trusted_true_results: 5,
        native_code_helper_applications: 8,
        tla_transition_cluster_applications: 3,
        symbolic_scalarization_projected_cells: 5,
        symbolic_scalarization_multi_cell_args: 2,
        lra_affine_original_clause_validation_attempts: 4,
        lra_affine_original_clause_validation_queries: 11,
        lra_affine_original_clause_validation_successes: 2,
        lra_affine_original_clause_validation_failures: 1,
        lra_affine_original_clause_validation_unknowns: 1,
        deterministic_bv_bool_transition_attempts: 5,
        deterministic_bv_bool_transition_recognized: 4,
        deterministic_bv_bool_transition_bmc_unsafe_validated: 2,
        deterministic_bv_bool_transition_kind_safe_validated: 3,
        deterministic_bv_bool_transition_kind_unsafe_validated: 1,
        deterministic_bv_bool_transition_bool_control_safe_validated: 2,
        deterministic_bv_bool_transition_validation_rejections: 1,
        accelerated_summary_modular_chain_summary_candidates: 5,
        accelerated_summary_modular_chain_family_summary_candidates: 6,
        accelerated_summary_trp_family_summary_candidates: 4,
        accelerated_summary_trp_affine_constant_delta_family_summaries: 2,
        accelerated_summary_trp_polynomial_closed_form_family_summaries: 1,
        accelerated_summary_trp_affine_preserved_difference_family_summaries: 1,
    };
    a.merge(&b);
    assert_eq!(a.iterations, 30);
    assert_eq!(a.lemmas_learned, 20);
    assert_eq!(a.restarts, 3);
    assert_eq!(a.smt_unknowns, 3);
    assert_eq!(a.cache_hits, 10);
    assert_eq!(a.cache_model_rejections, 5);
    assert_eq!(a.cache_solver_calls, 50);
    assert_eq!(a.trust_proof_fallbacks, 3);
    assert_eq!(a.native_code_helper_compile_attempts, 8);
    assert_eq!(a.native_code_helper_compile_successes, 6);
    assert_eq!(a.native_code_helper_compile_failures, 2);
    assert_eq!(a.native_code_helper_evaluations, 18);
    assert_eq!(a.native_code_helper_deopts, 3);
    assert_eq!(a.native_code_helper_fallbacks, 10);
    assert_eq!(a.native_code_helper_missing_var_fallbacks, 3);
    assert_eq!(a.native_code_helper_interpreter_confirmations, 7);
    assert_eq!(a.native_code_helper_trusted_true_results, 7);
    assert_eq!(a.native_code_helper_applications, 13);
    assert_eq!(a.tla_transition_cluster_applications, 5);
    assert_eq!(a.symbolic_scalarization_projected_cells, 8);
    assert_eq!(a.symbolic_scalarization_multi_cell_args, 3);
    assert_eq!(a.lra_affine_original_clause_validation_attempts, 7);
    assert_eq!(a.lra_affine_original_clause_validation_queries, 20);
    assert_eq!(a.lra_affine_original_clause_validation_successes, 3);
    assert_eq!(a.lra_affine_original_clause_validation_failures, 2);
    assert_eq!(a.lra_affine_original_clause_validation_unknowns, 2);
    assert_eq!(a.deterministic_bv_bool_transition_attempts, 8);
    assert_eq!(a.deterministic_bv_bool_transition_recognized, 6);
    assert_eq!(a.deterministic_bv_bool_transition_bmc_unsafe_validated, 3);
    assert_eq!(a.deterministic_bv_bool_transition_kind_safe_validated, 4);
    assert_eq!(a.deterministic_bv_bool_transition_kind_unsafe_validated, 1);
    assert_eq!(
        a.deterministic_bv_bool_transition_bool_control_safe_validated,
        3
    );
    assert_eq!(a.deterministic_bv_bool_transition_validation_rejections, 3);
    assert_eq!(a.accelerated_summary_modular_chain_summary_candidates, 7);
    assert_eq!(
        a.accelerated_summary_modular_chain_family_summary_candidates,
        8
    );
    assert_eq!(a.accelerated_summary_trp_family_summary_candidates, 7);
    assert_eq!(
        a.accelerated_summary_trp_affine_constant_delta_family_summaries,
        3
    );
    assert_eq!(
        a.accelerated_summary_trp_polynomial_closed_form_family_summaries,
        2
    );
    assert_eq!(
        a.accelerated_summary_trp_affine_preserved_difference_family_summaries,
        2
    );
}

#[test]
fn test_merge_max_frame_takes_maximum() {
    let mut a = ChcStatistics {
        max_frame: 10,
        ..Default::default()
    };
    let b = ChcStatistics {
        max_frame: 5,
        ..Default::default()
    };
    a.merge(&b);
    assert_eq!(a.max_frame, 10, "max_frame should keep larger value");

    let mut c = ChcStatistics {
        max_frame: 3,
        ..Default::default()
    };
    let d = ChcStatistics {
        max_frame: 8,
        ..Default::default()
    };
    c.merge(&d);
    assert_eq!(c.max_frame, 8, "max_frame should take other's larger value");
}

#[test]
fn test_merge_with_default_is_identity() {
    let a = ChcStatistics {
        iterations: 42,
        lemmas_learned: 7,
        max_frame: 3,
        restarts: 1,
        smt_unknowns: 0,
        cache_hits: 2,
        cache_model_rejections: 1,
        cache_solver_calls: 10,
        trust_proof_fallbacks: 1,
        native_code_helper_applications: 2,
        tla_transition_cluster_applications: 1,
        ..Default::default()
    };
    let mut b = a.clone();
    b.merge(&ChcStatistics::default());
    assert_eq!(b.iterations, a.iterations);
    assert_eq!(b.lemmas_learned, a.lemmas_learned);
    assert_eq!(b.max_frame, a.max_frame);
    assert_eq!(b.cache_solver_calls, a.cache_solver_calls);
}

#[test]
fn test_from_solver_stats_conversion() {
    let s = SolverStats {
        iterations: 100,
        lemmas_learned: 50,
        max_frame: 12,
        restart_count: 3,
        smt_unknowns: 5,
        implication_cache_hits: 20,
        implication_model_rejections: 10,
        implication_solver_calls: 80,
        chc_native_code_helper_compile_attempts: 6,
        chc_native_code_helper_compile_successes: 4,
        chc_native_code_helper_compile_failures: 2,
        chc_native_code_helper_evaluations: 11,
        chc_native_code_helper_deopts: 3,
        chc_native_code_helper_fallbacks: 5,
        chc_native_code_helper_missing_var_fallbacks: 1,
        chc_native_code_helper_interpreter_confirmations: 2,
        chc_native_code_helper_trusted_true_results: 7,
        chc_native_code_helper_applications: 8,
        chc_tla_transition_cluster_applications: 9,
        symbolic_scalarization_projected_cells: 13,
        symbolic_scalarization_multi_cell_args: 2,
        ..Default::default()
    };
    let chc: ChcStatistics = s.into();
    assert_eq!(chc.iterations, 100);
    assert_eq!(chc.lemmas_learned, 50);
    assert_eq!(chc.max_frame, 12);
    assert_eq!(chc.restarts, 3);
    assert_eq!(chc.smt_unknowns, 5);
    assert_eq!(chc.cache_hits, 20);
    assert_eq!(chc.cache_model_rejections, 10);
    assert_eq!(chc.cache_solver_calls, 80);
    assert_eq!(chc.native_code_helper_compile_attempts, 6);
    assert_eq!(chc.native_code_helper_compile_successes, 4);
    assert_eq!(chc.native_code_helper_compile_failures, 2);
    assert_eq!(chc.native_code_helper_evaluations, 11);
    assert_eq!(chc.native_code_helper_deopts, 3);
    assert_eq!(chc.native_code_helper_fallbacks, 5);
    assert_eq!(chc.native_code_helper_missing_var_fallbacks, 1);
    assert_eq!(chc.native_code_helper_interpreter_confirmations, 2);
    assert_eq!(chc.native_code_helper_trusted_true_results, 7);
    assert_eq!(chc.native_code_helper_applications, 8);
    assert_eq!(chc.tla_transition_cluster_applications, 9);
    assert_eq!(chc.symbolic_scalarization_projected_cells, 13);
    assert_eq!(chc.symbolic_scalarization_multi_cell_args, 2);
    assert_eq!(chc.lra_affine_original_clause_validation_attempts, 0);
    assert_eq!(chc.lra_affine_original_clause_validation_queries, 0);
    assert_eq!(chc.lra_affine_original_clause_validation_successes, 0);
    assert_eq!(chc.lra_affine_original_clause_validation_failures, 0);
    assert_eq!(chc.lra_affine_original_clause_validation_unknowns, 0);
    assert_eq!(chc.deterministic_bv_bool_transition_attempts, 0);
    assert_eq!(chc.deterministic_bv_bool_transition_recognized, 0);
    assert_eq!(chc.deterministic_bv_bool_transition_bmc_unsafe_validated, 0);
    assert_eq!(chc.deterministic_bv_bool_transition_kind_safe_validated, 0);
    assert_eq!(
        chc.deterministic_bv_bool_transition_kind_unsafe_validated,
        0
    );
    assert_eq!(
        chc.deterministic_bv_bool_transition_bool_control_safe_validated,
        0
    );
    assert_eq!(
        chc.deterministic_bv_bool_transition_validation_rejections,
        0
    );
    assert_eq!(chc.accelerated_summary_modular_chain_summary_candidates, 0);
    assert_eq!(
        chc.accelerated_summary_modular_chain_family_summary_candidates,
        0
    );
    assert_eq!(chc.accelerated_summary_trp_family_summary_candidates, 0);
    assert_eq!(
        chc.accelerated_summary_trp_affine_constant_delta_family_summaries,
        0
    );
    assert_eq!(
        chc.accelerated_summary_trp_polynomial_closed_form_family_summaries,
        0
    );
    assert_eq!(
        chc.accelerated_summary_trp_affine_preserved_difference_family_summaries,
        0
    );
}

#[test]
fn test_merge_saturates_on_overflow() {
    let mut a = ChcStatistics {
        iterations: u64::MAX - 1,
        lemmas_learned: u64::MAX - 2,
        max_frame: 1,
        restarts: u64::MAX - 3,
        smt_unknowns: u64::MAX - 4,
        cache_hits: u64::MAX - 5,
        cache_model_rejections: u64::MAX - 6,
        cache_solver_calls: u64::MAX - 7,
        trust_proof_fallbacks: u64::MAX - 8,
        native_code_helper_compile_attempts: u64::MAX - 9,
        native_code_helper_compile_successes: u64::MAX - 10,
        native_code_helper_compile_failures: u64::MAX - 11,
        native_code_helper_evaluations: u64::MAX - 12,
        native_code_helper_deopts: u64::MAX - 13,
        native_code_helper_fallbacks: u64::MAX - 14,
        native_code_helper_missing_var_fallbacks: u64::MAX - 15,
        native_code_helper_interpreter_confirmations: u64::MAX - 16,
        native_code_helper_trusted_true_results: u64::MAX - 17,
        native_code_helper_applications: u64::MAX - 18,
        tla_transition_cluster_applications: u64::MAX - 19,
        symbolic_scalarization_projected_cells: u64::MAX - 20,
        symbolic_scalarization_multi_cell_args: u64::MAX - 21,
        lra_affine_original_clause_validation_attempts: u64::MAX - 22,
        lra_affine_original_clause_validation_queries: u64::MAX - 23,
        lra_affine_original_clause_validation_successes: u64::MAX - 24,
        lra_affine_original_clause_validation_failures: u64::MAX - 25,
        lra_affine_original_clause_validation_unknowns: u64::MAX - 26,
        deterministic_bv_bool_transition_attempts: u64::MAX - 27,
        deterministic_bv_bool_transition_recognized: u64::MAX - 28,
        deterministic_bv_bool_transition_bmc_unsafe_validated: u64::MAX - 29,
        deterministic_bv_bool_transition_kind_safe_validated: u64::MAX - 30,
        deterministic_bv_bool_transition_kind_unsafe_validated: u64::MAX - 31,
        deterministic_bv_bool_transition_bool_control_safe_validated: u64::MAX - 32,
        deterministic_bv_bool_transition_validation_rejections: u64::MAX - 33,
        accelerated_summary_modular_chain_summary_candidates: u64::MAX - 34,
        accelerated_summary_modular_chain_family_summary_candidates: u64::MAX - 35,
        accelerated_summary_trp_family_summary_candidates: u64::MAX - 36,
        accelerated_summary_trp_affine_constant_delta_family_summaries: u64::MAX - 37,
        accelerated_summary_trp_polynomial_closed_form_family_summaries: u64::MAX - 38,
        accelerated_summary_trp_affine_preserved_difference_family_summaries: u64::MAX - 39,
    };
    let b = ChcStatistics {
        iterations: 100,
        lemmas_learned: 100,
        max_frame: 2,
        restarts: 100,
        smt_unknowns: 100,
        cache_hits: 100,
        cache_model_rejections: 100,
        cache_solver_calls: 100,
        trust_proof_fallbacks: 100,
        native_code_helper_compile_attempts: 100,
        native_code_helper_compile_successes: 100,
        native_code_helper_compile_failures: 100,
        native_code_helper_evaluations: 100,
        native_code_helper_deopts: 100,
        native_code_helper_fallbacks: 100,
        native_code_helper_missing_var_fallbacks: 100,
        native_code_helper_interpreter_confirmations: 100,
        native_code_helper_trusted_true_results: 100,
        native_code_helper_applications: 100,
        tla_transition_cluster_applications: 100,
        symbolic_scalarization_projected_cells: 100,
        symbolic_scalarization_multi_cell_args: 100,
        lra_affine_original_clause_validation_attempts: 100,
        lra_affine_original_clause_validation_queries: 100,
        lra_affine_original_clause_validation_successes: 100,
        lra_affine_original_clause_validation_failures: 100,
        lra_affine_original_clause_validation_unknowns: 100,
        deterministic_bv_bool_transition_attempts: 100,
        deterministic_bv_bool_transition_recognized: 100,
        deterministic_bv_bool_transition_bmc_unsafe_validated: 100,
        deterministic_bv_bool_transition_kind_safe_validated: 100,
        deterministic_bv_bool_transition_kind_unsafe_validated: 100,
        deterministic_bv_bool_transition_bool_control_safe_validated: 100,
        deterministic_bv_bool_transition_validation_rejections: 100,
        accelerated_summary_modular_chain_summary_candidates: 100,
        accelerated_summary_modular_chain_family_summary_candidates: 100,
        accelerated_summary_trp_family_summary_candidates: 100,
        accelerated_summary_trp_affine_constant_delta_family_summaries: 100,
        accelerated_summary_trp_polynomial_closed_form_family_summaries: 100,
        accelerated_summary_trp_affine_preserved_difference_family_summaries: 100,
    };
    a.merge(&b);

    assert_eq!(a.iterations, u64::MAX);
    assert_eq!(a.lemmas_learned, u64::MAX);
    assert_eq!(a.max_frame, 2);
    assert_eq!(a.restarts, u64::MAX);
    assert_eq!(a.smt_unknowns, u64::MAX);
    assert_eq!(a.cache_hits, u64::MAX);
    assert_eq!(a.cache_model_rejections, u64::MAX);
    assert_eq!(a.cache_solver_calls, u64::MAX);
    assert_eq!(a.trust_proof_fallbacks, u64::MAX);
    assert_eq!(a.native_code_helper_compile_attempts, u64::MAX);
    assert_eq!(a.native_code_helper_compile_successes, u64::MAX);
    assert_eq!(a.native_code_helper_compile_failures, u64::MAX);
    assert_eq!(a.native_code_helper_evaluations, u64::MAX);
    assert_eq!(a.native_code_helper_deopts, u64::MAX);
    assert_eq!(a.native_code_helper_fallbacks, u64::MAX);
    assert_eq!(a.native_code_helper_missing_var_fallbacks, u64::MAX);
    assert_eq!(a.native_code_helper_interpreter_confirmations, u64::MAX);
    assert_eq!(a.native_code_helper_trusted_true_results, u64::MAX);
    assert_eq!(a.native_code_helper_applications, u64::MAX);
    assert_eq!(a.tla_transition_cluster_applications, u64::MAX);
    assert_eq!(a.symbolic_scalarization_projected_cells, u64::MAX);
    assert_eq!(a.symbolic_scalarization_multi_cell_args, u64::MAX);
    assert_eq!(a.lra_affine_original_clause_validation_attempts, u64::MAX);
    assert_eq!(a.lra_affine_original_clause_validation_queries, u64::MAX);
    assert_eq!(a.lra_affine_original_clause_validation_successes, u64::MAX);
    assert_eq!(a.lra_affine_original_clause_validation_failures, u64::MAX);
    assert_eq!(a.lra_affine_original_clause_validation_unknowns, u64::MAX);
    assert_eq!(a.deterministic_bv_bool_transition_attempts, u64::MAX);
    assert_eq!(a.deterministic_bv_bool_transition_recognized, u64::MAX);
    assert_eq!(
        a.deterministic_bv_bool_transition_bmc_unsafe_validated,
        u64::MAX
    );
    assert_eq!(
        a.deterministic_bv_bool_transition_kind_safe_validated,
        u64::MAX
    );
    assert_eq!(
        a.deterministic_bv_bool_transition_kind_unsafe_validated,
        u64::MAX
    );
    assert_eq!(
        a.deterministic_bv_bool_transition_bool_control_safe_validated,
        u64::MAX
    );
    assert_eq!(
        a.deterministic_bv_bool_transition_validation_rejections,
        u64::MAX
    );
    assert_eq!(
        a.accelerated_summary_modular_chain_summary_candidates,
        u64::MAX
    );
    assert_eq!(
        a.accelerated_summary_modular_chain_family_summary_candidates,
        u64::MAX
    );
    assert_eq!(
        a.accelerated_summary_trp_family_summary_candidates,
        u64::MAX
    );
    assert_eq!(
        a.accelerated_summary_trp_affine_constant_delta_family_summaries,
        u64::MAX
    );
    assert_eq!(
        a.accelerated_summary_trp_polynomial_closed_form_family_summaries,
        u64::MAX
    );
    assert_eq!(
        a.accelerated_summary_trp_affine_preserved_difference_family_summaries,
        u64::MAX
    );
}

#[test]
fn test_record_algebraic_modular_chain_stats() {
    let validation = AlgebraicValidationStats {
        accelerated_summary_modular_chain_summary_candidates: 2,
        accelerated_summary_modular_chain_family_summary_candidates: 3,
        ..Default::default()
    };
    let mut stats = ChcStatistics::default();

    stats.record_lra_affine_original_clause_validation_stats(&validation);

    assert_eq!(
        stats.accelerated_summary_modular_chain_summary_candidates,
        2
    );
    assert_eq!(
        stats.accelerated_summary_modular_chain_family_summary_candidates,
        3
    );
}

#[test]
fn test_record_trp_family_summary_stats() {
    let trp_stats = AcceleratedSummaryTrpFamilySummaryStatistics {
        family_summary_candidates: 4,
        affine_constant_delta_family_summaries: 2,
        polynomial_closed_form_family_summaries: 1,
        affine_preserved_difference_family_summaries: 1,
    };
    let mut stats = ChcStatistics::default();

    stats.record_trp_family_summary_stats(&trp_stats);

    assert_eq!(stats.accelerated_summary_trp_family_summary_candidates, 4);
    assert_eq!(
        stats.accelerated_summary_trp_affine_constant_delta_family_summaries,
        2
    );
    assert_eq!(
        stats.accelerated_summary_trp_polynomial_closed_form_family_summaries,
        1
    );
    assert_eq!(
        stats.accelerated_summary_trp_affine_preserved_difference_family_summaries,
        1
    );
}

#[test]
fn test_record_tla_transition_cluster_applications_saturates() {
    let mut stats = ChcStatistics {
        tla_transition_cluster_applications: u64::MAX - 1,
        ..Default::default()
    };

    stats.record_tla_transition_cluster_applications(3);

    assert_eq!(stats.tla_transition_cluster_applications, u64::MAX);
}

#[test]
fn test_tla_transition_cluster_profile_does_not_increment_native_helper_applications() {
    let mut stats = ChcStatistics {
        native_code_helper_applications: 4,
        ..Default::default()
    };

    stats.record_tla_transition_cluster_applications(7);

    assert_eq!(stats.tla_transition_cluster_applications, 7);
    assert_eq!(stats.native_code_helper_applications, 4);
}
