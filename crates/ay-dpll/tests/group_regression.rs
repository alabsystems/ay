// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated regression integration tests for ay-dpll.
//! Groups 15 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

mod common;

#[path = "group_regression/array_lane_index_eq_livelock.rs"]
mod array_lane_index_eq_livelock;
#[path = "group_regression/array_repair_completeness_2026_09_24.rs"]
mod array_repair_completeness_2026_09_24;
#[path = "group_regression/array_wrong_verdicts_2026_09_23.rs"]
mod array_wrong_verdicts_2026_09_23;
#[path = "group_regression/ax_fixpoint_convergence_swap_abort.rs"]
mod ax_fixpoint_convergence_swap_abort;
#[path = "group_regression/boolarg_orphan_model_gate_gap.rs"]
mod boolarg_orphan_model_gate_gap;
#[path = "group_regression/bv_ite_bool_model_soundness.rs"]
mod bv_ite_bool_model_soundness;
#[path = "group_regression/bv_lia_guarded_mask_residue.rs"]
mod bv_lia_guarded_mask_residue;
#[path = "group_regression/bv_lia_int_blast_lane.rs"]
mod bv_lia_int_blast_lane;
#[path = "group_regression/cegqi_ce_free_resolve_branchstmt.rs"]
mod cegqi_ce_free_resolve_branchstmt;
#[path = "group_regression/certify_before_presentation.rs"]
mod certify_before_presentation;
#[path = "group_regression/combined_assumption_sat_canaries_6731.rs"]
mod combined_assumption_sat_canaries_6731;
#[path = "group_regression/combined_check_sat_assuming.rs"]
mod combined_check_sat_assuming;
#[path = "group_regression/combined_minimize_counterexamples_6731.rs"]
mod combined_minimize_counterexamples_6731;
#[path = "group_regression/dt_deepening_round_repeat.rs"]
mod dt_deepening_round_repeat;
#[path = "group_regression/false_unsat_20var_bb.rs"]
mod false_unsat_20var_bb;
#[path = "group_regression/false_unsat_6242.rs"]
mod false_unsat_6242;
#[path = "group_regression/false_unsat_array_ite_store_index.rs"]
mod false_unsat_array_ite_store_index;
#[path = "group_regression/false_unsat_auflia_disjunct_forall.rs"]
mod false_unsat_auflia_disjunct_forall;
#[path = "group_regression/false_unsat_auflia_exists_eq.rs"]
mod false_unsat_auflia_exists_eq;
#[path = "group_regression/false_unsat_auflia_rodin.rs"]
mod false_unsat_auflia_rodin;
#[path = "group_regression/false_unsat_bv_residue_and_extract_wrap.rs"]
mod false_unsat_bv_residue_and_extract_wrap;
#[path = "group_regression/false_unsat_incremental_store_select_syntactic.rs"]
mod false_unsat_incremental_store_select_syntactic;
#[path = "group_regression/false_unsat_large_coeff_ite.rs"]
mod false_unsat_large_coeff_ite;
#[path = "group_regression/false_unsat_to_int_mod_hnf.rs"]
mod false_unsat_to_int_mod_hnf;
#[path = "group_regression/farkas_degradation_tests.rs"]
mod farkas_degradation_tests;
#[path = "group_regression/fold_identity_hash_family.rs"]
mod fold_identity_hash_family;
#[path = "group_regression/g6_div0_forged_guard_abort.rs"]
mod g6_div0_forged_guard_abort;
#[path = "group_regression/hunt_quantifier_fixup_models.rs"]
mod hunt_quantifier_fixup_models;
#[path = "group_regression/hunt_quantifier_fixup_verdicts.rs"]
mod hunt_quantifier_fixup_verdicts;
#[path = "group_regression/hunt_quantifier_unused_array_model.rs"]
mod hunt_quantifier_unused_array_model;
#[path = "group_regression/hunt_quantifier_wrong_verdicts.rs"]
mod hunt_quantifier_wrong_verdicts;
#[path = "group_regression/hunt_scope_leak_h1_l1.rs"]
mod hunt_scope_leak_h1_l1;
#[path = "group_regression/hunt_scope_leak_wrong_verdicts.rs"]
mod hunt_scope_leak_wrong_verdicts;
#[path = "group_regression/int_const_subst_zero_divisor.rs"]
mod int_const_subst_zero_divisor;
#[path = "group_regression/issue4701_substr_splice_regression.rs"]
mod issue4701_substr_splice_regression;
#[path = "group_regression/issue_6481_implication_antecedent.rs"]
mod issue_6481_implication_antecedent;
#[path = "group_regression/lia_dioph_wrong_unsat.rs"]
mod lia_dioph_wrong_unsat;
#[path = "group_regression/lira_nonintegral_offset_wrong_unsat.rs"]
mod lira_nonintegral_offset_wrong_unsat;
#[path = "group_regression/lnh_lane_leak_regression.rs"]
mod lnh_lane_leak_regression;
#[path = "group_regression/lnh_r5_dt_carrier_completion.rs"]
mod lnh_r5_dt_carrier_completion;
#[path = "group_regression/lnh_r5_regression.rs"]
mod lnh_r5_regression;
#[path = "group_regression/lnh_symmetry_domain_soundness.rs"]
mod lnh_symmetry_domain_soundness;
#[path = "group_regression/lnh_wrong_unsat_regression.rs"]
mod lnh_wrong_unsat_regression;
#[path = "group_regression/nia_cube_decline_keeps_point.rs"]
mod nia_cube_decline_keeps_point;
#[path = "group_regression/nia_sign_cut_wrong_unsat.rs"]
mod nia_sign_cut_wrong_unsat;
#[path = "group_regression/nia_split_probe_sat.rs"]
mod nia_split_probe_sat;
#[path = "group_regression/nia_split_walk_sat.rs"]
mod nia_split_walk_sat;
#[path = "group_regression/nia_stale_accept_sat.rs"]
mod nia_stale_accept_sat;
#[path = "group_regression/nia_wrong_unsat_witnesses.rs"]
mod nia_wrong_unsat_witnesses;
#[path = "group_regression/qf_aufnia_corpus_routing.rs"]
mod qf_aufnia_corpus_routing;
#[path = "group_regression/qsat_route_lost_verdicts.rs"]
mod qsat_route_lost_verdicts;
#[path = "group_regression/qsat_unsat_evidence.rs"]
mod qsat_unsat_evidence;
#[path = "group_regression/quantified_model_check.rs"]
mod quantified_model_check;
#[path = "group_regression/simplifier_pipeline_quantified.rs"]
mod simplifier_pipeline_quantified;
#[path = "group_regression/ufdtnira_live_content_lane_kanig.rs"]
mod ufdtnira_live_content_lane_kanig;
#[path = "group_regression/ufnia_fixed_pair_wrong_unsat.rs"]
mod ufnia_fixed_pair_wrong_unsat;
#[path = "group_regression/ufnia_get_value_congruence.rs"]
mod ufnia_get_value_congruence;
#[path = "group_regression/unbounded_oscillation_1836.rs"]
mod unbounded_oscillation_1836;
#[path = "group_regression/unproductive_budget_vocabulary_scaling.rs"]
mod unproductive_budget_vocabulary_scaling;
#[path = "group_regression/validate_model_5488.rs"]
mod validate_model_5488;
#[path = "group_regression/validate_model_dag_perf.rs"]
mod validate_model_dag_perf;
#[path = "group_regression/verification_consumer_int_div_6165.rs"]
mod verification_consumer_int_div_6165;
#[path = "group_regression/verification_consumer_sum_first_n_9048.rs"]
mod verification_consumer_sum_first_n_9048;
#[path = "group_regression/verification_consumer_uninterpreted_sort_equality_8971.rs"]
mod verification_consumer_uninterpreted_sort_equality_8971;
#[path = "group_regression/wrong_verdict_fp_strings_round2_2026_09_26.rs"]
mod wrong_verdict_fp_strings_round2_2026_09_26;
#[path = "group_regression/wrong_verdict_strings_fp_2026_09_23.rs"]
mod wrong_verdict_strings_fp_2026_09_23;
#[path = "group_regression/zero_checked_validation_5488.rs"]
mod zero_checked_validation_5488;
