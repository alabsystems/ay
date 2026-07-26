// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated auflia integration tests for ay-dpll.
//! Groups 14 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

mod common;

#[path = "group_auflia/auflia_bridge_false_unsat_6930.rs"]
mod auflia_bridge_false_unsat_6930;
#[path = "group_auflia/auflia_const_array_model_eq_8596.rs"]
mod auflia_const_array_model_eq_8596;
#[path = "group_auflia/auflia_deep_neq_4877.rs"]
mod auflia_deep_neq_4877;
#[path = "group_auflia/auflia_determinism_3041.rs"]
mod auflia_determinism_3041;
#[path = "group_auflia/auflia_ematching_regression_7979.rs"]
mod auflia_ematching_regression_7979;
#[path = "group_auflia/auflia_incremental_push_pop.rs"]
mod auflia_incremental_push_pop;
#[path = "group_auflia/auflia_ite_sum_index_reconcile_w1b.rs"]
mod auflia_ite_sum_index_reconcile_w1b;
#[path = "group_auflia/auflia_lia_edge_cases_6661.rs"]
mod auflia_lia_edge_cases_6661;
#[path = "group_auflia/auflia_model_extraction.rs"]
mod auflia_model_extraction;
#[path = "group_auflia/auflia_seq_mixed_collection_9185.rs"]
mod auflia_seq_mixed_collection_9185;
#[path = "group_auflia/auflia_slack_reuse_6193.rs"]
mod auflia_slack_reuse_6193;
#[path = "group_auflia/auflia_slices_range_expression_split.rs"]
mod auflia_slices_range_expression_split;
#[path = "group_auflia/auflia_store_itesum_wrong_unsat_w11.rs"]
mod auflia_store_itesum_wrong_unsat_w11;
#[path = "group_auflia/auflia_storecomm_completeness_8785.rs"]
mod auflia_storecomm_completeness_8785;
#[path = "group_auflia/auflia_storecomm_tseitin_oob_8805.rs"]
mod auflia_storecomm_tseitin_oob_8805;
#[path = "group_auflia/auflia_storeinv_release_6546.rs"]
mod auflia_storeinv_release_6546;
#[path = "group_auflia/auflia_storeinv_t3_ai_8804.rs"]
mod auflia_storeinv_t3_ai_8804;
#[path = "group_auflia/auflia_unsupported_fragment_diagnostics.rs"]
mod auflia_unsupported_fragment_diagnostics;
#[path = "group_auflia/auflia_verification_consumer_6176.rs"]
mod auflia_verification_consumer_6176;
#[path = "group_auflia/auflia_verification_consumer_9185_reducers.rs"]
mod auflia_verification_consumer_9185_reducers;
#[path = "group_auflia/auflia_verification_consumer_array_quantifier_6920.rs"]
mod auflia_verification_consumer_array_quantifier_6920;
#[path = "group_auflia/auflia_verification_consumer_ext_eq_7956.rs"]
mod auflia_verification_consumer_ext_eq_7956;
#[path = "group_auflia/auflia_verification_consumer_regression_7883.rs"]
mod auflia_verification_consumer_regression_7883;
#[path = "group_auflia/auflira_bridged_conflict_verifier_6853.rs"]
mod auflira_bridged_conflict_verifier_6853;
#[path = "group_auflia/auflira_cross_sort_soundness.rs"]
mod auflira_cross_sort_soundness;
#[path = "group_auflia/const_array_definition_validation_sat.rs"]
mod const_array_definition_validation_sat;
#[path = "group_auflia/dt_uflia_array_free_routing_chc25.rs"]
mod dt_uflia_array_free_routing_chc25;
#[path = "group_auflia/qf_ax_swap_np_soundness.rs"]
mod qf_ax_swap_np_soundness;
#[path = "group_auflia/qf_ax_swap_sf_soundness.rs"]
mod qf_ax_swap_sf_soundness;
#[path = "group_auflia/recovered_array_false_unsat.rs"]
mod recovered_array_false_unsat;
#[path = "group_auflia/uflia_fd_rescue_04_06.rs"]
mod uflia_fd_rescue_04_06;
