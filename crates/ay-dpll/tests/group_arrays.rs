// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated arrays integration tests for ay-dpll.
//! Groups 10 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

mod common;

#[path = "group_arrays/abv_array_axiom_soundness.rs"]
mod abv_array_axiom_soundness;
#[path = "group_arrays/abv_bool_element_select_fc_soundness.rs"]
mod abv_bool_element_select_fc_soundness;
#[path = "group_arrays/abv_incremental_push_pop.rs"]
mod abv_incremental_push_pop;
#[path = "group_arrays/abv_model_5449.rs"]
mod abv_model_5449;
#[path = "group_arrays/abv_subst_select_index_model_wishlist1.rs"]
mod abv_subst_select_index_model_wishlist1;
#[path = "group_arrays/array_as_array_default_8534.rs"]
mod array_as_array_default_8534;
#[path = "group_arrays/array_assumption_axiom_6736.rs"]
mod array_assumption_axiom_6736;
#[path = "group_arrays/array_check_sat_assuming_6736.rs"]
mod array_check_sat_assuming_6736;
#[path = "group_arrays/array_cross_theory_prover_4665.rs"]
mod array_cross_theory_prover_4665;
#[path = "group_arrays/array_drain_prefix_6340.rs"]
mod array_drain_prefix_6340;
#[path = "group_arrays/array_interface_read_prune.rs"]
mod array_interface_read_prune;
#[path = "group_arrays/array_map_8533.rs"]
mod array_map_8533;
#[path = "group_arrays/array_model_store_chain_witness.rs"]
mod array_model_store_chain_witness;
#[path = "group_arrays/array_soundness_4304.rs"]
mod array_soundness_4304;
#[path = "group_arrays/census_memo_consistency.rs"]
mod census_memo_consistency;
#[path = "group_arrays/const_array_card1_soundness.rs"]
mod const_array_card1_soundness;
#[path = "group_arrays/default_lambda_wrong_sat.rs"]
mod default_lambda_wrong_sat;
#[path = "group_arrays/qf_aufnia_nested_array_row_wrong_sat.rs"]
mod qf_aufnia_nested_array_row_wrong_sat;
#[path = "group_arrays/qf_ax_benchmark_suite.rs"]
mod qf_ax_benchmark_suite;
#[path = "group_arrays/store_chain_computed_value_dead_node.rs"]
mod store_chain_computed_value_dead_node;
