// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated datatypes integration tests for ay-dpll.
//! Groups 7 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

mod common;

#[path = "group_datatypes/cause_b_parsed_gate.rs"]
mod cause_b_parsed_gate;
#[path = "group_datatypes/dt_array_field_model_witness.rs"]
mod dt_array_field_model_witness;
#[path = "group_datatypes/dt_bv_selector_over_ite_soundness.rs"]
mod dt_bv_selector_over_ite_soundness;
#[path = "group_datatypes/dt_combined_lane_soundness.rs"]
mod dt_combined_lane_soundness;
#[path = "group_datatypes/dt_d1_lazy_propagation.rs"]
mod dt_d1_lazy_propagation;
#[path = "group_datatypes/dt_d2_lazy_lane.rs"]
mod dt_d2_lazy_lane;
#[path = "group_datatypes/dt_egraph_acyclicity_soundness.rs"]
mod dt_egraph_acyclicity_soundness;
#[path = "group_datatypes/dt_selector_field_soundness.rs"]
mod dt_selector_field_soundness;
#[path = "group_datatypes/dt_stack_safety_8414.rs"]
mod dt_stack_safety_8414;
#[path = "group_datatypes/dt_uf_bridge_congruence.rs"]
mod dt_uf_bridge_congruence;
#[path = "group_datatypes/dt_value_eq_congruence_soundness.rs"]
mod dt_value_eq_congruence_soundness;
#[path = "group_datatypes/lazy_dt_deep_case_split.rs"]
mod lazy_dt_deep_case_split;
#[path = "group_datatypes/match_desugar_soundness.rs"]
mod match_desugar_soundness;
#[path = "group_datatypes/parametric_datatypes.rs"]
mod parametric_datatypes;
#[path = "group_datatypes/qf_dt_bv_model.rs"]
mod qf_dt_bv_model;
#[path = "group_datatypes/qf_dt_integration.rs"]
mod qf_dt_integration;
#[path = "group_datatypes/qf_dt_mixed.rs"]
mod qf_dt_mixed;
#[path = "group_datatypes/qf_dt_selectors.rs"]
mod qf_dt_selectors;
#[path = "group_datatypes/single_ctor_elimination.rs"]
mod single_ctor_elimination;
#[path = "group_datatypes/store_decomposition_soundness_6282.rs"]
mod store_decomposition_soundness_6282;
