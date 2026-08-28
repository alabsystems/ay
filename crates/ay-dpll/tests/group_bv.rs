// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Consolidated bv integration tests for ay-dpll.
//! Groups 14 test modules into a single binary to reduce link time.

#![allow(clippy::panic)]

mod common;

#[path = "group_bv/abv_sweep_false_unsat_8530.rs"]
mod abv_sweep_false_unsat_8530;
#[path = "group_bv/bool_arg_congruence_boolbox.rs"]
mod bool_arg_congruence_boolbox;
#[path = "group_bv/bv2nat_add_sub_modular_bridge.rs"]
mod bv2nat_add_sub_modular_bridge;
#[path = "group_bv/bv2nat_bvsub_bridge_9065.rs"]
mod bv2nat_bvsub_bridge_9065;
#[path = "group_bv/bv2nat_confirmed_invalid_model.rs"]
mod bv2nat_confirmed_invalid_model;
#[path = "group_bv/bv2nat_int2bv_subst_recovery.rs"]
mod bv2nat_int2bv_subst_recovery;
#[path = "group_bv/bv2nat_lia_bridge_sat_promotion_9065.rs"]
mod bv2nat_lia_bridge_sat_promotion_9065;
#[path = "group_bv/bv_array_assumption_roots_6739.rs"]
mod bv_array_assumption_roots_6739;
#[path = "group_bv/bv_array_smoke_tests.rs"]
mod bv_array_smoke_tests;
#[path = "group_bv/bv_check_sat_assuming_5437.rs"]
mod bv_check_sat_assuming_5437;
#[path = "group_bv/bv_check_sat_assuming_model_5443.rs"]
mod bv_check_sat_assuming_model_5443;
#[path = "group_bv/bv_concat_solve_8631.rs"]
mod bv_concat_solve_8631;
#[path = "group_bv/bv_delayed_circuit_persistence_8698.rs"]
mod bv_delayed_circuit_persistence_8698;
#[path = "group_bv/bv_div_rem_identity_4873.rs"]
mod bv_div_rem_identity_4873;
#[path = "group_bv/bv_exists_ematching_3593.rs"]
mod bv_exists_ematching_3593;
#[path = "group_bv/bv_extract_model_5512.rs"]
mod bv_extract_model_5512;
#[path = "group_bv/bv_incremental_false_unsat_7892.rs"]
mod bv_incremental_false_unsat_7892;
#[path = "group_bv/bv_incremental_push_pop.rs"]
mod bv_incremental_push_pop;
#[path = "group_bv/bv_sign_extend_validation_6280.rs"]
mod bv_sign_extend_validation_6280;
#[path = "group_bv/bv_width_overflow.rs"]
mod bv_width_overflow;
#[path = "group_bv/int2bv_backward_pin_sat_promotion.rs"]
mod int2bv_backward_pin_sat_promotion;
#[path = "group_bv/int2bv_pinned_source_bridge.rs"]
mod int2bv_pinned_source_bridge;
#[path = "group_bv/mixed_int_bv_5356.rs"]
mod mixed_int_bv_5356;
#[path = "group_bv/shift_formal_spec.rs"]
mod shift_formal_spec;
