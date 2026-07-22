// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Grouped miscellaneous integration tests: CHC, DRAT, ematching, quantifiers, etc.

#![allow(deprecated)]

#[path = "common/spawn.rs"]
pub mod spawn;

#[path = "group_misc/all_logic_datatype_acceptance.rs"]
mod all_logic_datatype_acceptance;

#[path = "group_misc/match_soundness_backstop.rs"]
mod match_soundness_backstop;

#[path = "group_misc/assertion_order_determinism_8719.rs"]
mod assertion_order_determinism_8719;

#[path = "group_misc/chc_array_portfolio_no_panic.rs"]
mod chc_array_portfolio_no_panic;

#[path = "group_misc/chc_bv_sendmail_5877.rs"]
mod chc_bv_sendmail_5877;

#[path = "group_misc/build_version_stamp_8870.rs"]
mod build_version_stamp_8870;

#[path = "group_misc/chc_bv64_7975.rs"]
mod chc_bv64_7975;

#[path = "group_misc/chc_output_clean_5970.rs"]
mod chc_output_clean_5970;

#[path = "group_misc/counterexample_minimize_8297.rs"]
mod counterexample_minimize_8297;

#[path = "group_misc/dimacs_xor_extension_7649.rs"]
mod dimacs_xor_extension_7649;

#[path = "group_misc/drat_coverage.rs"]
mod drat_coverage;

#[path = "group_misc/guard_cover_sidecar_8960.rs"]
mod guard_cover_sidecar_8960;

#[path = "group_misc/ematching_nested_patterns.rs"]
mod ematching_nested_patterns;

#[path = "group_misc/ematching_user_triggers.rs"]
mod ematching_user_triggers;

#[path = "group_misc/get_assertions_quantifiers.rs"]
mod get_assertions_quantifiers;

#[path = "group_misc/incremental_core_evolution_8154.rs"]
mod incremental_core_evolution_8154;

#[path = "group_misc/model_fp_string_seq_output.rs"]
mod model_fp_string_seq_output;

#[path = "group_misc/public_surface_contract_3147.rs"]
mod public_surface_contract_3147;

#[path = "group_misc/quantifier_unknown_regression.rs"]
mod quantifier_unknown_regression;

#[path = "group_misc/sat_par2_harness.rs"]
mod sat_par2_harness;

#[path = "group_misc/string_resolve_recursion_6260.rs"]
mod string_resolve_recursion_6260;

#[path = "group_misc/uflra_logic_acceptance.rs"]
mod uflra_logic_acceptance;

#[path = "group_misc/ay_subprocess_test.rs"]
mod ay_subprocess_test;
