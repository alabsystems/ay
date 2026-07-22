// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Consolidated miscellaneous CHC integration tests.
//!
//! Covers BMC, CEGAR, MBP, regressions, TLA2 trace validation,
//! SMT conversion, Farkas synthesis, and other CHC subsystems.
//!
//! Each submodule was previously a standalone integration test binary.
//! Grouping them into one binary reduces compilation overhead and prevents
//! OOM during `cargo test`.

#![allow(clippy::duplicate_mod)]

#[path = "group_misc/affine_transport_regressions.rs"]
mod affine_transport_regressions;
#[path = "group_misc/bmc_multi_pred_unsafe_6800.rs"]
mod bmc_multi_pred_unsafe_6800;
#[path = "group_misc/bmc_soundness.rs"]
mod bmc_soundness;
#[path = "group_misc/cegar_multi_predicate_6047.rs"]
mod cegar_multi_predicate_6047;
#[path = "group_misc/chc_regression_1615.rs"]
mod chc_regression_1615;
#[path = "group_misc/cyclic_array_bmc_unsafe_swaparray.rs"]
mod cyclic_array_bmc_unsafe_swaparray;
#[path = "group_misc/dillig12_m_regression_4751.rs"]
mod dillig12_m_regression_4751;
#[path = "group_misc/dt_bv_theory_combination_8419.rs"]
mod dt_bv_theory_combination_8419;
#[path = "group_misc/entry_value_inference_prover.rs"]
mod entry_value_inference_prover;
#[path = "group_misc/expr_reconstruction_proofs.rs"]
mod expr_reconstruction_proofs;
#[path = "group_misc/farkas_synthesis_2926.rs"]
mod farkas_synthesis_2926;
#[path = "group_misc/gj2007_m3_startup_gate_7626.rs"]
mod gj2007_m3_startup_gate_7626;
#[path = "group_misc/hwmcc_array_track_7971.rs"]
mod hwmcc_array_track_7971;
#[path = "group_misc/mbp_algorithm_audit.rs"]
mod mbp_algorithm_audit;
#[path = "group_misc/mbp_coverage_prover.rs"]
mod mbp_coverage_prover;
#[path = "group_misc/mbp_integer_sign_regression.rs"]
mod mbp_integer_sign_regression;
#[path = "group_misc/mbp_real_sign_regression.rs"]
mod mbp_real_sign_regression;
#[path = "group_misc/modular_hints_1362.rs"]
mod modular_hints_1362;
#[path = "group_misc/perf_dragon_bmc_depth1.rs"]
mod perf_dragon_bmc_depth1;
#[path = "group_misc/phases_m_startup_validation_1362.rs"]
mod phases_m_startup_validation_1362;
#[path = "group_misc/smt_convert_non_bool_6047.rs"]
mod smt_convert_non_bool_6047;
#[path = "group_misc/smt_mod_elimination_2881.rs"]
mod smt_mod_elimination_2881;
#[path = "group_misc/tla2_trace_mutation_validation.rs"]
mod tla2_trace_mutation_validation;
#[path = "group_misc/tla2_trace_validation.rs"]
mod tla2_trace_validation;
#[path = "group_misc/trl_dillig02_validation_7182.rs"]
mod trl_dillig02_validation_7182;
