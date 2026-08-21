// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Consolidated soundness and validation integration tests.
//!
//! Each submodule was previously a standalone integration test binary.
//! Grouping them into one binary reduces compilation overhead and prevents
//! OOM during `cargo test`.

#[path = "group_soundness/false_proof_array_equality_8675.rs"]
mod false_proof_array_equality_8675;
#[path = "group_soundness/ground_witness_backtranslation.rs"]
mod ground_witness_backtranslation;
#[path = "group_soundness/had_sat_no_cube_soundness.rs"]
mod had_sat_no_cube_soundness;
#[path = "group_soundness/init_fact_head_args_9312.rs"]
mod init_fact_head_args_9312;
#[path = "group_soundness/kind_soundness.rs"]
mod kind_soundness;
#[path = "group_soundness/pdkind_soundness.rs"]
mod pdkind_soundness;
#[path = "group_soundness/preprocessing_soundness.rs"]
mod preprocessing_soundness;
#[path = "group_soundness/query_safety_free_vars_022c.rs"]
mod query_safety_free_vars_022c;
#[path = "group_soundness/soundness_vs_z3.rs"]
mod soundness_vs_z3;
#[path = "group_soundness/unsat_benchmark_coverage.rs"]
mod unsat_benchmark_coverage;
#[path = "group_soundness/validation_benchmarks.rs"]
mod validation_benchmarks;
#[path = "group_soundness/value_parse_regression.rs"]
mod value_parse_regression;
#[path = "group_soundness/verify_model_universal_7912.rs"]
mod verify_model_universal_7912;
