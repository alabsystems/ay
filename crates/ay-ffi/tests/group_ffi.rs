// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Consolidated ay-ffi integration tests.
//!
//! Covers C consumer link tests, header coverage, and soundness regression.
//!
//! Each submodule was previously a standalone integration test binary.
//! Grouping them into one binary reduces compilation overhead (#8604).

#[path = "group_ffi/c_consumer_link.rs"]
mod c_consumer_link;
#[path = "group_ffi/capi_ast_containers_link.rs"]
mod capi_ast_containers_link;
#[path = "group_ffi/capi_finite_set_link.rs"]
mod capi_finite_set_link;
#[path = "group_ffi/capi_func_interp_link.rs"]
mod capi_func_interp_link;
#[path = "group_ffi/capi_goal_probe_link.rs"]
mod capi_goal_probe_link;
#[path = "group_ffi/capi_numeral_sortstruct_link.rs"]
mod capi_numeral_sortstruct_link;
#[path = "group_ffi/capi_optimize_link.rs"]
mod capi_optimize_link;
#[path = "group_ffi/capi_parser_context_link.rs"]
mod capi_parser_context_link;
#[path = "group_ffi/capi_quantifier_meta_link.rs"]
mod capi_quantifier_meta_link;
#[path = "group_ffi/capi_simplifier_link.rs"]
mod capi_simplifier_link;
#[path = "group_ffi/capi_solver_completion_link.rs"]
mod capi_solver_completion_link;
#[path = "group_ffi/capi_tactic_completion_link.rs"]
mod capi_tactic_completion_link;
#[path = "group_ffi/capi_z3_500_additional_link.rs"]
mod capi_z3_500_additional_link;
#[path = "group_ffi/capi_z3_500_remaining_link.rs"]
mod capi_z3_500_remaining_link;
#[path = "group_ffi/cpp_consumer_link.rs"]
mod cpp_consumer_link;
#[path = "group_ffi/header_coverage.rs"]
mod header_coverage;
#[path = "group_ffi/soundness_5511.rs"]
mod soundness_5511;
#[path = "group_ffi/z3_500_typed_surface_link.rs"]
mod z3_500_typed_surface_link;
