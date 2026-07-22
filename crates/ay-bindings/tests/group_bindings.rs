// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Consolidated ay-bindings integration tests.
//!
//! Covers API canary tests, expression drop safety, fold consistency,
//! execute_direct integration, and parser roundtrip tests.
//!
//! Each submodule was previously a standalone integration test binary.
//! Grouping them into one binary reduces compilation overhead (#8604).

#[path = "group_bindings/api_canary.rs"]
mod api_canary;
#[path = "group_bindings/expr_deep_drop.rs"]
mod expr_deep_drop;
#[path = "group_bindings/fold_consistency.rs"]
mod fold_consistency;
#[path = "group_bindings/incremental_execute_direct_8154.rs"]
mod incremental_execute_direct_8154;
#[path = "group_bindings/lra_execute_direct_5405.rs"]
mod lra_execute_direct_5405;
#[path = "group_bindings/parser_roundtrip.rs"]
mod parser_roundtrip;
