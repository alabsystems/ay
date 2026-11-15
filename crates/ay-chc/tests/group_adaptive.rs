// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Consolidated adaptive portfolio integration tests.
//!
//! Each submodule was previously a standalone integration test binary.
//! Grouping them into one binary reduces compilation overhead and prevents
//! OOM during `cargo test`.

#[path = "group_adaptive/adaptive_acyclic_ite_chain_model_checker_consumer.rs"]
mod adaptive_acyclic_ite_chain_model_checker_consumer;
#[path = "group_adaptive/adaptive_array_mbp_6047.rs"]
mod adaptive_array_mbp_6047;
#[path = "group_adaptive/adaptive_bv_model_checker_consumer_7019.rs"]
mod adaptive_bv_model_checker_consumer_7019;
#[path = "group_adaptive/adaptive_bv_route_5877.rs"]
mod adaptive_bv_route_5877;
#[path = "group_adaptive/adaptive_dt_bv_guard_7930.rs"]
mod adaptive_dt_bv_guard_7930;
#[path = "group_adaptive/adaptive_kind_dillig32_regression.rs"]
mod adaptive_kind_dillig32_regression;
#[path = "group_adaptive/adaptive_realloc_grow_model_checker_consumer.rs"]
mod adaptive_realloc_grow_model_checker_consumer;
#[path = "group_adaptive/adaptive_straight_line_query_clause.rs"]
mod adaptive_straight_line_query_clause;
