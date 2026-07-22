// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Consolidated ay-core integration tests.
//!
//! Covers theory push/pop contract and Tseitin let regression tests.
//!
//! Each submodule was previously a standalone integration test binary.
//! Grouping them into one binary reduces compilation overhead (#8604).

#[path = "group_core/theory_push_pop_contract_harness.rs"]
mod theory_push_pop_contract_harness;
#[path = "group_core/tseitin_let_regression_2889.rs"]
mod tseitin_let_regression_2889;
