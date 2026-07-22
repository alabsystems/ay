// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Consolidated portfolio and cancellation integration tests.
//!
//! Each submodule was previously a standalone integration test binary.
//! Grouping them into one binary reduces compilation overhead and prevents
//! OOM during `cargo test`.

#[path = "group_portfolio/cancellation_responsiveness.rs"]
mod cancellation_responsiveness;
#[path = "group_portfolio/portfolio_default_engine.rs"]
mod portfolio_default_engine;
#[path = "group_portfolio/portfolio_parallel_timeout.rs"]
mod portfolio_parallel_timeout;
#[path = "group_portfolio/portfolio_tests.rs"]
mod portfolio_tests;
