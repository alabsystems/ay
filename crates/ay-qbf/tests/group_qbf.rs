// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Consolidated ay-qbf integration tests.
//!
//! Covers QBF benchmarks and integration smoke tests.
//!
//! Each submodule was previously a standalone integration test binary.
//! Grouping them into one binary reduces compilation overhead (#8604).

#[path = "group_qbf/benchmarks.rs"]
mod benchmarks;
#[path = "group_qbf/integration_smoke.rs"]
mod integration_smoke;
