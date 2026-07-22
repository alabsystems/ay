// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Consolidated ay-translate integration tests.
//!
//! Covers API canary, dual host, and embedded state tests.
//!
//! Each submodule was previously a standalone integration test binary.
//! Grouping them into one binary reduces compilation overhead (#8604).

#[path = "group_translate/api_canary_4696.rs"]
mod api_canary_4696;
#[path = "group_translate/dual_host_6302.rs"]
mod dual_host_6302;
#[path = "group_translate/embedded_state_4696.rs"]
mod embedded_state_4696;
