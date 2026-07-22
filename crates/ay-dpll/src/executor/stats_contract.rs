// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Stats finalization contracts for executor theory paths.
//!
//! The `collect_sat_stats!` macro in `pipeline_setup_macros.rs` is a mechanical write-only
//! snapshot. Phase-sensitive invariant checks must NOT be placed inside
//! that macro because it expands at 28+ call sites across heterogeneous
//! theory paths where intermediate states are valid.
//!
//! This module provides finalize helpers that run debug assertions only
//! after all fields for a given solve path have been populated.
//!
//! See: the development design notes

#[cfg(test)]
#[path = "stats_contract_tests.rs"]
mod tests;
