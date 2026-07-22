// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]
#![allow(clippy::panic)]

//! Incremental solving test group for ay-sat.
//!
//! Consolidates all incremental SAT solving tests into a single test
//! binary to reduce compilation overhead.

mod common;

#[path = "group_incremental/incremental_soundness.rs"]
mod incremental_soundness;
#[path = "group_incremental/incremental_soundness_expanded.rs"]
mod incremental_soundness_expanded;
#[path = "group_incremental/incremental_soundness_regressions.rs"]
mod incremental_soundness_regressions;
#[path = "group_incremental/push_pop_hermeticity.rs"]
mod push_pop_hermeticity;
