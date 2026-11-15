// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-work-package test files of the session (design §8, Rung 1). Each owner
//! adds exactly one `mod` line here: `unit` (WP-3), `bridge_unit` (WP-2),
//! `pushpop_fuzz` / `diff_lra` / `replay` (WP-4). Registered from
//! `session/mod.rs` as `#[path = "tests/mod.rs"] mod wp_tests;` (the inline
//! `mod tests` there holds WP-1's own locks).

mod diff_lra;
mod pushpop_fuzz;
mod replay;
mod rung4_wiring;
mod soundness_locks;
mod unit;
