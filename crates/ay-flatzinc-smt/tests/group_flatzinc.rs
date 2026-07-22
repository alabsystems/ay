// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Consolidated ay-flatzinc-smt integration tests.
//!
//! Covers branching integration, builtin coverage, solve integration,
//! solver parsing, and solver roundtrip tests.
//!
//! Each submodule was previously a standalone integration test binary.
//! Grouping them into one binary reduces compilation overhead (#8604).

#[allow(dead_code)]
#[path = "group_flatzinc/common.rs"]
mod common;

#[path = "group_flatzinc/branching_integration.rs"]
mod branching_integration;
#[path = "group_flatzinc/builtin_coverage.rs"]
mod builtin_coverage;
#[path = "group_flatzinc/solve_integration.rs"]
mod solve_integration;
#[path = "group_flatzinc/solver_parsing_tests.rs"]
mod solver_parsing_tests;
#[path = "group_flatzinc/solver_roundtrip.rs"]
mod solver_roundtrip;
#[path = "group_flatzinc/solver_roundtrip_bv.rs"]
mod solver_roundtrip_bv;
