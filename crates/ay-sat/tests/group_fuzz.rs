// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]
#![allow(clippy::panic)]

//! CNF fuzz test group for ay-sat.
//!
//! Consolidates all random/fuzz testing of SAT solver correctness into a
//! single test binary to reduce compilation overhead.

mod common;

#[path = "group_fuzz/cnf_fuzz_bve_differential.rs"]
mod cnf_fuzz_bve_differential;
#[path = "group_fuzz/cnf_fuzz_bve_stress.rs"]
mod cnf_fuzz_bve_stress;
#[path = "group_fuzz/cnf_fuzz_differential.rs"]
mod cnf_fuzz_differential;
#[path = "group_fuzz/cnf_fuzz_inprocessing_interactions.rs"]
mod cnf_fuzz_inprocessing_interactions;
#[path = "group_fuzz/cnf_fuzz_proptest.rs"]
mod cnf_fuzz_proptest;
