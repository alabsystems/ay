// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]
#![allow(clippy::panic)]

//! DRAT/LRAT proof test group for ay-sat.
//!
//! Consolidates all DRAT and LRAT proof generation and verification tests
//! into a single test binary to reduce compilation overhead.

mod common;

#[path = "group_drat/drat_checker_e2e.rs"]
mod drat_checker_e2e;
#[path = "group_drat/drat_coverage_comprehensive.rs"]
mod drat_coverage_comprehensive;
#[path = "group_drat/drat_coverage_expansion.rs"]
mod drat_coverage_expansion;
#[path = "group_drat/drat_exhaustive.rs"]
mod drat_exhaustive;
#[path = "group_drat/drat_exhaustive_coverage.rs"]
mod drat_exhaustive_coverage;
#[path = "group_drat/drat_inprocessing.rs"]
mod drat_inprocessing;
#[path = "group_drat/drat_mode_braun.rs"]
mod drat_mode_braun;
#[path = "group_drat/drat_vivify_3481.rs"]
mod drat_vivify_3481;
#[path = "group_drat/lrat_chain_7108.rs"]
mod lrat_chain_7108;
#[path = "group_drat/lrat_chain_alloc_characterization.rs"]
mod lrat_chain_alloc_characterization;
#[path = "group_drat/lrat_external_check.rs"]
mod lrat_external_check;
#[path = "group_drat/lrat_level0_hints.rs"]
mod lrat_level0_hints;
#[path = "group_drat/test_vivify_drat.rs"]
mod test_vivify_drat;
