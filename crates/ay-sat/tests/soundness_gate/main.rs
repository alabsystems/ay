// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inprocessing Soundness Gate Tests (#3428)
//!
//! Each inprocessing feature is tested in isolation against known-UNSAT
//! benchmarks to prevent the enable/disable soundness cycle:
//!   1. Worker enables feature
//!   2. Wrong-UNSAT/SAT discovered much later
//!   3. Feature disabled, investigation begins
//!
//! Gate protocol: a feature may only be re-enabled (default true) when
//! it passes all gate tests in isolation mode (all other inprocessing
//! features disabled).

mod common;
mod isolation;
mod ledger;
mod pairwise;
mod regression;
#[path = "../common/mod.rs"]
mod test_common;
