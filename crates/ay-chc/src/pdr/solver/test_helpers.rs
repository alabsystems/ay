// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared test helpers for PDR solver tests.
//!
//! This module provides common utilities used across multiple test modules
//! to avoid duplicating test setup boilerplate.

use crate::pdr::config::PdrConfig;
use crate::{ChcParser, PdrSolver};

/// Parse an SMT-LIB CHC string and create a PdrSolver with default config.
///
/// This is the canonical test helper — use it instead of per-module copies.
pub(in crate::pdr::solver) fn solver_from_str(input: &str) -> PdrSolver {
    let problem = ChcParser::parse(input).expect("parse CHC input");
    PdrSolver::new(problem, PdrConfig::default())
}
