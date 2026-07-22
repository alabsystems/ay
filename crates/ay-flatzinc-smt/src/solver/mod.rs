// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// SMT solver driver for FlatZinc solving (Phase 4: optimization loop)

use ay_core::kani_compat::DetHashMap as HashMap;
use std::io::Write;
use std::time::{Duration, Instant};

use crate::output::format_dzn_solution;
use crate::translate::{SmtInt, TranslationResult, VarDomain};

mod error;
mod execution;
mod incremental;
mod optimization;
mod parse;
mod satisfaction;
#[cfg(test)]
mod tests;

pub use error::SolverError;
pub use parse::{parse_get_value, parse_smt_int};

pub(crate) use execution::{extract_reason_unknown, parse_ay_output, run_ay};
pub(crate) use incremental::IncrementalSolver;
#[cfg(test)]
use satisfaction::build_output_get_value;

/// Configuration for the in-process SMT solver.
#[derive(Default)]
pub struct SolverConfig {
    /// Timeout per check-sat call in milliseconds (None = no timeout).
    pub timeout_ms: Option<u64>,
    /// Enumerate all solutions for satisfaction problems (MiniZinc `-a` flag).
    /// For optimization problems this has no additional effect.
    pub all_solutions: bool,
    /// Global wall-clock deadline for the entire solve (set from `-t` flag).
    /// When set, optimization loops check remaining time before each probe
    /// and stop when the deadline is reached.
    pub global_deadline: Option<Instant>,
}

impl SolverConfig {
    /// Check if the global deadline has been reached.
    pub(crate) fn deadline_expired(&self) -> bool {
        self.global_deadline.is_some_and(|d| Instant::now() >= d)
    }
}

/// Outcome of a single check-sat call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckSatResult {
    Sat,
    Unsat,
    Unknown,
}

/// Solve a FlatZinc model via ay and print solutions to stdout.
///
/// For satisfaction problems: prints one solution + "----------".
/// For optimization problems: iteratively tightens the bound,
/// printing each improving solution + "----------", then "==========" when
/// optimality is proved (or best-found if interrupted).
///
/// Returns the number of solutions found.
pub fn solve(
    result: &TranslationResult,
    config: &SolverConfig,
    out: &mut dyn Write,
) -> Result<usize, SolverError> {
    if result.objective.is_some() {
        optimization::solve_optimization(result, config, out)
    } else {
        satisfaction::solve_satisfaction(result, config, out)
    }
}
