// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Solver driver: thin wrapper around ay_flatzinc_smt::solve().
//
// MiniZinc competition protocol:
//   - Print each solution followed by "----------"
//   - Print "==========" when optimality is proved or all solutions found
//   - Print "=====UNSATISFIABLE=====" if no solution exists
//   - Print "=====UNKNOWN=====" on timeout or inconclusive result
//   - Flush stdout after each solution (scoring uses best-found)

use std::io;
use std::time::{Duration, Instant};

use ay_flatzinc_smt::{SolverConfig, TranslationResult};

use crate::error::{Fzn2smtError, Result};

/// Solve a translated FlatZinc model through AY's in-process solver API.
///
/// When `fd_search` is true, uses the branching solver that follows
/// FlatZinc search annotations (FD Search track). Otherwise uses the
/// one-shot solver (Free Search track).
///
/// When `all_solutions` is true and the problem is a satisfaction problem,
/// enumerates all solutions by adding blocking clauses after each one.
/// For optimization problems, `-a` has no additional effect (intermediate
/// solutions are already printed).
pub fn cmd_solve(
    result: &TranslationResult,
    timeout_ms: Option<u64>,
    fd_search: bool,
    all_solutions: bool,
) -> Result<()> {
    let global_deadline = timeout_ms.map(|ms| Instant::now() + Duration::from_millis(ms));
    let config = SolverConfig {
        timeout_ms,
        all_solutions,
        global_deadline,
    };
    let mut out = io::stdout().lock();
    if fd_search {
        ay_flatzinc_smt::solve_branching(result, &config, &mut out)
            .map_err(|e| Fzn2smtError::Solver(e.to_string()))?;
    } else {
        ay_flatzinc_smt::solve(result, &config, &mut out)
            .map_err(|e| Fzn2smtError::Solver(e.to_string()))?;
    }
    Ok(())
}
