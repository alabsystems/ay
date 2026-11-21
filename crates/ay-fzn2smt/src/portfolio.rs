// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `ay flatzinc solve` portfolio: the direct CP engine when it supports
//! every constraint and its encoding fits, otherwise the SMT path.
//!
//! It writes the MiniZinc solution stream to a caller's writer so that the
//! CLI can supervise what was printed (see [`crate::memory_guard`]) and tests
//! can read it.

use std::io::Write;
use std::time::{Duration, Instant};

use ay_flatzinc_parser::ast::FznModel;

use crate::error::{Fzn2smtError, Result};

/// What `ay flatzinc solve` was asked to do.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PortfolioOptions {
    /// `-t`: wall-clock limit for the whole run in milliseconds; `None` means
    /// no limit of ay's own.
    pub timeout_ms: Option<u64>,
    /// Force the FD-track branching search on the SMT path.
    pub fd_search: bool,
    /// `-a`: enumerate all solutions.
    pub all_solutions: bool,
    /// `-f`: ignore search annotations.
    pub free_search: bool,
    /// `-p`: parallel workers (the CP portfolio clamps the count).
    pub parallel_workers: usize,
}

/// Solve `model` and write the FlatZinc solution stream to `out`; warnings
/// and notes go to `err`. `started` is when the run began: `-t` bounds the
/// whole run, so a backend that starts late gets what remains of it.
///
/// # Errors
///
/// A model neither backend accepts, an invalid timeout, a solver failure or
/// a write failure. A CP capacity decline is not an error: the SMT path takes
/// the model, and if it cannot translate it the answer is UNKNOWN.
pub fn solve_portfolio(
    model: &FznModel,
    options: &PortfolioOptions,
    started: Instant,
    out: &mut impl Write,
    err: &mut impl Write,
) -> Result<()> {
    // Probe the CP backend for unsupported constraints.
    let cp_unsupported = match crate::solve_cp::unsupported_constraints(model) {
        Ok(unsupported) => Some(unsupported),
        Err(e) => {
            writeln!(
                err,
                "warning: CP backend probe failed, falling back to SMT: {e}"
            )?;
            None
        }
    };

    let use_cp = cp_unsupported.as_ref().is_some_and(Vec::is_empty);
    let mut cp_declined = false;
    if use_cp {
        match crate::solve_cp::cmd_solve_cp_with_writers(
            model,
            options.timeout_ms,
            options.all_solutions,
            options.parallel_workers,
            cp_unsupported.as_deref(),
            out,
            err,
        ) {
            Ok(()) => return Ok(()),
            // The CP engine printed nothing: give the model, and the time
            // that remains, to the SMT path instead of answering UNKNOWN.
            Err(Fzn2smtError::CpEncodingCapacity(reason)) => {
                writeln!(
                    err,
                    "info: CP backend declined ({reason}); falling back to SMT"
                )?;
                cp_declined = true;
            }
            Err(e) => return Err(e),
        }
    }

    // Fall back to SMT solve path.
    let result = match ay_flatzinc_smt::translate(model) {
        Ok(result) => result,
        // After a CP capacity decline, an SMT translation failure leaves
        // the model unsolved, not erroneous: report UNKNOWN as before.
        Err(e) if cp_declined => {
            writeln!(err, "warning: SMT fallback cannot translate the model: {e}")?;
            writeln!(out, "=====UNKNOWN=====")?;
            out.flush()?;
            return Ok(());
        }
        Err(e) => return Err(Fzn2smtError::Message(format!("translation error: {e}"))),
    };

    // Auto-activate branching search when the model has search annotations
    // and the user didn't explicitly request free search with -f.
    let fd_search =
        options.fd_search || (!options.free_search && !result.search_annotations.is_empty());

    // `-t` bounds the whole run: after a CP decline, the SMT path gets what
    // remains of it, not a fresh budget.
    let timeout_ms = if cp_declined {
        let elapsed = started.elapsed();
        options
            .timeout_ms
            .map(|ms| remaining_timeout_ms(ms, elapsed))
    } else {
        options.timeout_ms
    };
    crate::solve::solve_translated(&result, timeout_ms, fd_search, options.all_solutions, out)
}

/// What remains of a `-t` of `timeout_ms` after `elapsed`: never 0, which
/// would read as "no time at all" in some solver layers, so at least 1 ms.
#[must_use]
pub fn remaining_timeout_ms(timeout_ms: u64, elapsed: Duration) -> u64 {
    let spent = u64::try_from(elapsed.as_millis()).unwrap_or(u64::MAX);
    timeout_ms.saturating_sub(spent).max(1)
}

#[cfg(test)]
#[path = "portfolio_tests.rs"]
mod tests;
