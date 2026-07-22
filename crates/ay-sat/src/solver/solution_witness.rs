// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Online model-witness configuration and test-only assignment helpers.
//
// When a solution witness is configured, every derived clause is checked at
// insertion time. The first clause falsified by the witness triggers an
// immediate panic, enabling early diagnosis of wrong-UNSAT bugs.

/// Error returned by [`Solver::try_set_solution`] when witness length is invalid.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum SetSolutionError {
    /// Assignment vector is shorter than required user-visible variables.
    #[error(
        "set_solution requires at least user_num_vars assignments: got {got}, expected >= {min}"
    )]
    TooShort {
        /// Provided assignment length.
        got: usize,
        /// Minimum required length (`user_num_vars`).
        min: usize,
    },
    /// Assignment vector is longer than current solver variable count.
    #[error("set_solution assignment length exceeds solver vars: got {got}, max {max}")]
    TooLong {
        /// Provided assignment length.
        got: usize,
        /// Maximum accepted length (`num_vars`).
        max: usize,
    },
}

impl Solver {
    /// Test helper: set variable assignment via vals[] (#3758 Phase 3).
    /// Replaces direct `solver.assignment[var] = Some(val)` in tests.
    #[cfg(test)]
    pub(super) fn set_var_assignment(&mut self, var_idx: usize, val: Option<bool>) {
        match val {
            Some(true) => {
                self.vals[var_idx * 2] = 1;
                self.vals[var_idx * 2 + 1] = -1;
            }
            Some(false) => {
                self.vals[var_idx * 2] = -1;
                self.vals[var_idx * 2 + 1] = 1;
            }
            None => {
                self.vals[var_idx * 2] = 0;
                self.vals[var_idx * 2 + 1] = 0;
            }
        }
    }

    /// Test helper: get variable assignment as Option<bool> (#3758 Phase 3).
    /// Replaces direct `solver.assignment[var]` reads in tests.
    #[cfg(test)]
    pub(super) fn get_var_assignment(&self, var_idx: usize) -> Option<bool> {
        match self.vals[var_idx * 2] {
            0 => None,
            v => Some(v > 0),
        }
    }

    #[inline]
    #[cfg(test)]
    pub(super) fn forward_checker_derived_count(&self) -> Option<u64> {
        self.cold.forward_checker
            .as_ref()
            .map(crate::forward_checker::ForwardChecker::derived_count)
    }

    /// Configure an online model witness for derived-clause validation.
    ///
    /// This ports CaDiCaL's "Sam Buss trick" debugging mode: every learned
    /// clause is checked at insertion time, and the first clause falsified by
    /// the witness triggers an immediate panic.
    ///
    /// `solution` may provide either:
    /// - `user_num_vars` entries (user-visible variables only), or
    /// - `num_vars` entries (full assignment including internal variables).
    ///
    /// Any trailing internal variables not covered by `solution` are marked as
    /// unknown (`None`) and do not cause false violations.
    pub fn try_set_solution(&mut self, solution: &[bool]) -> Result<(), SetSolutionError> {
        if solution.len() < self.user_num_vars {
            return Err(SetSolutionError::TooShort {
                got: solution.len(),
                min: self.user_num_vars,
            });
        }
        if solution.len() > self.num_vars {
            return Err(SetSolutionError::TooLong {
                got: solution.len(),
                max: self.num_vars,
            });
        }

        let mut witness = vec![None; self.num_vars];
        for (slot, value) in witness.iter_mut().zip(solution.iter().copied()) {
            *slot = Some(value);
        }
        self.cold.solution_witness = Some(witness);
        Ok(())
    }

    /// Panicking compatibility wrapper for [`Solver::try_set_solution`].
    ///
    /// New call sites should prefer `try_set_solution` to avoid panics on
    /// ordinary input validation failures.
    pub fn set_solution(&mut self, solution: Vec<bool>) {
        if let Err(error) = self.try_set_solution(&solution) {
            panic!("{error}");
        }
    }

    /// Disable online model-witness checking for learned clauses.
    pub fn clear_solution(&mut self) {
        self.cold.solution_witness = None;
    }

    /// Load a solution from a file in SAT competition format.
    ///
    /// The file should contain `v`-lines with DIMACS literals terminated by `0`:
    /// ```text
    /// s SATISFIABLE
    /// v 1 -2 3 0
    /// v 4 -5 0
    /// ```
    ///
    /// Positive literal `n` means variable `n-1` is true; negative literal `-n`
    /// means variable `n-1` is false. The `s` line is optional and ignored.
    ///
    /// After loading, every learned clause is checked against this assignment.
    /// The first unsatisfied learned clause triggers an immediate panic with the
    /// offending clause, for diagnosing wrong-UNSAT bugs.
    pub(crate) fn load_solution_file(&mut self, path: &str) -> std::io::Result<()> {
        use std::io::{BufRead, BufReader};

        let file = std::fs::File::open(path)?;
        let reader = BufReader::new(file);
        let mut assignment = vec![false; self.user_num_vars];

        for line in reader.lines() {
            let line = line?;
            let trimmed = line.trim();
            if !trimmed.starts_with('v') {
                continue;
            }
            // Parse "v 1 -2 3 0" — skip the 'v' prefix
            for token in trimmed[1..].split_whitespace() {
                let lit: i64 = match token.parse() {
                    Ok(n) => n,
                    Err(_) => continue,
                };
                if lit == 0 {
                    break;
                }
                let var_idx = (lit.unsigned_abs() as usize).saturating_sub(1);
                if var_idx < assignment.len() {
                    assignment[var_idx] = lit > 0;
                }
            }
        }

        self.set_solution(assignment);
        Ok(())
    }

    /// Load a solution witness from the `AY_SOLUTION_FILE` environment variable.
    ///
    /// No-op if the variable is not set. Panics if the file cannot be read.
    pub fn maybe_load_solution_from_env(&mut self) {
        // Delegates to ay-core's centralized TraceConfig (#8495).
        if let Some(path) = &ay_core::trace_config().solution_file_path {
            self.load_solution_file(path)
                .unwrap_or_else(|e| panic!("AY_SOLUTION_FILE={path}: {e}"));
        }
    }

    /// Last SAT-side `Unknown` reason from the most recent solve call.
    ///
    /// Returns `None` when no solve has returned `Unknown` since the last reset.
    #[must_use]
    pub fn last_unknown_reason(&self) -> Option<SatUnknownReason> {
        self.cold.last_unknown_reason
    }

    /// Human-readable detail explaining WHY the last Unknown was produced (#7917).
    ///
    /// When `last_unknown_reason()` returns `InvalidSatModel`, this provides
    /// the specific failure: which original clause was unsatisfied, whether
    /// reconstruction panicked, etc. Returns `None` for non-finalization
    /// Unknown reasons or when no detail was captured.
    #[must_use]
    pub fn last_unknown_detail(&self) -> Option<&str> {
        self.cold.last_unknown_detail.as_deref()
    }
}
