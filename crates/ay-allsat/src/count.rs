// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Definitive predicates derived from model enumeration.

use crate::{AllSatConfig, AllSatIncomplete, AllSatOutcome, AllSatSolver, AllSatStats};

fn incomplete_from_stats(stats: &AllSatStats) -> AllSatIncomplete {
    AllSatIncomplete {
        outcome: stats.outcome,
        solutions_found: stats.solutions_found,
        input_error: stats.input_error,
    }
}

impl AllSatSolver {
    /// Count all solutions exactly without storing them.
    ///
    /// Returns an error instead of a partial count if the SAT backend stops
    /// without proving exhaustion.
    pub fn count(&mut self) -> Result<u64, AllSatIncomplete> {
        self.count_with_config(AllSatConfig::default())
    }

    /// Count with custom configuration.
    ///
    /// Returns an error if the cap or SAT backend stops enumeration before
    /// exhaustion is proved. The error reports the partial number of solutions
    /// found, but that number must not be treated as the exact count.
    pub fn count_with_config(&mut self, config: AllSatConfig) -> Result<u64, AllSatIncomplete> {
        let mut count = 0u64;
        let mut overflowed = false;
        let stats = self.enumerate_with_callback(config, |_| {
            if let Some(next) = count.checked_add(1) {
                count = next;
                true
            } else {
                overflowed = true;
                false
            }
        });
        if overflowed {
            self.set_last_outcome(AllSatOutcome::CountOverflow, None);
            Err(AllSatIncomplete {
                outcome: AllSatOutcome::CountOverflow,
                solutions_found: u64::MAX,
                input_error: None,
            })
        } else if stats.outcome == AllSatOutcome::Exhaustive {
            Ok(count)
        } else {
            Err(incomplete_from_stats(&stats))
        }
    }

    /// Check if the formula is satisfiable.
    ///
    /// A discovered model proves satisfiability. If no model is found and the
    /// backend returns Unknown, this fails closed instead of reporting UNSAT.
    pub fn is_sat(&mut self) -> Result<bool, AllSatIncomplete> {
        let config = AllSatConfig {
            max_solutions: Some(1),
            ..Default::default()
        };
        let stats = self.enumerate_with_callback(config, |_| true);
        if stats.solutions_found > 0 {
            Ok(true)
        } else if stats.outcome == AllSatOutcome::Exhaustive {
            Ok(false)
        } else {
            Err(incomplete_from_stats(&stats))
        }
    }

    /// Check if the formula has exactly one solution.
    ///
    /// Two discovered models prove non-uniqueness. If fewer models are found
    /// and the backend cannot prove exhaustion, this fails closed.
    pub fn has_unique_solution(&mut self) -> Result<bool, AllSatIncomplete> {
        let config = AllSatConfig {
            max_solutions: Some(2),
            ..Default::default()
        };
        let stats = self.enumerate_with_callback(config, |_| true);
        if stats.solutions_found >= 2 {
            Ok(false)
        } else if stats.outcome == AllSatOutcome::Exhaustive {
            Ok(stats.solutions_found == 1)
        } else {
            Err(incomplete_from_stats(&stats))
        }
    }
}
