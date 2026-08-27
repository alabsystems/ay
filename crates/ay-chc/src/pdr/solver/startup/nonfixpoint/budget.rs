// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `startup::nonfixpoint` to preserve private paths.

/// Check whether the non-fixpoint startup budget is exhausted.
impl PdrSolver {
    fn nonfixpoint_budget_exceeded(
        &self,
        start: ay_core::time::Instant,
        budget: Option<std::time::Duration>,
    ) -> bool {
        if let Some(b) = budget {
            if start.elapsed() >= b {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Non-fixpoint startup budget exhausted ({:?} >= {:?}), skipping remaining passes",
                        start.elapsed(),
                        b
                    );
                }
                return true;
            }
        }
        false
    }
}
