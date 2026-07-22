// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental core evolution tracking (#8154, #8306).
//!
//! Computes how the UNSAT core changes between consecutive check-sat calls,
//! reporting which assertions persisted, entered, or exited the core.
//!
//! The heavy lifting is done by [`CoreEvolutionTracker`], which consumers can
//! also use directly for more flexible borrow patterns.

use crate::api::types::IncrementalCoreEvolution;
use crate::api::Solver;
use crate::SolverError;

impl Solver {
    /// Return the evolution of the UNSAT core since the last call.
    ///
    /// Returns `None` on the first UNSAT result (no previous core to diff)
    /// or if the last result was not UNSAT.
    ///
    /// For more flexible borrow patterns, use
    /// [`CoreEvolutionTracker`](crate::api::types::CoreEvolutionTracker) directly.
    pub fn core_evolution(&mut self) -> Option<IncrementalCoreEvolution> {
        self.try_core_evolution().ok().flatten()
    }

    /// Fallible version of [`core_evolution`](Solver::core_evolution).
    ///
    /// For more flexible borrow patterns, use
    /// [`CoreEvolutionTracker`](crate::api::types::CoreEvolutionTracker) directly.
    pub fn try_core_evolution(&mut self) -> Result<Option<IncrementalCoreEvolution>, SolverError> {
        let current_core_strings = match self.try_get_unsat_core() {
            Ok(core) => core,
            Err(_) => return Ok(None),
        };

        Ok(self.core_tracker.update(&current_core_strings))
    }
}
