// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::term::TermId;
use ay_core::CnfClause;

/// Standalone FP solver placeholder.
pub struct FpSolverStandalone {
    pub(crate) clauses: Vec<CnfClause>,
    pub(crate) next_var: u32,
    pub(crate) trail: Vec<TermId>,
    pub(crate) trail_stack: Vec<usize>,
}

impl FpSolverStandalone {
    /// Create a new standalone FP solver.
    #[must_use]
    pub fn new() -> Self {
        Self {
            clauses: Vec::new(),
            next_var: 1,
            trail: Vec::new(),
            trail_stack: Vec::new(),
        }
    }

    /// Push a new scope. Records the current trail length for later pop.
    pub fn push(&mut self) {
        self.trail_stack.push(self.trail.len());
    }

    /// Pop the most recent scope, restoring trail to the saved position.
    pub fn pop(&mut self) {
        if let Some(saved_len) = self.trail_stack.pop() {
            self.trail.truncate(saved_len);
        }
    }

    /// Reset all state to initial values.
    pub fn reset(&mut self) {
        self.clauses.clear();
        self.trail.clear();
        self.trail_stack.clear();
        self.next_var = 1;
    }
}

impl Default for FpSolverStandalone {
    fn default() -> Self {
        Self::new()
    }
}
