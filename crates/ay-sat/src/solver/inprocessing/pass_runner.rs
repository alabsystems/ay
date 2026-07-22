// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared helpers for running inprocessing passes from the restart scheduler.

use super::*;
use std::io::Write;

impl Solver {
    /// Run one inprocessing pass with scoped diagnostic tracing.
    #[inline]
    pub(super) fn run_diagnostic_inprocessing_pass<T>(
        &mut self,
        pass: DiagnosticPass,
        run: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.set_diagnostic_pass(pass);
        let result = run(self);
        self.clear_diagnostic_pass();
        result
    }

    /// Run full level-0 propagation after a pass and return whether UNSAT was derived.
    #[inline]
    pub(super) fn propagate_level0_unsat_after_pass(&mut self) -> bool {
        self.propagate_check_unsat()
    }

    /// Run propagation after a pass and record the conflict chain if a level-0 conflict appears.
    #[inline]
    pub(super) fn propagate_level0_conflict_after_pass(&mut self) -> bool {
        if let Some(conflict_ref) = self.propagate() {
            self.record_level0_conflict_chain(conflict_ref);
            return true;
        }
        false
    }
}
