// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{FpSolver, FpSolverStandalone};
use ay_core::{TheoryPropagation, TheoryResult, TheorySolver};

mod reset;

impl TheorySolver for FpSolver<'_> {
    fn assert_literal(&mut self, _literal: ay_core::term::TermId, _value: bool) {}

    fn check(&mut self) -> TheoryResult {
        self.check_count += 1;
        tracing::debug!("FP check: sat (eager bit-blast)");
        if self.debug {
            tracing::trace!(
                terms = self.term_to_fp.len(),
                clauses = self.clauses.len(),
                "FP check verbose (eager bit-blast, trivially sat)"
            );
        }
        TheoryResult::Sat
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        Vec::new()
    }

    fn collect_statistics(&self) -> Vec<(&'static str, u64)> {
        vec![
            ("fp_checks", self.check_count),
            ("fp_conflicts", self.conflict_count),
            ("fp_propagations", self.propagation_count),
        ]
    }

    fn push(&mut self) {}

    fn pop(&mut self) {}

    fn reset(&mut self) {
        self.reset_encoding_state();
    }
}

impl TheorySolver for FpSolverStandalone {
    fn assert_literal(&mut self, _literal: ay_core::term::TermId, _value: bool) {}

    fn check(&mut self) -> TheoryResult {
        tracing::debug!("FP standalone check: sat (eager bit-blast)");
        TheoryResult::Sat
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        Vec::new()
    }

    fn push(&mut self) {
        self.trail_stack.push(self.trail.len());
    }

    fn pop(&mut self) {
        if let Some(len) = self.trail_stack.pop() {
            self.trail.truncate(len);
        }
    }

    fn reset(&mut self) {
        self.clauses.clear();
        self.next_var = 1;
        self.trail.clear();
        self.trail_stack.clear();
        // Shrink collections that may have grown (#8599).
        self.clauses.shrink_to_fit();
        self.trail.shrink_to_fit();
        self.trail_stack.shrink_to_fit();
    }
}
