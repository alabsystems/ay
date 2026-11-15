// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Own detached buffers before any fallible operation can run. On a terminal
/// refusal/unwind no stale cursor may claim an unfinished suffix was scanned.
pub(in crate::solver) struct Scratch<'s, 'p> {
    pub(in crate::solver) solver: &'s mut Solver,
    pub(in crate::solver) pinned: Vec<usize>,
    pub(in crate::solver) hints: Vec<u64>,
    pub(in crate::solver) kept: usize,
    pub(in crate::solver) cursor: usize,
    pub(in crate::solver) complete: bool,
    owner: Option<&'p CountedAdmission>,
}

impl<'s, 'p> Scratch<'s, 'p> {
    pub(in crate::solver) fn new(
        solver: &'s mut Solver,
        owner: Option<&'p CountedAdmission>,
    ) -> Self {
        let pinned = std::mem::take(&mut solver.cold.lrat_level0_unit_materialize_pinned);
        let hints = std::mem::take(&mut solver.cold.lrat_materialize_hints_buf);
        Self {
            solver,
            pinned,
            hints,
            kept: 0,
            cursor: 0,
            complete: false,
            owner,
        }
    }
}

impl Drop for Scratch<'_, '_> {
    fn drop(&mut self) {
        if !self.complete {
            if let Some(owner) = self.owner {
                if std::thread::panicking() {
                    owner.refuse(CountedAdmissionError::Original(
                        OriginalAdmissionError::OperationPanicked,
                    ));
                }
                if let Some(trace) = self.solver.cold.clause_trace.as_mut() {
                    trace.mark_proof_work_exhausted();
                }
                if let Some(writer) = self.solver.cold.decision_trace.take() {
                    writer.discard_without_flush();
                }
            }
            self.kept = 0;
            self.cursor = 0; // any later ordinary use must rescan the full prefix
        }
        self.hints.clear();
        self.pinned.truncate(self.kept);
        self.solver.cold.lrat_materialize_hints_buf = std::mem::take(&mut self.hints);
        self.solver.cold.lrat_level0_unit_materialize_pinned = std::mem::take(&mut self.pinned);
        self.solver.cold.lrat_level0_unit_materialize_cursor = self.cursor;
    }
}
