// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The undo record of factoring's candidate marks under a proof transaction.

use super::*;

impl Solver {
    /// Open a factoring application's undo record of the candidate marks: the
    /// writes from here on are logged, so a rejected application restores
    /// them at the cost of the marks it touched. A copy of all the marks per
    /// application cost O(variables) each time, quadratic over a pass: on
    /// dbbcaa77 (229K factors over 780K variables) it was 8 s of copying and
    /// 8 s of unmapping, half the solve, and only under a proof.
    pub(super) fn begin_factor_candidate_marks_undo(&mut self) {
        self.cold.factor_marks_undo = Some((self.cold.factor_candidate_marks.len(), Vec::new()));
    }

    /// Close the undo record; with `rollback`, restore every logged mark and
    /// the length the marks had when it opened.
    pub(super) fn end_factor_candidate_marks_undo(&mut self, rollback: bool) {
        let Some((len, writes)) = self.cold.factor_marks_undo.take() else {
            return;
        };
        if rollback {
            for &(var, old) in writes.iter().rev() {
                if let Some(mark) = self.cold.factor_candidate_marks.get_mut(var as usize) {
                    *mark = old;
                }
            }
            self.cold.factor_candidate_marks.truncate(len);
        }
    }
}
