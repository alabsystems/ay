// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl QbfSolver {
    /// Get variable assignment
    pub(super) fn value(&self, var: u32) -> Assignment {
        if var > 0 && (var as usize) <= self.assignments.len() {
            self.assignments[var as usize - 1]
        } else {
            Assignment::Unassigned
        }
    }

    /// Get literal value
    pub(super) fn lit_value(&self, lit: Literal) -> Assignment {
        let var_val = self.value(lit.variable().id());
        match var_val {
            Assignment::Unassigned => Assignment::Unassigned,
            Assignment::True => {
                if lit.is_positive() {
                    Assignment::True
                } else {
                    Assignment::False
                }
            }
            Assignment::False => {
                if lit.is_positive() {
                    Assignment::False
                } else {
                    Assignment::True
                }
            }
        }
    }

    /// Assign a variable
    ///
    /// Variable ids are 1-based. Id 0 has no slot, and [`Self::value`]
    /// already reports it as unassigned, so assigning it records nothing.
    pub(super) fn assign(&mut self, lit: Literal, reason: Reason) {
        let var = lit.variable().id();
        let Some(slot) = (var as usize).checked_sub(1) else {
            return;
        };
        let value = if lit.is_positive() {
            Assignment::True
        } else {
            Assignment::False
        };

        self.assignments[slot] = value;
        self.levels[slot] = self.decision_level;
        self.reasons[slot] = reason;
        self.trail.push(lit);
    }

    /// Unassign variables back to a given trail position
    pub(super) fn unassign_to(&mut self, pos: usize) {
        while self.trail.len() > pos {
            let lit = self
                .trail
                .pop()
                .expect("loop guard checked trail.len() > pos");
            // `assign` never puts slot-less variable 0 on the trail.
            let Some(slot) = (lit.variable().id() as usize).checked_sub(1) else {
                continue;
            };
            self.assignments[slot] = Assignment::Unassigned;
        }
    }

    /// Check if all variables are assigned
    pub(super) fn all_assigned(&self) -> bool {
        self.assignments.iter().all(|a| a.is_assigned())
    }

    /// Check if formula is satisfied under current assignment
    pub(super) fn is_satisfied(&self) -> bool {
        // Check all original clauses
        for clause in self.formula.clauses() {
            if !self.clause_satisfied(clause) {
                return false;
            }
        }
        // Check all learned clauses
        for clause in &self.learned {
            if !self.clause_satisfied(clause) {
                return false;
            }
        }
        true
    }

    /// Check if a clause is satisfied
    pub(super) fn clause_satisfied(&self, clause: &[Literal]) -> bool {
        clause
            .iter()
            .any(|&lit| self.lit_value(lit) == Assignment::True)
    }
}
