// Copyright 2026 Andrew Yates
// Backward DRAT checking: verify only clauses needed for the empty clause
// derivation. Typically 10-100x faster than forward checking on industrial
// proofs. Algorithm from drat-trim (Heule & Wetzler 2014).
//
// Two-pass: (1) forward replay building clause DB + watches + trail, mark
// ACTIVE from empty clause; (2) backward walk verifying only ACTIVE steps,
// marking more clauses via MARK-based conflict analysis (drat-trim parity).

#[cfg(test)]
use crate::drat_parser::ProofStep;
use crate::literal::Literal;

use super::{DratChecker, Stats};

mod mark_active;
mod verify;

/// Record of a proof step with its clause index in the arena.
#[derive(Clone, Copy)]
struct StepRecord {
    cidx: usize,
    is_delete: bool,
    /// Trail length before this step was applied. Used to unwind
    /// transitive propagations when undoing additions in the backward pass.
    trail_len_before: usize,
}

/// Backward DRAT checker.
///
/// Wraps a `DratChecker` for the BCP engine and adds ACTIVE marking
/// and the two-pass backward algorithm. Reason tracking is handled by
/// `DratChecker.reasons` (set during BCP via `assign_with_reason`).
pub struct BackwardChecker {
    inner: DratChecker,
    /// ACTIVE flag per clause index. Only ACTIVE clauses are verified
    /// in the backward pass.
    active: Vec<bool>,
    /// Records of proof steps mapped to clause indices.
    step_records: Vec<StepRecord>,
    /// Number of original clauses (before proof steps).
    num_original: usize,
    /// Clause index where the empty clause was derived (or conflict detected).
    conflict_cidx: Option<usize>,
    /// Step index (into step_records/steps) where the conflict was found.
    conflict_step: Option<usize>,
}

impl BackwardChecker {
    pub fn new(num_vars: usize, check_rat: bool) -> Self {
        Self {
            inner: DratChecker::new(num_vars, check_rat),
            active: Vec::new(),
            step_records: Vec::new(),
            num_original: 0,
            conflict_cidx: None,
            conflict_step: None,
        }
    }

    pub fn stats(&self) -> &Stats {
        &self.inner.stats
    }

    /// Returns true if a clause at `cidx` was marked ACTIVE during
    /// backward verification. Used for testing dependency tracking.
    #[cfg(test)]
    pub(crate) fn is_active(&self, cidx: usize) -> bool {
        cidx < self.active.len() && self.active[cidx]
    }
}

/// Remove literals at the given positions from a clause.
/// Positions must be sorted ascending. drat-trim.c:174-179.
fn reduce_clause(clause: &[Literal], positions: &[usize]) -> Vec<Literal> {
    let mut reduced = Vec::with_capacity(clause.len() - positions.len());
    let mut remove_iter = positions.iter().peekable();
    for (i, &lit) in clause.iter().enumerate() {
        if remove_iter.peek() == Some(&&i) {
            remove_iter.next();
        } else {
            reduced.push(lit);
        }
    }
    reduced
}

#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_backward_rejection;
#[cfg(test)]
mod tests_boundary;
#[cfg(test)]
mod tests_clause_reduction;
#[cfg(test)]
mod tests_core_first;
#[cfg(test)]
mod tests_exhaustive;
#[cfg(test)]
mod tests_proptest;
#[cfg(test)]
mod tests_rat;
#[cfg(test)]
mod tests_regression;
