// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CaDiCaL-style temporary constraint clause API (#8207).
//!
//! The `constrain()` method adds a temporary clause that is active for exactly
//! one `solve_with_assumptions()` call. After the solve returns, the constraint
//! is automatically cleared. This avoids the activation literal overhead pattern
//! used by IC3/PDR engines where each temporary clause creates a permanent
//! variable that accumulates garbage over thousands of iterations.
//!
//! ## Design
//!
//! The constraint is handled as a "pseudo-assumption" after all real
//! assumptions are decided. If any constraint literal is already satisfied
//! by assumptions, the constraint is trivially met. If there is an
//! unassigned literal, it is decided to satisfy the constraint. If all
//! literals are falsified, the solve returns UNSAT.
//!
//! ## Reference
//!
//! - CaDiCaL `constrain.cpp` (constraint addition and normalization)
//! - CaDiCaL `decide.cpp:237-320` (constraint handling in CDCL loop)
//! - CaDiCaL `internal.hpp:260-261` (constraint state fields)

use super::*;

impl Solver {
    /// Add a temporary constraint clause active for exactly one solve call.
    ///
    /// The constraint clause is automatically cleared after the next
    /// `solve_with_assumptions()` or `solve_with_assumptions_interruptible()`
    /// call returns. If the constraint has zero satisfiable literals after
    /// assumptions, the solve returns UNSAT.
    ///
    /// This is the ay-sat equivalent of CaDiCaL's `constrain()` API.
    /// It avoids the activation literal overhead used by IC3/PDR engines
    /// where each temporary clause creates a permanent variable.
    ///
    /// # Semantics
    ///
    /// - An empty constraint is immediately unsatisfiable.
    /// - A tautological constraint (containing both `x` and `!x`) is ignored.
    /// - Calling `constrain()` again replaces the previous constraint.
    /// - The constraint is consumed by the next solve call and cleared.
    pub fn constrain(&mut self, clause: &[Literal]) {
        // Clear any previous constraint
        self.reset_constraint();

        if clause.is_empty() {
            // Empty constraint is immediately unsatisfiable
            self.cold.unsat_constraint = true;
            return;
        }

        // Normalize: sort, deduplicate, check for tautology
        let mut lits: Vec<Literal> = clause.to_vec();
        lits.sort_by_key(|l| l.0);
        lits.dedup();

        // Tautology check: complementary literals (x and !x)
        for i in 1..lits.len() {
            if lits[i].variable() == lits[i - 1].variable() {
                // Tautological constraint — always satisfied, no-op
                return;
            }
        }

        // Filter out-of-range variables and keep valid literals.
        //
        // NOTE: CaDiCaL simplifies against level-0 values here (constrain.cpp:24-36),
        // but that works because CaDiCaL backtracks to level 0 at the start of
        // constrain(). In ay-sat, vals[] between solve calls contains stale data
        // from the previous solve (full assignment, not just level-0 propagations).
        // reset_search_state() clears vals at the start of the next solve.
        // Simplifying against stale vals causes false UNSAT when a constraint
        // literal was coincidentally falsified in the previous solve's model.
        // Instead, defer value-based simplification to handle_constraint() which
        // runs during the CDCL loop when vals[] is authoritative.
        let mut kept = Vec::with_capacity(lits.len());
        for &lit in &lits {
            let var_idx = lit.variable().index();
            if var_idx >= self.num_vars {
                continue;
            }
            kept.push(lit);
        }

        if kept.is_empty() {
            // All literals out of range — constraint is UNSAT
            self.cold.unsat_constraint = true;
            return;
        }

        // CaDiCaL constrain.cpp:48-49: Freeze constraint variables to protect
        // them from elimination during inprocessing.
        for &lit in &kept {
            self.freeze(lit.variable());
        }

        self.cold.constraint = kept;
    }

    /// Returns true if the constraint was used to prove unsatisfiability.
    ///
    /// Only meaningful after a `solve_with_assumptions()` call that returned
    /// UNSAT. If the constraint clause was the reason for UNSAT (all its
    /// literals were falsified by the assumptions), this returns `true`.
    ///
    /// Reference: CaDiCaL `failed_constraint()` (constrain.cpp:53)
    #[inline]
    pub fn failed_constraint(&self) -> bool {
        self.cold.unsat_constraint
    }

    /// Clear the constraint state after a solve call.
    ///
    /// Melts (unfreezes) constraint variables and clears the constraint
    /// literals. Called automatically at the start of each solve call.
    /// Can also be called manually to cancel a pending constraint.
    ///
    /// Reference: CaDiCaL `reset_constraint()` (constrain.cpp:55-62)
    pub(super) fn reset_constraint(&mut self) {
        // Melt (unfreeze) constraint variables
        for i in 0..self.cold.constraint.len() {
            let var = self.cold.constraint[i].variable();
            self.melt(var);
        }
        self.cold.constraint.clear();
        self.cold.unsat_constraint = false;
    }

    /// Handle the constraint clause during the CDCL assumption loop.
    ///
    /// Called after all assumptions are decided. Returns:
    /// - `Proceed` if the constraint is satisfied or not active
    /// - `Continue` if a decision was made to satisfy the constraint
    /// - `Unsat(core)` if the constraint is violated (all literals falsified)
    ///
    /// Reference: CaDiCaL decide.cpp:237-320
    pub(super) fn handle_constraint(&mut self, failed_assumptions: &[Literal]) -> ConstraintAction {
        if self.cold.constraint.is_empty() {
            return ConstraintAction::Proceed;
        }

        let mut satisfied = false;
        let mut best_unassigned: Option<Literal> = None;

        for &lit in &self.cold.constraint {
            let val = self.vals[lit.index()];
            if val > 0 {
                // Literal is true — constraint is satisfied
                satisfied = true;
                break;
            }
            if val == 0 && best_unassigned.is_none() {
                best_unassigned = Some(lit);
            }
        }

        if satisfied {
            // Constraint already satisfied by assumptions — proceed normally
            // CaDiCaL decide.cpp:277-287
            ConstraintAction::Proceed
        } else if let Some(lit) = best_unassigned {
            // Decide the unassigned literal to satisfy the constraint.
            // CaDiCaL decide.cpp:303-306.
            self.decide(lit);
            ConstraintAction::Continue
        } else {
            // All constraint literals falsified -> UNSAT
            // CaDiCaL decide.cpp:308-312.
            self.cold.unsat_constraint = true;
            ConstraintAction::Unsat(failed_assumptions.to_vec())
        }
    }
}

/// Result of constraint handling in the CDCL loop.
pub(super) enum ConstraintAction {
    /// Constraint is satisfied or not active — proceed to regular decisions.
    Proceed,
    /// A decision was made to satisfy the constraint — continue propagation.
    Continue,
    /// All constraint literals falsified — return UNSAT with failed assumptions.
    Unsat(Vec<Literal>),
}
