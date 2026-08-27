// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory closure entry points for DPLL(T)-style solving.

use super::super::*;
use super::theory_callback::TheoryClosureCallback;

impl Solver {
    /// Solve with theory propagation callback
    ///
    /// Similar to `solve_interruptible`, but the callback is called after each
    /// propagation round (before making a decision). This allows integration
    /// with theory solvers for DPLL(T)-style solving.
    ///
    /// The callback receives `&mut self` access to add clauses via `add_clause()`.
    /// It should return:
    /// - `TheoryPropResult::Continue` if no propagations were found
    /// - `TheoryPropResult::Propagate` if clauses were added (triggers re-propagation)
    /// - `TheoryPropResult::Conflict(clause)` if a conflict was detected
    /// - `TheoryPropResult::Stop` to interrupt solving
    ///
    /// Note: For full DPLL(T), use this in combination with `trail()` and `value()`
    /// to incrementally sync theory state and check for propagations.
    pub fn solve_with_theory<F>(&mut self, theory_check: F) -> SolverSatResult
    where
        F: FnMut(&mut Self) -> TheoryPropResult,
    {
        SolverSatResult::from_solver_result(self.solve_with_theory_raw(theory_check))
    }

    /// Internal theory solve returning raw `SatResult`.
    fn solve_with_theory_raw<F>(&mut self, theory_check: F) -> SatResult
    where
        F: FnMut(&mut Self) -> TheoryPropResult,
    {
        self.cold.last_unknown_reason = None;
        self.cold.last_unknown_detail = None;

        if let Some(result) = self.finish_stopped_sat_entry(&|| false) {
            return result;
        }

        if self.has_empty_clause {
            let result = self.declare_unsat();
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        if self.cold.scope_selectors.is_empty() {
            let result = self.solve_no_assumptions_with_theory(theory_check);
            self.trace_sat_result(&result);
            self.finish_tla_trace();
            return result;
        }

        let assumptions = self.compose_scope_assumptions(&[]);

        // Thread theory callback through assumption-based solving (#3343)
        let mut theory_check = theory_check;
        let result = match self.solve_with_assumptions_impl(
            &assumptions,
            None::<&fn() -> bool>,
            Some(&mut theory_check),
            None,
            None,
        ) {
            AssumeResult::Sat(model) => {
                self.sat_from_assume_model(model, "solve_with_theory() scope-selector path")
            }
            AssumeResult::Unsat(..) => SatResult::Unsat(ProofCertificate::empty()),
            AssumeResult::Unknown => SatResult::Unknown,
        };
        self.trace_sat_result(&result);
        self.finish_tla_trace();
        result
    }

    pub(super) fn solve_no_assumptions_with_theory<F>(&mut self, mut theory_check: F) -> SatResult
    where
        F: FnMut(&mut Self) -> TheoryPropResult,
    {
        let mut callback = TheoryClosureCallback {
            theory_check: &mut theory_check,
        };
        self.solve_no_assumptions_with_theory_backend(&mut callback, || false)
    }
}
