// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Panic-safe wrappers for `check_sat` and `check_sat_assuming`.

use ay_core::panic_payload_to_string;

use std::time::Duration;

use crate::api::types::{
    AssumptionSolveDetails, SolveDetails, SolverError, Term, VerifiedSolveResult,
};
use crate::api::Solver;

impl Solver {
    /// Convert an infallible solve's recorded artifact-export failure back into
    /// a typed error for the `try_check_sat*` contract.
    fn fail_on_artifact_export<T>(&self, value: T) -> Result<T, SolverError> {
        if let Some(error) = self.last_artifact_export_error() {
            Err(error)
        } else {
            Ok(value)
        }
    }

    /// Check satisfiability, catching any internal panics.
    ///
    /// This is a panic-safe wrapper around [`check_sat`]. If the solver panics
    /// during solving, the panic is caught and returned as
    /// [`SolverError::SolverPanic`] instead of unwinding the caller's stack.
    ///
    /// Downstream consumers (verification-consumer, deductive-checks, model-checker-consumer) can use this instead of
    /// independently implementing `catch_unwind(AssertUnwindSafe(...))` wrappers.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Solver, Logic, SolveResult};
    ///
    /// let mut solver = Solver::new(Logic::QfLia);
    /// let x = solver.declare_const("x", ay_dpll::api::Sort::Int);
    /// let zero = solver.int_const(0);
    /// let gt = solver.gt(x, zero);
    /// solver.assert_term(gt);
    ///
    /// let result = solver.try_check_sat();
    /// assert!(result.is_ok());
    /// assert_eq!(result.unwrap(), SolveResult::Sat);
    /// ```
    ///
    /// [`check_sat`]: Solver::check_sat
    pub fn try_check_sat(&mut self) -> Result<VerifiedSolveResult, SolverError> {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.check_sat()))
            .map_err(|e| SolverError::SolverPanic(panic_payload_to_string(&*e)))?;
        self.fail_on_artifact_export(result)
    }

    /// Check satisfiability under temporary assumptions, catching any internal panics.
    ///
    /// This is a panic-safe wrapper around [`check_sat_assuming`]. If the solver
    /// panics during solving, the panic is caught and returned as
    /// [`SolverError::SolverPanic`].
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Solver, Logic, SolveResult, Sort};
    ///
    /// let mut solver = Solver::new(Logic::QfLia);
    /// let x = solver.declare_const("x", Sort::Int);
    /// let zero = solver.int_const(0);
    /// let x_gt_0 = solver.gt(x, zero);
    /// solver.assert_term(x_gt_0);
    ///
    /// let x_lt_0 = solver.lt(x, zero);
    /// let result = solver.try_check_sat_assuming(&[x_lt_0]);
    /// assert!(result.is_ok());
    /// assert!(result.unwrap().is_unsat());
    /// ```
    ///
    /// [`check_sat_assuming`]: Solver::check_sat_assuming
    pub fn try_check_sat_assuming(
        &mut self,
        assumptions: &[Term],
    ) -> Result<VerifiedSolveResult, SolverError> {
        self.resolve_terms("check_sat_assuming", assumptions)?;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.check_sat_assuming(assumptions)
        }))
        .map_err(|e| SolverError::SolverPanic(panic_payload_to_string(&*e)))?;
        self.fail_on_artifact_export(result)
    }

    /// Check satisfiability with a per-call timeout, catching any internal panics.
    ///
    /// Panic-safe wrapper around [`check_sat_with_timeout`]. On panic, returns
    /// [`SolverError::SolverPanic`] instead of unwinding.
    ///
    /// [`check_sat_with_timeout`]: Solver::check_sat_with_timeout
    pub fn try_check_sat_with_timeout(
        &mut self,
        timeout: Duration,
    ) -> Result<VerifiedSolveResult, SolverError> {
        // Restore the configured timeout even if solving panics. Calling the
        // infallible convenience method inside `catch_unwind` would otherwise
        // leave its temporary override installed on the poisoned solver.
        let saved = self.timeout;
        self.timeout = Some(timeout);
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.check_sat()));
        self.timeout = saved;
        let result = outcome.map_err(|e| SolverError::SolverPanic(panic_payload_to_string(&*e)))?;
        self.fail_on_artifact_export(result)
    }

    /// Check satisfiability and return atomic result details, catching panics.
    ///
    /// Panic-safe wrapper around [`check_sat_with_details`]. On panic, returns
    /// [`SolverError::SolverPanic`] instead of unwinding.
    ///
    /// [`check_sat_with_details`]: Solver::check_sat_with_details
    pub fn try_check_sat_with_details(&mut self) -> Result<SolveDetails, SolverError> {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.check_sat_with_details()
        }))
        .map_err(|e| SolverError::SolverPanic(panic_payload_to_string(&*e)))?;
        self.fail_on_artifact_export(result)
    }

    /// Check satisfiability under assumptions and return atomic result details
    /// including unsat assumptions, catching panics.
    ///
    /// Panic-safe wrapper around [`check_sat_assuming_with_details`]. On panic,
    /// returns [`SolverError::SolverPanic`] instead of unwinding.
    ///
    /// [`check_sat_assuming_with_details`]: Solver::check_sat_assuming_with_details
    pub fn try_check_sat_assuming_with_details(
        &mut self,
        assumptions: &[Term],
    ) -> Result<AssumptionSolveDetails, SolverError> {
        self.resolve_terms("check_sat_assuming_with_details", assumptions)?;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.check_sat_assuming_with_details(assumptions)
        }))
        .map_err(|e| SolverError::SolverPanic(panic_payload_to_string(&*e)))?;
        self.fail_on_artifact_export(result)
    }
}
