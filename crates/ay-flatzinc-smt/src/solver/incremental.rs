// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// --- Incremental solver (in-process ay Solver API with push/pop) ---

/// Incremental SMT solver with push/pop for backtracking search.
///
/// Uses the in-process ay Solver API — no subprocess, no pipes. Declarations
/// are sent once, ay reuses learned clauses across calls, and process spawn
/// overhead is eliminated.
pub(crate) struct IncrementalSolver {
    solver: Box<ay_dpll::api::Solver>,
}

impl IncrementalSolver {
    /// Create incremental solver using the in-process ay Solver API.
    ///
    /// Uses the native `Solver` API which provides:
    /// - Direct push/pop/check-sat without SMT-LIB text reparsing
    /// - Timeout support via `Solver::set_timeout()`
    /// - Interrupt handle for cancellation from other threads
    #[allow(deprecated)]
    pub(crate) fn new(config: &SolverConfig, declarations: &str) -> Result<Self, SolverError> {
        use ay_dpll::api::{Logic, Solver};

        // Create solver with permissive logic; parse_smtlib2 will override
        // with the actual logic from the declarations (set-logic is idempotent).
        let mut solver = Solver::new(Logic::All);

        // Set timeout from config so all check_sat calls respect it
        if let Some(ms) = config.timeout_ms {
            solver.set_timeout(Some(Duration::from_millis(ms)));
        }

        // Load declarations (set-logic, declare-const, assert, etc.)
        // Skips query commands (check-sat, get-model, etc.)
        solver
            .parse_smtlib2(declarations)
            .map_err(|e| SolverError::SolverError(format!("parse error: {e}")))?;

        Ok(Self {
            solver: Box::new(solver),
        })
    }

    /// Push a scope, send assertions, check satisfiability.
    pub(crate) fn check_sat_incremental(
        &mut self,
        assertions: &str,
    ) -> Result<CheckSatResult, SolverError> {
        use ay_dpll::api::SolveResult;

        // Native push — no text parsing needed
        self.solver
            .try_push()
            .map_err(|e| SolverError::SolverError(format!("{e}")))?;

        // Parse and assert the bound constraint (still text since the
        // optimization loop constructs assertions as SMT-LIB strings)
        if !assertions.trim().is_empty() {
            self.solver
                .parse_smtlib2(assertions)
                .map_err(|e| SolverError::SolverError(format!("parse error: {e}")))?;
        }

        // Native check-sat — respects Solver::set_timeout()
        match self.solver.check_sat().result() {
            SolveResult::Sat => Ok(CheckSatResult::Sat),
            SolveResult::Unsat(_) => Ok(CheckSatResult::Unsat),
            SolveResult::Unknown | _ => Ok(CheckSatResult::Unknown),
        }
    }

    /// Pop the most recent scope.
    pub(crate) fn pop(&mut self) -> Result<(), SolverError> {
        self.solver
            .try_pop()
            .map_err(|e| SolverError::SolverError(format!("{e}")))
    }

    /// Query variable values after a successful check-sat.
    pub(crate) fn get_value(&mut self, vars: &str) -> Result<HashMap<String, String>, SolverError> {
        // Use the native Model API to extract values without text
        // round-tripping through (get-value (...)) serialization.
        let verified_model = self.solver.model().ok_or(SolverError::EmptyOutput)?;
        let model = verified_model.model();

        let mut result = HashMap::default();
        for var_name in vars.split_whitespace() {
            if let Some(val) = model.int_val(var_name) {
                // Format as SMT-LIB integer for compatibility with
                // parse_smt_int: negative uses (- N) syntax.
                use num_traits::Signed;
                if val.is_negative() {
                    result.insert(var_name.to_string(), format!("(- {})", val.abs()));
                } else {
                    result.insert(var_name.to_string(), val.to_string());
                }
            } else if let Some(val) = model.bool_val(var_name) {
                result.insert(var_name.to_string(), val.to_string());
            } else if let Some(val) = model.real_val(var_name) {
                // Format BigRational for SMT-LIB
                use num_traits::ToPrimitive;
                if let Some(f) = val.to_f64() {
                    result.insert(var_name.to_string(), format!("{f}"));
                }
            }
            // Skip variables not in model (solver may assign defaults)
        }
        Ok(result)
    }
}
