// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use std::collections::BTreeMap;
use std::panic::AssertUnwindSafe;

use ay_core::catch_ay_panics;
use ay_dpll::api::{FuncDecl, Logic, Solver, SolverError, Term};
use ay_translate::{TranslationSession, TranslationState};

use super::ExecuteError;

/// Execution context for translating AYProgram to solver calls.
pub(super) struct ExecutionContext {
    pub(super) solver: Solver,
    /// Shared translation state for declared variables and functions.
    pub(super) translation_state: TranslationState<String>,
    /// Bound-variable overlays for quantifier translation.
    pub(super) bound_var_scopes: Vec<BTreeMap<String, Term>>,
    /// Terms requested via get-value commands, to be evaluated after check-sat.
    /// Stores (original_expr_display, translated_term) pairs.
    pub(super) get_value_terms: Vec<(String, Term)>,
    /// Declared datatypes, keyed by name. Needed for constructor translation
    /// which requires the full DatatypeSort to pass to the solver API.
    pub(super) declared_datatypes: BTreeMap<String, ay_core::DatatypeSort>,
    /// Assumptions from check-sat-assuming commands (#5456).
    /// When non-empty, execute() calls check_sat_assuming instead of check_sat.
    pub(super) check_sat_assumptions: Vec<Term>,
}

impl ExecutionContext {
    /// Create a new execution context with the specified logic.
    pub(super) fn new(logic: Logic) -> Result<Self, ExecuteError> {
        let solver = Solver::try_new(logic).map_err(|e| ExecuteError::SolverInit(e.to_string()))?;

        // Timeout policy is explicit program input (`set-option :timeout`),
        // processed by the normal constraint path. Ambient environment cannot
        // change a solver verdict behind the caller's cache/configuration key.

        Ok(Self {
            solver,
            translation_state: TranslationState::new(),
            bound_var_scopes: Vec::new(),
            get_value_terms: Vec::new(),
            declared_datatypes: BTreeMap::new(),
            check_sat_assumptions: Vec::new(),
        })
    }

    pub(super) fn session(&mut self) -> TranslationSession<'_, String> {
        TranslationSession::new(&mut self.solver, &mut self.translation_state)
    }

    pub(super) fn lookup_var(&self, name: &str) -> Option<Term> {
        self.bound_var_scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
            .or_else(|| self.translation_state.get_var(name))
    }

    pub(super) fn lookup_func(&self, name: &str) -> Option<FuncDecl> {
        self.translation_state.get_func(name).cloned()
    }
}

/// Panic-boundary helper for execute_direct stages.
///
/// Wraps `ay_core::catch_ay_panics` with `AssertUnwindSafe` (the closures
/// capture `&mut` execution state). ay-classified panics are downgraded via
/// `on_ay_panic`; non-ay panics (programmer errors) propagate via
/// `resume_unwind`.
pub(crate) fn catch_execute_stage<T>(
    op: impl FnOnce() -> T,
    on_ay_panic: impl FnOnce(String) -> T,
) -> T {
    catch_ay_panics(AssertUnwindSafe(op), on_ay_panic)
}

/// Maps a fallible `try_*` solver operation to `ExecuteError::ExprTranslation`.
///
/// Used to replace deprecated panicking builder calls with their `try_*`
/// equivalents. Translation failures become ordinary errors, not panics.
pub(super) fn expr_solver_op<T>(
    result: Result<T, SolverError>,
    operation: &str,
) -> Result<T, ExecuteError> {
    result.map_err(|e| ExecuteError::ExprTranslation(format!("{operation}: {e}")))
}
