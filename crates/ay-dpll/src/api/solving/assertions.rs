// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assertion stack management: assert, push, pop, scopes, reset.

use ay_core::Sort;
use ay_frontend::command::Term as ParsedTerm;
use ay_frontend::Command;

use crate::api::types::{NativeReplayEventKind, SolverError, Term};
use crate::api::Solver;

impl Solver {
    /// Assert a constraint (must be a Boolean term)
    ///
    /// # Panics
    /// Panics if `term` is not Bool sort. Use [`Self::try_assert_term`] for a fallible version.
    #[allow(clippy::panic)]
    pub fn assert_term(&mut self, term: Term) {
        self.try_assert_term(term).unwrap_or_else(|e| panic!("{e}"));
    }

    /// Try to assert a constraint (must be a Boolean term).
    ///
    /// Fallible version of [`assert_term`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `term` is not a Bool sort.
    ///
    /// [`assert_term`]: Solver::assert_term
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_assert_term(&mut self, term: Term) -> Result<(), SolverError> {
        let sort = self.terms().sort(term.0).clone();
        if sort != Sort::Bool {
            return Err(SolverError::SortMismatch {
                operation: "assert_term",
                expected: "Bool",
                got: vec![sort],
            });
        }

        self.executor.note_api_assertion_mutation();

        // Keep assertions_parsed aligned with assertions for proof-rewrite
        // invariants when assertions are added via the native API path.
        let ctx = self.executor.context_mut();
        ctx.add_assertion_with_parsed(
            term.0,
            ParsedTerm::Symbol("__ay_api_assertion__".to_string()),
        );
        self.record_native_replay_event(NativeReplayEventKind::Assert {
            term: term.0,
            name: None,
        });
        Ok(())
    }

    /// Assert a named constraint for unsat core attribution.
    ///
    /// Equivalent to `(assert (! term :named name))` in SMT-LIB.
    /// After an UNSAT result, call [`try_get_unsat_core`] to get the subset
    /// of names that contributed to unsatisfiability.
    ///
    /// This is the stable consumer workflow for vacuity detection:
    /// 1. Enable cores with [`set_produce_unsat_cores`](Self::set_produce_unsat_cores).
    /// 2. Name each top-level assertion group (for example
    ///    `preconditions`, `encoding_axioms`, `negated_postcondition`).
    /// 3. Solve and inspect [`try_get_unsat_core`](Self::try_get_unsat_core).
    /// 4. If `negated_postcondition` is absent from the core, the UNSAT proof
    ///    is vacuous with respect to the postcondition.
    ///
    /// Assertion names should be unique within the currently active solver
    /// scope. Reusing a name overwrites the earlier core-reporting entry for
    /// that name.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `term` is not a Bool sort.
    ///
    /// [`try_get_unsat_core`]: Solver::try_get_unsat_core
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_assert_named(&mut self, term: Term, name: &str) -> Result<(), SolverError> {
        let sort = self.terms().sort(term.0).clone();
        if sort != Sort::Bool {
            return Err(SolverError::SortMismatch {
                operation: "assert_named",
                expected: "Bool",
                got: vec![sort],
            });
        }

        self.executor.note_api_assertion_mutation();

        let ctx = self.executor.context_mut();
        ctx.add_assertion_with_parsed(term.0, ParsedTerm::Symbol(format!("__ay_named_{name}__")));
        ctx.register_named_term(name.to_string(), term.0);
        self.record_native_replay_event(NativeReplayEventKind::Assert {
            term: term.0,
            name: Some(name.to_string()),
        });
        Ok(())
    }

    /// Push a new scope for incremental solving
    ///
    /// # Panics
    ///
    /// Panics if the executor fails to push a scope. Use [`try_push`] for a
    /// fallible version that returns an error instead.
    ///
    /// [`try_push`]: Solver::try_push
    #[allow(clippy::panic)]
    pub fn push(&mut self) {
        self.try_push()
            .unwrap_or_else(|e| panic!("Failed to push scope: {e}"));
    }

    /// Try to push a new scope for incremental solving.
    ///
    /// Fallible version of [`push`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns an error if the executor fails to push a scope.
    ///
    /// [`push`]: Solver::push
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_push(&mut self) -> Result<(), SolverError> {
        self.executor.execute(&Command::Push(1))?;
        self.scope_level += 1;
        self.record_native_replay_event(NativeReplayEventKind::Push);
        Ok(())
    }

    /// Pop the most recent scope
    ///
    /// # Panics
    ///
    /// Panics if there are no scopes to pop or if the executor fails.
    /// Use [`try_pop`] for a fallible version that returns an error instead.
    ///
    /// [`try_pop`]: Solver::try_pop
    #[allow(clippy::panic)]
    pub fn pop(&mut self) {
        self.try_pop()
            .unwrap_or_else(|e| panic!("Failed to pop scope: {e}"));
    }

    /// Try to pop the most recent scope.
    ///
    /// Fallible version of [`pop`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns an error if there are no scopes to pop or if the executor fails.
    ///
    /// [`pop`]: Solver::pop
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_pop(&mut self) -> Result<(), SolverError> {
        if self.scope_level == 0 {
            return Err(SolverError::ExecutorError(crate::ExecutorError::Elaborate(
                ay_frontend::ElaborateError::ScopeUnderflow,
            )));
        }
        self.executor.execute(&Command::Pop(1))?;
        self.scope_level -= 1;
        self.record_native_replay_event(NativeReplayEventKind::Pop);
        Ok(())
    }

    /// Return the number of backtracking scopes (push/pop levels).
    #[must_use]
    pub fn num_scopes(&self) -> u32 {
        self.scope_level
    }

    /// Return the current set of asserted terms.
    #[must_use]
    pub fn assertions(&self) -> Vec<Term> {
        self.executor
            .context()
            .assertions
            .iter()
            .map(|&id| Term(id))
            .collect()
    }

    /// Reset the solver, clearing all assertions
    ///
    /// # Panics
    ///
    /// Panics if the executor fails to reset. Use [`try_reset`] for a
    /// fallible version that returns an error instead.
    ///
    /// [`try_reset`]: Solver::try_reset
    #[allow(clippy::panic)]
    pub fn reset(&mut self) {
        self.try_reset()
            .unwrap_or_else(|e| panic!("Failed to reset solver: {e}"));
    }

    /// Try to reset the solver, clearing all assertions.
    ///
    /// Fallible version of [`reset`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns an error if the executor fails to reset.
    ///
    /// [`reset`]: Solver::reset
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_reset(&mut self) -> Result<(), SolverError> {
        self.executor.execute(&Command::Reset)?;
        self.scope_level = 0;
        self.var_names.clear();
        self.var_sorts.clear();
        self.last_assumptions = None;
        self.last_unknown_reason = None;
        self.last_executor_error = None;
        self.last_artifact_export_failure = None;
        self.soft_constraints.clear();
        self.defined_funs.clear();
        self.scope_level = 0;
        self.core_tracker = crate::api::types::CoreEvolutionTracker::new();
        self.native_replay_events.clear();
        self.record_native_replay_event(NativeReplayEventKind::Reset);
        Ok(())
    }

    /// Reset all assertions and scopes, preserving logic and declarations.
    ///
    /// Unlike [`try_reset`] which clears everything (logic, declarations,
    /// assertions), this preserves the current logic and all declared
    /// constants/functions. Only assertions and scope levels are cleared.
    ///
    /// Equivalent to `(reset-assertions)` in SMT-LIB 2.6 section 4.2.2.
    ///
    /// # Errors
    ///
    /// Returns an error if the executor fails to reset assertions.
    ///
    /// [`try_reset`]: Solver::try_reset
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_reset_assertions(&mut self) -> Result<(), SolverError> {
        self.executor.execute(&Command::ResetAssertions)?;
        self.scope_level = 0;
        // Preserve var_names and var_sorts — declarations survive reset_assertions.
        // Clear defined_funs because their bodies reference terms from the old
        // assertion context that may become invalid after reset-assertions.
        self.defined_funs.clear();
        self.last_assumptions = None;
        self.last_unknown_reason = None;
        self.last_executor_error = None;
        self.last_artifact_export_failure = None;
        self.soft_constraints.clear();
        self.core_tracker = crate::api::types::CoreEvolutionTracker::new();
        self.record_native_replay_event(NativeReplayEventKind::ResetAssertions);
        Ok(())
    }
}
