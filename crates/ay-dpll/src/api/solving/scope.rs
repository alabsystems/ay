// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! RAII guard for solver push/pop scopes.
//!
//! Ensures each `try_push()` is paired with a `try_pop()`, even when the scope
//! exits via `?`, `return`, or panic.

use std::ops::{Deref, DerefMut};
use std::panic::{catch_unwind, resume_unwind, AssertUnwindSafe};

use crate::api::types::SolverError;
use crate::api::Solver;

/// RAII guard that calls `try_push()` on creation and `try_pop()` on drop.
///
/// `SolverScope` restores the solver to the scope depth it had before
/// construction. Additional scopes pushed through the dereferenced solver are
/// also popped on drop. Popping or resetting the solver below the guard's entry
/// depth via [`Solver::try_pop`], [`Solver::pop`], [`Solver::try_reset`],
/// [`Solver::reset`], or [`Solver::try_reset_assertions`] violates that
/// invariant and will panic on drop unless the thread is already unwinding.
///
/// # Panics
///
/// On the normal path, dropping the guard panics if the solver's scope stack
/// has already been unwound below the guard's entry depth or if `try_pop()`
/// fails while restoring the entry depth.
#[must_use = "SolverScope pops on drop; dropping immediately would push then instantly pop"]
pub struct SolverScope<'a> {
    solver: &'a mut Solver,
    entry_scope_level: u32,
}

impl<'a> SolverScope<'a> {
    /// Push a new solver scope and return a guard that pops it on drop.
    ///
    /// # Errors
    ///
    /// Returns any error produced by [`Solver::try_push`].
    pub fn new(solver: &'a mut Solver) -> Result<Self, SolverError> {
        let entry_scope_level = solver.num_scopes();
        solver.try_push()?;
        Ok(Self {
            solver,
            entry_scope_level,
        })
    }
}

impl Deref for SolverScope<'_> {
    type Target = Solver;

    fn deref(&self) -> &Self::Target {
        self.solver
    }
}

impl DerefMut for SolverScope<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.solver
    }
}

impl Drop for SolverScope<'_> {
    fn drop(&mut self) {
        let unwinding = std::thread::panicking();
        let solver = &mut *self.solver;
        let expected_active_level = self.entry_scope_level.saturating_add(1);
        let current_scope_level = solver.num_scopes();
        if current_scope_level < expected_active_level {
            if unwinding {
                // Suppress drop-side scope mismatches during an outer unwind:
                // panicking again here would abort the process.
                return;
            }
            panic!(
                "SolverScope drop found scope stack below guard entry: expected at least \
                 {expected_active_level}, found {current_scope_level}"
            );
        }

        while solver.num_scopes() > self.entry_scope_level {
            match catch_unwind(AssertUnwindSafe(|| solver.try_pop())) {
                Ok(Ok(())) => {}
                Ok(Err(_)) if unwinding => {
                    // Suppress drop-side scope mismatches during an outer
                    // unwind: panicking again here would abort the process.
                    return;
                }
                Ok(Err(err)) => panic!("SolverScope drop failed to pop scope: {err}"),
                Err(_) if unwinding => {
                    // Suppress a second panic if `try_pop()` panics while the
                    // caller is already unwinding from the scoped body.
                    return;
                }
                Err(payload) => resume_unwind(payload),
            }
        }
    }
}
