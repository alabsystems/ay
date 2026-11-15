// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed refusal twins for existing DATA introspection methods.

use super::super::{Solver, SolverError, Term};
use ay_core::Sort;

impl Solver {
    /// Return the term's sort after authenticating its exact live handle.
    ///
    /// This is the fallible twin of [`Self::term_sort`], with the same lookup
    /// and returned sort. Foreign, raw, reset, or discarded entry handles return
    /// [`SolverError::InvalidTermHandle`] before any term-store sort lookup.
    ///
    /// This DATA copy is not a bounded original-query operation.
    ///
    /// # Errors
    ///
    /// [`SolverError::InvalidTermHandle`] when `term` is not a live handle of
    /// this solver.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_term_sort(&self, term: Term) -> Result<Sort, SolverError> {
        let id = self.resolve_term("term_sort", term)?;
        Ok(self.sort_of_live_term(id))
    }

    /// Render an authenticated live term in canonical, store-independent form.
    ///
    /// This is the fallible twin of [`Self::render_term_canonical`], using the
    /// exact same renderer. Foreign, raw, reset, or discarded entry handles
    /// return [`SolverError::InvalidTermHandle`] before rendering.
    ///
    /// Canonical text omits declaration context and is not by itself an external
    /// problem binding, proof, or solver verdict. Rendering and its owned String
    /// remain ordinary unpriced DATA operations, as in the legacy method.
    ///
    /// # Errors
    ///
    /// [`SolverError::InvalidTermHandle`] when `term` is not a live handle of
    /// this solver.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_render_term_canonical(&self, term: Term) -> Result<String, SolverError> {
        let id = self.resolve_term("render_term_canonical", term)?;
        Ok(ay_proof::render_term_canonical(self.executor.terms(), id))
    }
}
