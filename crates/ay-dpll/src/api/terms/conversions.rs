// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Convert an integer term to a real term (to_real).
    ///
    /// # Panics
    /// Panics if the argument is not Int sort. Use [`Self::try_int_to_real`] for a fallible version.
    pub fn int_to_real(&mut self, int_term: Term) -> Term {
        self.try_int_to_real(int_term)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert an integer term to a real term (to_real).
    ///
    /// Fallible version of [`int_to_real`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `int_term` is not Int sort.
    ///
    /// [`int_to_real`]: Solver::int_to_real
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_int_to_real(&mut self, int_term: Term) -> Result<Term, SolverError> {
        self.expect_int("int_to_real", int_term)?;
        Ok(Term(self.terms_mut().mk_to_real(int_term.0)))
    }

    /// Convert a real term to an integer via floor (to_int).
    ///
    /// # Panics
    /// Panics if the argument is not Real sort. Use [`Self::try_real_to_int`] for a fallible version.
    pub fn real_to_int(&mut self, real_term: Term) -> Term {
        self.try_real_to_int(real_term)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert a real term to an integer via floor (to_int).
    ///
    /// Fallible version of [`real_to_int`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `real_term` is not Real sort.
    ///
    /// [`real_to_int`]: Solver::real_to_int
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_real_to_int(&mut self, real_term: Term) -> Result<Term, SolverError> {
        self.expect_real("real_to_int", real_term)?;
        Ok(Term(self.terms_mut().mk_to_int(real_term.0)))
    }

    /// Test if a real term has an integer value (is_int).
    ///
    /// Returns a Bool term that is true iff the real value equals its floor.
    ///
    /// # Panics
    /// Panics if the argument is not Real sort. Use [`Self::try_is_int`] for a fallible version.
    pub fn is_int(&mut self, real_term: Term) -> Term {
        self.try_is_int(real_term).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to test if a real term has an integer value (is_int).
    ///
    /// Fallible version of [`is_int`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `real_term` is not Real sort.
    ///
    /// [`is_int`]: Solver::is_int
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_is_int(&mut self, real_term: Term) -> Result<Term, SolverError> {
        self.expect_real("is_int", real_term)?;
        Ok(Term(self.terms_mut().mk_is_int(real_term.0)))
    }
}
