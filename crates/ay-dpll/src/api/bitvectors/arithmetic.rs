// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitvector arithmetic: add, sub, mul.

use super::*;

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Create a bitvector addition
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvadd`] for a fallible version.
    pub fn bvadd(&mut self, a: Term, b: Term) -> Term {
        self.try_bvadd(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector addition.
    ///
    /// Fallible version of [`bvadd`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvadd`]: Solver::bvadd
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvadd(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvadd", a, b)?;
        Ok(Term(self.terms_mut().mk_bvadd(vec![a.0, b.0])))
    }

    /// Create a bitvector subtraction
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvsub`] for a fallible version.
    pub fn bvsub(&mut self, a: Term, b: Term) -> Term {
        self.try_bvsub(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector subtraction.
    ///
    /// Fallible version of [`bvsub`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvsub`]: Solver::bvsub
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvsub(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvsub", a, b)?;
        Ok(Term(self.terms_mut().mk_bvsub(vec![a.0, b.0])))
    }

    /// Create a bitvector multiplication
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvmul`] for a fallible version.
    pub fn bvmul(&mut self, a: Term, b: Term) -> Term {
        self.try_bvmul(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector multiplication.
    ///
    /// Fallible version of [`bvmul`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvmul`]: Solver::bvmul
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvmul(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvmul", a, b)?;
        Ok(Term(self.terms_mut().mk_bvmul(vec![a.0, b.0])))
    }
}
