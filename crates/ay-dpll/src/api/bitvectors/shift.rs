// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitvector shifts: shl, lshr, ashr.

use super::*;

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Create a bitvector shift left
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvshl`] for a fallible version.
    pub fn bvshl(&mut self, a: Term, b: Term) -> Term {
        self.try_bvshl(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector shift left.
    ///
    /// Fallible version of [`bvshl`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvshl`]: Solver::bvshl
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvshl(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvshl", a, b)?;
        Ok(Term(self.terms_mut().mk_bvshl(vec![a.0, b.0])))
    }

    /// Create a bitvector logical shift right
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvlshr`] for a fallible version.
    pub fn bvlshr(&mut self, a: Term, b: Term) -> Term {
        self.try_bvlshr(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector logical shift right.
    ///
    /// Fallible version of [`bvlshr`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvlshr`]: Solver::bvlshr
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvlshr(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvlshr", a, b)?;
        Ok(Term(self.terms_mut().mk_bvlshr(vec![a.0, b.0])))
    }

    /// Create a bitvector arithmetic shift right
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvashr`] for a fallible version.
    pub fn bvashr(&mut self, a: Term, b: Term) -> Term {
        self.try_bvashr(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector arithmetic shift right.
    ///
    /// Fallible version of [`bvashr`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvashr`]: Solver::bvashr
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvashr(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvashr", a, b)?;
        Ok(Term(self.terms_mut().mk_bvashr(vec![a.0, b.0])))
    }
}
