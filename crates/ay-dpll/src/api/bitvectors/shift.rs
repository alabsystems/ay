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
        let a_id = self.resolve_term("bvshl", a)?;
        let b_id = self.resolve_term("bvshl", b)?;
        self.expect_same_bitvec_width("bvshl", a, b)?;
        let result = self.terms_mut().mk_bvshl(vec![a_id, b_id]);
        Ok(self.wrap_term(result))
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
        let a_id = self.resolve_term("bvlshr", a)?;
        let b_id = self.resolve_term("bvlshr", b)?;
        self.expect_same_bitvec_width("bvlshr", a, b)?;
        let result = self.terms_mut().mk_bvlshr(vec![a_id, b_id]);
        Ok(self.wrap_term(result))
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
        let a_id = self.resolve_term("bvashr", a)?;
        let b_id = self.resolve_term("bvashr", b)?;
        self.expect_same_bitvec_width("bvashr", a, b)?;
        let result = self.terms_mut().mk_bvashr(vec![a_id, b_id]);
        Ok(self.wrap_term(result))
    }
}
