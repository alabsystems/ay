// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitvector division: udiv, sdiv, urem, srem.

use super::*;

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Create a bitvector unsigned division
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvudiv`] for a fallible version.
    pub fn bvudiv(&mut self, a: Term, b: Term) -> Term {
        self.try_bvudiv(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector unsigned division.
    ///
    /// Fallible version of [`bvudiv`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvudiv`]: Solver::bvudiv
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvudiv(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvudiv", a, b)?;
        Ok(Term(self.terms_mut().mk_bvudiv(vec![a.0, b.0])))
    }

    /// Create a bitvector signed division
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvsdiv`] for a fallible version.
    pub fn bvsdiv(&mut self, a: Term, b: Term) -> Term {
        self.try_bvsdiv(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector signed division.
    ///
    /// Fallible version of [`bvsdiv`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvsdiv`]: Solver::bvsdiv
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvsdiv(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvsdiv", a, b)?;
        Ok(Term(self.terms_mut().mk_bvsdiv(vec![a.0, b.0])))
    }

    /// Create a bitvector unsigned remainder
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvurem`] for a fallible version.
    pub fn bvurem(&mut self, a: Term, b: Term) -> Term {
        self.try_bvurem(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector unsigned remainder.
    ///
    /// Fallible version of [`bvurem`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvurem`]: Solver::bvurem
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvurem(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvurem", a, b)?;
        Ok(Term(self.terms_mut().mk_bvurem(vec![a.0, b.0])))
    }

    /// Create a bitvector signed remainder
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvsrem`] for a fallible version.
    pub fn bvsrem(&mut self, a: Term, b: Term) -> Term {
        self.try_bvsrem(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector signed remainder.
    ///
    /// Fallible version of [`bvsrem`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvsrem`]: Solver::bvsrem
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvsrem(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvsrem", a, b)?;
        Ok(Term(self.terms_mut().mk_bvsrem(vec![a.0, b.0])))
    }
}
