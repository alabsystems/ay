// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitvector comparisons: unsigned and signed, plus bvcomp.

use super::*;

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Create a bitvector unsigned less-than
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvult`] for a fallible version.
    pub fn bvult(&mut self, a: Term, b: Term) -> Term {
        self.try_bvult(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector unsigned less-than.
    ///
    /// Fallible version of [`bvult`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvult`]: Solver::bvult
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvult(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvult", a, b)?;
        Ok(Term(self.terms_mut().mk_bvult(a.0, b.0)))
    }

    /// Create a bitvector signed less-than
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvslt`] for a fallible version.
    pub fn bvslt(&mut self, a: Term, b: Term) -> Term {
        self.try_bvslt(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector signed less-than.
    ///
    /// Fallible version of [`bvslt`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvslt`]: Solver::bvslt
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvslt(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvslt", a, b)?;
        Ok(Term(self.terms_mut().mk_bvslt(a.0, b.0)))
    }

    /// Create a bitvector unsigned less-than-or-equal
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvule`] for a fallible version.
    pub fn bvule(&mut self, a: Term, b: Term) -> Term {
        self.try_bvule(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector unsigned less-than-or-equal.
    ///
    /// Fallible version of [`bvule`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvule`]: Solver::bvule
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvule(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvule", a, b)?;
        Ok(Term(self.terms_mut().mk_bvule(a.0, b.0)))
    }

    /// Create a bitvector unsigned greater-than
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvugt`] for a fallible version.
    pub fn bvugt(&mut self, a: Term, b: Term) -> Term {
        self.try_bvugt(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector unsigned greater-than.
    ///
    /// Fallible version of [`bvugt`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvugt`]: Solver::bvugt
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvugt(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvugt", a, b)?;
        Ok(Term(self.terms_mut().mk_bvugt(a.0, b.0)))
    }

    /// Create a bitvector unsigned greater-than-or-equal
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvuge`] for a fallible version.
    pub fn bvuge(&mut self, a: Term, b: Term) -> Term {
        self.try_bvuge(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector unsigned greater-than-or-equal.
    ///
    /// Fallible version of [`bvuge`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvuge`]: Solver::bvuge
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvuge(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvuge", a, b)?;
        Ok(Term(self.terms_mut().mk_bvuge(a.0, b.0)))
    }

    /// Create a bitvector signed less-than-or-equal
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvsle`] for a fallible version.
    pub fn bvsle(&mut self, a: Term, b: Term) -> Term {
        self.try_bvsle(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector signed less-than-or-equal.
    ///
    /// Fallible version of [`bvsle`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvsle`]: Solver::bvsle
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvsle(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvsle", a, b)?;
        Ok(Term(self.terms_mut().mk_bvsle(a.0, b.0)))
    }

    /// Create a bitvector signed greater-than
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvsgt`] for a fallible version.
    pub fn bvsgt(&mut self, a: Term, b: Term) -> Term {
        self.try_bvsgt(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector signed greater-than.
    ///
    /// Fallible version of [`bvsgt`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvsgt`]: Solver::bvsgt
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvsgt(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvsgt", a, b)?;
        Ok(Term(self.terms_mut().mk_bvsgt(a.0, b.0)))
    }

    /// Create a bitvector signed greater-than-or-equal
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvsge`] for a fallible version.
    pub fn bvsge(&mut self, a: Term, b: Term) -> Term {
        self.try_bvsge(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector signed greater-than-or-equal.
    ///
    /// Fallible version of [`bvsge`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvsge`]: Solver::bvsge
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvsge(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvsge", a, b)?;
        Ok(Term(self.terms_mut().mk_bvsge(a.0, b.0)))
    }

    /// Create a bitvector comparison returning a 1-bit bitvector
    ///
    /// Returns `#b1` if `a = b`, `#b0` if `a != b`.
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvcomp`] for a fallible version.
    pub fn bvcomp(&mut self, a: Term, b: Term) -> Term {
        self.try_bvcomp(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector comparison returning a 1-bit bitvector.
    ///
    /// Returns `#b1` if `a = b`, `#b0` if `a != b`.
    ///
    /// Fallible version of [`bvcomp`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvcomp`]: Solver::bvcomp
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvcomp(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_bitvec_width("bvcomp", a, b)?;
        Ok(Term(self.terms_mut().mk_bvcomp(a.0, b.0)))
    }
}
