// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitvector bitwise operations: not, neg, and, or, xor, nand, nor, xnor.

use super::*;

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Create a bitvector bitwise NOT
    ///
    /// # Panics
    /// Panics if the argument is not a bitvector.
    /// Use [`Self::try_bvnot`] for a fallible version.
    pub fn bvnot(&mut self, a: Term) -> Term {
        self.try_bvnot(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector bitwise NOT.
    ///
    /// Fallible version of [`bvnot`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if the argument is not a bitvector.
    ///
    /// [`bvnot`]: Solver::bvnot
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvnot(&mut self, a: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("bvnot", a)?;
        self.expect_bitvec_width("bvnot", a)?;
        let result = self.terms_mut().mk_bvnot(a_id);
        Ok(self.wrap_term(result))
    }

    /// Create a bitvector arithmetic negation (two's complement)
    ///
    /// # Panics
    /// Panics if the argument is not a bitvector.
    /// Use [`Self::try_bvneg`] for a fallible version.
    pub fn bvneg(&mut self, a: Term) -> Term {
        self.try_bvneg(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector arithmetic negation (two's complement).
    ///
    /// Fallible version of [`bvneg`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if the argument is not a bitvector.
    ///
    /// [`bvneg`]: Solver::bvneg
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvneg(&mut self, a: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("bvneg", a)?;
        self.expect_bitvec_width("bvneg", a)?;
        let result = self.terms_mut().mk_bvneg(a_id);
        Ok(self.wrap_term(result))
    }

    /// Create a bitvector bitwise AND
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvand`] for a fallible version.
    pub fn bvand(&mut self, a: Term, b: Term) -> Term {
        self.try_bvand(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector bitwise AND.
    ///
    /// Fallible version of [`bvand`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvand`]: Solver::bvand
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvand(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("bvand", a)?;
        let b_id = self.resolve_term("bvand", b)?;
        self.expect_same_bitvec_width("bvand", a, b)?;
        let result = self.terms_mut().mk_bvand(vec![a_id, b_id]);
        Ok(self.wrap_term(result))
    }

    /// Create a bitvector bitwise OR
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvor`] for a fallible version.
    pub fn bvor(&mut self, a: Term, b: Term) -> Term {
        self.try_bvor(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector bitwise OR.
    ///
    /// Fallible version of [`bvor`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvor`]: Solver::bvor
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvor(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("bvor", a)?;
        let b_id = self.resolve_term("bvor", b)?;
        self.expect_same_bitvec_width("bvor", a, b)?;
        let result = self.terms_mut().mk_bvor(vec![a_id, b_id]);
        Ok(self.wrap_term(result))
    }

    /// Create a bitvector bitwise XOR
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvxor`] for a fallible version.
    pub fn bvxor(&mut self, a: Term, b: Term) -> Term {
        self.try_bvxor(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector bitwise XOR.
    ///
    /// Fallible version of [`bvxor`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvxor`]: Solver::bvxor
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvxor(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("bvxor", a)?;
        let b_id = self.resolve_term("bvxor", b)?;
        self.expect_same_bitvec_width("bvxor", a, b)?;
        let result = self.terms_mut().mk_bvxor(vec![a_id, b_id]);
        Ok(self.wrap_term(result))
    }

    /// Create a bitvector bitwise NAND
    ///
    /// Defined as: `bvnand(a, b) = bvnot(bvand(a, b))`
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvnand`] for a fallible version.
    pub fn bvnand(&mut self, a: Term, b: Term) -> Term {
        self.try_bvnand(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector bitwise NAND.
    ///
    /// Defined as: `bvnand(a, b) = bvnot(bvand(a, b))`
    ///
    /// Fallible version of [`bvnand`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvnand`]: Solver::bvnand
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvnand(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("bvnand", a)?;
        let b_id = self.resolve_term("bvnand", b)?;
        self.expect_same_bitvec_width("bvnand", a, b)?;
        let result = self.terms_mut().mk_bvnand(vec![a_id, b_id]);
        Ok(self.wrap_term(result))
    }

    /// Create a bitvector bitwise NOR
    ///
    /// Defined as: `bvnor(a, b) = bvnot(bvor(a, b))`
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvnor`] for a fallible version.
    pub fn bvnor(&mut self, a: Term, b: Term) -> Term {
        self.try_bvnor(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector bitwise NOR.
    ///
    /// Defined as: `bvnor(a, b) = bvnot(bvor(a, b))`
    ///
    /// Fallible version of [`bvnor`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvnor`]: Solver::bvnor
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvnor(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("bvnor", a)?;
        let b_id = self.resolve_term("bvnor", b)?;
        self.expect_same_bitvec_width("bvnor", a, b)?;
        let result = self.terms_mut().mk_bvnor(vec![a_id, b_id]);
        Ok(self.wrap_term(result))
    }

    /// Create a bitvector bitwise XNOR
    ///
    /// Defined as: `bvxnor(a, b) = bvnot(bvxor(a, b))`
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvxnor`] for a fallible version.
    pub fn bvxnor(&mut self, a: Term, b: Term) -> Term {
        self.try_bvxnor(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector bitwise XNOR.
    ///
    /// Defined as: `bvxnor(a, b) = bvnot(bvxor(a, b))`
    ///
    /// Fallible version of [`bvxnor`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvxnor`]: Solver::bvxnor
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvxnor(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("bvxnor", a)?;
        let b_id = self.resolve_term("bvxnor", b)?;
        self.expect_same_bitvec_width("bvxnor", a, b)?;
        let result = self.terms_mut().mk_bvxnor(vec![a_id, b_id]);
        Ok(self.wrap_term(result))
    }
}
