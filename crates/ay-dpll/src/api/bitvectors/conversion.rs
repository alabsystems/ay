// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitvector ↔ integer conversions.

use super::*;

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Convert bitvector to integer (unsigned interpretation)
    ///
    /// Maps bv[n-1:0] to an unsigned integer in range [0, 2^n - 1].
    ///
    /// # Panics
    /// Panics if `bv` is not a bitvector sort.
    /// Use [`Self::try_bv2int`] for a fallible version.
    pub fn bv2int(&mut self, bv: Term) -> Term {
        self.try_bv2int(bv).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Convert bitvector to integer (signed interpretation)
    ///
    /// Maps bv[n-1:0] to integer value in range [-2^(n-1), 2^(n-1) - 1].
    /// The high bit is interpreted as the sign bit.
    ///
    /// # Example
    /// ```
    /// # use ay_dpll::api::{Solver, Sort, Logic};
    /// let mut solver = Solver::new(Logic::QfAufbv);
    /// let bv = solver.bv_const(-1i64, 8);  // 0xFF
    /// let int_val = solver.bv2int_signed(bv);
    /// // int_val represents the integer -1
    /// ```
    ///
    /// # Panics
    /// Panics if `bv` is not a bitvector sort.
    /// Use [`Self::try_bv2int_signed`] for a fallible version.
    pub fn bv2int_signed(&mut self, bv: Term) -> Term {
        self.try_bv2int_signed(bv).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert bitvector to integer (unsigned interpretation).
    ///
    /// Fallible version of [`bv2int`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `bv` is not a bitvector sort.
    ///
    /// [`bv2int`]: Solver::bv2int
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bv2int(&mut self, bv: Term) -> Result<Term, SolverError> {
        let bv_id = self.resolve_term("bv2int", bv)?;
        self.expect_bitvec("bv2int", bv)?;
        let result = self.terms_mut().mk_bv2int(bv_id, false);
        Ok(self.wrap_term(result))
    }

    /// Try to convert bitvector to integer (signed interpretation).
    ///
    /// Fallible version of [`bv2int_signed`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `bv` is not a bitvector sort.
    ///
    /// [`bv2int_signed`]: Solver::bv2int_signed
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bv2int_signed(&mut self, bv: Term) -> Result<Term, SolverError> {
        let bv_id = self.resolve_term("bv2int_signed", bv)?;
        self.expect_bitvec("bv2int_signed", bv)?;
        let result = self.terms_mut().mk_bv2int(bv_id, true);
        Ok(self.wrap_term(result))
    }

    /// Convert integer to bitvector of specified width
    ///
    /// Semantics: `int2bv(w, n)` is `n mod 2^w`, represented as a bitvector of width `w`.
    ///
    /// # Example
    /// ```
    /// # use ay_dpll::api::{Solver, Sort, Logic};
    /// let mut solver = Solver::new(Logic::QfAufbv);
    /// let int_val = solver.int_const(255);
    /// let bv = solver.int2bv(int_val, 8);
    /// // bv represents the 8-bit bitvector 0xFF
    /// ```
    ///
    /// # Panics
    /// Panics if `int_term` is not an Int sort.
    /// Use [`Self::try_int2bv`] for a fallible version.
    pub fn int2bv(&mut self, int_term: Term, width: u32) -> Term {
        self.try_int2bv(int_term, width)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert integer to bitvector of specified width.
    ///
    /// Fallible version of [`int2bv`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `int_term` is not an Int sort.
    ///
    /// [`int2bv`]: Solver::int2bv
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_int2bv(&mut self, int_term: Term, width: u32) -> Result<Term, SolverError> {
        let int_id = self.resolve_term("int2bv", int_term)?;
        self.expect_int("int2bv", int_term)?;
        let result = self.terms_mut().mk_int2bv(width, int_id);
        Ok(self.wrap_term(result))
    }
}
