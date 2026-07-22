// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitvector extract, concat, zero/sign extend.

use super::*;

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Extract bits `[high:low]` from a bitvector (0-indexed, inclusive)
    ///
    /// # Panics
    /// Panics if the argument is not a bitvector sort or if the bit range is invalid.
    /// Use [`Self::try_bvextract`] for a fallible version that returns an error instead.
    pub fn bvextract(&mut self, a: Term, high: u32, low: u32) -> Term {
        self.try_bvextract(a, high, low)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to extract bits `[high:low]` from a bitvector (0-indexed, inclusive).
    ///
    /// Fallible version of [`bvextract`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::InvalidArgument`] if:
    /// - `low > high`
    /// - `high >= bitvector_width`
    ///
    /// Returns [`SolverError::SortMismatch`] if `a` is not a bitvector.
    ///
    /// [`bvextract`]: Solver::bvextract
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvextract(&mut self, a: Term, high: u32, low: u32) -> Result<Term, SolverError> {
        if low > high {
            return Err(SolverError::InvalidArgument {
                operation: "bvextract",
                message: format!("low ({low}) must be <= high ({high})"),
            });
        }

        let width = self.expect_bitvec_width("bvextract", a)?;
        if high >= width {
            return Err(SolverError::InvalidArgument {
                operation: "bvextract",
                message: format!("high ({high}) must be < bitvector width ({width})"),
            });
        }
        // Note: low <= high < width guaranteed by checks above, so low < width implicitly

        Ok(Term(self.terms_mut().mk_bvextract(high, low, a.0)))
    }

    /// Concatenate two bitvectors (a is the high bits, b is the low bits)
    ///
    /// # Panics
    /// Panics if either argument is not a bitvector sort, or if the resulting width overflows u32.
    /// Use [`Self::try_bvconcat`] for a fallible version that returns an error instead.
    pub fn bvconcat(&mut self, a: Term, b: Term) -> Term {
        self.try_bvconcat(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to concatenate two bitvectors (a is the high bits, b is the low bits).
    ///
    /// Fallible version of [`bvconcat`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::InvalidArgument`] if the resulting width overflows u32.
    ///
    /// Returns [`SolverError::SortMismatch`] if either `a` or `b` is not a bitvector.
    ///
    /// [`bvconcat`]: Solver::bvconcat
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvconcat(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let (a_w, b_w) = self.expect_bitvec_width2("bvconcat", a, b)?;
        let out_w = u64::from(a_w) + u64::from(b_w);
        if out_w > u64::from(u32::MAX) {
            return Err(SolverError::InvalidArgument {
                operation: "bvconcat",
                message: format!("resulting bitvector width overflows u32: {a_w} + {b_w}"),
            });
        }
        Ok(Term(self.terms_mut().mk_bvconcat(vec![a.0, b.0])))
    }

    /// Zero-extend a bitvector by n bits
    ///
    /// # Panics
    /// Panics if the argument is not a bitvector sort, or if the resulting width overflows u32.
    /// Use [`Self::try_bvzeroext`] for a fallible version that returns an error instead.
    pub fn bvzeroext(&mut self, a: Term, n: u32) -> Term {
        self.try_bvzeroext(a, n).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to zero-extend a bitvector by n bits.
    ///
    /// Fallible version of [`bvzeroext`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::InvalidArgument`] if the resulting width overflows u32.
    ///
    /// Returns [`SolverError::SortMismatch`] if `a` is not a bitvector.
    ///
    /// [`bvzeroext`]: Solver::bvzeroext
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvzeroext(&mut self, a: Term, n: u32) -> Result<Term, SolverError> {
        let w = self.expect_bitvec_width("bvzeroext", a)?;
        let out_w = u64::from(w) + u64::from(n);
        if out_w > u64::from(u32::MAX) {
            return Err(SolverError::InvalidArgument {
                operation: "bvzeroext",
                message: format!("resulting bitvector width overflows u32: {w} + {n}"),
            });
        }
        Ok(Term(self.terms_mut().mk_bvzero_extend(n, a.0)))
    }

    /// Sign-extend a bitvector by n bits
    ///
    /// # Panics
    /// Panics if the argument is not a bitvector sort, or if the resulting width overflows u32.
    /// Use [`Self::try_bvsignext`] for a fallible version that returns an error instead.
    pub fn bvsignext(&mut self, a: Term, n: u32) -> Term {
        self.try_bvsignext(a, n).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to sign-extend a bitvector by n bits.
    ///
    /// Fallible version of [`bvsignext`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::InvalidArgument`] if the resulting width overflows u32.
    ///
    /// Returns [`SolverError::SortMismatch`] if `a` is not a bitvector.
    ///
    /// [`bvsignext`]: Solver::bvsignext
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvsignext(&mut self, a: Term, n: u32) -> Result<Term, SolverError> {
        let w = self.expect_bitvec_width("bvsignext", a)?;
        let out_w = u64::from(w) + u64::from(n);
        if out_w > u64::from(u32::MAX) {
            return Err(SolverError::InvalidArgument {
                operation: "bvsignext",
                message: format!("resulting bitvector width overflows u32: {w} + {n}"),
            });
        }
        Ok(Term(self.terms_mut().mk_bvsign_extend(n, a.0)))
    }
}
