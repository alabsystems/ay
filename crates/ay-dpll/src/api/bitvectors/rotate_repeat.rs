// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitvector smod, repeat, rotate, smin, all_ones.

use super::*;

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Create a bitvector signed modulo
    ///
    /// # Panics
    /// Panics if arguments are not bitvectors of the same width.
    /// Use [`Self::try_bvsmod`] for a fallible version.
    pub fn bvsmod(&mut self, a: Term, b: Term) -> Term {
        self.try_bvsmod(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector signed modulo.
    ///
    /// Fallible version of [`bvsmod`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if arguments are not bitvectors
    /// of the same width.
    ///
    /// [`bvsmod`]: Solver::bvsmod
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvsmod(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("bvsmod", a)?;
        let b_id = self.resolve_term("bvsmod", b)?;
        self.expect_same_bitvec_width("bvsmod", a, b)?;
        let result = self.terms_mut().mk_bvsmod(vec![a_id, b_id]);
        Ok(self.wrap_term(result))
    }

    /// Repeat a bitvector `n` times (SMT-LIB: `(_ repeat n)`).
    ///
    /// # Panics
    /// Panics if the argument is not a bitvector sort, if `n == 0`, or if the resulting width
    /// overflows. Use [`Self::try_bvrepeat`] for a fallible version instead.
    pub fn bvrepeat(&mut self, a: Term, n: u32) -> Term {
        self.try_bvrepeat(a, n).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to repeat a bitvector `n` times (SMT-LIB: `(_ repeat n)`).
    ///
    /// Fallible version of [`bvrepeat`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::InvalidArgument`] if:
    /// - `n == 0`
    /// - resulting width overflows u32
    ///
    /// Returns [`SolverError::SortMismatch`] if `a` is not a bitvector.
    ///
    /// [`bvrepeat`]: Solver::bvrepeat
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvrepeat(&mut self, a: Term, n: u32) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("bvrepeat", a)?;
        if n == 0 {
            return Err(SolverError::InvalidArgument {
                operation: "bvrepeat",
                message: "repeat count (0) must be > 0".to_string(),
            });
        }

        let w = self.expect_bitvec_width("bvrepeat", a)?;
        let out_w_u64 = u64::from(w) * u64::from(n);
        if out_w_u64 > u64::from(u32::MAX) {
            return Err(SolverError::InvalidArgument {
                operation: "bvrepeat",
                message: format!("resulting bitvector width overflows u32: {w} * {n}"),
            });
        }
        let result = self.terms_mut().mk_bvrepeat(n, a_id);
        Ok(self.wrap_term(result))
    }

    /// Rotate a bitvector left by `n` bits (SMT-LIB: `(_ rotate_left n)`).
    ///
    /// # Panics
    /// Panics if the argument is not a bitvector sort. Use [`Self::try_bvrotl`] for a fallible
    /// version that returns an error instead.
    pub fn bvrotl(&mut self, a: Term, n: u32) -> Term {
        self.try_bvrotl(a, n).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to rotate a bitvector left by `n` bits (SMT-LIB: `(_ rotate_left n)`).
    ///
    /// Fallible version of [`bvrotl`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `a` is not a bitvector.
    ///
    /// [`bvrotl`]: Solver::bvrotl
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvrotl(&mut self, a: Term, n: u32) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("bvrotl", a)?;
        self.expect_bitvec_width("bvrotl", a)?;
        let result = self.terms_mut().mk_bvrotate_left(n, a_id);
        Ok(self.wrap_term(result))
    }

    /// Rotate a bitvector right by `n` bits (SMT-LIB: `(_ rotate_right n)`).
    ///
    /// # Panics
    /// Panics if the argument is not a bitvector sort. Use [`Self::try_bvrotr`] for a fallible
    /// version that returns an error instead.
    pub fn bvrotr(&mut self, a: Term, n: u32) -> Term {
        self.try_bvrotr(a, n).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to rotate a bitvector right by `n` bits (SMT-LIB: `(_ rotate_right n)`).
    ///
    /// Fallible version of [`bvrotr`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `a` is not a bitvector.
    ///
    /// [`bvrotr`]: Solver::bvrotr
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvrotr(&mut self, a: Term, n: u32) -> Result<Term, SolverError> {
        let a_id = self.resolve_term("bvrotr", a)?;
        self.expect_bitvec_width("bvrotr", a)?;
        let result = self.terms_mut().mk_bvrotate_right(n, a_id);
        Ok(self.wrap_term(result))
    }

    // =========================================================================
    // Bitvector overflow predicates (#1301)
    // =========================================================================

    /// Create the signed minimum value for a bitvector width (0x80...00)
    pub(super) fn bv_smin(&mut self, width: u32) -> Term {
        // Signed min is 1 followed by (width-1) zeros, i.e., 2^(width-1) in unsigned
        // For i64, this is i64::MIN when width <= 64
        if width <= 63 {
            self.bv_const(1i64 << (width - 1), width)
        } else {
            // For larger widths, construct using shift
            let one = self.bv_const(1, width);
            let shift = self.bv_const(i64::from(width - 1), width);
            self.bvshl(one, shift)
        }
    }

    /// Create all-ones value for a bitvector width (0xFF...FF = -1 signed)
    pub(super) fn bv_all_ones(&mut self, width: u32) -> Term {
        self.bv_const(-1i64, width)
    }
}
