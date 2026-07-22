// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bitvector overflow/underflow check predicates.

use super::*;

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Check that addition does not overflow (positive direction only for signed).
    ///
    /// Returns true iff `a + b` does not produce a value greater than the
    /// maximum representable signed value (i.e., no positive overflow).
    ///
    /// **Warning:** For signed addition (`is_signed == true`), this only checks
    /// positive overflow (two positives summing to negative). It does NOT check
    /// negative underflow (two negatives summing to positive). To check both
    /// directions, combine with [`bvadd_no_underflow`]:
    ///
    /// ```text
    /// let no_overflow = solver.bvadd_no_overflow(a, b, true);
    /// let no_underflow = solver.bvadd_no_underflow(a, b);
    /// let no_signed_wrap = solver.and(no_overflow, no_underflow);
    /// ```
    ///
    /// For unsigned addition, overflow occurs when the result wraps around.
    /// This is checked by zero-extending both operands, adding, and checking
    /// that the high bit of the extended result is 0.
    ///
    /// # Panics
    /// Panics if either argument is not a bitvector sort. Use [`Self::try_bvadd_no_overflow`] for a
    /// fallible version that returns an error instead.
    ///
    /// [`bvadd_no_underflow`]: Solver::bvadd_no_underflow
    pub fn bvadd_no_overflow(&mut self, a: Term, b: Term, is_signed: bool) -> Term {
        self.try_bvadd_no_overflow(a, b, is_signed)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an overflow check predicate for bitvector addition.
    ///
    /// Fallible version of [`bvadd_no_overflow`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `a` and `b` are not bitvectors
    /// of the same width.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `is_signed == false` and the unsigned overflow
    /// check would require a 1-bit extension that overflows u32.
    ///
    /// [`bvadd_no_overflow`]: Solver::bvadd_no_overflow
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvadd_no_overflow(
        &mut self,
        a: Term,
        b: Term,
        is_signed: bool,
    ) -> Result<Term, SolverError> {
        let width = self.expect_same_bitvec_width("bvadd_no_overflow", a, b)?;
        if is_signed {
            // Signed: (a >s 0 && b >s 0) => (a + b) >s 0
            let zero = self.bv_const(0, width);
            let sum = self.try_bvadd(a, b)?;
            let a_pos = self.try_bvsgt(a, zero)?;
            let b_pos = self.try_bvsgt(b, zero)?;
            let both_pos = self.try_and(a_pos, b_pos)?;
            let sum_pos = self.try_bvsgt(sum, zero)?;
            Ok(self.try_implies(both_pos, sum_pos)?)
        } else {
            // Unsigned: `a + b` overflows iff the modular sum wraps below `a`.
            // Equivalently `bvadd(a, b) >=u a` holds iff there is NO overflow:
            // `b >= 0` always, so no-wrap => sum >= a, while a (single) wrap =>
            // sum = a + b - 2^w < a. This stays at the OPERAND width.
            //
            // The previous encoding zero-extended by 1 bit (sum at width+1) and
            // checked the high bit — but for 64-bit inputs that is a 65-bit
            // bitvector, which the backend cannot represent, so u64/usize
            // add-overflow checks silently came back `unknown` (signed-64 and u32
            // worked because they need no >64-bit intermediate). Same-width and
            // sound; `width` is still validated by expect_same_bitvec_width above.
            let _ = width;
            let sum = self.try_bvadd(a, b)?;
            self.try_bvuge(sum, a)
        }
    }

    /// Check that signed addition does not underflow
    ///
    /// Returns true iff `a + b` does not produce a value less than the
    /// minimum representable signed value (i.e., no negative overflow).
    ///
    /// Underflow occurs when adding two negative numbers produces a
    /// positive result: (a <s 0 && b <s 0) => (a + b) <s 0
    ///
    /// # Panics
    /// Panics if either argument is not a bitvector sort. Use [`Self::try_bvadd_no_underflow`] for a
    /// fallible version that returns an error instead.
    pub fn bvadd_no_underflow(&mut self, a: Term, b: Term) -> Term {
        self.try_bvadd_no_underflow(a, b)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an underflow check predicate for signed bitvector addition.
    ///
    /// Fallible version of [`bvadd_no_underflow`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `a` and `b` are not bitvectors
    /// of the same width.
    ///
    /// [`bvadd_no_underflow`]: Solver::bvadd_no_underflow
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvadd_no_underflow(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let width = self.expect_same_bitvec_width("bvadd_no_underflow", a, b)?;
        let zero = self.bv_const(0, width);
        let sum = self.try_bvadd(a, b)?;
        let a_neg = self.try_bvslt(a, zero)?;
        let b_neg = self.try_bvslt(b, zero)?;
        let both_neg = self.try_and(a_neg, b_neg)?;
        let sum_neg = self.try_bvslt(sum, zero)?;
        self.try_implies(both_neg, sum_neg)
    }

    /// Check that signed addition does not wrap in either direction.
    ///
    /// Returns `bvadd_no_overflow(a, b, true) ∧ bvadd_no_underflow(a, b)`.
    /// This is the complete signed addition safety check that most callers want.
    ///
    /// # Panics
    /// Panics if either argument is not a bitvector sort.
    /// Use [`try_bvadd_no_overflow_signed`](Self::try_bvadd_no_overflow_signed)
    /// for a fallible version.
    pub fn bvadd_no_overflow_signed(&mut self, a: Term, b: Term) -> Term {
        self.try_bvadd_no_overflow_signed(a, b)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to check that signed addition does not wrap in either direction.
    ///
    /// Fallible version of [`bvadd_no_overflow_signed`](Self::bvadd_no_overflow_signed).
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `a` and `b` are not bitvectors
    /// of the same width.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvadd_no_overflow_signed(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let _width = self.expect_same_bitvec_width("bvadd_no_overflow_signed", a, b)?;
        let no_overflow = self.try_bvadd_no_overflow(a, b, true)?;
        let no_underflow = self.try_bvadd_no_underflow(a, b)?;
        self.try_and(no_overflow, no_underflow)
    }

    /// Check that signed subtraction does not overflow
    ///
    /// Signed subtraction a - b overflows when b = MIN and a < 0.
    /// Otherwise, it's equivalent to checking a + (-b) doesn't overflow.
    ///
    /// # Panics
    /// Panics if either argument is not a bitvector sort. Use [`Self::try_bvsub_no_overflow`] for a
    /// fallible version that returns an error instead.
    pub fn bvsub_no_overflow(&mut self, a: Term, b: Term) -> Term {
        self.try_bvsub_no_overflow(a, b)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an overflow check predicate for signed bitvector subtraction.
    ///
    /// Fallible version of [`bvsub_no_overflow`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `a` and `b` are not bitvectors
    /// of the same width.
    ///
    /// Returns [`SolverError::InvalidArgument`] if the bitvector width is 0.
    ///
    /// [`bvsub_no_overflow`]: Solver::bvsub_no_overflow
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvsub_no_overflow(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let width = self.expect_same_bitvec_width("bvsub_no_overflow", a, b)?;
        if width == 0 {
            return Err(SolverError::InvalidArgument {
                operation: "bvsub_no_overflow",
                message: "bitvector width (0) must be > 0".to_string(),
            });
        }
        let min = self.bv_smin(width);
        let b_is_min = self.try_eq(b, min)?;
        let zero = self.bv_const(0, width);
        let a_neg = self.try_bvslt(a, zero)?;
        let neg_b = self.try_bvneg(b)?;
        let add_no_ovfl = self.try_bvadd_no_overflow(a, neg_b, true)?;
        // If b == MIN: result is a_neg (only safe if a < 0)
        // Otherwise: check add_no_overflow(a, -b)
        self.try_ite(b_is_min, a_neg, add_no_ovfl)
    }

    /// Check that subtraction does not underflow
    ///
    /// For signed: underflow when subtracting a positive from a negative
    /// wraps to positive. Check via (0 <s b) => no_underflow(a + (-b))
    ///
    /// For unsigned: underflow when b > a (result would wrap negative).
    ///
    /// # Panics
    /// Panics if either argument is not a bitvector sort. Use [`Self::try_bvsub_no_underflow`] for a
    /// fallible version that returns an error instead.
    pub fn bvsub_no_underflow(&mut self, a: Term, b: Term, is_signed: bool) -> Term {
        self.try_bvsub_no_underflow(a, b, is_signed)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an underflow check predicate for bitvector subtraction.
    ///
    /// Fallible version of [`bvsub_no_underflow`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `a` and `b` are not bitvectors
    /// of the same width.
    ///
    /// [`bvsub_no_underflow`]: Solver::bvsub_no_underflow
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvsub_no_underflow(
        &mut self,
        a: Term,
        b: Term,
        is_signed: bool,
    ) -> Result<Term, SolverError> {
        let width = self.expect_same_bitvec_width("bvsub_no_underflow", a, b)?;
        if is_signed {
            let zero = self.bv_const(0, width);
            let b_pos = self.try_bvsgt(b, zero)?;
            let neg_b = self.try_bvneg(b)?;
            let add_no_udfl = self.try_bvadd_no_underflow(a, neg_b)?;
            Ok(self.try_implies(b_pos, add_no_udfl)?)
        } else {
            // Unsigned: no underflow iff b <= a
            Ok(self.try_bvule(b, a)?)
        }
    }

    /// Check that signed multiplication does not overflow
    ///
    /// Multiplication overflow is complex. We use the approach of
    /// sign-extending both operands to double width, multiplying,
    /// and checking that the high bits are all sign extension of the result.
    ///
    /// # Panics
    /// Panics if either argument is not a bitvector sort. Use [`Self::try_bvmul_no_overflow`] for a
    /// fallible version that returns an error instead.
    pub fn bvmul_no_overflow(&mut self, a: Term, b: Term, is_signed: bool) -> Term {
        self.try_bvmul_no_overflow(a, b, is_signed)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an overflow check predicate for bitvector multiplication.
    ///
    /// Fallible version of [`bvmul_no_overflow`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `a` and `b` are not bitvectors
    /// of the same width.
    ///
    /// Returns [`SolverError::InvalidArgument`] if the bitvector width is 0 or the intermediate
    /// widened width (2 * width) overflows u32.
    ///
    /// [`bvmul_no_overflow`]: Solver::bvmul_no_overflow
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvmul_no_overflow(
        &mut self,
        a: Term,
        b: Term,
        is_signed: bool,
    ) -> Result<Term, SolverError> {
        let width = self.expect_same_bitvec_width("bvmul_no_overflow", a, b)?;
        Self::validate_mul_predicate_width("bvmul_no_overflow", width)?;
        if is_signed {
            let fits = self.try_signed_mul_fits_in_width(a, b, width)?;
            let sign_a = self.try_bvextract(a, width - 1, width - 1)?;
            let sign_b = self.try_bvextract(b, width - 1, width - 1)?;
            let same_sign = self.try_eq(sign_a, sign_b)?;
            // Signed overflow can only happen for same-sign operands.
            Ok(self.try_implies(same_sign, fits)?)
        } else {
            // Zero-extend both to 2*width, multiply, check high bits are 0
            let a_ext = self.try_bvzeroext(a, width)?;
            let b_ext = self.try_bvzeroext(b, width)?;
            let prod_ext = self.try_bvmul(a_ext, b_ext)?;
            let high = self.try_bvextract(prod_ext, 2 * width - 1, width)?;
            let zero = self.bv_const(0, width);
            Ok(self.try_eq(high, zero)?)
        }
    }

    /// Check that signed multiplication does not underflow
    ///
    /// Similar to overflow but checking for negative overflow.
    ///
    /// # Panics
    /// Panics if either argument is not a bitvector sort. Use [`Self::try_bvmul_no_underflow`] for a
    /// fallible version that returns an error instead.
    pub fn bvmul_no_underflow(&mut self, a: Term, b: Term) -> Term {
        self.try_bvmul_no_underflow(a, b)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an underflow check predicate for signed bitvector multiplication.
    ///
    /// Fallible version of [`bvmul_no_underflow`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `a` and `b` are not bitvectors
    /// of the same width.
    ///
    /// Returns [`SolverError::InvalidArgument`] if the bitvector width is 0 or the intermediate
    /// widened width (2 * width) overflows u32.
    ///
    /// [`bvmul_no_underflow`]: Solver::bvmul_no_underflow
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvmul_no_underflow(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let width = self.expect_same_bitvec_width("bvmul_no_underflow", a, b)?;
        Self::validate_mul_predicate_width("bvmul_no_underflow", width)?;
        let fits = self.try_signed_mul_fits_in_width(a, b, width)?;
        let sign_a = self.try_bvextract(a, width - 1, width - 1)?;
        let sign_b = self.try_bvextract(b, width - 1, width - 1)?;
        let same_signs = self.try_eq(sign_a, sign_b)?;
        let different_signs = self.try_not(same_signs)?;
        // Signed underflow can only happen for different-sign operands.
        self.try_implies(different_signs, fits)
    }

    fn try_signed_mul_fits_in_width(
        &mut self,
        a: Term,
        b: Term,
        width: u32,
    ) -> Result<Term, SolverError> {
        // Sign-extend both to 2*width, multiply, check result fits in width.
        let a_ext = self.try_bvsignext(a, width)?;
        let b_ext = self.try_bvsignext(b, width)?;
        let prod_ext = self.try_bvmul(a_ext, b_ext)?;
        let high = self.try_bvextract(prod_ext, 2 * width - 1, width)?;
        let low = self.try_bvextract(prod_ext, width - 1, 0)?;
        let sign_bit = self.try_bvextract(low, width - 1, width - 1)?;
        let sign_ext = self.try_bvsignext(sign_bit, width - 1)?;
        self.try_eq(high, sign_ext)
    }

    fn validate_mul_predicate_width(
        operation: &'static str,
        width: u32,
    ) -> Result<(), SolverError> {
        if width == 0 {
            return Err(SolverError::InvalidArgument {
                operation,
                message: "bitvector width (0) must be > 0".to_string(),
            });
        }
        let out_w_u64 = u64::from(width) * 2;
        if out_w_u64 > u64::from(u32::MAX) {
            return Err(SolverError::InvalidArgument {
                operation,
                message: format!("resulting bitvector width overflows u32: {width} * 2"),
            });
        }
        Ok(())
    }

    /// Check that signed negation does not overflow
    ///
    /// The only case where negation overflows is when negating MIN,
    /// since -MIN cannot be represented (it would be MAX + 1).
    ///
    /// # Panics
    /// Panics if the argument is not a bitvector sort. Use [`Self::try_bvneg_no_overflow`] for a
    /// fallible version that returns an error instead.
    pub fn bvneg_no_overflow(&mut self, a: Term) -> Term {
        self.try_bvneg_no_overflow(a)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an overflow check predicate for signed bitvector negation.
    ///
    /// Fallible version of [`bvneg_no_overflow`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `a` is not a bitvector.
    ///
    /// Returns [`SolverError::InvalidArgument`] if the bitvector width is 0.
    ///
    /// [`bvneg_no_overflow`]: Solver::bvneg_no_overflow
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvneg_no_overflow(&mut self, a: Term) -> Result<Term, SolverError> {
        let width = self.expect_bitvec_width("bvneg_no_overflow", a)?;
        if width == 0 {
            return Err(SolverError::InvalidArgument {
                operation: "bvneg_no_overflow",
                message: "bitvector width (0) must be > 0".to_string(),
            });
        }
        // Negation overflows only when a == MIN (since -MIN = MAX + 1)
        let min = self.bv_smin(width);
        let a_is_min = self.try_eq(a, min)?;
        let result = self.try_not(a_is_min)?;
        Ok(result)
    }

    /// Check that signed division does not overflow
    ///
    /// The only overflow case for signed division is MIN / -1,
    /// which would produce MAX + 1 (not representable).
    ///
    /// # Panics
    /// Panics if either argument is not a bitvector sort. Use [`Self::try_bvsdiv_no_overflow`] for a
    /// fallible version that returns an error instead.
    pub fn bvsdiv_no_overflow(&mut self, a: Term, b: Term) -> Term {
        self.try_bvsdiv_no_overflow(a, b)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create an overflow check predicate for signed bitvector division.
    ///
    /// Fallible version of [`bvsdiv_no_overflow`]. Returns an error instead of panicking.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `a` and `b` are not bitvectors
    /// of the same width.
    ///
    /// Returns [`SolverError::InvalidArgument`] if the bitvector width is 0.
    ///
    /// [`bvsdiv_no_overflow`]: Solver::bvsdiv_no_overflow
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bvsdiv_no_overflow(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let width = self.expect_same_bitvec_width("bvsdiv_no_overflow", a, b)?;
        if width == 0 {
            return Err(SolverError::InvalidArgument {
                operation: "bvsdiv_no_overflow",
                message: "bitvector width (0) must be > 0".to_string(),
            });
        }
        // Signed division overflows only when a == MIN and b == -1
        // because MIN / -1 = MAX + 1 (not representable)
        let min = self.bv_smin(width);
        let neg_one = self.bv_all_ones(width);
        let a_is_min = self.try_eq(a, min)?;
        let b_is_neg_one = self.try_eq(b, neg_one)?;
        let bad_case = self.try_and(a_is_min, b_is_neg_one)?;
        let result = self.try_not(bad_case)?;
        Ok(result)
    }
}
