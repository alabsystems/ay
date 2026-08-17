// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fallible floating-point constant construction and format validation.

use super::super::types::{SolverError, Term};
use super::super::Solver;
use ay_core::{Sort, Symbol};
use num_bigint::BigInt;

/// Dense native FP construction bounds shared by all fallible API builders.
const MAX_API_FP_EXPONENT_BITS: u32 = 31;
const MAX_API_FP_SIGNIFICAND_BITS: u32 = 1 << 20;

impl Solver {
    pub(in crate::api) fn checked_fp_total_width(
        &self,
        operation: &'static str,
        eb: u32,
        sb: u32,
    ) -> Result<u32, SolverError> {
        if !(2..=MAX_API_FP_EXPONENT_BITS).contains(&eb)
            || !(2..=MAX_API_FP_SIGNIFICAND_BITS).contains(&sb)
        {
            return Err(SolverError::InvalidArgument {
                operation,
                message: format!(
                    "FP format outside supported ranges: eb={eb} (2..={MAX_API_FP_EXPONENT_BITS}), sb={sb} (2..={MAX_API_FP_SIGNIFICAND_BITS})"
                ),
            });
        }
        eb.checked_add(sb)
            .ok_or_else(|| SolverError::InvalidArgument {
                operation,
                message: format!("FP width eb+sb overflows u32, got eb={eb}, sb={sb}"),
            })
    }

    /// Try to create an FP constant from a raw IEEE 754 bit pattern.
    ///
    /// The bit pattern is interpreted as: sign (1 bit) | exponent (`eb` bits) |
    /// significand (`sb - 1` bits). Total width = `eb + sb`.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `(eb, sb)` is outside the
    /// supported FP format envelope.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_const_from_bits(
        &mut self,
        bits: u64,
        eb: u32,
        sb: u32,
    ) -> Result<Term, SolverError> {
        self.try_fp_const_from_bits_bigint(&BigInt::from(bits), eb, sb)
    }

    /// Try to create an FP constant from an arbitrary-width IEEE 754 bit pattern.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `(eb, sb)` is outside the
    /// supported FP format envelope.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_const_from_bits_bigint(
        &mut self,
        bits: &BigInt,
        eb: u32,
        sb: u32,
    ) -> Result<Term, SolverError> {
        // Validate the compact format before constructing the backing BV.
        // Otherwise a near-u32::MAX width can request a multi-gigabyte
        // allocation only to be rejected by the later FP conversion.
        let total_width = self.checked_fp_total_width("fp_const_from_bits", eb, sb)?;
        let bv = self.try_bv_const_bigint(bits, total_width)?;
        self.try_bv_to_fp_reinterpret(bv, eb, sb)
    }

    /// Try to create FP +infinity constant for the given precision.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `eb` or `sb` is zero, or if
    /// `eb + sb` overflows.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_plus_infinity(&mut self, eb: u32, sb: u32) -> Result<Term, SolverError> {
        self.checked_fp_total_width("fp_plus_infinity", eb, sb)?;
        let sort = Sort::FloatingPoint(eb, sb);
        let result = self
            .terms_mut()
            .mk_app(Symbol::indexed("+oo", vec![eb, sb]), vec![], sort);
        Ok(self.wrap_term(result))
    }

    /// Try to create FP -infinity constant for the given precision.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `eb` or `sb` is zero, or if
    /// `eb + sb` overflows.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_minus_infinity(&mut self, eb: u32, sb: u32) -> Result<Term, SolverError> {
        self.checked_fp_total_width("fp_minus_infinity", eb, sb)?;
        let sort = Sort::FloatingPoint(eb, sb);
        let result = self
            .terms_mut()
            .mk_app(Symbol::indexed("-oo", vec![eb, sb]), vec![], sort);
        Ok(self.wrap_term(result))
    }

    /// Try to create FP NaN constant for the given precision.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `eb` or `sb` is zero, or if
    /// `eb + sb` overflows.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_nan(&mut self, eb: u32, sb: u32) -> Result<Term, SolverError> {
        self.checked_fp_total_width("fp_nan", eb, sb)?;
        let sort = Sort::FloatingPoint(eb, sb);
        let result = self
            .terms_mut()
            .mk_app(Symbol::indexed("NaN", vec![eb, sb]), vec![], sort);
        Ok(self.wrap_term(result))
    }

    /// Try to create FP +zero constant for the given precision.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `eb` or `sb` is zero, or if
    /// `eb + sb` overflows.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_plus_zero(&mut self, eb: u32, sb: u32) -> Result<Term, SolverError> {
        self.checked_fp_total_width("fp_plus_zero", eb, sb)?;
        let sort = Sort::FloatingPoint(eb, sb);
        let result = self
            .terms_mut()
            .mk_app(Symbol::indexed("+zero", vec![eb, sb]), vec![], sort);
        Ok(self.wrap_term(result))
    }

    /// Try to create FP -zero constant for the given precision.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `eb` or `sb` is zero, or if
    /// `eb + sb` overflows.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_minus_zero(&mut self, eb: u32, sb: u32) -> Result<Term, SolverError> {
        self.checked_fp_total_width("fp_minus_zero", eb, sb)?;
        let sort = Sort::FloatingPoint(eb, sb);
        let result = self
            .terms_mut()
            .mk_app(Symbol::indexed("-zero", vec![eb, sb]), vec![], sort);
        Ok(self.wrap_term(result))
    }
}
