// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Floating-point operations for AY Solver API (#5774).
//!
//! FP operations are constructed via `mk_app` with SMT-LIB standard symbol
//! names. The FP theory solver recognizes these symbols and handles them via
//! eager bit-blasting.

use super::types::{SolverError, Term};
use super::Solver;
use ay_core::{Sort, Symbol};
use num_bigint::BigInt;

/// Dense native FP construction bounds shared by all fallible API builders.
const MAX_API_FP_EXPONENT_BITS: u32 = 31;
const MAX_API_FP_SIGNIFICAND_BITS: u32 = 1 << 20;

impl Solver {
    // --- Sort helpers ---

    pub(super) fn expect_fp(
        &self,
        operation: &'static str,
        t: Term,
    ) -> Result<(u32, u32), SolverError> {
        let sort = self.terms().sort(t.0).clone();
        match sort {
            Sort::FloatingPoint(eb, sb) => {
                self.checked_fp_total_width(operation, eb, sb)?;
                Ok((eb, sb))
            }
            other => Err(SolverError::SortMismatch {
                operation,
                expected: "FloatingPoint",
                got: vec![other],
            }),
        }
    }

    pub(super) fn expect_same_fp(
        &self,
        operation: &'static str,
        a: Term,
        b: Term,
    ) -> Result<(u32, u32), SolverError> {
        let (eb_a, sb_a) = self.expect_fp(operation, a)?;
        let (eb_b, sb_b) = self.expect_fp(operation, b)?;
        if eb_a != eb_b || sb_a != sb_b {
            return Err(SolverError::SortMismatch {
                operation,
                expected: "FloatingPoint (same precision)",
                got: vec![
                    Sort::FloatingPoint(eb_a, sb_a),
                    Sort::FloatingPoint(eb_b, sb_b),
                ],
            });
        }
        Ok((eb_a, sb_a))
    }

    pub(super) fn checked_fp_total_width(
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

    // --- FP constants ---

    /// Create an FP constant from a raw IEEE 754 bit pattern.
    ///
    /// The bit pattern is interpreted as: sign (1 bit) | exponent (`eb` bits) |
    /// significand (`sb - 1` bits). Total width = `eb + sb`.
    ///
    /// Supports standard precisions whose bit pattern fits in `u64`:
    /// - FP16: `eb=5, sb=11` (16 bits total)
    /// - FP32: `eb=8, sb=24` (32 bits total)
    /// - FP64: `eb=11, sb=53` (64 bits total)
    ///
    /// Correctly handles special values (NaN payloads, denormals, signed zeros).
    /// Use [`try_fp_const_from_bits_bigint`](Self::try_fp_const_from_bits_bigint)
    /// for FP128 or other wider bit patterns.
    ///
    /// # Panics
    ///
    /// Panics if `(eb, sb)` is outside the supported FP format envelope.
    /// Use [`try_fp_const_from_bits`](Self::try_fp_const_from_bits) for a fallible version.
    pub fn fp_const_from_bits(&mut self, bits: u64, eb: u32, sb: u32) -> Term {
        self.try_fp_const_from_bits(bits, eb, sb)
            .unwrap_or_else(|e| panic!("{e}"))
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

    /// Create an FP constant from an arbitrary-width IEEE 754 bit pattern.
    ///
    /// Use this for FP128 (`eb=15, sb=113`) and any future format wider than
    /// 64 bits. The bit pattern is interpreted modulo `2^(eb + sb)`, matching
    /// the bitvector constructor used underneath.
    ///
    /// # Panics
    ///
    /// Panics if `(eb, sb)` is outside the supported FP format envelope.
    /// Use [`try_fp_const_from_bits_bigint`](Self::try_fp_const_from_bits_bigint)
    /// for a fallible version.
    pub fn fp_const_from_bits_bigint(&mut self, bits: &BigInt, eb: u32, sb: u32) -> Term {
        self.try_fp_const_from_bits_bigint(bits, eb, sb)
            .unwrap_or_else(|e| panic!("{e}"))
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

    /// Create FP +infinity constant for the given precision.
    #[must_use = "this creates a term that is usually needed for assertions"]
    pub fn fp_plus_infinity(&mut self, eb: u32, sb: u32) -> Term {
        self.try_fp_plus_infinity(eb, sb)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP +infinity constant for the given precision.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `eb` or `sb` is zero, or if
    /// `eb + sb` overflows.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_plus_infinity(&mut self, eb: u32, sb: u32) -> Result<Term, SolverError> {
        self.checked_fp_total_width("fp_plus_infinity", eb, sb)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::indexed("+oo", vec![eb, sb]),
            vec![],
            sort,
        )))
    }

    /// Create FP -infinity constant for the given precision.
    #[must_use = "this creates a term that is usually needed for assertions"]
    pub fn fp_minus_infinity(&mut self, eb: u32, sb: u32) -> Term {
        self.try_fp_minus_infinity(eb, sb)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP -infinity constant for the given precision.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `eb` or `sb` is zero, or if
    /// `eb + sb` overflows.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_minus_infinity(&mut self, eb: u32, sb: u32) -> Result<Term, SolverError> {
        self.checked_fp_total_width("fp_minus_infinity", eb, sb)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::indexed("-oo", vec![eb, sb]),
            vec![],
            sort,
        )))
    }

    /// Create FP NaN constant for the given precision.
    #[must_use = "this creates a term that is usually needed for assertions"]
    pub fn fp_nan(&mut self, eb: u32, sb: u32) -> Term {
        self.try_fp_nan(eb, sb).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP NaN constant for the given precision.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `eb` or `sb` is zero, or if
    /// `eb + sb` overflows.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_nan(&mut self, eb: u32, sb: u32) -> Result<Term, SolverError> {
        self.checked_fp_total_width("fp_nan", eb, sb)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::indexed("NaN", vec![eb, sb]),
            vec![],
            sort,
        )))
    }

    /// Create FP +zero constant for the given precision.
    #[must_use = "this creates a term that is usually needed for assertions"]
    pub fn fp_plus_zero(&mut self, eb: u32, sb: u32) -> Term {
        self.try_fp_plus_zero(eb, sb)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP +zero constant for the given precision.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `eb` or `sb` is zero, or if
    /// `eb + sb` overflows.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_plus_zero(&mut self, eb: u32, sb: u32) -> Result<Term, SolverError> {
        self.checked_fp_total_width("fp_plus_zero", eb, sb)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::indexed("+zero", vec![eb, sb]),
            vec![],
            sort,
        )))
    }

    /// Create FP -zero constant for the given precision.
    #[must_use = "this creates a term that is usually needed for assertions"]
    pub fn fp_minus_zero(&mut self, eb: u32, sb: u32) -> Term {
        self.try_fp_minus_zero(eb, sb)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP -zero constant for the given precision.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `eb` or `sb` is zero, or if
    /// `eb + sb` overflows.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_minus_zero(&mut self, eb: u32, sb: u32) -> Result<Term, SolverError> {
        self.checked_fp_total_width("fp_minus_zero", eb, sb)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::indexed("-zero", vec![eb, sb]),
            vec![],
            sort,
        )))
    }

    // --- FP unary operations ---

    /// Create FP absolute value.
    pub fn fp_abs(&mut self, a: Term) -> Term {
        self.try_fp_abs(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP absolute value (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_abs(&mut self, a: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_fp("fp.abs", a)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.abs"),
            vec![a.0],
            sort,
        )))
    }

    /// Create FP negation.
    pub fn fp_neg(&mut self, a: Term) -> Term {
        self.try_fp_neg(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP negation (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_neg(&mut self, a: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_fp("fp.neg", a)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.neg"),
            vec![a.0],
            sort,
        )))
    }

    // --- FP comparison predicates (return Bool) ---

    /// Create FP IEEE equality.
    pub fn fp_eq(&mut self, a: Term, b: Term) -> Term {
        self.try_fp_eq(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP IEEE equality (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_eq(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_fp("fp.eq", a, b)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.eq"),
            vec![a.0, b.0],
            Sort::Bool,
        )))
    }

    /// Create FP less-than.
    pub fn fp_lt(&mut self, a: Term, b: Term) -> Term {
        self.try_fp_lt(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP less-than (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_lt(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_fp("fp.lt", a, b)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.lt"),
            vec![a.0, b.0],
            Sort::Bool,
        )))
    }

    /// Create FP less-than-or-equal.
    pub fn fp_le(&mut self, a: Term, b: Term) -> Term {
        self.try_fp_le(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP less-than-or-equal (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_le(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_fp("fp.leq", a, b)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.leq"),
            vec![a.0, b.0],
            Sort::Bool,
        )))
    }

    /// Create FP greater-than.
    pub fn fp_gt(&mut self, a: Term, b: Term) -> Term {
        self.try_fp_gt(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP greater-than (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_gt(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_fp("fp.gt", a, b)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.gt"),
            vec![a.0, b.0],
            Sort::Bool,
        )))
    }

    /// Create FP greater-than-or-equal.
    pub fn fp_ge(&mut self, a: Term, b: Term) -> Term {
        self.try_fp_ge(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP greater-than-or-equal (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_ge(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        self.expect_same_fp("fp.geq", a, b)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.geq"),
            vec![a.0, b.0],
            Sort::Bool,
        )))
    }

    // --- FP classification predicates (return Bool) ---

    /// Create FP isNaN predicate.
    pub fn fp_is_nan(&mut self, a: Term) -> Term {
        self.try_fp_is_nan(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP isNaN predicate (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_is_nan(&mut self, a: Term) -> Result<Term, SolverError> {
        self.expect_fp("fp.isNaN", a)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.isNaN"),
            vec![a.0],
            Sort::Bool,
        )))
    }

    /// Create FP isInfinite predicate.
    pub fn fp_is_infinite(&mut self, a: Term) -> Term {
        self.try_fp_is_infinite(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP isInfinite predicate (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_is_infinite(&mut self, a: Term) -> Result<Term, SolverError> {
        self.expect_fp("fp.isInfinite", a)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.isInfinite"),
            vec![a.0],
            Sort::Bool,
        )))
    }

    /// Create FP isZero predicate.
    pub fn fp_is_zero(&mut self, a: Term) -> Term {
        self.try_fp_is_zero(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP isZero predicate (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_is_zero(&mut self, a: Term) -> Result<Term, SolverError> {
        self.expect_fp("fp.isZero", a)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.isZero"),
            vec![a.0],
            Sort::Bool,
        )))
    }

    /// Create FP isNormal predicate.
    pub fn fp_is_normal(&mut self, a: Term) -> Term {
        self.try_fp_is_normal(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP isNormal predicate (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_is_normal(&mut self, a: Term) -> Result<Term, SolverError> {
        self.expect_fp("fp.isNormal", a)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.isNormal"),
            vec![a.0],
            Sort::Bool,
        )))
    }

    /// Create FP isSubnormal predicate.
    pub fn fp_is_subnormal(&mut self, a: Term) -> Term {
        self.try_fp_is_subnormal(a)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP isSubnormal predicate (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_is_subnormal(&mut self, a: Term) -> Result<Term, SolverError> {
        self.expect_fp("fp.isSubnormal", a)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.isSubnormal"),
            vec![a.0],
            Sort::Bool,
        )))
    }

    /// Create FP isPositive predicate.
    pub fn fp_is_positive(&mut self, a: Term) -> Term {
        self.try_fp_is_positive(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP isPositive predicate (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_is_positive(&mut self, a: Term) -> Result<Term, SolverError> {
        self.expect_fp("fp.isPositive", a)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.isPositive"),
            vec![a.0],
            Sort::Bool,
        )))
    }

    /// Create FP isNegative predicate.
    pub fn fp_is_negative(&mut self, a: Term) -> Term {
        self.try_fp_is_negative(a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP isNegative predicate (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_is_negative(&mut self, a: Term) -> Result<Term, SolverError> {
        self.expect_fp("fp.isNegative", a)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.isNegative"),
            vec![a.0],
            Sort::Bool,
        )))
    }

    // --- FP min/max ---

    /// Create FP minimum.
    pub fn fp_min(&mut self, a: Term, b: Term) -> Term {
        self.try_fp_min(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP minimum (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_min(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_same_fp("fp.min", a, b)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.min"),
            vec![a.0, b.0],
            sort,
        )))
    }

    /// Create FP maximum.
    pub fn fp_max(&mut self, a: Term, b: Term) -> Term {
        self.try_fp_max(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP maximum (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_max(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_same_fp("fp.max", a, b)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.max"),
            vec![a.0, b.0],
            sort,
        )))
    }

    // --- Rounding mode ---

    /// Create a rounding mode term from its SMT-LIB short name.
    ///
    /// Valid names: "RNE", "RNA", "RTP", "RTN", "RTZ".
    /// The FP solver matches on the symbol name, not the sort.
    ///
    /// # Panics
    ///
    /// Panics if `name` is not a valid rounding mode.
    /// Use [`try_fp_rounding_mode`](Self::try_fp_rounding_mode) for a fallible version.
    pub fn fp_rounding_mode(&mut self, name: &str) -> Term {
        self.try_fp_rounding_mode(name)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a rounding mode term from its SMT-LIB short name.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `name` is not one of
    /// "RNE", "RNA", "RTP", "RTN", "RTZ".
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_rounding_mode(&mut self, name: &str) -> Result<Term, SolverError> {
        if !matches!(name, "RNE" | "RNA" | "RTP" | "RTN" | "RTZ") {
            return Err(SolverError::InvalidArgument {
                operation: "fp_rounding_mode",
                message: format!(
                    "invalid rounding mode '{name}': expected RNE, RNA, RTP, RTN, or RTZ"
                ),
            });
        }
        // RoundingMode-sorted, matching both the frontend's literal elaboration
        // and the sort of a declared `RoundingMode` constant. The historical
        // `Sort::Bool` encoding made `rm == RTP()` panic on the sort mismatch
        // in `Term::eq` (#P0.2 symbolic RoundingMode).
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named(name),
            vec![],
            Sort::Uninterpreted("RoundingMode".to_string()),
        )))
    }

    // Conversion and arithmetic operations are in floating_point_conv.rs.
}
