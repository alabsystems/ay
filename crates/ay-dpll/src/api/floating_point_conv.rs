// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Floating-point conversion and arithmetic operations.
//!
//! FP-to-BV, BV-to-FP, FP-to-Real, FP precision conversion, and rounded
//! arithmetic (add, sub, mul, div, sqrt, fma, rem, roundToIntegral).
//! Predicate and comparison operations are in `floating_point.rs`.

use super::types::{SolverError, Term};
use super::Solver;
use ay_core::{BitVecSort, Sort, Symbol};

/// FP classification values returned by [`Solver::try_fp_classify`] as BV3.
///
/// These match the encoding: 0=normal, 1=subnormal, 2=zero, 3=infinity, 4=NaN.
pub mod fp_class {
    /// Normal floating-point number.
    pub const NORMAL: i64 = 0;
    /// Subnormal (denormalized) floating-point number.
    pub const SUBNORMAL: i64 = 1;
    /// Positive or negative zero.
    pub const ZERO: i64 = 2;
    /// Positive or negative infinity.
    pub const INFINITY: i64 = 3;
    /// Not a Number.
    pub const NAN: i64 = 4;
}

impl Solver {
    // --- FP conversions ---

    /// Convert FP to signed bitvector: ((_ fp.to_sbv w) rm x).
    /// Panics if `x` is not a FloatingPoint sort.
    pub fn fp_to_sbv(&mut self, rm: Term, x: Term, width: u32) -> Term {
        self.try_fp_to_sbv(rm, x, width)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert FP to signed bitvector (fallible).
    ///
    /// Returns [`SolverError::SortMismatch`] if `x` is not a FloatingPoint sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_to_sbv(&mut self, rm: Term, x: Term, width: u32) -> Result<Term, SolverError> {
        self.expect_fp("fp.to_sbv", x)?;
        let sort = Sort::BitVec(BitVecSort { width });
        Ok(Term(self.terms_mut().mk_app(
            Symbol::indexed("fp.to_sbv", vec![width]),
            vec![rm.0, x.0],
            sort,
        )))
    }

    /// Convert FP to unsigned bitvector: ((_ fp.to_ubv w) rm x).
    /// Panics if `x` is not a FloatingPoint sort.
    pub fn fp_to_ubv(&mut self, rm: Term, x: Term, width: u32) -> Term {
        self.try_fp_to_ubv(rm, x, width)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert FP to unsigned bitvector (fallible).
    ///
    /// Returns [`SolverError::SortMismatch`] if `x` is not a FloatingPoint sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_to_ubv(&mut self, rm: Term, x: Term, width: u32) -> Result<Term, SolverError> {
        self.expect_fp("fp.to_ubv", x)?;
        let sort = Sort::BitVec(BitVecSort { width });
        Ok(Term(self.terms_mut().mk_app(
            Symbol::indexed("fp.to_ubv", vec![width]),
            vec![rm.0, x.0],
            sort,
        )))
    }

    /// Convert FP to real: (fp.to_real x).
    /// Panics if `x` is not a FloatingPoint sort.
    pub fn fp_to_real(&mut self, x: Term) -> Term {
        self.try_fp_to_real(x).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert FP to real (fallible).
    ///
    /// Returns [`SolverError::SortMismatch`] if `x` is not a FloatingPoint sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_to_real(&mut self, x: Term) -> Result<Term, SolverError> {
        self.expect_fp("fp.to_real", x)?;
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.to_real"),
            vec![x.0],
            Sort::Real,
        )))
    }

    /// Convert FP to IEEE 754 bitvector (bit-pattern reinterpretation): (fp.to_ieee_bv x).
    ///
    /// Returns [`SolverError::SortMismatch`] if `x` is not a FloatingPoint sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_to_ieee_bv(&mut self, x: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_fp("fp.to_ieee_bv", x)?;
        let width = self.checked_fp_total_width("fp.to_ieee_bv", eb, sb)?;
        let sort = Sort::BitVec(BitVecSort { width });
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.to_ieee_bv"),
            vec![x.0],
            sort,
        )))
    }

    /// Construct FP from sign, exponent, significand bitvectors: (fp sign exp sig).
    /// Panics if `sign`, `exp`, or `sig` are not bitvector sorts.
    pub fn fp_from_bvs(&mut self, sign: Term, exp: Term, sig: Term, eb: u32, sb: u32) -> Term {
        self.try_fp_from_bvs(sign, exp, sig, eb, sb)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to construct FP from sign, exponent, significand bitvectors (fallible).
    ///
    /// Returns [`SolverError::SortMismatch`] if any argument is not a bitvector sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_from_bvs(
        &mut self,
        sign: Term,
        exp: Term,
        sig: Term,
        eb: u32,
        sb: u32,
    ) -> Result<Term, SolverError> {
        self.checked_fp_total_width("fp", eb, sb)?;
        let sign_width = self.expect_bitvec_width("fp (sign)", sign)?;
        let exp_width = self.expect_bitvec_width("fp (exponent)", exp)?;
        let sig_width = self.expect_bitvec_width("fp (significand)", sig)?;
        let expected_sig_width = sb - 1;
        if sign_width != 1 || exp_width != eb || sig_width != expected_sig_width {
            return Err(SolverError::InvalidArgument {
                operation: "fp",
                message: format!(
                    "component widths must be sign=1, exponent={eb}, significand={expected_sig_width}; \
                     got sign={sign_width}, exponent={exp_width}, significand={sig_width}"
                ),
            });
        }
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp"),
            vec![sign.0, exp.0, sig.0],
            sort,
        )))
    }

    /// Convert bitvector to FP (interpret as IEEE 754): ((_ to_fp eb sb) rm bv).
    /// Panics if `bv` is not a bitvector sort.
    pub fn bv_to_fp(&mut self, rm: Term, bv: Term, eb: u32, sb: u32) -> Term {
        self.try_bv_to_fp(rm, bv, eb, sb)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert bitvector to FP (fallible).
    ///
    /// Returns [`SolverError::SortMismatch`] if `bv` is not a bitvector sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bv_to_fp(
        &mut self,
        rm: Term,
        bv: Term,
        eb: u32,
        sb: u32,
    ) -> Result<Term, SolverError> {
        self.expect_bitvec("to_fp", bv)?;
        self.checked_fp_total_width("to_fp", eb, sb)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::indexed("to_fp", vec![eb, sb]),
            vec![rm.0, bv.0],
            sort,
        )))
    }

    /// Convert unsigned bitvector to FP: ((_ to_fp_unsigned eb sb) rm bv).
    /// Panics if `bv` is not a bitvector sort.
    pub fn bv_to_fp_unsigned(&mut self, rm: Term, bv: Term, eb: u32, sb: u32) -> Term {
        self.try_bv_to_fp_unsigned(rm, bv, eb, sb)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert unsigned bitvector to FP (fallible).
    ///
    /// Returns [`SolverError::SortMismatch`] if `bv` is not a bitvector sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bv_to_fp_unsigned(
        &mut self,
        rm: Term,
        bv: Term,
        eb: u32,
        sb: u32,
    ) -> Result<Term, SolverError> {
        self.expect_bitvec("to_fp_unsigned", bv)?;
        self.checked_fp_total_width("to_fp_unsigned", eb, sb)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::indexed("to_fp_unsigned", vec![eb, sb]),
            vec![rm.0, bv.0],
            sort,
        )))
    }

    /// Convert FP to different precision: ((_ to_fp eb sb) rm fp).
    /// Panics if `fp` is not a FloatingPoint sort.
    pub fn fp_to_fp(&mut self, rm: Term, fp: Term, eb: u32, sb: u32) -> Term {
        self.try_fp_to_fp(rm, fp, eb, sb)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to convert FP to different precision (fallible).
    ///
    /// Returns [`SolverError::SortMismatch`] if `fp` is not a FloatingPoint sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_to_fp(
        &mut self,
        rm: Term,
        fp: Term,
        eb: u32,
        sb: u32,
    ) -> Result<Term, SolverError> {
        self.expect_fp("to_fp (fp)", fp)?;
        self.checked_fp_total_width("to_fp", eb, sb)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::indexed("to_fp", vec![eb, sb]),
            vec![rm.0, fp.0],
            sort,
        )))
    }

    // --- FP rounded arithmetic operations ---

    /// Create FP addition with rounding mode: `(fp.add rm a b)`.
    pub fn fp_add(&mut self, rm: Term, a: Term, b: Term) -> Term {
        self.try_fp_add(rm, a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP addition with rounding mode (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_add(&mut self, rm: Term, a: Term, b: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_same_fp("fp.add", a, b)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.add"),
            vec![rm.0, a.0, b.0],
            sort,
        )))
    }

    /// Create FP subtraction with rounding mode: `(fp.sub rm a b)`.
    pub fn fp_sub(&mut self, rm: Term, a: Term, b: Term) -> Term {
        self.try_fp_sub(rm, a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP subtraction with rounding mode (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_sub(&mut self, rm: Term, a: Term, b: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_same_fp("fp.sub", a, b)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.sub"),
            vec![rm.0, a.0, b.0],
            sort,
        )))
    }

    /// Create FP multiplication with rounding mode: `(fp.mul rm a b)`.
    pub fn fp_mul(&mut self, rm: Term, a: Term, b: Term) -> Term {
        self.try_fp_mul(rm, a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP multiplication with rounding mode (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_mul(&mut self, rm: Term, a: Term, b: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_same_fp("fp.mul", a, b)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.mul"),
            vec![rm.0, a.0, b.0],
            sort,
        )))
    }

    /// Create FP division with rounding mode: `(fp.div rm a b)`.
    pub fn fp_div(&mut self, rm: Term, a: Term, b: Term) -> Term {
        self.try_fp_div(rm, a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP division with rounding mode (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_div(&mut self, rm: Term, a: Term, b: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_same_fp("fp.div", a, b)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.div"),
            vec![rm.0, a.0, b.0],
            sort,
        )))
    }

    /// Create FP square root with rounding mode: `(fp.sqrt rm a)`.
    pub fn fp_sqrt(&mut self, rm: Term, a: Term) -> Term {
        self.try_fp_sqrt(rm, a).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP square root with rounding mode (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_sqrt(&mut self, rm: Term, a: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_fp("fp.sqrt", a)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.sqrt"),
            vec![rm.0, a.0],
            sort,
        )))
    }

    /// Create FP fused multiply-add with rounding mode: `(fp.fma rm a b c)`.
    ///
    /// Computes `a * b + c` with a single rounding.
    pub fn fp_fma(&mut self, rm: Term, a: Term, b: Term, c: Term) -> Term {
        self.try_fp_fma(rm, a, b, c)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP fused multiply-add with rounding mode (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_fma(&mut self, rm: Term, a: Term, b: Term, c: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_same_fp("fp.fma", a, b)?;
        let (eb_c, sb_c) = self.expect_fp("fp.fma", c)?;
        if eb != eb_c || sb != sb_c {
            return Err(SolverError::SortMismatch {
                operation: "fp.fma",
                expected: "FloatingPoint (same precision for all operands)",
                got: vec![Sort::FloatingPoint(eb, sb), Sort::FloatingPoint(eb_c, sb_c)],
            });
        }
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.fma"),
            vec![rm.0, a.0, b.0, c.0],
            sort,
        )))
    }

    /// Create FP remainder: `(fp.rem a b)`.
    ///
    /// IEEE 754 remainder (no rounding mode needed).
    pub fn fp_rem(&mut self, a: Term, b: Term) -> Term {
        self.try_fp_rem(a, b).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP remainder (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_rem(&mut self, a: Term, b: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_same_fp("fp.rem", a, b)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.rem"),
            vec![a.0, b.0],
            sort,
        )))
    }

    /// Create FP round-to-integral: `(fp.roundToIntegral rm a)`.
    pub fn fp_round_to_integral(&mut self, rm: Term, a: Term) -> Term {
        self.try_fp_round_to_integral(rm, a)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create FP round-to-integral (fallible).
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_round_to_integral(&mut self, rm: Term, a: Term) -> Result<Term, SolverError> {
        let (eb, sb) = self.expect_fp("fp.roundToIntegral", a)?;
        let sort = Sort::FloatingPoint(eb, sb);
        Ok(Term(self.terms_mut().mk_app(
            Symbol::named("fp.roundToIntegral"),
            vec![rm.0, a.0],
            sort,
        )))
    }

    // --- FP/BV bridge operations for crypto and DSP analysis (#8332) ---

    /// Convert an FP expression to its IEEE 754 bitvector bit-pattern.
    ///
    /// This is a convenience wrapper around [`try_fp_to_ieee_bv`](Self::try_fp_to_ieee_bv).
    /// For Float32 (eb=8, sb=24), returns BV32 (sign\[1\] + exp\[8\] + mantissa\[23\]).
    /// For Float64 (eb=11, sb=53), returns BV64.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `fp_expr` is not a FloatingPoint sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_to_bv(&mut self, fp_expr: Term) -> Result<Term, SolverError> {
        self.try_fp_to_ieee_bv(fp_expr)
    }

    /// Convert a BV expression to FP by reinterpreting bits as IEEE 754.
    ///
    /// This is the 1-argument `to_fp` variant that performs raw bit-pattern
    /// reinterpretation -- no rounding mode is needed because the bit pattern
    /// directly encodes the FP value.
    ///
    /// The BV width must equal `eb + sb` (total FP bit width). For example:
    /// - BV32 -> Float32 (eb=8, sb=24)
    /// - BV64 -> Float64 (eb=11, sb=53)
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `bv_expr` is not a BitVec sort.
    /// Returns [`SolverError::InvalidArgument`] if the BV width does not match `eb + sb`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bv_to_fp_reinterpret(
        &mut self,
        bv_expr: Term,
        eb: u32,
        sb: u32,
    ) -> Result<Term, SolverError> {
        let bv_width = self.expect_bitvec_width("bv_to_fp_reinterpret", bv_expr)?;
        let expected_width = self.checked_fp_total_width("bv_to_fp_reinterpret", eb, sb)?;
        if bv_width != expected_width {
            return Err(SolverError::InvalidArgument {
                operation: "bv_to_fp_reinterpret",
                message: format!(
                    "BV width {bv_width} does not match FP total width {expected_width} \
                     (eb={eb} + sb={sb})"
                ),
            });
        }
        let sort = Sort::FloatingPoint(eb, sb);
        // 1-arg to_fp: reinterpret BV bits as IEEE 754 FP
        Ok(Term(self.terms_mut().mk_app(
            Symbol::indexed("to_fp", vec![eb, sb]),
            vec![bv_expr.0],
            sort,
        )))
    }

    /// Classify an FP expression, returning a BV3 value.
    ///
    /// Classification encoding (matching [`fp_class`] constants):
    /// - 0 = normal
    /// - 1 = subnormal
    /// - 2 = zero
    /// - 3 = infinity
    /// - 4 = NaN
    ///
    /// Implemented as an ITE chain over the standard FP classification
    /// predicates (fp.isNaN, fp.isInfinite, fp.isZero, fp.isSubnormal).
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `fp_expr` is not a FloatingPoint sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_fp_classify(&mut self, fp_expr: Term) -> Result<Term, SolverError> {
        self.expect_fp("fp_classify", fp_expr)?;

        // Build classification predicates
        let is_nan = self.try_fp_is_nan(fp_expr)?;
        let is_inf = self.try_fp_is_infinite(fp_expr)?;
        let is_zero = self.try_fp_is_zero(fp_expr)?;
        let is_subnormal = self.try_fp_is_subnormal(fp_expr)?;

        // Build BV3 constants for each class
        let normal_bv = self.try_bv_const(fp_class::NORMAL, 3)?;
        let subnormal_bv = self.try_bv_const(fp_class::SUBNORMAL, 3)?;
        let zero_bv = self.try_bv_const(fp_class::ZERO, 3)?;
        let inf_bv = self.try_bv_const(fp_class::INFINITY, 3)?;
        let nan_bv = self.try_bv_const(fp_class::NAN, 3)?;

        // Build ITE chain: NaN check first (highest priority), then inf, zero, subnormal
        // Default is normal (0)
        let result = self.try_ite(is_subnormal, subnormal_bv, normal_bv)?;
        let result = self.try_ite(is_zero, zero_bv, result)?;
        let result = self.try_ite(is_inf, inf_bv, result)?;
        let result = self.try_ite(is_nan, nan_bv, result)?;

        Ok(result)
    }
}
