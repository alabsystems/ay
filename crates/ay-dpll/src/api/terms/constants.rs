// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::api::MAX_API_BITVECTOR_WIDTH;

fn validate_bitvector_width(operation: &'static str, width: u32) -> Result<(), SolverError> {
    if width == 0 || width > MAX_API_BITVECTOR_WIDTH {
        return Err(SolverError::InvalidArgument {
            operation,
            message: format!(
                "bitvector width {width} is outside the supported range 1..={MAX_API_BITVECTOR_WIDTH}"
            ),
        });
    }
    Ok(())
}

#[allow(clippy::panic, deprecated)]
impl Solver {
    /// Create a boolean constant
    pub fn bool_const(&mut self, value: bool) -> Term {
        let result = self.terms_mut().mk_bool(value);
        self.wrap_term(result)
    }

    /// Create an integer constant
    pub fn int_const(&mut self, value: i64) -> Term {
        let result = self.terms_mut().mk_int(BigInt::from(value));
        self.wrap_term(result)
    }

    /// Create an integer constant from an arbitrary-precision value.
    pub fn int_const_bigint(&mut self, value: &BigInt) -> Term {
        let result = self.terms_mut().mk_int(value.clone());
        self.wrap_term(result)
    }

    /// Create a real constant from a floating-point value.
    ///
    /// # Panics
    ///
    /// Panics if `value` is NaN or infinite. Use [`try_real_const`](Self::try_real_const)
    /// for a fallible version.
    pub fn real_const(&mut self, value: f64) -> Term {
        self.try_real_const(value).unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a real constant from a floating-point value.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `value` is NaN or infinite.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_real_const(&mut self, value: f64) -> Result<Term, SolverError> {
        if !value.is_finite() {
            return Err(SolverError::InvalidArgument {
                operation: "real_const",
                message: format!("value must be finite, got {value}"),
            });
        }
        let r = BigRational::from_float(value).unwrap_or_else(|| {
            BigRational::new(
                BigInt::from((value * 1e15) as i64),
                BigInt::from(1_000_000_000_000_000i64),
            )
        });
        let result = self.terms_mut().mk_rational(r);
        Ok(self.wrap_term(result))
    }

    /// Create a real constant from a rational (numerator/denominator).
    ///
    /// # Panics
    ///
    /// Panics if `denom` is zero. Use [`try_rational_const`](Self::try_rational_const)
    /// for a fallible version.
    pub fn rational_const(&mut self, numer: i64, denom: i64) -> Term {
        self.try_rational_const(numer, denom)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a real constant from a rational (numerator/denominator).
    ///
    /// Returns [`SolverError::InvalidArgument`] if `denom` is zero.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_rational_const(&mut self, numer: i64, denom: i64) -> Result<Term, SolverError> {
        if denom == 0 {
            return Err(SolverError::InvalidArgument {
                operation: "rational_const",
                message: "denominator cannot be zero".to_string(),
            });
        }
        let r = BigRational::new(BigInt::from(numer), BigInt::from(denom));
        let result = self.terms_mut().mk_rational(r);
        Ok(self.wrap_term(result))
    }

    /// Create a real constant from arbitrary-precision rational numerator/denominator.
    ///
    /// Use this for rationals that exceed i64 range.
    ///
    /// # Panics
    ///
    /// Panics if `denom` is zero. Use [`try_rational_const_bigint`](Self::try_rational_const_bigint)
    /// for a fallible version.
    pub fn rational_const_bigint(&mut self, numer: &BigInt, denom: &BigInt) -> Term {
        self.try_rational_const_bigint(numer, denom)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a real constant from arbitrary-precision rational numerator/denominator.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `denom` is zero.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_rational_const_bigint(
        &mut self,
        numer: &BigInt,
        denom: &BigInt,
    ) -> Result<Term, SolverError> {
        if denom.is_zero() {
            return Err(SolverError::InvalidArgument {
                operation: "rational_const_bigint",
                message: "denominator cannot be zero".to_string(),
            });
        }
        let r = BigRational::new(numer.clone(), denom.clone());
        let result = self.terms_mut().mk_rational(r);
        Ok(self.wrap_term(result))
    }

    /// Create a real constant from a BigRational value.
    ///
    /// Use this when you already have a BigRational.
    pub fn rational_const_ratio(&mut self, value: &BigRational) -> Term {
        let result = self.terms_mut().mk_rational(value.clone());
        self.wrap_term(result)
    }

    /// Create a bitvector constant.
    ///
    /// # Panics
    ///
    /// Panics if `width` is outside the supported dense-BV envelope. Use
    /// [`try_bv_const`](Self::try_bv_const) for a fallible version.
    pub fn bv_const(&mut self, value: i64, width: u32) -> Term {
        self.try_bv_const(value, width)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector constant.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `width` is outside the
    /// supported dense-BV envelope.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bv_const(&mut self, value: i64, width: u32) -> Result<Term, SolverError> {
        validate_bitvector_width("bv_const", width)?;
        let result = self.terms_mut().mk_bitvec(BigInt::from(value), width);
        Ok(self.wrap_term(result))
    }

    /// Create a bitvector constant from an unsigned 64-bit value.
    ///
    /// Use this when constructing BV constants from u64 values that may exceed
    /// i64::MAX (e.g., 0xFFFFFFFF_FFFFFFFF for all-ones masks).
    /// The value is interpreted as an unsigned integer modulo 2^width.
    ///
    /// # Panics
    ///
    /// Panics if `width` is outside the supported dense-BV envelope. Use
    /// [`try_bv_const_u64`](Self::try_bv_const_u64) for a fallible version.
    pub fn bv_const_u64(&mut self, value: u64, width: u32) -> Term {
        self.try_bv_const_u64(value, width)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector constant from an unsigned 64-bit value.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `width` is outside the
    /// supported dense-BV envelope.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bv_const_u64(&mut self, value: u64, width: u32) -> Result<Term, SolverError> {
        validate_bitvector_width("bv_const_u64", width)?;
        let result = self.terms_mut().mk_bitvec(BigInt::from(value), width);
        Ok(self.wrap_term(result))
    }

    /// Create a bitvector constant from an arbitrary-precision value.
    ///
    /// Use this for bitvectors wider than 63 bits or when the value exceeds i64 range.
    /// The value is interpreted modulo 2^width (standard two's complement semantics).
    ///
    /// # Panics
    ///
    /// Panics if `width` is outside the supported dense-BV envelope.
    ///
    /// # Example
    ///
    /// ```
    /// use ay_dpll::api::{Logic, Solver, Sort, SolveResult};
    /// use num_bigint::BigInt;
    ///
    /// let mut solver = Solver::new(Logic::QfBv);
    /// // Create a 128-bit constant with value 2^100
    /// let large_val = BigInt::from(1) << 100;
    /// let bv = solver.bv_const_bigint(&large_val, 128);
    /// let x = solver.declare_const("x", Sort::bitvec(128));
    /// let eq = solver.eq(x, bv);
    /// solver.assert_term(eq);
    /// assert_eq!(solver.check_sat(), SolveResult::Sat);
    /// ```
    pub fn bv_const_bigint(&mut self, value: &BigInt, width: u32) -> Term {
        self.try_bv_const_bigint(value, width)
            .unwrap_or_else(|e| panic!("{e}"))
    }

    /// Try to create a bitvector constant from an arbitrary-precision value.
    ///
    /// Returns [`SolverError::InvalidArgument`] if `width` is outside the
    /// supported dense-BV envelope.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_bv_const_bigint(&mut self, value: &BigInt, width: u32) -> Result<Term, SolverError> {
        validate_bitvector_width("bv_const_bigint", width)?;
        let result = self.terms_mut().mk_bitvec(value.clone(), width);
        Ok(self.wrap_term(result))
    }
}
