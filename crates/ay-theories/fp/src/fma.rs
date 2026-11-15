// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fused multiply-add encoding.

use ay_core::term::{Constant, TermData, TermId};
use ay_core::CnfLit;

mod controlled;
mod finish;
mod phases;
#[cfg(test)]
mod tests;

use super::construction::control::{uninterrupted, BuildControl};
use super::construction::FpBuildStage;
use super::{FpDecomposed, FpPrecision, FpSolver, RmOperand, RoundingMode};

/// Static classification of an FP operand. Used by the fma-zero rewriter to
/// short-circuit the expensive FMA bit-blast when a multiplicand is known
/// statically to be a particular special value.
///
/// See [`FpSolver::classify_fp_zero_const`] for the recognition predicate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FpConstClass {
    /// `+0.0` (positive zero).
    PosZero,
    /// `-0.0` (negative zero).
    NegZero,
}

impl FpSolver<'_> {
    /// Classify a syntactic FP term as a concrete zero constant, if recognizable.
    ///
    /// Recognizes:
    /// - `(_ +zero eb sb)` → [`FpConstClass::PosZero`]
    /// - `(_ -zero eb sb)` → [`FpConstClass::NegZero`]
    /// - `(fp (_ bv0 1) (_ bv0 eb) (_ bv0 sb))` → [`FpConstClass::PosZero`]
    /// - `(fp (_ bv1 1) (_ bv0 eb) (_ bv0 sb))` → [`FpConstClass::NegZero`]
    ///
    /// Returns `None` for everything else (including symbolic terms and
    /// non-zero constants such as `+oo`, `NaN`, `0.5`).
    ///
    /// Used by [`FpSolver::try_make_fma_zero_factor`] to detect the
    /// Z3 issue #8185 rewrite pattern at decompose time, avoiding the
    /// expensive full FMA bit-blast circuit.
    pub(crate) fn classify_fp_zero_const(&self, term: TermId) -> Option<FpConstClass> {
        let data = self.terms.get(term);
        let TermData::App(sym, args) = data else {
            return None;
        };
        match sym.name() {
            // Indexed nullary constants from `(_ +zero eb sb)` / `(_ -zero eb sb)`.
            "+zero" | "fp.zero" if args.is_empty() => Some(FpConstClass::PosZero),
            "-zero" if args.is_empty() => Some(FpConstClass::NegZero),
            // `(fp sign exp sig)` triple with concrete zero exponent and significand.
            "fp" if args.len() == 3 => {
                let sign = self.extract_bv_bit(args[0])?;
                if !self.bv_is_zero(args[1]) || !self.bv_is_zero(args[2]) {
                    return None;
                }
                if sign {
                    Some(FpConstClass::NegZero)
                } else {
                    Some(FpConstClass::PosZero)
                }
            }
            _ => None,
        }
    }

    /// Extract a single-bit BV constant as a bool; returns `None` if not a
    /// 1-bit BV constant.
    fn extract_bv_bit(&self, term: TermId) -> Option<bool> {
        match self.terms.get(term) {
            TermData::Const(Constant::BitVec { value, width }) if *width == 1 => {
                Some(value.sign() == num_bigint::Sign::Plus && value.bit(0))
            }
            _ => None,
        }
    }

    /// Check if a BV term is a concrete all-zero constant.
    fn bv_is_zero(&self, term: TermId) -> bool {
        matches!(
            self.terms.get(term),
            TermData::Const(Constant::BitVec { value, .. }) if value.sign() == num_bigint::Sign::NoSign
        )
    }

    /// Detect FP zero-multiplicand fma pattern and emit a reduced encoding.
    ///
    /// Port of Z3 PR #9038 (fix for Z3 issue #8185): when one of the two
    /// multiplicands of `fma(rm, a, b, c)` is a concrete FP zero, the full
    /// FMA bit-blast circuit is unnecessary and can be replaced by a
    /// simpler `ite(isFinite(other), add(product_zero, c), NaN)` form.
    ///
    /// IEEE 754-2008 § 7.2 / § 6.1 semantics:
    /// - `0 * NaN = NaN`, `0 * ±inf = NaN`.
    /// - `±0 * finite = ±0` with sign = sign(zero) XOR sign(finite).
    /// - `fma(rm, ±0, y, c) = fp.add(rm, product_zero, c)` where
    ///   `product_zero` is `±0` chosen by the sign rule above.
    ///
    /// Returns `Some(result)` if the rewrite applies; otherwise `None` so
    /// the caller falls back to the full [`FpSolver::make_fma`] bit-blast.
    pub(crate) fn try_make_fma_zero_factor(
        &mut self,
        x_term: TermId,
        y_term: TermId,
        z: &FpDecomposed,
        rm: RmOperand,
    ) -> Option<FpDecomposed> {
        uninterrupted(|control| {
            self.try_make_fma_zero_factor_with_control(x_term, y_term, z, rm, control)
        })
    }

    pub(crate) fn try_make_fma_zero_factor_with_control<C: BuildControl>(
        &mut self,
        x_term: TermId,
        y_term: TermId,
        z: &FpDecomposed,
        rm: RmOperand,
        control: &mut C,
    ) -> Result<Option<FpDecomposed>, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Term))?;
        // Identify which of (x, y) is the concrete zero multiplicand.
        let (zero_class, other_term) = if let Some(c) = self.classify_fp_zero_const(x_term) {
            (c, y_term)
        } else {
            let Some(c) = self.classify_fp_zero_const(y_term) else {
                return Ok(None);
            };
            (c, x_term)
        };

        let precision = z.precision;
        let other = self.get_fp_with_control(other_term, control)?;
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = self
            .encode_fma_zero_factor_with_control(zero_class, &other, z, rm, precision, control)?;
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        Ok(Some(result))
    }

    /// Encode the reduced fma-with-zero-factor circuit.
    ///
    /// Produces `ite(isNaN(other) | isInf(other), NaN, add(product_zero, z))`
    /// where `product_zero`'s sign follows IEEE 754 sign-of-product rules:
    /// `sign(±0 * other) = sign(zero) XOR sign(other)`.
    ///
    /// This avoids the multi-thousand-clause FMA bit-blast circuit when
    /// one multiplicand is known statically to be zero.
    fn encode_fma_zero_factor_with_control<C: BuildControl>(
        &mut self,
        zero_class: FpConstClass,
        other: &FpDecomposed,
        z: &FpDecomposed,
        rm: RmOperand,
        precision: FpPrecision,
        control: &mut C,
    ) -> Result<FpDecomposed, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = {
            // product_zero = ±0 with sign = sign(zero) XOR sign(other).
            // - zero = +0: product_sign = sign(other) (0 XOR s = s)
            // - zero = -0: product_sign = NOT sign(other) (1 XOR s = !s)
            let pos_zero = self.make_zero(precision, false);
            let neg_zero = self.make_zero(precision, true);
            let product_sign = match zero_class {
                FpConstClass::PosZero => other.sign,
                FpConstClass::NegZero => -other.sign,
            };
            let product_zero = self.make_ite_fp(product_sign, &neg_zero, &pos_zero, precision);

            // Compute the IEEE 754 sum product_zero + z under the rounding mode.
            // make_add handles: +0 + z = z for finite nonzero z,
            //                    -0 + +0 = +0 (except RTN which gives -0),
            //                    ±0 + NaN = NaN,
            //                    ±0 + ±inf = ±inf.
            control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
            let add_result = self.make_add(&product_zero, z, rm);
            control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;

            // When the symbolic other factor is NaN or ±inf, the result must be
            // NaN (because 0 * NaN = NaN and 0 * ±inf = NaN).
            let other_nan = self.is_nan(other);
            let other_inf = self.is_infinite(other);
            let other_non_finite = self.make_or(other_nan, other_inf);
            let nan_value = self.make_nan_value(precision);

            // Final: ite(other is non-finite, NaN, add_result).
            self.make_ite_fp(other_non_finite, &nan_value, &add_result, precision)
        };
        // Original owner is observed after all helper temporaries were freed.
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        Ok(result)
    }

    /// Fused multiply-add: `(x * y) + z` with a single rounding.
    ///
    /// The legacy entry uses the same private controlled algorithm without
    /// installing a new cancellation owner or changing arithmetic semantics.
    pub fn make_fma(
        &mut self,
        x: &FpDecomposed,
        y: &FpDecomposed,
        z: &FpDecomposed,
        rm: impl Into<RmOperand>,
    ) -> FpDecomposed {
        let rm = rm.into();
        uninterrupted(|control| self.make_fma_with_control(x, y, z, rm, control))
    }
}
