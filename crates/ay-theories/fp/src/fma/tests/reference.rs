// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Test-only frozen arithmetic. Its six phase bodies are authenticated against
//! the original unpartitioned body by the source auditor, not by this comment.

use super::super::controlled::{Aligned, Magnitude, Normalized, Product, Special};
use super::*;
use ay_core::CnfClause;

include!("oracle/controlled.rs");
include!("oracle/phases.rs");
include!("oracle/finish.rs");

impl FpSolver<'_> {
    pub(super) fn legacy_encode_fma_zero_factor(
        &mut self,
        zero_class: FpConstClass,
        other: &FpDecomposed,
        z: &FpDecomposed,
        rm: RmOperand,
        precision: FpPrecision,
    ) -> FpDecomposed {
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
        let add_result = self.make_add(&product_zero, z, rm);

        // When the symbolic other factor is NaN or ±inf, the result must be
        // NaN (because 0 * NaN = NaN and 0 * ±inf = NaN).
        let other_nan = self.is_nan(other);
        let other_inf = self.is_infinite(other);
        let other_non_finite = self.make_or(other_nan, other_inf);
        let nan_value = self.make_nan_value(precision);

        // Final: ite(other is non-finite, NaN, add_result).
        self.make_ite_fp(other_non_finite, &nan_value, &add_result, precision)
    }
}
