// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact truncating remainder without the IEEE nearest-quotient adjustment.
//!
//! The significand reduction is the existing remainder circuit's exact
//! integer modular reduction, not a rounded FP division. Compare the standard
//! significand remainder algorithm in musl's fmod:
//! https://git.musl-libc.org/cgit/musl/tree/src/math/fmod.c
//! Rust's operator uses a truncating quotient; SMT fp.rem uses nearest/ties-even:
//! https://doc.rust-lang.org/std/ops/trait.Rem.html
//! https://smt-lib.org/theories-FloatingPoint.shtml
//! These are logical FP values, not Rust NaN payload/source-bit contracts.

use crate::construction::control::BuildControl;
use crate::{FpBuildStage, FpDecomposed, FpSolver};

impl FpSolver<'_> {
    pub(crate) fn make_truncating_rem_with_control<C: BuildControl>(
        &mut self,
        x: &FpDecomposed,
        y: &FpDecomposed,
        control: &mut C,
    ) -> Result<FpDecomposed, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let precision = x.precision;
        let special_cases = self.rem_special_cases(x, y);
        let core = self.rem_round_down_candidate(x, y, control)?;
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        // For |x| >= |y|, normalization gives a nonnegative exponent difference.
        // The existing core is sign(x) * ((a_sig * 2^diff) mod b_sig) at y's
        // quantum. It is representable exactly: R < b_sig has <= sb bits, and
        // both operands are multiples of the format's smallest subnormal.
        //
        // For |x| < |y|, the truncating quotient is zero, so retain x exactly
        // instead of using the core's lossy negative-exponent guard branch.
        // IEEE fields excluding sign are ordered unsigned by finite magnitude.
        let x_magnitude = Self::bv_concat(&x.significand, &x.exponent);
        let y_magnitude = Self::bv_concat(&y.significand, &y.exponent);
        let smaller = self.make_unsigned_lt(&x_magnitude, &y_magnitude);
        let base = self.make_ite_fp(smaller, x, &core.rndd, precision);
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        // Retain the existing NaN/infinity/zero precedence. The IEEE small-x
        // shortcut is valid here too; the broader |x| < |y| guard is above.
        let result = self.rem_apply_special_cases(x, &special_cases, &base, precision);
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        let result = self.rem_fix_zero_sign(x, &result, precision);
        control.checkpoint(self.construction_progress(FpBuildStage::Operation))?;
        Ok(result)
    }
}

#[cfg(test)]
mod tests;
