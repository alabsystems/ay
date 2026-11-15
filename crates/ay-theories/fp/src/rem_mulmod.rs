// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private full-product/narrow-restoring kernels for IEEE remainder only.
//!
//! Schoolbook accumulation follows [LLVM APInt::tcFullMultiply]'s row shape;
//! restoring shift/subtract follows [compiler-rt's __udivmoddi4]. The local
//! invariants below justify the narrower widths. Existing generic BV
//! multiplication/division remain unchanged. Literal vectors are LSB first
//! and share the caller's CNF.
//!
//! [LLVM APInt::tcFullMultiply]: https://llvm.org/doxygen/APInt_8cpp_source.html
//! [compiler-rt's __udivmoddi4]: https://github.com/llvm/llvm-project/blob/main/compiler-rt/lib/builtins/udivmoddi4.c

use ay_core::CnfLit;

use crate::construction::control::BuildControl;
use crate::gates::neg_lit;
use crate::{FpBuildStage, FpSolver};

#[cfg(test)]
mod tests;

impl FpSolver<'_> {
    /// A literal-prefix comparison can establish the restoring row's invariant
    /// before allocating an unused subtraction. Equal symbolic literals are
    /// equal bits; any other unknown pair makes this comparison abstain.
    fn rem_known_unsigned_less(&self, a: &[CnfLit], b: &[CnfLit], zero: CnfLit) -> Option<bool> {
        for index in (0..a.len().max(b.len())).rev() {
            let left = a.get(index).copied().unwrap_or(zero);
            let right = b.get(index).copied().unwrap_or(zero);
            if left == right {
                continue;
            }
            match (
                self.known_literal_value(left),
                self.known_literal_value(right),
            ) {
                (Some(left), Some(right)) if left != right => return Some(!left && right),
                (Some(_), Some(_)) => {}
                _ => return None,
            }
        }
        Some(false)
    }

    /// Prefer one exact shift/restoring reduction when it has no more divider
    /// rows than repeated modular squaring. The positive signed exponent fits
    /// in `exponent_bits - 1` bits, so this width loses no numerator bit.
    /// Overflow or a more expensive direct divider retains modular squaring.
    pub(crate) fn rem_direct_shift_width(width: usize, exponent_bits: usize) -> Option<usize> {
        let positive_bits = u32::try_from(exponent_bits.checked_sub(1)?).ok()?;
        let max_shift = 1usize.checked_shl(positive_bits)?.checked_sub(1)?;
        let direct_rows = width.checked_add(max_shift)?;
        let modular_rows = width
            .checked_mul(2)?
            .checked_mul(exponent_bits.checked_add(1)?)?;
        (direct_rows <= modular_rows).then_some(direct_rows)
    }

    /// Exact `(a << exponent) mod modulus` for the nonnegative signed branch.
    /// The selected width covers every possible nonnegative exponent, not an
    /// estimate from a candidate model. Negative exponents use the caller's
    /// existing separate branch. Both kernels share its original controller.
    pub(crate) fn rem_direct_scale_with_control<C: BuildControl>(
        &mut self,
        a: &[CnfLit],
        exponent: &[CnfLit],
        modulus: &[CnfLit],
        width: usize,
        control: &mut C,
    ) -> Result<Vec<CnfLit>, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::RemainderExponent))?;
        debug_assert_eq!(
            Some(width),
            Self::rem_direct_shift_width(a.len(), exponent.len())
        );
        let mut extended = a.to_vec();
        extended.resize(width, self.const_false());
        control.checkpoint(self.construction_progress(FpBuildStage::RemainderExponent))?;
        let numerator = self.bv_shl_with_control(&extended, exponent, control)?;
        drop(extended);
        control.checkpoint(self.construction_progress(FpBuildStage::RemainderExponent))?;
        let result = self.rem_narrow_remainder_with_control(&numerator, modulus, control)?;
        drop(numerator);
        control.checkpoint(self.construction_progress(FpBuildStage::RemainderExponent))?;
        Ok(result)
    }

    /// (a * 2^exponent) mod 2^power, without constructing exponentiation.
    /// Only the low `power` bits can contribute; a larger shift is zero.
    pub(crate) fn rem_power_scale_with_control<C: BuildControl>(
        &mut self,
        a: &[CnfLit],
        exponent: &[CnfLit],
        power: usize,
        control: &mut C,
    ) -> Result<Vec<CnfLit>, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::RemainderExponent))?;
        debug_assert!(power <= a.len());
        let mut result = self.bv_shl_with_control(&a[..power], exponent, control)?;
        result.resize(a.len(), self.const_false());
        control.checkpoint(self.construction_progress(FpBuildStage::RemainderExponent))?;
        Ok(result)
    }

    /// Recognize a literal modulus only; candidate assignments convey no authority.
    pub(crate) fn rem_literal_power_with_control<C: BuildControl>(
        &mut self,
        modulus: &[CnfLit],
        control: &mut C,
    ) -> Result<Option<usize>, C::Error> {
        let zero = self.const_false();
        let one = self.const_true();
        let mut power = None;
        for (index, &bit) in modulus.iter().enumerate() {
            control.checkpoint(self.construction_progress(FpBuildStage::DivideRow))?;
            if bit == zero || bit == neg_lit(one) {
                continue;
            }
            if (bit == one || bit == neg_lit(zero)) && power.is_none() {
                power = Some(index);
            } else {
                return Ok(None);
            }
        }
        control.checkpoint(self.construction_progress(FpBuildStage::DivideRow))?;
        Ok(power)
    }

    /// Product modulo 2^k: carries at weight 2^k cannot affect any lower bit.
    pub(crate) fn rem_low_product_with_control<C: BuildControl>(
        &mut self,
        a: &[CnfLit],
        b: &[CnfLit],
        power: usize,
        control: &mut C,
    ) -> Result<Vec<CnfLit>, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::MultiplyRow))?;
        debug_assert_eq!(a.len(), b.len());
        debug_assert!(power <= a.len());
        let zero = self.const_false();
        let mut product = vec![zero; a.len()];
        for (row, &bit) in b.iter().take(power).enumerate() {
            control.checkpoint(self.construction_progress(FpBuildStage::MultiplyRow))?;
            let mut carry = zero;
            for (column, &a_bit) in a.iter().take(power - row).enumerate() {
                let position = row + column;
                let partial = self.make_and(a_bit, bit);
                let (sum, next) = self.full_adder(product[position], partial, carry);
                product[position] = sum;
                carry = next;
            }
            // Every omitted addend and this final carry has weight >= 2^k.
        }
        control.checkpoint(self.construction_progress(FpBuildStage::MultiplyRow))?;
        Ok(product)
    }

    /// Full unsigned product of equal-width inputs, with no discarded carry.
    pub(crate) fn rem_full_product_with_control<C: BuildControl>(
        &mut self,
        a: &[CnfLit],
        b: &[CnfLit],
        control: &mut C,
    ) -> Result<Vec<CnfLit>, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::MultiplyRow))?;
        debug_assert_eq!(a.len(), b.len());
        let width = a.len();
        if width == 0 {
            control.checkpoint(self.construction_progress(FpBuildStage::MultiplyRow))?;
            return Ok(Vec::new());
        }
        // A valid i32 slice's byte size fits isize, so twice its length fits
        // usize. Allocation remains subject to the original construction owner.
        let zero = self.const_false();
        let mut product = vec![zero; 2 * width];
        for (row, &b_bit) in b.iter().enumerate() {
            control.checkpoint(self.construction_progress(FpBuildStage::MultiplyRow))?;
            let mut carry = zero;
            for (column, &a_bit) in a.iter().enumerate() {
                let position = row + column;
                let partial = self.make_and(a_bit, b_bit);
                let (sum, next) = self.full_adder(product[position], partial, carry);
                product[position] = sum;
                carry = next;
            }
            // Before row i, acc = a*(b mod 2^i) < 2^(width+i).
            // Hence this high slot is zero, not an omitted addend. Lower i
            // bits stay untouched; the final carry is the next high bit.
            product[row + width] = carry;
        }
        control.checkpoint(self.construction_progress(FpBuildStage::MultiplyRow))?;
        Ok(product)
    }

    /// Low divisor-width remainder of an unsigned numerator of any width.
    ///
    /// For m>0 the invariant is 0<=R<m, so the shifted R fits width+1 bits.
    /// For m=0, subtracting zero is the identity at every row; returning low
    /// width bits preserves the old padded divider's SMT zero-divisor result.
    pub(crate) fn rem_narrow_remainder_with_control<C: BuildControl>(
        &mut self,
        numerator: &[CnfLit],
        modulus: &[CnfLit],
        control: &mut C,
    ) -> Result<Vec<CnfLit>, C::Error> {
        control.checkpoint(self.construction_progress(FpBuildStage::DivideRow))?;
        let width = modulus.len();
        if width == 0 {
            control.checkpoint(self.construction_progress(FpBuildStage::DivideRow))?;
            return Ok(Vec::new());
        }
        let zero = self.const_false();
        let one = self.const_true();
        // Unsigned N mod 2^k is exactly N's low k bits. Recognize only
        // canonical constant literals (including their complements), never
        // a candidate SAT assignment. This is particularly important for
        // IEEE remainder's modulus 16*b_sig when the divisor is a power of
        // two: no restoring divider is needed for that modular reduction.
        if let Some(power) = self.rem_literal_power_with_control(modulus, control)? {
            let mut remainder = vec![zero; width];
            for (output, &input) in remainder[..power].iter_mut().zip(numerator) {
                *output = input;
            }
            control.checkpoint(self.construction_progress(FpBuildStage::DivideRow))?;
            return Ok(remainder);
        }
        let mut remainder = vec![zero; width + 1];
        for &bit in numerator.iter().rev() {
            control.checkpoint(self.construction_progress(FpBuildStage::DivideRow))?;
            let mut shifted = Vec::new();
            // Match existing native arithmetic's fallible capacity hint; no
            // new allowance is created if the allocator cannot honor it.
            let _ = shifted.try_reserve_exact(width + 1);
            shifted.push(bit);
            shifted.extend_from_slice(&remainder[..width]);
            if self.rem_known_unsigned_less(&shifted, modulus, zero) == Some(true) {
                // R' < m already: subtract-and-select would discard its whole
                // difference circuit. This particularly removes the leading
                // rows before a normalized divisor's known one can be reached.
                remainder = shifted;
                continue;
            }
            let mut difference = Vec::new();
            let _ = difference.try_reserve_exact(width + 1);
            let mut carry = one;
            for (&value, &divisor) in shifted.iter().zip(modulus) {
                let (sum, next) = self.full_adder(value, neg_lit(divisor), carry);
                difference.push(sum);
                carry = next;
            }
            // The zero-extended divisor's top bit is 0, so its complement
            // is 1. The final carry is exactly unsigned shifted >= modulus.
            let (top, no_borrow) = self.full_adder(shifted[width], one, carry);
            difference.push(top);
            remainder = self.make_ite_bits(no_borrow, &difference, &shifted);
        }
        remainder.truncate(width);
        control.checkpoint(self.construction_progress(FpBuildStage::DivideRow))?;
        Ok(remainder)
    }
}
