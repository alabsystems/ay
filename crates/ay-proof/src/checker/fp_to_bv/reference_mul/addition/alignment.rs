// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! For A>=B, exact magnitude=(I+F)*2^scale, 0<=F<1; tail iff F>0.
//! An inexact alignment implies gap>3 and no near cancellation. The result
//! exponent can drop by at most one, so rounding quantum shift>=2 and the
//! unknown fraction is used only as a sticky bit below an INTEGER guard.
//! Exact alignment retains every cancellation bit, including subnormals.

use super::{Aligned, Binary, Bits, RefId, Reference, Result};

impl Reference<'_, '_> {
    fn ordered(
        &mut self,
        x: Bits,
        y: Bits,
        bias: RefId,
    ) -> Result<(RefId, RefId, RefId, RefId, RefId)> {
        let xm = self.significand(x)?;
        let ym = self.significand(y)?;
        let ex = self.unbiased(x.exponent, bias)?;
        let ey = self.unbiased(y.exponent, bias)?;
        let exp_less = self.slt(ex, ey)?;
        let exp_equal = self.binary(Binary::Eq, ex, ey)?;
        let mantissa_less = self.binary(Binary::Ult, xm, ym)?;
        let equal_and_less = self.binary(Binary::And, exp_equal, mantissa_less)?;
        let swap = self.binary(Binary::Or, exp_less, equal_and_less)?;
        // Subnormals and the smallest normal share Emin. Otherwise the
        // larger exponent has a normal hidden bit and dominates magnitude.
        let high = self.select(swap, ym, xm)?;
        let low = self.select(swap, xm, ym)?;
        let large_exponent = self.select(swap, ey, ex)?;
        let small_exponent = self.select(swap, ex, ey)?;
        let sign = self.select(swap, y.sign, x.sign)?;
        Ok((high, low, large_exponent, small_exponent, sign))
    }

    pub(super) fn aligned_sum(
        &mut self,
        x: Bits,
        y: Bits,
        bias: RefId,
        rm: RefId,
    ) -> Result<Aligned> {
        let (high, low, large_exponent, small_exponent, sign) = self.ordered(x, y, bias)?;
        let width = self.format.product_width; // p+4 for Add/Sub; never 2^eb.
        let three = self.small(3, width)?;
        let large = self.binary(Binary::Shl, high, three)?;
        let low_scaled = self.binary(Binary::Shl, low, three)?;
        let gap = self.binary(Binary::Sub, large_exponent, small_exponent)?;
        // Clamp the full exponent-sized amount BEFORE narrowing; a huge gap
        // produces floor0 with nonzero tail, not a masked small shift.
        let floor = self.shift(Binary::Lshr, low_scaled, gap)?;
        let restored = self.shift(Binary::Shl, floor, gap)?;
        let remainder = self.binary(Binary::Sub, low_scaled, restored)?;
        let tail = self.nonzero(remainder)?;
        let same = self.binary(Binary::Eq, x.sign, y.sign)?;
        let sum = self.binary(Binary::Add, large, floor)?;
        let difference = self.binary(Binary::Sub, large, floor)?;
        let borrow = self.resize(tail, width)?;
        // a-(b+f)=(a-b-1)+(1-f) for0<f<1. Without this borrow,
        // positive directed-downward 1-tiny would round to WRONG1.
        let difference = self.binary(Binary::Sub, difference, borrow)?;
        let integer = self.select(same, sum, difference)?;
        let fraction_and_guard =
            self.small(u64::from(self.format.p) + 2, self.format.exponent_width)?;
        let scale = self.binary(Binary::Sub, large_exponent, fraction_and_guard)?;
        let integer_zero = self.is_zero(integer)?;
        let exact_tail = self.not(tail)?;
        let exact_zero = self.binary(Binary::And, integer_zero, exact_tail)?;
        let rtn = self.small(3, 3)?;
        let toward_negative = self.binary(Binary::Eq, rm, rtn)?;
        // Same effective-sign zeros retain that sign. Opposite zeros and
        // exact finite cancellation are -0 ONLY under roundTowardNegative.
        let zero_sign = self.select(same, sign, toward_negative)?;
        let sign = self.select(exact_zero, zero_sign, sign)?;
        Ok(Aligned {
            integer,
            fractional_tail: tail,
            sign,
            scale,
        })
    }
}
