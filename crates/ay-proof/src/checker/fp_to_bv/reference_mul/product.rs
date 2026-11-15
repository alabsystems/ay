// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Full unsigned significand product, exact binary scale, and ONE direct
//! normal/subnormal target quantum. No producer unpack or rounding is reused.

use super::{
    graph::{Binary, Bits, RefId},
    Output, Reference, Result,
};

impl Reference<'_, '_> {
    pub(super) fn bias(&mut self) -> Result<RefId> {
        let low = self.ones(self.format.eb - 1)?;
        self.resize(low, self.format.exponent_width)
    }

    pub(super) fn significand(&mut self, input: Bits) -> Result<RefId> {
        let exp_zero = self.is_zero(input.exponent)?;
        let hidden = self.power(self.format.p - 1, self.format.product_width)?;
        let zero = self.small(0, self.format.product_width)?;
        let hidden = self.select(exp_zero, zero, hidden)?;
        let fraction = self.resize(input.fraction, self.format.product_width)?;
        self.binary(Binary::Or, hidden, fraction)
    }

    pub(super) fn unbiased(&mut self, exponent: RefId, bias: RefId) -> Result<RefId> {
        let zero = self.is_zero(exponent)?;
        let exponent = self.resize(exponent, self.format.exponent_width)?;
        let one = self.small(1, self.format.exponent_width)?;
        let effective = self.select(zero, one, exponent)?;
        self.binary(Binary::Sub, effective, bias)
    }

    pub(super) fn leading_index(&mut self, value: RefId) -> Result<RefId> {
        let mut index = self.small(0, self.format.exponent_width)?;
        for bit in 0..self.format.product_width {
            // Increasing positions replace the selected index only for a SET
            // bit. Zero is harmless here; signed zero is packed independently.
            self.charge(1, 0)?;
            let set = self.bit(value, bit)?;
            let position = self.small(u64::from(bit), self.format.exponent_width)?;
            index = self.select(set, position, index)?;
        }
        Ok(index)
    }

    pub(super) fn product(&mut self, x: Bits, y: Bits, rm: RefId) -> Result<Bits> {
        let bias = self.bias()?;
        let xm = self.significand(x)?;
        let ym = self.significand(y)?;
        // Both M < 2^p: zero-extending FIRST to 2p+1 means that the word
        // multiply retains the entire 2p-bit product, plus a rounding carry.
        let product = self.binary(Binary::Mul, xm, ym)?;
        let ex = self.unbiased(x.exponent, bias)?;
        let ey = self.unbiased(y.exponent, bias)?;
        let ex_ey = self.binary(Binary::Add, ex, ey)?;
        let twice_fraction =
            self.small(u64::from(self.format.p - 1) * 2, self.format.exponent_width)?;
        // Exact finite magnitude = product * 2^scale, not a rounded value.
        let scale = self.binary(Binary::Sub, ex_ey, twice_fraction)?;
        let index = self.leading_index(product)?;
        let real_exponent = self.binary(Binary::Add, scale, index)?;
        let one = self.small(1, self.format.exponent_width)?;
        let emin = self.binary(Binary::Sub, one, bias)?;
        let subnormal = self.slt(real_exponent, emin)?;
        let base = self.select(subnormal, emin, real_exponent)?;
        let fraction = self.small(u64::from(self.format.p - 1), self.format.exponent_width)?;
        let quantum = self.binary(Binary::Sub, base, fraction)?;
        let shift = self.binary(Binary::Sub, quantum, scale)?;
        let sign = self.binary(Binary::Xor, x.sign, y.sign)?;
        let rounded = self.round_product(product, shift, sign, rm)?;
        self.pack(rounded, base, bias, sign, rm)
    }

    pub(super) fn pack(
        &mut self,
        rounded: RefId,
        base: RefId,
        bias: RefId,
        sign: RefId,
        rm: RefId,
    ) -> Result<Bits> {
        // Q < 2^p and increment <= 1, so this is the ONLY possible carry.
        let carry = self.bit(rounded, self.format.p)?;
        let one_word = self.small(1, self.format.product_width)?;
        let half = self.binary(Binary::Lshr, rounded, one_word)?;
        let significand = self.select(carry, half, rounded)?;
        let one_exp = self.small(1, self.format.exponent_width)?;
        let raised = self.binary(Binary::Add, base, one_exp)?;
        let exponent = self.select(carry, raised, base)?;
        let normal_boundary = self.power(self.format.p - 1, self.format.product_width)?;
        let tiny = self.binary(Binary::Ult, significand, normal_boundary)?;
        let biased = self.binary(Binary::Add, exponent, bias)?;
        let encoded = self.resize(biased, self.format.eb)?;
        let zero_exp = self.small(0, self.format.eb)?;
        let encoded = self.select(tiny, zero_exp, encoded)?;
        let fraction = self.extract(significand, self.format.p - 2, 0)?;
        let overflow = self.slt(bias, exponent)?;
        let all_exp = self.ones(self.format.eb)?;
        let one = self.small(1, self.format.eb)?;
        let max_exp = self.binary(Binary::Sub, all_exp, one)?;
        let all_fraction = self.ones(self.format.p - 1)?;
        let zero_fraction = self.small(0, self.format.p - 1)?;
        let toward_inf = self.overflow_to_infinity(rm, sign)?;
        let over_exp = self.select(toward_inf, all_exp, max_exp)?;
        let over_fraction = self.select(toward_inf, zero_fraction, all_fraction)?;
        Ok(Bits {
            sign,
            exponent: self.select(overflow, over_exp, encoded)?,
            fraction: self.select(overflow, over_fraction, fraction)?,
        })
    }

    pub(super) fn classifications(&mut self, value: Bits) -> Result<(RefId, RefId, RefId)> {
        let all_exp = self.ones(self.format.eb)?;
        let exp_all = self.binary(Binary::Eq, value.exponent, all_exp)?;
        let fraction_zero = self.is_zero(value.fraction)?;
        let fraction_nonzero = self.not(fraction_zero)?;
        let nan = self.binary(Binary::And, exp_all, fraction_nonzero)?;
        let infinity = self.binary(Binary::And, exp_all, fraction_zero)?;
        let exp_zero = self.is_zero(value.exponent)?;
        let zero = self.binary(Binary::And, exp_zero, fraction_zero)?;
        Ok((nan, infinity, zero))
    }

    pub(super) fn specials(
        &mut self,
        x: Bits,
        y: Bits,
        finite: Bits,
        rm_domain: RefId,
    ) -> Result<Output> {
        let (xn, xi, xz) = self.classifications(x)?;
        let (yn, yi, yz) = self.classifications(y)?;
        let invalid_x = self.binary(Binary::And, xi, yz)?;
        let invalid_y = self.binary(Binary::And, yi, xz)?;
        let invalid = self.binary(Binary::Or, invalid_x, invalid_y)?;
        let input_nan = self.binary(Binary::Or, xn, yn)?;
        let nan = self.binary(Binary::Or, input_nan, invalid)?;
        let infinity = self.binary(Binary::Or, xi, yi)?;
        let zero = self.binary(Binary::Or, xz, yz)?;
        let zero_exp = self.small(0, self.format.eb)?;
        let zero_fraction = self.small(0, self.format.p - 1)?;
        let one_fraction = self.small(1, self.format.p - 1)?;
        let all_exp = self.ones(self.format.eb)?;
        let exp = self.select(zero, zero_exp, finite.exponent)?;
        let fraction = self.select(zero, zero_fraction, finite.fraction)?;
        let exp = self.select(infinity, all_exp, exp)?;
        let fraction = self.select(infinity, zero_fraction, fraction)?;
        // This canonical carrier is only a representative of SMT's ONE NaN.
        // A later whole-clause FP equality must compare NaN classes, not bits;
        // source Rust raw NaN needs its independently authenticated relation.
        let zero_sign = self.small(0, 1)?;
        Ok(Output {
            sign: self.select(nan, zero_sign, finite.sign)?,
            exponent: self.select(nan, all_exp, exp)?,
            fraction: self.select(nan, one_fraction, fraction)?,
            rm_domain,
        })
    }
}
