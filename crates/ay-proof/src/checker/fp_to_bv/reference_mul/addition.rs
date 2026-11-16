// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent exact finite sum/difference followed by ONE IEEE rounding.
//! Fixed three-bit alignment and a SEPARATE fractional-tail flag suffice;
//! opposite-sign tail must borrow one integer unit, not be OR-jammed.
//! See BTRW15 <https://smt-lib.org/papers/BTRW15.pdf>.

use super::{
    graph::{Binary, Bits, RefId},
    Arithmetic, Output, Reference, Result,
};

mod alignment;

struct Aligned {
    integer: RefId,
    fractional_tail: RefId,
    sign: RefId,
    scale: RefId,
}

impl Reference<'_, '_> {
    pub(super) fn addition(
        &mut self,
        x: Bits,
        mut y: Bits,
        rm: RefId,
        rm_domain: RefId,
    ) -> Result<Output> {
        // Subtraction changes only the EFFECTIVE second sign. Input NaN is
        // still a logical class; this is not a raw Rust NaN payload transform.
        if self.operation == Arithmetic::Sub {
            y.sign = self.not(y.sign)?;
        }
        let bias = self.bias()?;
        let aligned = self.aligned_sum(x, y, bias, rm)?;
        let index = self.leading_index(aligned.integer)?;
        let actual_exponent = self.binary(Binary::Add, aligned.scale, index)?;
        let one = self.small(1, self.format.exponent_width)?;
        let emin = self.binary(Binary::Sub, one, bias)?;
        let is_tiny = self.slt(actual_exponent, emin)?;
        let base = self.select(is_tiny, emin, actual_exponent)?;
        let fraction = self.small(u64::from(self.format.p - 1), self.format.exponent_width)?;
        let quantum = self.binary(Binary::Sub, base, fraction)?;
        let shift = self.binary(Binary::Sub, quantum, aligned.scale)?;
        // A nonzero fractional tail implies exponent gap>3, hence a NORMAL
        // result with shift>=2. It never enters an exact left-shift branch.
        let rounded = self.round_with_tail(
            aligned.integer,
            shift,
            aligned.sign,
            rm,
            Some(aligned.fractional_tail),
        )?;
        let finite = self.pack(rounded, base, bias, aligned.sign, rm)?;
        self.sum_specials(x, y, finite, rm_domain)
    }

    fn sum_specials(
        &mut self,
        x: Bits,
        y: Bits,
        finite: Bits,
        _rm_domain: RefId,
    ) -> Result<Output> {
        let (xn, xi, _) = self.classifications(x)?;
        let (yn, yi, _) = self.classifications(y)?;
        let both_infinite = self.binary(Binary::And, xi, yi)?;
        let opposite = self.binary(Binary::Xor, x.sign, y.sign)?;
        let invalid = self.binary(Binary::And, both_infinite, opposite)?;
        let input_nan = self.binary(Binary::Or, xn, yn)?;
        let nan = self.binary(Binary::Or, input_nan, invalid)?;
        let infinity = self.binary(Binary::Or, xi, yi)?;
        let infinite_sign = self.select(xi, x.sign, y.sign)?;
        let sign = self.select(infinity, infinite_sign, finite.sign)?;
        let all_exp = self.ones(self.format.eb)?;
        let zero_fraction = self.small(0, self.format.p - 1)?;
        let exponent = self.select(infinity, all_exp, finite.exponent)?;
        let fraction = self.select(infinity, zero_fraction, finite.fraction)?;
        let zero_sign = self.small(0, 1)?;
        let one_fraction = self.small(1, self.format.p - 1)?;
        Ok(Output {
            sign: self.select(nan, zero_sign, sign)?,
            exponent: self.select(nan, all_exp, exponent)?,
            fraction: self.select(nan, one_fraction, fraction)?,
            #[cfg(test)]
            rm_domain: _rm_domain,
        })
    }
}
