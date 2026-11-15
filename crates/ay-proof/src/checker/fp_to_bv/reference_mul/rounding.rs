// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Direct quantum rounding of the exact product. The whole discarded prefix
//! is represented by guard + tail; enormous shifts saturate BEFORE narrowing.

use super::{
    graph::{Binary, RefId},
    Reference, Result,
};

impl Reference<'_, '_> {
    fn mode(&mut self, rm: RefId, number: u64) -> Result<RefId> {
        let constant = self.small(number, 3)?;
        self.binary(Binary::Eq, rm, constant)
    }

    pub(super) fn round_product(
        &mut self,
        product: RefId,
        shift: RefId,
        sign: RefId,
        rm: RefId,
    ) -> Result<RefId> {
        self.round_with_tail(product, shift, sign, rm, None)
    }

    pub(super) fn round_with_tail(
        &mut self,
        product: RefId,
        shift: RefId,
        sign: RefId,
        rm: RefId,
        fractional_tail: Option<RefId>,
    ) -> Result<RefId> {
        let zero_exp = self.small(0, self.format.exponent_width)?;
        let positive_shift = self.slt(zero_exp, shift)?;
        let negative_shift = self.binary(Binary::Sub, zero_exp, shift)?;
        let shifted_left = self.shift(Binary::Shl, product, negative_shift)?;
        let shifted_right = self.shift(Binary::Lshr, product, shift)?;
        let retained = self.select(positive_shift, shifted_right, shifted_left)?;
        let one_exp = self.small(1, self.format.exponent_width)?;
        let preceding = self.binary(Binary::Sub, shift, one_exp)?;
        let half_floor = self.shift(Binary::Lshr, product, preceding)?;
        let guard = self.bit(half_floor, 0)?;
        let restored_half = self.shift(Binary::Shl, half_floor, preceding)?;
        let below_guard = self.binary(Binary::Sub, product, restored_half)?;
        let tail = self.nonzero(below_guard)?;
        let tail = if let Some(fractional_tail) = fractional_tail {
            self.binary(Binary::Or, tail, fractional_tail)?
        } else {
            tail
        };
        let odd = self.bit(retained, 0)?;
        let odd_or_tail = self.binary(Binary::Or, odd, tail)?;
        let nearest_even = self.binary(Binary::And, guard, odd_or_tail)?;
        let any_discarded = self.binary(Binary::Or, guard, tail)?;
        let not_sign = self.not(sign)?;
        let upward = self.binary(Binary::And, not_sign, any_discarded)?;
        let downward = self.binary(Binary::And, sign, any_discarded)?;
        let rne = self.mode(rm, 0)?;
        let rna = self.mode(rm, 1)?;
        let rtp = self.mode(rm, 2)?;
        let rtn = self.mode(rm, 3)?;
        let rne_increment = self.binary(Binary::And, rne, nearest_even)?;
        let rna_increment = self.binary(Binary::And, rna, guard)?;
        let rtp_increment = self.binary(Binary::And, rtp, upward)?;
        let rtn_increment = self.binary(Binary::And, rtn, downward)?;
        let nearest = self.binary(Binary::Or, rne_increment, rna_increment)?;
        let directed = self.binary(Binary::Or, rtp_increment, rtn_increment)?;
        let increment = self.binary(Binary::Or, nearest, directed)?;
        // No remainder exists for d <= 0; computations in inactive branches
        // cannot leak a directed increment into an exactly shifted integer.
        let increment = self.binary(Binary::And, positive_shift, increment)?;
        let increment = self.resize(increment, self.format.product_width)?;
        self.binary(Binary::Add, retained, increment)
    }

    pub(super) fn overflow_to_infinity(&mut self, rm: RefId, sign: RefId) -> Result<RefId> {
        let rne = self.mode(rm, 0)?;
        let rna = self.mode(rm, 1)?;
        let nearest = self.binary(Binary::Or, rne, rna)?;
        let rtp = self.mode(rm, 2)?;
        let rtn = self.mode(rm, 3)?;
        let not_sign = self.not(sign)?;
        let positive = self.binary(Binary::And, rtp, not_sign)?;
        let negative = self.binary(Binary::And, rtn, sign)?;
        let directed = self.binary(Binary::Or, positive, negative)?;
        self.binary(Binary::Or, nearest, directed)
    }
}
