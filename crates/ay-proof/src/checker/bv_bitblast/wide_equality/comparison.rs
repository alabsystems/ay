// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ordered words via low-to-high subtraction with an exact borrow bit.
//! Each intermediate is at most 65 bits; no wide producer word or duplicate
//! boxed operand tree is constructed. Flipping the most significant bit
//! converts two's-complement signed order to unsigned order.

use super::*;

impl ProofProducingLowerer<'_, '_> {
    pub(in crate::checker::bv_bitblast) fn lower_wide_comparison(
        &mut self,
        name: &str,
        lhs: TermId,
        rhs: TermId,
    ) -> Result<BvExpr, String> {
        let (signed, reversed, negated) = match name {
            "bvult" => (false, false, false),
            "bvule" => (false, true, true),
            "bvugt" => (false, true, false),
            "bvuge" => (false, false, true),
            "bvslt" => (true, false, false),
            "bvsle" => (true, true, true),
            "bvsgt" => (true, true, false),
            "bvsge" => (true, false, true),
            _ => return Err("unsupported wide order predicate".into()),
        };
        let slices = self
            .planned_slices(lhs, rhs, Partition::Limbs)
            .map_err(|error| self.planning_error(error))?;
        let mut borrow = None;
        for (index, (left, right)) in slices.iter().enumerate() {
            let width = left.width();
            let mut zero_operands = matches!(left, Piece::Constant { value: 0, .. })
                && matches!(right, Piece::Constant { value: 0, .. });
            // Keep the source request order even for reversed predicates.
            // Validate both pieces before simplifying a zero limb.
            let mut left = self.lower_piece(left)?;
            let mut right = self.lower_piece(right)?;
            if reversed {
                std::mem::swap(&mut left, &mut right);
            }
            if signed && index + 1 == slices.len() {
                self.charge_wide_constructed(4)?;
                let mask = 1u128 << (width - 1);
                left = BvExpr::xor(left, BvExpr::const_val(mask, width));
                right = BvExpr::xor(right, BvExpr::const_val(mask, width));
                zero_operands = false;
            }
            borrow = Some(if zero_operands {
                self.lower_zero_limb(Arithmetic::Sub, borrow, width, Part::Carry)?
            } else {
                self.lower_limb_values(Arithmetic::Sub, left, right, borrow, width, Part::Carry)?
            });
        }
        let borrow = borrow.ok_or_else(|| "wide order has no planned limbs".to_string())?;
        if negated {
            self.charge_wide_constructed(1)?;
            Ok(BvExpr::not(borrow))
        } else {
            Ok(borrow)
        }
    }
}
