// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A product by a constant, lowered as the signed sum of shifted copies its
//! non-adjacent form names (`crate::non_adjacent_form`), exactly as the
//! printer re-spells it (`complete_blast/constant_product.rs`).
//!
//! `x * K ≡ Σ ±(x << k) (mod 2^w)` whenever `Σ ±2^k ≡ K`, so the lowering is
//! exact; a shift by a literal is wiring, so the product costs one adder per
//! digit instead of the `w²` shift-and-add array. The array is not merely
//! larger: its internal signals line up with nothing, so `(bvmul x #xff..ff)`
//! against `(bvneg x)` is a multiplier identity no sweep merges. Measured
//! 2026-09-30 on external-codegen's IDIV remainder rows, `a - (a sdiv b) * b` with
//! `b = -1`: the array's refutation exceeded the checker's proof-size caps.
//! The constant is a literal, a closed term, or a variable a hypothesis or
//! case fixes (`constants`).

use super::*;
use crate::non_adjacent_form::non_adjacent_form;

impl ProofProducingLowerer<'_, '_> {
    /// `lhs * rhs` when either factor is a known constant.
    pub(super) fn constant_product(
        &self,
        (lhs, lhs_term): (&BvExpr, TermId),
        (rhs, rhs_term): (&BvExpr, TermId),
        width: u32,
    ) -> Option<BvExpr> {
        for (constant, constant_term, factor) in [(rhs, rhs_term, lhs), (lhs, lhs_term, rhs)] {
            let value = match constant {
                BvExpr::Const { value, .. } => Some(*value),
                _ => bounded_eval::closed_bv_in(self.terms, constant_term, &self.constants)
                    .map(u128::from),
            };
            if let Some(value) = value {
                return Some(signed_shift_sum(factor, value, width));
            }
        }
        None
    }
}

/// `Σ ±(x << k)` over the non-adjacent form of `value` at `width` bits.
fn signed_shift_sum(x: &BvExpr, value: u128, width: u32) -> BvExpr {
    let term = |power: u32| {
        if power == 0 {
            x.clone()
        } else {
            BvExpr::shl(x.clone(), BvExpr::const_val(u128::from(power), width))
        }
    };
    let mut sum: Option<BvExpr> = None;
    for (power, negative) in non_adjacent_form(value, width) {
        let term = term(power);
        sum = Some(match (sum, negative) {
            (None, false) => term,
            (None, true) => BvExpr::sub(BvExpr::const_val(0, width), term),
            (Some(sum), false) => BvExpr::add(sum, term),
            (Some(sum), true) => BvExpr::sub(sum, term),
        });
    }
    sum.unwrap_or_else(|| BvExpr::const_val(0, width))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The value of the sum's shapes (`x`, literals, literal shifts, `+`, `-`)
    /// at `x`, modulo `2^width`.
    fn value(expr: &BvExpr, x: u128, width: u32) -> u128 {
        let mask = u128::MAX >> (128 - width);
        match expr {
            BvExpr::Leaf { .. } => x & mask,
            BvExpr::Const { value, .. } => *value,
            BvExpr::Shl(inner, amount) => {
                let BvExpr::Const { value: amount, .. } = amount.as_ref() else {
                    panic!("a shift by a non-literal")
                };
                value(inner, x, width)
                    .checked_shl(*amount as u32)
                    .unwrap_or(0)
                    & mask
            }
            BvExpr::Add(a, b) => value(a, x, width).wrapping_add(value(b, x, width)) & mask,
            BvExpr::Sub(a, b) => value(a, x, width).wrapping_sub(value(b, x, width)) & mask,
            other => panic!("unexpected shape {other:?}"),
        }
    }

    #[test]
    fn the_signed_shift_sum_is_the_product_modulo_the_width() {
        for width in [1_u32, 8, 32, 64, 128] {
            let mask = u128::MAX >> (128 - width);
            for constant in [0_u128, 1, 3, 127, 0x55, u128::MAX, 1 << 63, 0x8000_0001] {
                let constant = constant & mask;
                let sum = signed_shift_sum(&BvExpr::leaf("x", width), constant, width);
                for x in [0_u128, 1, 2, 0xdead_beef, u128::MAX, 1 << 100] {
                    let x = x & mask;
                    assert_eq!(
                        value(&sum, x, width),
                        x.wrapping_mul(constant) & mask,
                        "{x} * {constant} at {width}"
                    );
                }
            }
        }
    }
}
