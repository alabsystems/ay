// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Project concatenated vectors before duplicating their expression trees.
//!
//! The complete source operand is lowered first, including both children of
//! every concat. Projection therefore cannot hide malformed or unsupported
//! discarded operands. Only then do the checked widths select the exact bits
//! needed by the extract. The selected operands are TAKEN OUT of the lowered
//! concat ([`concat_operands`]), never lowered again: the source is the one
//! request an `extract` makes, which is what the census counts
//! (`lowering_share.rs`). Lowering an operand again built the same
//! expression (`lowering_census_tests.rs`) once per level of the chain. The
//! original source terms and proof premises stay unchanged; the bounded
//! bit-blast and independent resolution replay still run.

use super::*;

#[cfg(test)]
mod tests;

impl ProofProducingLowerer<'_, '_> {
    pub(super) fn lower_bv_extract(
        &mut self,
        source: TermId,
        high: u32,
        low: u32,
    ) -> Result<(BvExpr, u32), String> {
        self.poll_lowering()?;
        let (inner, width) = self.lower_bv(source)?;
        self.project(source, inner, width, high, low)
    }

    /// Bits `high..=low` of `expr`, the lowering of `source`, `width` bits.
    pub(super) fn project(
        &mut self,
        source: TermId,
        expr: BvExpr,
        width: u32,
        high: u32,
        low: u32,
    ) -> Result<(BvExpr, u32), String> {
        self.poll_lowering()?;
        if low > high || high >= width {
            return Err(format!("extract range {high}:{low} exceeds width {width}"));
        }
        let result_width = high - low + 1;
        if result_width == width {
            return Ok((expr, width));
        }
        // Bits below a `zero_extend` are its operand's own: take the operand's
        // lowering out of the lowered extension, as for a concat's children.
        let expr = match (self.extended_operand(source, width), expr) {
            (Some((operand, operand_width)), BvExpr::ZeroExt(inner, added))
                if high < operand_width && operand_width.checked_add(added) == Some(width) =>
            {
                return self.project(operand, *inner, operand_width, high, low);
            }
            (_, expr) => expr,
        };
        let children = match self.terms.get(source) {
            TermData::App(Symbol::Named(name), args) if name == "concat" => match args.as_slice() {
                [left, right] => Some((*left, *right)),
                _ => None,
            },
            _ => None,
        };
        // A definitional lowering names the concat itself
        // (`proof_producing_control/definitional.rs`): its bits are read off
        // the name, which equals the concat under its definition.
        let Some((left, right)) = children.filter(|_| !matches!(expr, BvExpr::Leaf { .. })) else {
            return Ok((BvExpr::extract(expr, high, low), result_width));
        };
        // Both child sorts and their sum were checked when the concat was
        // lowered.
        let Sort::BitVec(right_sort) = self.terms.sort(right) else {
            return Err("validated concat child lost its BitVec sort".to_string());
        };
        let right_width = right_sort.width;
        let left_width = width - right_width;
        let (upper, lower) = concat_operands(expr)?;
        if high < right_width {
            return self.project(right, lower, right_width, high, low);
        }
        if low >= right_width {
            return self.project(
                left,
                upper,
                left_width,
                high - right_width,
                low - right_width,
            );
        }
        let (upper, upper_width) = self.project(left, upper, left_width, high - right_width, 0)?;
        let (lower, lower_width) = self.project(right, lower, right_width, right_width - 1, low)?;
        let upper = BvExpr::zero_ext(upper, lower_width);
        let lower = BvExpr::zero_ext(lower, upper_width);
        let shifted = BvExpr::shl(
            upper,
            BvExpr::const_val(u128::from(lower_width), result_width),
        );
        Ok((BvExpr::or(shifted, lower), result_width))
    }
}

impl ProofProducingLowerer<'_, '_> {
    /// `(x, width(x))` when `source`, `width` bits, is `((_ zero_extend k) x)`
    /// with `width(x) + k == width`, which `lower_bv_app` lowers as
    /// `(zero_extend x k)`.
    fn extended_operand(&self, source: TermId, width: u32) -> Option<(TermId, u32)> {
        let TermData::App(Symbol::Indexed(name, indices), args) = self.terms.get(source) else {
            return None;
        };
        let (&[added], &[operand]) = (indices.as_slice(), args.as_slice()) else {
            return None;
        };
        let Sort::BitVec(operand_sort) = self.terms.sort(operand) else {
            return None;
        };
        (name == "zero_extend" && operand_sort.width.checked_add(added) == Some(width))
            .then_some((operand, operand_sort.width))
    }
}

/// The lowered operands of a lowered `concat`, which `lower_bv_app` builds as
/// `(bvor (bvshl (zero_extend L) w) (zero_extend R))`.
fn concat_operands(expr: BvExpr) -> Result<(BvExpr, BvExpr), String> {
    let unexpected = || "a lowered concat has an unexpected shape".to_string();
    let BvExpr::Or(shifted, low) = expr else {
        return Err(unexpected());
    };
    let (BvExpr::Shl(high, _), BvExpr::ZeroExt(right, _)) = (*shifted, *low) else {
        return Err(unexpected());
    };
    let BvExpr::ZeroExt(left, _) = *high else {
        return Err(unexpected());
    };
    Ok((*left, *right))
}
