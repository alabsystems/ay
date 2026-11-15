// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A product by a literal, lowered as the signed sum of shifts a compiler
//! writes for it.
//!
//! `(bvmul c t)` over `w` bits is `c * T mod 2^w`. When the non-adjacent form
//! of `c` modulo `2^w`, `c = Σ ±2^k` with every `k < w`, has fewer digits
//! than `c` has one bits, the product is lowered as that sum of `t << k`
//! terms — `(bvsub (bvshl t 9) t)` for `c = 511` — instead of a `w`-row
//! shift-and-add array. `2^k * T mod 2^w` is `(bvshl t k)` for `k < w`, so the
//! rewrite is an identity of the operators' SMT-LIB semantics and the lowered
//! clause has exactly the models of the source clause; the digits are
//! re-evaluated modulo `2^w` before they are used, and any other literal keeps
//! the array.
//!
//! Why: external-codegen states strength reductions as `x * (2^a - 1) == (x << a) - x`
//! (gate rows 1901 and 1903: `511` and `2^32 - 1` at 64 bits). The array for
//! the literal has `a` live rows whose sums line up with no signal of the
//! subtractor, so the miter is left to CDCL: 16 s at 48 bits, and at 64 bits
//! the checker refused the lemma, so the rows published no proof. Lowered by
//! its digits, the product is the very `(bvsub (bvshl t a) t)` circuit of the
//! other side. The printer re-spells the same products through the same
//! digits (`alethe_printer/complete_blast/constant_product.rs`); this module
//! computes them independently, since the judge does not import the printer.

use super::*;

/// Most signed digits a literal is lowered through: each digit copies the
/// other operand's lowering once.
const MAX_DIGITS: usize = 4;

impl ProofProducingLowerer<'_, '_> {
    /// The lowering of the `width`-bit `(bvmul lhs rhs)`, whose operands lower
    /// to `lhs_expr` and `rhs_expr`: a signed sum of shifts when either
    /// operand is a literal the module docs admit, otherwise the array.
    pub(super) fn lower_product(
        &self,
        (lhs, lhs_expr): (TermId, BvExpr),
        (rhs, rhs_expr): (TermId, BvExpr),
        width: u32,
    ) -> BvExpr {
        if let Some(digits) = self.literal_digits(lhs, width) {
            return shift_sum(&rhs_expr, &digits, width);
        }
        if let Some(digits) = self.literal_digits(rhs, width) {
            return shift_sum(&lhs_expr, &digits, width);
        }
        BvExpr::mul(lhs_expr, rhs_expr)
    }

    /// The signed digits of `term` when it is a `width`-bit literal whose
    /// non-adjacent form is shorter than its binary form (module docs).
    fn literal_digits(&self, term: TermId, width: u32) -> Option<Vec<(u32, bool)>> {
        let TermData::Const(Constant::BitVec {
            value,
            width: literal_width,
        }) = self.terms.get(term)
        else {
            return None;
        };
        if *literal_width != width || width == 0 || width > u128::BITS {
            return None;
        }
        let value = value.to_u128()? & mask(width);
        let digits = non_adjacent_form(value, width);
        let shorter = digits.len() < value.count_ones() as usize;
        (shorter && digits.len() <= MAX_DIGITS && evaluate(&digits, width) == value)
            .then_some(digits)
    }
}

/// `Σ ±(t << k)` over `digits`, most significant first.
fn shift_sum(operand: &BvExpr, digits: &[(u32, bool)], width: u32) -> BvExpr {
    let mut sum: Option<BvExpr> = None;
    for &(power, negative) in digits {
        let term = if power == 0 {
            operand.clone()
        } else {
            BvExpr::shl(operand.clone(), BvExpr::const_val(u128::from(power), width))
        };
        sum = Some(match (sum, negative) {
            (None, false) => term,
            (None, true) => BvExpr::sub(BvExpr::const_val(0, width), term),
            (Some(acc), false) => BvExpr::add(acc, term),
            (Some(acc), true) => BvExpr::sub(acc, term),
        });
    }
    // `literal_digits` never answers an empty form (a zero literal has no one
    // bits to be shorter than).
    sum.unwrap_or_else(|| BvExpr::const_val(0, width))
}

fn mask(width: u32) -> u128 {
    u128::MAX >> (u128::BITS - width)
}

/// The non-adjacent form of `value` modulo `2^width` (`1 <= width <= 128`),
/// most significant digit first, as `(power, negative)` with every power below
/// `width`: Reitwiesner's recoding `d_i = b_i + c_i - 2 c_{i+1}`, `c_{i+1} =
/// ⌊(b_i + b_{i+1} + c_i) / 2⌋`, dropping the carry out of the top bit
/// (`2^width ≡ 0`).
fn non_adjacent_form(value: u128, width: u32) -> Vec<(u32, bool)> {
    let bit = |index: u32| u8::from(index < width && (value >> index) & 1 == 1);
    let mut digits = Vec::new();
    let mut carry = 0_u8;
    for index in 0..width {
        let (low, high) = (bit(index), bit(index + 1));
        let next = (low + high + carry) / 2;
        let digit = i16::from(low) + i16::from(carry) - 2 * i16::from(next);
        if digit != 0 {
            digits.push((index, digit < 0));
        }
        carry = next;
    }
    digits.reverse();
    digits
}

/// `Σ ±2^power` modulo `2^width`.
fn evaluate(digits: &[(u32, bool)], width: u32) -> u128 {
    let sum = digits.iter().fold(0_u128, |acc, &(power, negative)| {
        let term = 1_u128 << power;
        if negative {
            acc.wrapping_sub(term)
        } else {
            acc.wrapping_add(term)
        }
    });
    sum & mask(width)
}

#[cfg(test)]
#[path = "literal_product_tests.rs"]
mod tests;
