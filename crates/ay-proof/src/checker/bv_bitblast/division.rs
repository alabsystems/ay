// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof-producing unsigned division and signed literal lowering.
//!
//! Unsigned closed power-of-two divisors use the existing shift/mask route.
//! Other unspecialized division terms use one canonical opaque leaf in lemma
//! validation; the existing counted exact-divider fallback is unchanged.
//!
//! Signed literal +1/-1 divisors lower exactly in lemma validation: quotient
//! identity/modular negation, and zero remainder/modulo. Both operands must
//! already lower and have the same width. This adds no constant evaluator,
//! hypothesis binding, retry, credit, or expensive-step exemption.
//! Literal zero divisors also lower exactly: rem/mod preserve the dividend;
//! quotient is one for negative dividends and all ones otherwise.
//! Nonzero signed power-of-two magnitudes use biased arithmetic shifts and
//! masks. Large scalar operands are named before lowering under the existing
//! functional-definition rules, so internal copies stay bounded without a new
//! retry, source census, or budget. Array retry eligibility is unchanged.
//!
//! Exact signed shortcuts may change expression shape and shared-copy costs
//! compared with an opaque leaf; unchanged caps do not guarantee preservation
//! of every old admission. Query authentication still refuses reserved names.
//! Unary aliases and nonliteral divisors retain their old path.

use super::*;

struct SignedPower {
    width: u32,
    magnitude: u128,
    negative: bool,
}

impl<'a, 'p> ProofProducingLowerer<'a, 'p> {
    /// Start bounded scalar naming before operands can be copied internally.
    pub(super) fn prepare_signed_power(&mut self, name: &str, divisor: TermId) {
        if matches!(name, "bvsdiv" | "bvsrem" | "bvsmod")
            && self.signed_power_divisor(divisor).is_some()
        {
            self.record_scalar_definitions();
        }
    }

    fn signed_power_divisor(&self, divisor: TermId) -> Option<SignedPower> {
        if !self.abstract_reserved_bv_operators {
            return None;
        }
        let TermData::Const(Constant::BitVec { value, width }) = self.terms.get(divisor) else {
            return None;
        };
        let width = *width;
        if !(2..=128).contains(&width) {
            return None;
        }
        let mask = if width == 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        };
        let value = value.to_u128()?;
        if value == 0 || value == 1 || value == mask || value > mask {
            return None;
        }
        let negative = value & (1u128 << (width - 1)) != 0;
        let magnitude = if negative {
            mask.checked_sub(value)?.checked_add(1)?
        } else {
            value
        };
        magnitude.is_power_of_two().then_some(SignedPower {
            width,
            magnitude,
            negative,
        })
    }

    /// Exact signed zero/unit literal semantics for lemma validation only.
    /// Negation wraps at the signed minimum; width1's unit bit pattern also
    /// works because modular negation is the identity at that width.
    pub(super) fn signed_literal_divisor(
        &self,
        name: &str,
        lhs: BvExpr,
        divisor: TermId,
        width: u32,
    ) -> Result<BvExpr, BvExpr> {
        if !self.abstract_reserved_bv_operators
            || !matches!(name, "bvsdiv" | "bvsrem" | "bvsmod")
            || width == 0
            || width > 128
        {
            return Err(lhs);
        }
        let TermData::Const(Constant::BitVec {
            value,
            width: divisor_width,
        }) = self.terms.get(divisor)
        else {
            return Err(lhs);
        };
        let all_ones = if width == 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        };
        let Some(value) = value.to_u128() else {
            return Err(lhs);
        };
        if *divisor_width != width {
            return Err(lhs);
        }
        if value == 0 {
            return Ok(if name == "bvsdiv" {
                // The sign mask is all ones exactly for a negative dividend.
                // Its complement OR one is therefore one or all ones.
                let sign = BvExpr::extract(lhs, width - 1, width - 1);
                let mask = BvExpr::sign_ext(sign, width - 1);
                BvExpr::or(BvExpr::not(mask), BvExpr::const_val(1, width))
            } else {
                lhs
            });
        }
        if value != 1 && value != all_ones {
            return match self.signed_power_divisor(divisor) {
                Some(power) => Ok(signed_power_expression(name, lhs, power)),
                None => Err(lhs),
            };
        }
        if name != "bvsdiv" {
            Ok(BvExpr::const_val(0, width))
        } else if value == all_ones {
            Ok(BvExpr::sub(BvExpr::const_val(0, width), lhs))
        } else {
            Ok(lhs)
        }
    }

    /// The divisor `2^k` (`k` below `width`) of a `bvudiv`/`bvurem`, which is
    /// exactly a shift and a mask: `(bvudiv x 2^k)` is `(bvlshr x k)` and
    /// `(bvurem x 2^k)` is `(bvand x 2^k-1)`. The divisor is a literal or a
    /// CLOSED term the bounded evaluator folds (`bounded_eval::closed_bv_in`);
    /// any other stays outside the exact fragment (`BvApplicationLowering`).
    pub(super) fn power_of_two_divisor(
        &self,
        name: &str,
        divisor: TermId,
        width: u32,
    ) -> Option<u128> {
        if !matches!(name, "bvudiv" | "bvurem") {
            return None;
        }
        let value = match self.terms.get(divisor) {
            TermData::Const(Constant::BitVec { value, .. }) => value.to_u128()?,
            _ => u128::from(bounded_eval::closed_bv_in(
                self.terms,
                divisor,
                &self.constants,
            )?),
        };
        Some(value).filter(|d| d.is_power_of_two() && d.trailing_zeros() < width)
    }

    /// `(bvudiv lhs 2^k)` as `(bvlshr lhs k)` and `(bvurem lhs 2^k)` as
    /// `(bvand lhs 2^k-1)` when [`Self::power_of_two_divisor`] finds the
    /// divisor; otherwise `lhs` is handed back untouched.
    pub(super) fn power_of_two_quotient(
        &self,
        name: &str,
        lhs: BvExpr,
        divisor: TermId,
        width: u32,
    ) -> Result<BvExpr, BvExpr> {
        let Some(divisor) = self.power_of_two_divisor(name, divisor, width) else {
            return Err(lhs);
        };
        Ok(if name == "bvudiv" {
            let shift = u128::from(divisor.trailing_zeros());
            BvExpr::lshr(lhs, BvExpr::const_val(shift, width))
        } else {
            BvExpr::and(lhs, BvExpr::const_val(divisor - 1, width))
        })
    }

    /// [`Self::new_for_lemma_validation`] with exact division.
    pub(super) fn new_with_exact_division(terms: &'a TermStore, deadline: Instant) -> Self {
        Self {
            exact_division: true,
            ..Self::new_for_lemma_validation(terms, deadline)
        }
    }
}

/// For m=2^k, bias=(x<0 ? m-1 : 0) makes arithmetic shift round toward zero.
/// The same bias gives signed remainder as ((x+bias)&(m-1))-bias.
fn signed_power_expression(name: &str, lhs: BvExpr, power: SignedPower) -> BvExpr {
    let SignedPower {
        width,
        magnitude,
        negative,
    } = power;
    let mask = magnitude - 1;
    if name == "bvsmod" {
        return if negative {
            let absolute_low = BvExpr::and(
                BvExpr::sub(BvExpr::const_val(0, width), lhs),
                BvExpr::const_val(mask, width),
            );
            BvExpr::sub(BvExpr::const_val(0, width), absolute_low)
        } else {
            BvExpr::and(lhs, BvExpr::const_val(mask, width))
        };
    }
    let sign = BvExpr::sign_ext(
        BvExpr::extract(lhs.clone(), width - 1, width - 1),
        width - 1,
    );
    let bias = BvExpr::and(sign, BvExpr::const_val(mask, width));
    if name == "bvsrem" {
        let low = BvExpr::and(
            BvExpr::add(lhs, bias.clone()),
            BvExpr::const_val(mask, width),
        );
        BvExpr::sub(low, bias)
    } else {
        let quotient = BvExpr::ashr(
            BvExpr::add(lhs, bias),
            BvExpr::const_val(u128::from(magnitude.trailing_zeros()), width),
        );
        if negative {
            BvExpr::sub(BvExpr::const_val(0, width), quotient)
        } else {
            quotient
        }
    }
}

/// Whether `clause` mentions `bvudiv` or `bvurem` (a bounded walk; a clause
/// too large to walk is treated as not mentioning one).
pub(super) fn clause_mentions_division(terms: &TermStore, clause: &[TermId]) -> bool {
    const MAX_VISITS: usize = 1 << 20;
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack: Vec<TermId> = clause.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > MAX_VISITS {
            return false;
        }
        if let TermData::App(Symbol::Named(name), _) = terms.get(term) {
            if matches!(name.as_str(), "bvudiv" | "bvurem") {
                return true;
            }
        }
        stack.extend(terms.children(term));
    }
    false
}
