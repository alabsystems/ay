// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A product with a zero-padded operand, lowered at the width that matters.
//!
//! `(bvmul (concat x 0_k) t)` over `w` bits is `2^k * X * T mod 2^w`, which is
//! `2^k * (X * T mod 2^(w-k))`, and `X * T mod 2^(w-k)` reads only the low
//! `w-k` bits of `t`. So it is lowered as `(concat (bvmul x t[w-k-1:0]) 0_k)`,
//! a `(w-k)`-bit multiplier, and symmetrically with the padded operand second
//! (the narrow product keeps the operand order, so its partial-product rows
//! are the ones a same-order narrow product in the clause builds).
//!
//! Why: the `w`-bit array multiplier over a zero-padded operand does not fold
//! its constant rows, so its high half is a renamed copy of the narrow array,
//! a miter CDCL does not close in the gate's budget (measured on
//! `(bvmul (concat a 0_64) ((_ zero_extend 64) b))` against
//! `(concat (bvmul a b) 0_64)`: interrupted at 130 s), and its full-width gate
//! estimate is four times the narrow one's. Lowered narrow, the two sides share
//! one multiplier and the clause closes by propagation. external-codegen's i128
//! multiply lowering (gate row 2023) needs two such products in one lemma.
//!
//! The rewrite is an identity of the operators' SMT-LIB semantics, so the
//! lowered clause has exactly the models of the source clause.

use super::*;
use num_traits::Zero;

impl ProofProducingLowerer<'_, '_> {
    /// The narrow lowering of `(name lhs rhs)` when it is a `bvmul` with a
    /// literal zero-padded `concat` operand, or `None` (module docs).
    pub(super) fn lower_padded_product(
        &mut self,
        name: &str,
        lhs: TermId,
        rhs: TermId,
    ) -> Result<Option<(BvExpr, u32)>, String> {
        if name != "bvmul" {
            return Ok(None);
        }
        for (padded, other, padded_first) in [(lhs, rhs, true), (rhs, lhs, false)] {
            let Some((high, shift)) = self.zero_padded(padded) else {
                continue;
            };
            let (high_expr, high_width) = self.lower_bv(high)?;
            let (other_expr, width) = self.lower_bv(other)?;
            if high_width.checked_add(shift) != Some(width) {
                return Err(format!(
                    "`bvmul` width mismatch: {} vs {width}",
                    high_width.saturating_add(shift)
                ));
            }
            // The operand's own low bits where its term spells them (a
            // concat's low limb, a zero_extend's operand), so the narrow
            // product is the very node a narrow product of that limb builds.
            let (low, _) = self.project(other, other_expr, width, high_width - 1, 0)?;
            let product = if padded_first {
                BvExpr::mul(high_expr, low)
            } else {
                BvExpr::mul(low, high_expr)
            };
            let shifted = BvExpr::shl(
                BvExpr::zero_ext(product, shift),
                BvExpr::const_val(u128::from(shift), width),
            );
            return Ok(Some((shifted, width)));
        }
        Ok(None)
    }

    /// The operands [`Self::lower_padded_product`] requests for `(symbol
    /// args)`, or `None` when it does not apply: the census counts these in
    /// place of the product's own arguments.
    pub(super) fn padded_product_operands(
        &self,
        symbol: &Symbol,
        args: &[TermId],
    ) -> Option<[TermId; 2]> {
        let (Symbol::Named(name), &[lhs, rhs]) = (symbol, args) else {
            return None;
        };
        if name != "bvmul" {
            return None;
        }
        [(lhs, rhs), (rhs, lhs)]
            .into_iter()
            .find_map(|(padded, other)| Some([self.zero_padded(padded)?.0, other]))
    }

    /// `(x, k)` when `term` is `(concat x 0_k)` with `x` and the literal zero
    /// both at least one bit wide.
    fn zero_padded(&self, term: TermId) -> Option<(TermId, u32)> {
        let TermData::App(Symbol::Named(name), args) = self.terms.get(term) else {
            return None;
        };
        let &[high, low] = args.as_slice() else {
            return None;
        };
        if name != "concat" || !matches!(self.terms.sort(high), Sort::BitVec(bv) if bv.width > 0) {
            return None;
        }
        match self.terms.get(low) {
            TermData::Const(Constant::BitVec { value, width }) if value.is_zero() && *width > 0 => {
                Some((high, *width))
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::checker::bv_bitblast::recognize_bv_bitblast;
    use ay_core::{Sort, Symbol, TermId, TermStore};

    fn app(terms: &mut TermStore, op: &str, args: [TermId; 2], width: u32) -> TermId {
        terms.mk_app(Symbol::named(op), args, Sort::bitvec(width))
    }

    /// `(bvmul (concat a 0) (zext b))` against `(concat (bvmul a b) 0)`, and
    /// `(bvmul (zext b) (concat a 0))` against `(concat (bvmul b a) 0)`, are
    /// recognized at 64-bit limbs: the narrow product keeps the operand
    /// order, so each is the narrow product of its own right-hand side. A
    /// wrong narrow product is not an identity the lowering invents.
    #[test]
    fn a_zero_padded_product_is_its_narrow_product_shifted() {
        let (width, half) = (128, 64);
        let mut terms = TermStore::new();
        let [a, b] = ["a", "b"].map(|name| terms.mk_var(name, Sort::bitvec(half)));
        let zero = terms.mk_bitvec(0u8.into(), half);
        let padded = app(&mut terms, "concat", [a, zero], width);
        let widened = terms.mk_app(
            Symbol::indexed("zero_extend", vec![half]),
            [b],
            Sort::bitvec(width),
        );
        for (wide, narrow) in [([padded, widened], [a, b]), ([widened, padded], [b, a])] {
            let wide = app(&mut terms, "bvmul", wide, width);
            let narrow = app(&mut terms, "bvmul", narrow, half);
            let shifted = app(&mut terms, "concat", [narrow, zero], width);
            let identity = terms.mk_eq(wide, shifted);
            assert!(recognize_bv_bitblast(&terms, &[identity]));
        }
        let wrong = app(&mut terms, "bvmul", [a, a], half);
        let wrong = app(&mut terms, "concat", [wrong, zero], width);
        let wide = app(&mut terms, "bvmul", [padded, widened], width);
        let false_identity = terms.mk_eq(wide, wrong);
        assert!(!recognize_bv_bitblast(&terms, &[false_identity]));
    }

    /// At 6 bits with at least 9 free input bits (past the exhaustive
    /// evaluator, so the proof-producing lowering decides), a product with a padded operand is recognized equal
    /// to the same product spelled with a literal `2^k` and never equal to that
    /// product plus `2^k`, for every pad width and both operand orders.
    #[test]
    fn the_padded_lowering_agrees_with_the_full_product() {
        let width = 6;
        let mut terms = TermStore::new();
        let t = terms.mk_var("t", Sort::bitvec(width));
        for shift in 1..=3 {
            let x = terms.mk_var(format!("x{shift}"), Sort::bitvec(width - shift));
            let zero = terms.mk_bitvec(0u8.into(), shift);
            let padded = app(&mut terms, "concat", [x, zero], width);
            let scale = terms.mk_bitvec((1u16 << shift).into(), width);
            let widened = terms.mk_app(
                Symbol::indexed("zero_extend", vec![shift]),
                [x],
                Sort::bitvec(width),
            );
            let scaled = app(&mut terms, "bvmul", [scale, widened], width);
            for padded_first in [true, false] {
                let (product, reference) = if padded_first {
                    (
                        app(&mut terms, "bvmul", [padded, t], width),
                        app(&mut terms, "bvmul", [scaled, t], width),
                    )
                } else {
                    (
                        app(&mut terms, "bvmul", [t, padded], width),
                        app(&mut terms, "bvmul", [t, scaled], width),
                    )
                };
                let identity = terms.mk_eq(product, reference);
                assert!(recognize_bv_bitblast(&terms, &[identity]), "k={shift}");
                let off = app(&mut terms, "bvadd", [reference, scale], width);
                let false_identity = terms.mk_eq(product, off);
                assert!(
                    !recognize_bv_bitblast(&terms, &[false_identity]),
                    "k={shift}"
                );
            }
        }
    }
}
