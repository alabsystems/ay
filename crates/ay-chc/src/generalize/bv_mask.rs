// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV mask-based generalization for PDR lemmas (#7968).
//!
//! For a BV equality `(= var #bvC)`, weaken to `(= (bvand var mask) (bvand #bvC mask))`
//! by clearing bits in the mask that are don't-cares for inductiveness.
//!
//! This is complementary to bit-level decomposition: instead of expanding to per-bit
//! constraints and dropping individual bits, this keeps the equality structure but
//! relaxes which bits must match.
//!
//! Reference: Z3 Spacer's `expand_literals` concept (spacer_util.cpp:357-370),
//! adapted to use mask-based weakening instead of per-bit expansion.

use super::{ChcExpr, LemmaGeneralizer, TransitionSystemRef};
use crate::expr::{ChcOp, ChcSort, ChcVar};
use std::sync::Arc;

/// Maximum BV width for mask-based generalization. Wider BVs would require
/// too many inductiveness checks (one per bit).
const MAX_BV_WIDTH_FOR_MASK: u32 = 64;

/// Mask-based BV equality generalization.
///
/// For each BV equality `(= var #bvC)` in the lemma, tries clearing bits in a
/// mask (MSB to LSB) to produce `(= (bvand var mask) (bvand C mask))`.
/// Each cleared bit is kept if the weakened formula remains inductive.
pub(crate) struct BvMaskGeneralizer;

impl Default for BvMaskGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl BvMaskGeneralizer {
    pub(crate) fn new() -> Self {
        Self
    }

    /// Try to generalize a single BV equality by clearing mask bits.
    ///
    /// Returns `Some(weakened_expr)` if any bits could be cleared, `None` otherwise.
    fn generalize_single_bv_equality(
        var: &ChcVar,
        value: u128,
        width: u32,
        other_conjuncts: &[ChcExpr],
        level: u32,
        ts: &mut dyn TransitionSystemRef,
    ) -> Option<ChcExpr> {
        if width > MAX_BV_WIDTH_FOR_MASK || width == 0 {
            return None;
        }

        let all_ones_mask: u128 = if width >= 128 {
            u128::MAX
        } else {
            (1u128 << width) - 1
        };
        let mut mask = all_ones_mask;
        let mut any_cleared = false;

        // Try clearing each bit from MSB to LSB
        for bit in (0..width).rev() {
            let test_mask = mask & !(1u128 << bit);
            if test_mask == mask {
                continue; // bit already cleared
            }

            let weakened = build_masked_equality(var, value, test_mask, width);
            let mut test_conjuncts: Vec<ChcExpr> = other_conjuncts.to_vec();
            test_conjuncts.push(weakened.clone());
            let formula = ChcExpr::and_all(test_conjuncts);

            if ts.check_inductive(&formula, level) {
                mask = test_mask;
                any_cleared = true;
            }
        }

        if any_cleared {
            Some(build_masked_equality(var, value, mask, width))
        } else {
            None
        }
    }
}

/// Build `(= (bvand var mask) (bvand value mask))`.
///
/// If mask is all-ones, returns the original equality (no masking needed).
fn build_masked_equality(var: &ChcVar, value: u128, mask: u128, width: u32) -> ChcExpr {
    let all_ones: u128 = if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };

    if mask == all_ones {
        // No masking needed — original equality
        ChcExpr::eq(ChcExpr::Var(var.clone()), ChcExpr::BitVec(value, width))
    } else {
        let mask_expr = Arc::new(ChcExpr::BitVec(mask, width));
        let var_masked = ChcExpr::Op(
            ChcOp::BvAnd,
            vec![Arc::new(ChcExpr::Var(var.clone())), mask_expr.clone()],
        );
        let val_masked = ChcExpr::Op(
            ChcOp::BvAnd,
            vec![Arc::new(ChcExpr::BitVec(value, width)), mask_expr],
        );
        ChcExpr::eq(var_masked, val_masked)
    }
}

/// Extract (variable, value, width) from a BV equality.
fn extract_bv_eq(expr: &ChcExpr) -> Option<(ChcVar, u128, u32)> {
    if let ChcExpr::Op(ChcOp::Eq, args) = expr {
        if args.len() == 2 {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::BitVec(val, w))
                | (ChcExpr::BitVec(val, w), ChcExpr::Var(v))
                    if matches!(v.sort, ChcSort::BitVec(_)) =>
                {
                    Some((v.clone(), *val, *w))
                }
                _ => None,
            }
        } else {
            None
        }
    } else {
        None
    }
}

impl LemmaGeneralizer for BvMaskGeneralizer {
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr {
        let conjuncts = lemma.collect_conjuncts();
        if conjuncts.len() < 2 {
            return lemma.clone();
        }

        let mut result = conjuncts.clone();
        let mut any_changed = false;

        for i in 0..result.len() {
            if let Some((var, value, width)) = extract_bv_eq(&result[i]) {
                // Build the other conjuncts (everything except index i)
                let other: Vec<ChcExpr> = result
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, c)| c.clone())
                    .collect();

                if let Some(weakened) =
                    Self::generalize_single_bv_equality(&var, value, width, &other, level, ts)
                {
                    result[i] = weakened;
                    any_changed = true;
                }
            }
        }

        if any_changed {
            ChcExpr::and_all(result)
        } else {
            lemma.clone()
        }
    }

    fn name(&self) -> &'static str {
        "bv-mask"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::generalize::tests::MockTransitionSystem;

    fn bv_var(name: &str, width: u32) -> ChcVar {
        ChcVar::new(name, ChcSort::BitVec(width))
    }

    #[test]
    fn test_build_masked_equality_all_ones() {
        let var = bv_var("x", 8);
        let result = build_masked_equality(&var, 42, 0xFF, 8);
        // Should be a plain equality (no masking)
        assert!(matches!(result, ChcExpr::Op(ChcOp::Eq, _)));
    }

    #[test]
    fn test_build_masked_equality_with_mask() {
        let var = bv_var("x", 8);
        let result = build_masked_equality(&var, 42, 0xF0, 8);
        // Should contain bvand operations
        if let ChcExpr::Op(ChcOp::Eq, args) = &result {
            assert!(matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::BvAnd, _)));
            assert!(matches!(args[1].as_ref(), ChcExpr::Op(ChcOp::BvAnd, _)));
        } else {
            panic!("Expected Eq operation");
        }
    }

    #[test]
    fn test_extract_bv_eq() {
        let var = bv_var("x", 8);
        let eq = ChcExpr::eq(ChcExpr::Var(var.clone()), ChcExpr::BitVec(42, 8));
        let result = extract_bv_eq(&eq);
        assert!(result.is_some());
        let (v, val, w) = result.unwrap();
        assert_eq!(v.name, "x");
        assert_eq!(val, 42);
        assert_eq!(w, 8);
    }

    #[test]
    fn test_mask_generalizer_no_bv_equalities() {
        let g = BvMaskGeneralizer::new();
        let mut ts = MockTransitionSystem::new();

        // Non-BV lemma should be returned unchanged
        let x = ChcVar::new("x", ChcSort::Int);
        let lemma = ChcExpr::and(
            ChcExpr::eq(ChcExpr::Var(x.clone()), ChcExpr::Int(5)),
            ChcExpr::gt(ChcExpr::Var(x), ChcExpr::Int(0)),
        );

        let result = g.generalize(&lemma, 1, &mut ts);
        assert_eq!(result, lemma);
    }

    #[test]
    fn test_mask_generalizer_name() {
        let g = BvMaskGeneralizer::new();
        assert_eq!(g.name(), "bv-mask");
    }
}
