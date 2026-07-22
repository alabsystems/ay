// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV per-bit replacement generalization for PDR lemmas (#7968).
//!
//! Ports Z3 Spacer's per-bit replacement technique from
//! `spacer_generalizers.cpp:62-142` (`lemma_bool_inductive_generalizer`).
//!
//! For a BV equality `(= var #bvC)` with width `w`, try replacing the full
//! equality with a single bit check `(= (extract j j var) #bK)` for each bit j.
//! This is more aggressive than mask-based weakening: instead of keeping a
//! masked equality, it finds that a single bit position suffices to maintain
//! inductiveness.
//!
//! Also tries contiguous subfield replacements: `(= (extract hi lo var) subval)`.

use super::{ChcExpr, LemmaGeneralizer, TransitionSystemRef};
use crate::expr::{ChcOp, ChcSort, ChcVar};
use std::sync::Arc;

/// Maximum BV width for per-bit replacement. Wider BVs have too many bit
/// positions to check individually.
const MAX_BV_WIDTH_FOR_REPLACEMENT: u32 = 64;

/// Per-bit replacement BV generalizer.
///
/// Phase 1: Try replacing a BV equality with a single bit check (MSB first).
/// Phase 2: If no single bit works, try contiguous subfield replacements
///          (upper half, lower half, byte boundaries).
pub(crate) struct BvPerBitReplacementGeneralizer;

impl Default for BvPerBitReplacementGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl BvPerBitReplacementGeneralizer {
    pub(crate) fn new() -> Self {
        Self
    }

    /// Try replacing a BV equality with a single bit constraint.
    /// Returns `Some(replacement)` if any single bit suffices, `None` otherwise.
    fn try_single_bit_replacement(
        var: &ChcVar,
        value: u128,
        width: u32,
        other_conjuncts: &[ChcExpr],
        level: u32,
        ts: &mut dyn TransitionSystemRef,
    ) -> Option<ChcExpr> {
        // Try each bit position from MSB to LSB (high bits are more likely to
        // be structurally important in hardware designs)
        for bit in (0..width).rev() {
            let bit_val = (value >> bit) & 1;
            let constraint = build_bit_constraint(var, bit, bit_val);

            let mut test_conjuncts: Vec<ChcExpr> = other_conjuncts.to_vec();
            test_conjuncts.push(constraint.clone());
            let formula = ChcExpr::and_all(test_conjuncts);

            if ts.check_inductive(&formula, level) {
                return Some(constraint);
            }
        }
        None
    }

    /// Try replacing a BV equality with a contiguous subfield constraint.
    /// Tries upper half, lower half, then byte-aligned subfields.
    fn try_subfield_replacement(
        var: &ChcVar,
        value: u128,
        width: u32,
        other_conjuncts: &[ChcExpr],
        level: u32,
        ts: &mut dyn TransitionSystemRef,
    ) -> Option<ChcExpr> {
        if width < 2 {
            return None;
        }

        // Define subfield boundaries to try (ordered by size — smaller is more general)
        let mut subfields: Vec<(u32, u32)> = Vec::new();

        // Upper half and lower half
        let mid = width / 2;
        subfields.push((width - 1, mid)); // upper half
        subfields.push((mid - 1, 0)); // lower half

        // Byte boundaries (for widths >= 8)
        if width >= 8 {
            let byte_count = width / 8;
            for b in 0..byte_count {
                let lo = b * 8;
                let hi = lo + 7;
                if hi < width {
                    subfields.push((hi, lo));
                }
            }
        }

        // Nibble boundaries (for widths >= 4)
        if width >= 4 {
            let nibble_count = width / 4;
            for n in 0..nibble_count {
                let lo = n * 4;
                let hi = lo + 3;
                if hi < width {
                    subfields.push((hi, lo));
                }
            }
        }

        // Deduplicate and sort by subfield size (smaller first = more general)
        subfields.sort_by_key(|(hi, lo)| hi - lo);
        subfields.dedup();

        for (hi, lo) in subfields {
            let subfield_width = hi - lo + 1;
            let subfield_mask: u128 = if subfield_width >= 128 {
                u128::MAX
            } else {
                (1u128 << subfield_width) - 1
            };
            let subfield_val = (value >> lo) & subfield_mask;

            let constraint = build_subfield_constraint(var, hi, lo, subfield_val, subfield_width);

            let mut test_conjuncts: Vec<ChcExpr> = other_conjuncts.to_vec();
            test_conjuncts.push(constraint.clone());
            let formula = ChcExpr::and_all(test_conjuncts);

            if ts.check_inductive(&formula, level) {
                return Some(constraint);
            }
        }

        None
    }
}

/// Build a single-bit constraint: `(= (extract j j var) #bK)`.
fn build_bit_constraint(var: &ChcVar, bit_pos: u32, bit_val: u128) -> ChcExpr {
    let extract = ChcExpr::Op(
        ChcOp::BvExtract(bit_pos, bit_pos),
        vec![Arc::new(ChcExpr::Var(var.clone()))],
    );
    ChcExpr::eq(extract, ChcExpr::BitVec(bit_val, 1))
}

/// Build a subfield constraint: `(= (extract hi lo var) #bvVAL)`.
fn build_subfield_constraint(var: &ChcVar, hi: u32, lo: u32, value: u128, width: u32) -> ChcExpr {
    let extract = ChcExpr::Op(
        ChcOp::BvExtract(hi, lo),
        vec![Arc::new(ChcExpr::Var(var.clone()))],
    );
    ChcExpr::eq(extract, ChcExpr::BitVec(value, width))
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

impl LemmaGeneralizer for BvPerBitReplacementGeneralizer {
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr {
        let conjuncts = lemma.collect_conjuncts();
        if conjuncts.len() < 2 {
            return lemma.clone();
        }

        let mut result = conjuncts.clone();
        let mut any_changed = false;

        for i in 0..result.len() {
            if let Some((var, value, width)) = extract_bv_eq(&result[i]) {
                if width > MAX_BV_WIDTH_FOR_REPLACEMENT || width == 0 {
                    continue;
                }

                // Build the other conjuncts (everything except index i)
                let other: Vec<ChcExpr> = result
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, c)| c.clone())
                    .collect();

                // Phase 1: Try single-bit replacement (most aggressive)
                if let Some(replacement) =
                    Self::try_single_bit_replacement(&var, value, width, &other, level, ts)
                {
                    result[i] = replacement;
                    any_changed = true;
                    continue;
                }

                // Phase 2: Try subfield replacement (less aggressive)
                if let Some(replacement) =
                    Self::try_subfield_replacement(&var, value, width, &other, level, ts)
                {
                    result[i] = replacement;
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
        "bv-per-bit-replacement"
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
    fn test_build_bit_constraint() {
        let var = bv_var("x", 8);
        let c = build_bit_constraint(&var, 3, 1);
        if let ChcExpr::Op(ChcOp::Eq, args) = &c {
            assert!(matches!(
                args[0].as_ref(),
                ChcExpr::Op(ChcOp::BvExtract(3, 3), _)
            ));
            assert!(matches!(args[1].as_ref(), ChcExpr::BitVec(1, 1)));
        } else {
            panic!("Expected Eq operation");
        }
    }

    #[test]
    fn test_build_subfield_constraint() {
        let var = bv_var("x", 16);
        let c = build_subfield_constraint(&var, 7, 0, 0xAB, 8);
        if let ChcExpr::Op(ChcOp::Eq, args) = &c {
            assert!(matches!(
                args[0].as_ref(),
                ChcExpr::Op(ChcOp::BvExtract(7, 0), _)
            ));
            assert!(matches!(args[1].as_ref(), ChcExpr::BitVec(0xAB, 8)));
        } else {
            panic!("Expected Eq operation");
        }
    }

    #[test]
    fn test_per_bit_generalizer_no_bv() {
        let g = BvPerBitReplacementGeneralizer::new();
        let mut ts = MockTransitionSystem::new();

        let x = ChcVar::new("x", ChcSort::Int);
        let lemma = ChcExpr::and(
            ChcExpr::eq(ChcExpr::Var(x.clone()), ChcExpr::Int(5)),
            ChcExpr::gt(ChcExpr::Var(x), ChcExpr::Int(0)),
        );

        let result = g.generalize(&lemma, 1, &mut ts);
        assert_eq!(result, lemma);
    }

    #[test]
    fn test_per_bit_generalizer_name() {
        let g = BvPerBitReplacementGeneralizer::new();
        assert_eq!(g.name(), "bv-per-bit-replacement");
    }
}
