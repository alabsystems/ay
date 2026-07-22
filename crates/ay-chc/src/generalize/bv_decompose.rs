// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! BV bit-decomposition generalizer for BV-native PDR (#5877 Wave 3).
//!
//! When PDR operates on BV-sorted predicates (Lane C, no BV transforms), blocking
//! formulas contain BV equality conjuncts like `(= var (_ bv4294967295 32))`. These
//! are maximally specific — they block exactly one BV state.
//!
//! This generalizer implements Z3 Spacer's `expand_literals` technique: decompose
//! BV equalities into per-bit constraints via `extract`, then try dropping individual
//! bit constraints. This enables blocking ranges of BV values rather than point values.
//!
//! Example:
//!   Input:  `(= x (_ bv10 4))` (x = #b1010)
//!   Expand: `(= (extract x 3 3) #b1) AND (= (extract x 2 2) #b0)
//!            AND (= (extract x 1 1) #b1) AND (= (extract x 0 0) #b0)`
//!   After drop-literal: maybe `(= (extract x 3 3) #b1) AND (= (extract x 1 1) #b1)`
//!   (blocks all x with bits 3 and 1 set, regardless of bits 2 and 0)
//!
//! Reference: Z3 Spacer `expand_literals` in `spacer_util.cpp:319-374`.

use crate::expr::{ChcExpr, ChcOp, ChcSort, ChcVar};
use std::sync::Arc;

use super::{LemmaGeneralizer, TransitionSystemRef};

/// BV bit-decomposition generalizer: expands BV equalities into per-bit constraints,
/// then drops redundant bit constraints (#5877 Wave 3).
pub(crate) struct BvBitDecompositionGeneralizer;

impl BvBitDecompositionGeneralizer {
    pub(crate) fn new() -> Self {
        Self
    }

    /// Check if a conjunct is a BV equality: `(= var bv_const)` or `(= bv_const var)`.
    fn extract_bv_equality(conjunct: &ChcExpr) -> Option<(ChcVar, u128, u32)> {
        match conjunct {
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (ChcExpr::Var(v), ChcExpr::BitVec(val, w))
                    | (ChcExpr::BitVec(val, w), ChcExpr::Var(v))
                        if matches!(v.sort, ChcSort::BitVec(_)) =>
                    {
                        Some((v.clone(), *val, *w))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Decompose a BV equality `(= var bv_const)` into per-bit constraints.
    fn decompose_bv_equality(var: &ChcVar, value: u128, width: u32) -> Vec<ChcExpr> {
        (0..width)
            .map(|i| {
                let bit_val = (value >> i) & 1;
                let extract = ChcExpr::Op(
                    ChcOp::BvExtract(i, i),
                    vec![Arc::new(ChcExpr::Var(var.clone()))],
                );
                ChcExpr::eq(extract, ChcExpr::BitVec(bit_val, 1))
            })
            .collect()
    }

    /// Phase 1: Try dropping entire BV equality conjuncts.
    fn try_drop_whole_bv_equalities(
        conjuncts: &[ChcExpr],
        bv_indices: &[(usize, ChcVar, u128, u32)],
        level: u32,
        ts: &mut dyn TransitionSystemRef,
    ) -> (Vec<bool>, bool) {
        let mut keep = vec![true; conjuncts.len()];
        let mut any_dropped = false;
        for &(idx, _, _, _) in bv_indices {
            keep[idx] = false;
            let candidate: Vec<ChcExpr> = conjuncts
                .iter()
                .enumerate()
                .filter(|(i, _)| keep[*i])
                .map(|(_, c)| c.clone())
                .collect();
            if candidate.is_empty() || !ts.check_inductive(&ChcExpr::and_all(candidate), level) {
                keep[idx] = true;
            } else {
                any_dropped = true;
            }
        }
        (keep, any_dropped)
    }

    /// Phase 2: Expand undropped BV equalities into per-bit constraints.
    fn expand_bv_to_bits(conjuncts: &[ChcExpr], keep: &[bool]) -> (Vec<ChcExpr>, bool) {
        let mut expanded = Vec::new();
        let mut has_expansion = false;
        for (idx, conjunct) in conjuncts.iter().enumerate() {
            if !keep[idx] {
                continue;
            }
            if let Some((ref var, val, width)) = Self::extract_bv_equality(conjunct) {
                if width <= 64 {
                    expanded.extend(Self::decompose_bv_equality(var, val, width));
                    has_expansion = true;
                } else {
                    expanded.push(conjunct.clone());
                }
            } else {
                expanded.push(conjunct.clone());
            }
        }
        (expanded, has_expansion)
    }

    /// Phase 3: Try dropping individual bit constraints from expanded formula.
    fn try_drop_individual_bits(
        expanded: &[ChcExpr],
        level: u32,
        ts: &mut dyn TransitionSystemRef,
    ) -> (Vec<bool>, bool) {
        let mut keep = vec![true; expanded.len()];
        let mut changed = false;
        for i in 0..expanded.len() {
            let is_bit = matches!(
                &expanded[i],
                ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2
                    && matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::BvExtract(_, _), _))
            );
            if !is_bit {
                continue;
            }
            keep[i] = false;
            let candidate: Vec<ChcExpr> = expanded
                .iter()
                .enumerate()
                .filter(|(j, _)| keep[*j])
                .map(|(_, c)| c.clone())
                .collect();
            if candidate.is_empty() || !ts.check_inductive(&ChcExpr::and_all(candidate), level) {
                keep[i] = true;
            } else {
                changed = true;
            }
        }
        (keep, changed)
    }

    /// Collect kept conjuncts into a conjunction, returning lemma if empty.
    fn collect_kept(conjuncts: &[ChcExpr], keep: &[bool], fallback: &ChcExpr) -> ChcExpr {
        let result: Vec<ChcExpr> = conjuncts
            .iter()
            .enumerate()
            .filter(|(i, _)| keep[*i])
            .map(|(_, c)| c.clone())
            .collect();
        if result.is_empty() {
            fallback.clone()
        } else {
            ChcExpr::and_all(result)
        }
    }
}

impl LemmaGeneralizer for BvBitDecompositionGeneralizer {
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr {
        let conjuncts = lemma.collect_conjuncts();
        if conjuncts.len() <= 1 {
            return lemma.clone();
        }

        let bv_eqs: Vec<(usize, ChcVar, u128, u32)> = conjuncts
            .iter()
            .enumerate()
            .filter_map(|(i, c)| Self::extract_bv_equality(c).map(|(v, val, w)| (i, v, val, w)))
            .collect();
        if bv_eqs.is_empty() {
            return lemma.clone();
        }

        let (keep, any_dropped) =
            Self::try_drop_whole_bv_equalities(&conjuncts, &bv_eqs, level, ts);
        let (expanded, has_expansion) = Self::expand_bv_to_bits(&conjuncts, &keep);

        if !has_expansion && !any_dropped {
            return lemma.clone();
        }
        if !has_expansion {
            return Self::collect_kept(&conjuncts, &keep, lemma);
        }

        let (bit_keep, bit_changed) = Self::try_drop_individual_bits(&expanded, level, ts);
        if !bit_changed && !any_dropped {
            return lemma.clone();
        }

        let result: Vec<ChcExpr> = expanded
            .into_iter()
            .enumerate()
            .filter(|(i, _)| bit_keep[*i])
            .map(|(_, c)| c)
            .collect();
        if result.is_empty() {
            lemma.clone()
        } else {
            ChcExpr::and_all(result)
        }
    }

    fn name(&self) -> &'static str {
        "bv-bit-decompose"
    }
}
