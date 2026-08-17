// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bit-group generalizer integration regressions.

use super::*;

// =========================================================================
// BvBitGroupGeneralizer Integration Tests (#5877)
// =========================================================================

#[test]
fn test_bv_bit_group_generalizer_name() {
    let g = BvBitGroupGeneralizer::new(vec![]);
    assert_eq!(g.name(), "bv-bit-group");
}

#[test]
fn test_bv_bit_group_empty_groups_returns_unchanged() {
    let g = BvBitGroupGeneralizer::new(vec![]);
    let mut ts = MockTransitionSystem::new();

    // Canonical BV bit-blasted point assignment: __p0_a0 AND NOT(__p0_a1)
    let a0 = ChcExpr::Var(ChcVar::new("__p0_a0", ChcSort::Bool));
    let a1 = ChcExpr::not(ChcExpr::Var(ChcVar::new("__p0_a1", ChcSort::Bool)));
    let lemma = ChcExpr::and(a0, a1);

    let result = g.generalize(&lemma, 1, &mut ts);
    assert_eq!(result, lemma);
}

#[test]
fn test_bv_bit_group_single_conjunct_returns_unchanged() {
    // Single conjunct = nothing to drop
    let g = BvBitGroupGeneralizer::new(vec![(0, 4)]);
    let mut ts = MockTransitionSystem::new();

    let a0 = ChcExpr::Var(ChcVar::new("__p0_a0", ChcSort::Bool));
    let result = g.generalize(&a0, 1, &mut ts);
    assert_eq!(result, a0);
}

#[test]
fn test_bv_bit_group_drops_entire_group_when_inductive() {
    // BV(4) = groups at arg indices [0..4) and [4..8)
    // Lemma: __p0_a0 AND NOT(__p0_a1) AND __p0_a2 AND __p0_a3
    //        AND __p0_a4 AND NOT(__p0_a5) AND __p0_a6 AND __p0_a7
    // Group 0: indices 0-3, Group 1: indices 4-7
    // If dropping group 0 is inductive, result should only contain group 1 bits.
    let g = BvBitGroupGeneralizer::new(vec![(0, 4), (4, 4)]);
    let mut ts = MockTransitionSystem::new();

    let bits: Vec<ChcExpr> = (0..8)
        .map(|i| {
            let var = ChcExpr::Var(ChcVar::new(&format!("__p0_a{i}"), ChcSort::Bool));
            if i % 2 == 1 {
                ChcExpr::not(var)
            } else {
                var
            }
        })
        .collect();

    let lemma = ChcExpr::and_all(bits.iter().cloned());

    // Mark group-1-only (bits 4-7) as inductive
    let group1_only = ChcExpr::and_all(bits[4..8].iter().cloned());
    ts.mark_inductive(&format!("{group1_only:?}"));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should have dropped group 0, keeping only group 1 bits
    assert_eq!(result, group1_only);
}

#[test]
fn test_bv_bit_group_preserves_when_drop_not_inductive() {
    // Two BV(2) groups: [0..2) and [2..4)
    // Neither group alone is inductive, so both must be kept
    let g = BvBitGroupGeneralizer::new(vec![(0, 2), (2, 2)]);
    let mut ts = MockTransitionSystem::new();

    let bits: Vec<ChcExpr> = (0..4)
        .map(|i| ChcExpr::Var(ChcVar::new(&format!("__p0_a{i}"), ChcSort::Bool)))
        .collect();
    let lemma = ChcExpr::and_all(bits.iter().cloned());

    // Only the full lemma is inductive, not any subset
    ts.mark_inductive(&format!("{lemma:?}"));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should preserve original (no group can be dropped)
    assert_eq!(result, lemma);
}

#[test]
fn test_bv_bit_group_non_canonical_conjuncts_preserved() {
    // Mix of canonical BV bits and non-BV conjuncts
    // Group: indices [0..2), plus a non-BV conjunct (no canonical index)
    let g = BvBitGroupGeneralizer::new(vec![(0, 2)]);
    let mut ts = MockTransitionSystem::new();

    let a0 = ChcExpr::Var(ChcVar::new("__p0_a0", ChcSort::Bool));
    let a1 = ChcExpr::Var(ChcVar::new("__p0_a1", ChcSort::Bool));
    let non_bv = ChcExpr::ge(
        ChcExpr::Var(ChcVar::new("counter", ChcSort::Int)),
        ChcExpr::int(0),
    );

    let lemma = ChcExpr::and_all([a0, a1, non_bv.clone()]);

    // Mark the non-BV conjunct alone as inductive (dropping the BV group is valid)
    ts.mark_inductive(&format!("{non_bv:?}"));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should keep only the non-BV conjunct
    assert_eq!(result, non_bv);
}
