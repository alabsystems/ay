// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

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

// =========================================================================
// BvBitDecompositionGeneralizer Integration Tests (#5877 Wave 3)
// =========================================================================

#[test]
fn test_bv_bit_decompose_generalizer_name() {
    let g = BvBitDecompositionGeneralizer::new();
    assert_eq!(g.name(), "bv-bit-decompose");
}

#[test]
fn test_bv_bit_decompose_no_bv_equalities_returns_unchanged() {
    let g = BvBitDecompositionGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Pure integer lemma — no BV equalities to decompose
    use crate::expr::{ChcSort, ChcVar};
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let lemma = ChcExpr::and(
        ChcExpr::ge(x.clone(), ChcExpr::int(0)),
        ChcExpr::le(x, ChcExpr::int(10)),
    );

    let result = g.generalize(&lemma, 1, &mut ts);
    assert_eq!(result, lemma);
}

#[test]
fn test_bv_bit_decompose_single_conjunct_returns_unchanged() {
    let g = BvBitDecompositionGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Single BV equality — nothing to drop (need >= 2 conjuncts)
    use crate::expr::{ChcSort, ChcVar};
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(4)));
    let lemma = ChcExpr::eq(x, ChcExpr::BitVec(10, 4)); // x = 0b1010

    let result = g.generalize(&lemma, 1, &mut ts);
    assert_eq!(result, lemma);
}

#[test]
fn test_bv_bit_decompose_drops_entire_bv_equality_when_inductive() {
    let g = BvBitDecompositionGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Lemma: (= x bv10_4) AND (= y bv5_4)
    // If dropping (= x bv10_4) is inductive, phase 1 removes it.
    use crate::expr::{ChcSort, ChcVar};
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(4)));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::BitVec(4)));
    let x_eq = ChcExpr::eq(x, ChcExpr::BitVec(10, 4));
    let y_eq = ChcExpr::eq(y, ChcExpr::BitVec(5, 4));
    let lemma = ChcExpr::and(x_eq, y_eq.clone());

    // Mark y_eq alone as inductive (dropping x_eq is valid)
    ts.mark_inductive(&format!("{y_eq:?}"));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Phase 1 should drop x_eq. Phase 2 expands remaining y_eq to per-bit.
    // Phase 3 tries dropping individual bits of y.
    // Since no individual bit subset is marked inductive, all bits of y are kept.
    // Result should be the per-bit expansion of y_eq.
    let y_var = ChcVar::new("y", ChcSort::BitVec(4));
    let expected_bits: Vec<ChcExpr> = (0..4u32)
        .map(|i| {
            let extract = ChcExpr::Op(
                ChcOp::BvExtract(i, i),
                vec![Arc::new(ChcExpr::Var(y_var.clone()))],
            );
            ChcExpr::eq(extract, ChcExpr::BitVec((5 >> i) & 1, 1))
        })
        .collect();
    let expected = ChcExpr::and_all(expected_bits);

    assert_eq!(result, expected);
}

#[test]
fn test_bv_bit_decompose_drops_individual_bits_phase3() {
    let g = BvBitDecompositionGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Lemma: (= x bv10_4) AND (counter >= 0)
    // x = 0b1010: bit3=1, bit2=0, bit1=1, bit0=0
    // Phase 1: x_eq is not independently droppable
    // Phase 2: expand x_eq into 4 per-bit constraints + keep counter >= 0
    // Phase 3: try dropping individual bits; mark bits 0 and 2 as droppable
    use crate::expr::{ChcSort, ChcVar};
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(4)));
    let x_eq = ChcExpr::eq(x, ChcExpr::BitVec(10, 4));
    let counter_ge = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("counter", ChcSort::Int)),
        ChcExpr::int(0),
    );
    let lemma = ChcExpr::and(x_eq, counter_ge.clone());

    // The per-bit expansion of x = 0b1010 gives 4 bit constraints.
    // We want bits 1 and 3 (value=1 bits) to be sufficient.
    let x_var = ChcVar::new("x", ChcSort::BitVec(4));
    let bit_exprs: Vec<ChcExpr> = (0..4u32)
        .map(|i| {
            let extract = ChcExpr::Op(
                ChcOp::BvExtract(i, i),
                vec![Arc::new(ChcExpr::Var(x_var.clone()))],
            );
            ChcExpr::eq(extract, ChcExpr::BitVec((10 >> i) & 1, 1))
        })
        .collect();

    // Mark the formula with bits 1 and 3 + counter_ge as inductive.
    // This means bits 0 and 2 can be dropped.
    let kept = ChcExpr::and_all([
        bit_exprs[1].clone(),
        bit_exprs[3].clone(),
        counter_ge.clone(),
    ]);
    ts.mark_inductive(&format!("{kept:?}"));

    // Also mark intermediate stages where we try dropping bit 0 first
    // (the algorithm drops greedily from index 0)
    let without_bit0 = ChcExpr::and_all([
        bit_exprs[1].clone(),
        bit_exprs[2].clone(),
        bit_exprs[3].clone(),
        counter_ge,
    ]);
    ts.mark_inductive(&format!("{without_bit0:?}"));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should have dropped bits 0 and 2, keeping bits 1, 3 and counter_ge
    assert_eq!(result, kept);
}

#[test]
fn test_bv_bit_decompose_preserves_when_nothing_droppable() {
    let g = BvBitDecompositionGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Lemma: (= x bv3_2) AND (= y bv1_2) — two BV(2) equalities
    // Nothing is droppable (no subset marked inductive)
    use crate::expr::{ChcSort, ChcVar};
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(2)));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::BitVec(2)));
    let lemma = ChcExpr::and(
        ChcExpr::eq(x, ChcExpr::BitVec(3, 2)),
        ChcExpr::eq(y, ChcExpr::BitVec(1, 2)),
    );

    // Only full lemma is inductive
    ts.mark_inductive(&format!("{lemma:?}"));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should preserve original (nothing can be dropped)
    assert_eq!(result, lemma);
}

#[test]
fn test_bv_bit_decompose_extract_bv_equality_reversed() {
    // Verify that (= bv_const var) is also recognized (reversed operand order)
    let g = BvBitDecompositionGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    use crate::expr::{ChcSort, ChcVar};
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(4)));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::BitVec(4)));
    // Reversed: (= bv_const var)
    let x_eq = ChcExpr::eq(ChcExpr::BitVec(10, 4), x);
    let y_eq = ChcExpr::eq(ChcExpr::BitVec(5, 4), y);
    let lemma = ChcExpr::and(x_eq, y_eq.clone());

    // Mark y_eq alone as inductive
    ts.mark_inductive(&format!("{y_eq:?}"));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should have dropped x_eq (phase 1), expanded y_eq to per-bit
    // Result should be different from lemma (decomposition occurred)
    assert_ne!(result, lemma);
}

// =========================================================================
// BvFlagGuardGeneralizer Tests (#5877 bit-guard packet)
// =========================================================================

#[test]
fn test_bv_flag_guard_generalizer_name() {
    let g = BvFlagGuardGeneralizer::new();
    assert_eq!(g.name(), "bv-flag-guards");
}

#[test]
fn test_bv_flag_guard_generalizer_preserves_zero_equality() {
    let g = BvFlagGuardGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(32)));
    let guard = ChcExpr::Var(ChcVar::new("a", ChcSort::Bool));
    let lemma = ChcExpr::and(guard, ChcExpr::eq(x, ChcExpr::BitVec(0, 32)));

    let result = g.generalize(&lemma, 1, &mut ts);

    assert_eq!(result, lemma);
    assert!(
        ts.queries.borrow().is_empty(),
        "preserving x = 0 should not require inductiveness queries"
    );
}

#[test]
fn test_bv_flag_guard_generalizer_rewrites_one_to_lsb_when_inductive() {
    let g = BvFlagGuardGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    let x_var = ChcVar::new("x", ChcSort::BitVec(32));
    let x_eq_one = ChcExpr::eq(ChcExpr::var(x_var.clone()), ChcExpr::BitVec(1, 32));
    let counter_ge = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("counter", ChcSort::Int)),
        ChcExpr::int(0),
    );
    let lemma = ChcExpr::and(x_eq_one, counter_ge.clone());

    let bit0 = ChcExpr::eq(
        ChcExpr::Op(ChcOp::BvExtract(0, 0), vec![Arc::new(ChcExpr::Var(x_var))]),
        ChcExpr::BitVec(1, 1),
    );
    let expected = ChcExpr::and(bit0, counter_ge);
    ts.mark_inductive(&format!("{expected:?}"));

    let result = g.generalize(&lemma, 1, &mut ts);

    assert_eq!(result, expected);
}

#[test]
fn test_bv_flag_guard_generalizer_leaves_non_flag_constants_unchanged() {
    let g = BvFlagGuardGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(32)));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::BitVec(32)));
    let lemma = ChcExpr::and(
        ChcExpr::eq(x, ChcExpr::BitVec(2, 32)),
        ChcExpr::eq(y, ChcExpr::BitVec(10, 32)),
    );

    let result = g.generalize(&lemma, 1, &mut ts);

    assert_eq!(result, lemma);
    assert!(
        ts.queries.borrow().is_empty(),
        "non-flag constants should not trigger inductiveness queries"
    );
}

// =========================================================================
// LiteralWeakeningGeneralizer BV-specific Tests (#5877)
// =========================================================================

#[test]
fn test_literal_weakening_bv_equality_generates_signed_candidates() {
    let g = LiteralWeakeningGeneralizer::new();

    // (= x #x0A) where x is BitVec(32)
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(32)));
    let lit = ChcExpr::eq(x.clone(), ChcExpr::BitVec(0x0A, 32));

    let candidates = g.generate_weakenings(&lit);

    // Should produce 4 candidates: bvsle(x,K), bvsle(K,x), bvule(x,K), bvule(K,x)
    assert_eq!(
        candidates.len(),
        4,
        "BV equality should produce 4 weakening candidates"
    );

    // Check candidate 0: bvsle(x, #x0A) — signed x <= 10
    match &candidates[0] {
        ChcExpr::Op(ChcOp::BvSLe, args) if args.len() == 2 => {
            assert_eq!(args[0].as_ref(), &x, "first arg should be x");
            assert_eq!(args[1].as_ref(), &ChcExpr::BitVec(0x0A, 32));
        }
        other => panic!("Expected BvSLe(x, #x0A), got {other:?}"),
    }

    // Check candidate 1: bvsle(#x0A, x) — signed 10 <= x
    match &candidates[1] {
        ChcExpr::Op(ChcOp::BvSLe, args) if args.len() == 2 => {
            assert_eq!(args[0].as_ref(), &ChcExpr::BitVec(0x0A, 32));
            assert_eq!(args[1].as_ref(), &x, "second arg should be x");
        }
        other => panic!("Expected BvSLe(#x0A, x), got {other:?}"),
    }

    // Check candidate 2: bvule(x, #x0A) — unsigned x <= 10
    match &candidates[2] {
        ChcExpr::Op(ChcOp::BvULe, args) if args.len() == 2 => {
            assert_eq!(args[0].as_ref(), &x, "first arg should be x");
            assert_eq!(args[1].as_ref(), &ChcExpr::BitVec(0x0A, 32));
        }
        other => panic!("Expected BvULe(x, #x0A), got {other:?}"),
    }

    // Check candidate 3: bvule(#x0A, x) — unsigned 10 <= x
    match &candidates[3] {
        ChcExpr::Op(ChcOp::BvULe, args) if args.len() == 2 => {
            assert_eq!(args[0].as_ref(), &ChcExpr::BitVec(0x0A, 32));
            assert_eq!(args[1].as_ref(), &x, "second arg should be x");
        }
        other => panic!("Expected BvULe(#x0A, x), got {other:?}"),
    }
}

#[test]
fn test_literal_weakening_bv_msb_extract_signed_negative() {
    let g = LiteralWeakeningGeneralizer::new();

    // (= (extract 31 31 x) #b1) — MSB=1, signed negative
    let x_var = ChcVar::new("x", ChcSort::BitVec(32));
    let extract = ChcExpr::Op(
        ChcOp::BvExtract(31, 31),
        vec![Arc::new(ChcExpr::Var(x_var.clone()))],
    );
    let lit = ChcExpr::eq(extract, ChcExpr::BitVec(1, 1));

    let candidates = g.generate_weakenings(&lit);

    // Should produce bvslt(x, 0) — signed x < 0
    assert!(
        !candidates.is_empty(),
        "MSB=1 extract equality should produce weakening candidates"
    );
    match &candidates[0] {
        ChcExpr::Op(ChcOp::BvSLt, args) if args.len() == 2 => {
            assert_eq!(args[0].as_ref(), &ChcExpr::Var(x_var));
            assert_eq!(args[1].as_ref(), &ChcExpr::BitVec(0, 32));
        }
        other => panic!("Expected BvSLt(x, bv0_32), got {other:?}"),
    }
}

#[test]
fn test_literal_weakening_bv_msb_extract_signed_nonneg() {
    let g = LiteralWeakeningGeneralizer::new();

    // (= (extract 31 31 x) #b0) — MSB=0, signed non-negative
    let x_var = ChcVar::new("x", ChcSort::BitVec(32));
    let extract = ChcExpr::Op(
        ChcOp::BvExtract(31, 31),
        vec![Arc::new(ChcExpr::Var(x_var.clone()))],
    );
    let lit = ChcExpr::eq(extract, ChcExpr::BitVec(0, 1));

    let candidates = g.generate_weakenings(&lit);

    // Should produce bvsle(0, x) — signed 0 <= x
    assert!(
        !candidates.is_empty(),
        "MSB=0 extract equality should produce weakening candidates"
    );
    match &candidates[0] {
        ChcExpr::Op(ChcOp::BvSLe, args) if args.len() == 2 => {
            assert_eq!(args[0].as_ref(), &ChcExpr::BitVec(0, 32));
            assert_eq!(args[1].as_ref(), &ChcExpr::Var(x_var));
        }
        other => panic!("Expected BvSLe(bv0_32, x), got {other:?}"),
    }
}

#[test]
fn test_literal_weakening_bv_non_msb_extract_no_msb_weakening() {
    let g = LiteralWeakeningGeneralizer::new();

    // (= (extract 5 5 x) #b1) where x is BV(32) — NOT the MSB
    // Should NOT produce MSB-specific weakening (bvslt/bvsle)
    let x_var = ChcVar::new("x", ChcSort::BitVec(32));
    let extract = ChcExpr::Op(ChcOp::BvExtract(5, 5), vec![Arc::new(ChcExpr::Var(x_var))]);
    let lit = ChcExpr::eq(extract, ChcExpr::BitVec(1, 1));

    let candidates = g.generate_weakenings(&lit);

    // extract_msb_var checks hi == w-1, so (extract 5 5 x) where x is BV(32)
    // will NOT match MSB path. The 1-bit BV result is_bitvec → general BV weakening
    // produces bvsle/bvule on the 1-bit extract result, but NOT bvslt(x, 0).
    for c in &candidates {
        if let ChcExpr::Op(ChcOp::BvSLt, _) = c {
            panic!("Non-MSB extract should not produce BvSLt(x, 0) weakening");
        }
    }
}

#[test]
fn test_literal_weakening_bv_applies_first_inductive_candidate() {
    let g = LiteralWeakeningGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Lemma: (= x #x0A) where x is BV(32)
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(32)));
    let lemma = ChcExpr::eq(x.clone(), ChcExpr::BitVec(0x0A, 32));

    // Mark only bvsle(#x0A, x) (candidate 1, signed x >= 10) as inductive.
    // The generalizer should skip candidate 0 (bvsle(x, K)) and use candidate 1.
    let expected = ChcExpr::Op(
        ChcOp::BvSLe,
        vec![Arc::new(ChcExpr::BitVec(0x0A, 32)), Arc::new(x)],
    );
    ts.mark_inductive(&format!("{expected:?}"));

    let result = g.generalize(&lemma, 1, &mut ts);

    assert_eq!(
        result, expected,
        "Should apply first inductive candidate (bvsle(K, x))"
    );
}

#[test]
fn test_literal_weakening_bv_no_inductive_candidate_preserves() {
    let g = LiteralWeakeningGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Lemma: (= x #x0A) where x is BV(32)
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(32)));
    let lemma = ChcExpr::eq(x, ChcExpr::BitVec(0x0A, 32));

    // Don't mark anything as inductive — all candidates should fail.
    let result = g.generalize(&lemma, 1, &mut ts);

    assert_eq!(result, lemma, "No inductive candidate → preserve original");
}

#[test]
fn test_literal_weakening_bv_int_equality_no_bv_candidates() {
    let g = LiteralWeakeningGeneralizer::new();

    // (= x 5) where x is Int — should produce le candidates, not bvsle/bvule
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let lit = ChcExpr::eq(x, ChcExpr::int(5));

    let candidates = g.generate_weakenings(&lit);

    // Should produce exactly 2 candidates: le(x, 5) and le(5, x)
    assert_eq!(candidates.len(), 2, "Int equality produces 2 le candidates");
    for c in &candidates {
        if let ChcExpr::Op(ChcOp::BvSLe | ChcOp::BvULe, _) = c {
            panic!("Int equality should not produce BV weakening candidates");
        }
    }
}
