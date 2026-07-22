// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ChcExpr;

/// Test that dropping deep obligation chains does not cause stack overflow.
/// Without the custom Drop implementation, a chain of 100,000 obligations
/// would require 100,000 stack frames and overflow the stack.
#[test]
fn test_drop_deep_obligation_chain_no_stack_overflow() {
    const CHAIN_DEPTH: usize = 100_000;
    let mut current = ProofObligation::new(PredicateId::new(0), ChcExpr::Bool(true), 0);
    for _ in 0..CHAIN_DEPTH {
        current =
            ProofObligation::new(PredicateId::new(0), ChcExpr::Bool(true), 0).with_parent(current);
    }
    // Verify chain depth using the tracked depth field (O(1) vs O(N) traversal)
    assert_eq!(
        current.depth, CHAIN_DEPTH,
        "Chain should have {CHAIN_DEPTH} levels"
    );
    // Explicit drop - should not stack overflow
    drop(current);
}

#[test]
fn test_proof_obligation_priority_ordering() {
    // Lower level = higher priority
    let pob1 = ProofObligation::new(PredicateId::new(0), ChcExpr::Bool(true), 1);
    let pob2 = ProofObligation::new(PredicateId::new(0), ChcExpr::Bool(true), 2);

    let ppob1 = PriorityPob(pob1);
    let ppob2 = PriorityPob(pob2);

    // In a max-heap, higher priority items should compare as "greater"
    // Since we want lower level first, pob1 (level 1) should be "greater" than pob2 (level 2)
    assert!(
        ppob1 > ppob2,
        "Level 1 should have higher priority than level 2"
    );
}

#[test]
fn test_proof_obligation_with_parent() {
    let parent = ProofObligation::new(PredicateId::new(0), ChcExpr::Bool(true), 0);
    let child =
        ProofObligation::new(PredicateId::new(1), ChcExpr::Bool(false), 1).with_parent(parent);

    assert_eq!(child.depth, 1);
    assert!(child.parent.is_some());
    assert_eq!(
        child.parent.as_ref().unwrap().predicate,
        PredicateId::new(0)
    );
}

#[test]
fn test_proof_obligation_with_clause_info() {
    let pob = ProofObligation::new(PredicateId::new(0), ChcExpr::Bool(true), 0)
        .with_incoming_clause(5)
        .with_query_clause(10);

    assert_eq!(pob.incoming_clause, Some(5));
    assert_eq!(pob.query_clause, Some(10));
}

#[test]
fn test_new_obligation_defaults_to_must_kind() {
    let pob = ProofObligation::new(PredicateId::new(0), ChcExpr::Bool(true), 3);
    assert_eq!(pob.kind, PobKind::Must);
    assert!(!pob.is_may());
    assert_eq!(pob.gas, 0);
    assert_eq!(pob.desired_level, 3, "desired_level defaults to level");
}

#[test]
fn test_with_may_sets_kind_gas_and_clamps_desired_level() {
    let pob = ProofObligation::new(PredicateId::new(1), ChcExpr::Bool(true), 2).with_may(
        PobKind::MaySubsume,
        15,
        5,
    );
    assert_eq!(pob.kind, PobKind::MaySubsume);
    assert!(pob.is_may());
    assert_eq!(pob.gas, 15);
    assert_eq!(pob.desired_level, 5);

    // desired_level below the pob's own level is clamped up to the level.
    let clamped = ProofObligation::new(PredicateId::new(1), ChcExpr::Bool(true), 4).with_may(
        PobKind::MayConjecture,
        5,
        1,
    );
    assert_eq!(clamped.desired_level, 4);
    assert!(clamped.is_may());
}

#[test]
fn test_may_promotion_ladder_stops_at_desired_level() {
    // Spawned at level 1 with desired_level 3 and gas 2: block at 1 promotes
    // to 2, block at 2 promotes to 3, block at 3 stops (desired reached).
    let pob = ProofObligation::new(PredicateId::new(0), ChcExpr::Bool(true), 1).with_may(
        PobKind::MaySubsume,
        2,
        3,
    );

    let p1 = pob
        .may_promotion_after_block(1, 10)
        .expect("blocked below desired level should promote");
    assert_eq!(p1.level, 2);
    assert_eq!(p1.gas, 1, "promotion costs one unit of gas");
    assert_eq!(p1.kind, PobKind::MaySubsume);
    assert_eq!(p1.desired_level, 3);

    let p2 = p1
        .may_promotion_after_block(2, 10)
        .expect("still below desired level");
    assert_eq!(p2.level, 3);
    assert_eq!(p2.gas, 0);

    assert!(
        p2.may_promotion_after_block(3, 10).is_none(),
        "no promotion once the desired level is reached"
    );
}

#[test]
fn test_may_promotion_respects_gas_exhaustion_and_frame_ceiling() {
    // Gas exhaustion: zero gas never promotes, even below desired level.
    let out_of_gas = ProofObligation::new(PredicateId::new(0), ChcExpr::Bool(true), 1).with_may(
        PobKind::MayConjecture,
        0,
        4,
    );
    assert!(
        out_of_gas.may_promotion_after_block(1, 10).is_none(),
        "gas-exhausted may-pob must not promote"
    );

    // Frame ceiling: desired_level is clamped to max_level.
    let pob = ProofObligation::new(PredicateId::new(0), ChcExpr::Bool(true), 1).with_may(
        PobKind::MaySubsume,
        10,
        8,
    );
    assert!(
        pob.may_promotion_after_block(2, 2).is_none(),
        "promotion must not exceed the current frame ceiling"
    );
    assert!(pob.may_promotion_after_block(1, 2).is_some());

    // MUST pobs never promote.
    let must = ProofObligation::new(PredicateId::new(0), ChcExpr::Bool(true), 1);
    assert!(must.may_promotion_after_block(1, 10).is_none());
}

#[test]
fn test_may_pob_kill_switch_env_value_parsing() {
    // Default ON; only the literal "0" disables.
    assert!(may_pob_enabled_from_env_value(None));
    assert!(may_pob_enabled_from_env_value(Some("1")));
    assert!(may_pob_enabled_from_env_value(Some("")));
    assert!(!may_pob_enabled_from_env_value(Some("0")));
}

#[test]
fn test_proof_obligation_with_smt_model() {
    use crate::smt::SmtValue;

    // Create a model with various value types
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(42));
    model.insert("flag".to_string(), SmtValue::Bool(true));
    model.insert("bits".to_string(), SmtValue::BitVec(0xFF, 8));

    let pob =
        ProofObligation::new(PredicateId::new(0), ChcExpr::Bool(true), 0).with_smt_model(model);

    // Verify model is stored
    assert!(pob.smt_model.is_some(), "Model should be stored");

    // Verify model contents with explicit value checks
    let stored_model = pob.smt_model.as_ref().unwrap();
    assert_eq!(stored_model.len(), 3, "Model should contain 3 entries");

    // Verify each value with explicit assertions
    assert_eq!(
        stored_model.get("x"),
        Some(&SmtValue::Int(42)),
        "Integer value should be exactly 42"
    );
    assert_eq!(
        stored_model.get("flag"),
        Some(&SmtValue::Bool(true)),
        "Boolean value should be true"
    );
    assert_eq!(
        stored_model.get("bits"),
        Some(&SmtValue::BitVec(0xFF, 8)),
        "BitVec value should be 0xFF with width 8"
    );
}
