// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boundary controls for opaque datatype construction work accounting.

use super::super::dt_construct::eval_to_mv;
use super::super::dt_construct_budget::{OpaqueDtCollectionBudget, OpaqueDtConstructionBudget};
use super::super::EvalValue;
use ay_core::Sort;
use ay_model_check::ModelValue;
use num_bigint::BigInt;

#[test]
fn candidate_budget_is_reserved_before_construction() {
    let mut exact = OpaqueDtConstructionBudget::with_limit(1024 * 272);
    assert!(exact.charge_candidate(0));
    assert!(!exact.charge_candidate(0));
    assert!(exact.exhausted());
}

#[test]
fn ground_clone_budget_fails_closed_at_exact_value_boundary() {
    let value = ModelValue::Datatype {
        ctor: "x".repeat(256),
        args: Vec::new(),
    };
    let mut exact = OpaqueDtConstructionBudget::with_limit(257);
    assert!(exact.charge_value(&value));
    assert!(!exact.charge_value(&value));
    assert!(exact.exhausted());
}

#[test]
fn canonical_string_clone_has_a_separate_exact_byte_charge() {
    let mut exact = OpaqueDtConstructionBudget::with_limit(8);
    assert!(exact.charge_bytes(8));
    assert!(!exact.charge_bytes(1));
    assert!(exact.exhausted());
}

#[test]
fn canonical_render_is_charged_before_allocation_at_exact_length() {
    let value = ModelValue::Datatype {
        ctor: "K".to_string(),
        args: vec![ModelValue::Bool(false)],
    };
    let mut exact = OpaqueDtConstructionBudget::with_limit(9);
    assert!(exact.charge_render(&value));
    assert!(!exact.charge_bytes(1));
}

#[test]
fn distinct_collection_counts_raw_arity_and_aggregate_pairs() {
    let mut oversized = OpaqueDtCollectionBudget::new();
    assert!(!oversized.record_distinct(1025));

    let mut aggregate = OpaqueDtCollectionBudget::new();
    assert!(aggregate.record_distinct(1024));
    assert!(
        !aggregate.record_distinct(1024),
        "the second raw 1024-ary atom must not hide behind repeated term IDs"
    );
    assert!(aggregate.finish(1, 0, 0, 1).is_none());
}

#[test]
fn field_selector_scan_is_precharged_multiplicatively() {
    let mut exact = OpaqueDtConstructionBudget::with_limit(4 * 3 * 272);
    assert!(exact.charge_field_scans(4, 2, 1));
    assert!(!exact.charge_field_scans(1, 1, 0));
}

#[test]
fn malformed_bitvector_payload_declines_before_clone() {
    let huge = EvalValue::BitVec {
        value: BigInt::from(1u8) << 1024,
        width: 1,
    };
    assert!(eval_to_mv(&huge, &Sort::bitvec(1)).is_none());

    let negative = EvalValue::BitVec {
        value: BigInt::from(-1),
        width: 8,
    };
    assert!(eval_to_mv(&negative, &Sort::bitvec(8)).is_none());
}
