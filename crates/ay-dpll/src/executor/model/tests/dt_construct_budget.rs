// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boundary controls for opaque datatype construction work accounting.

use super::super::dt_construct::eval_to_mv;
use super::super::dt_construct_budget::{
    OpaqueDtCollectionBudget, OpaqueDtConstructionBudget, MAX_DT_FIELD_SCAN_COMPARISONS,
    MAX_DT_FIELD_SCAN_FIELDS, MAX_DT_FIELD_SCAN_ROWS,
};
use super::super::EvalValue;
use ay_core::Sort;
use ay_model_check::{ArrayValue, ModelValue};
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
fn canonical_render_charges_arrays_nested_in_datatypes() {
    let value = ModelValue::Datatype {
        ctor: "K".to_string(),
        args: vec![ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Bool(false),
            store: vec![(ModelValue::Bool(true), ModelValue::Bool(false))],
        }))],
    };
    let mut exact = OpaqueDtConstructionBudget::with_limit(29);
    assert!(exact.charge_render(&value));
    assert!(!exact.charge_bytes(1));

    let mut short = OpaqueDtConstructionBudget::with_limit(28);
    assert!(!short.charge_render(&value));
    assert!(short.exhausted());
}

#[test]
fn canonical_render_charges_escaped_strings_nested_in_arrays() {
    let value = ModelValue::Datatype {
        ctor: "K".to_string(),
        args: vec![ModelValue::Array(Box::new(ArrayValue {
            default: ModelValue::Str("\"\t\\u{61}".to_string()),
            store: Vec::new(),
        }))],
    };
    let mut exact = OpaqueDtConstructionBudget::with_limit(31);
    assert!(exact.charge_render(&value));
    assert!(!exact.charge_bytes(1));

    let mut short = OpaqueDtConstructionBudget::with_limit(30);
    assert!(!short.charge_render(&value));
    assert!(short.exhausted());
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
fn native_field_scan_budget_is_unconditional_and_aggregate() {
    let mut native = OpaqueDtConstructionBudget::new(0).expect("native budget exists");
    for _ in 0..(MAX_DT_FIELD_SCAN_COMPARISONS / MAX_DT_FIELD_SCAN_ROWS) {
        assert!(native.charge_field_scans(1, MAX_DT_FIELD_SCAN_ROWS, 0));
    }
    let remainder = MAX_DT_FIELD_SCAN_COMPARISONS % MAX_DT_FIELD_SCAN_ROWS;
    assert!(native.charge_field_scans(1, remainder, 0));
    assert!(!native.charge_field_scans(1, 1, 0));
    assert!(native.exhausted());

    let mut overflow = OpaqueDtConstructionBudget::new(0).expect("native budget exists");
    assert!(!overflow.charge_field_scans(usize::MAX, 2, 0));
    assert!(overflow.exhausted());

    let mut fields = OpaqueDtConstructionBudget::new(0).expect("native budget exists");
    assert!(fields.charge_field_scans(MAX_DT_FIELD_SCAN_FIELDS, 0, 0));
    assert!(!fields.charge_field_scans(MAX_DT_FIELD_SCAN_FIELDS + 1, 0, 0));

    let mut rows = OpaqueDtConstructionBudget::new(0).expect("native budget exists");
    assert!(rows.charge_field_scans(0, MAX_DT_FIELD_SCAN_ROWS, 0));
    assert!(!rows.charge_field_scans(0, MAX_DT_FIELD_SCAN_ROWS + 1, 0));
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

/// The pair envelope counts pair visits, not identifier bytes. A model-checker-consumer BMC
/// query with 35 selector and 20 constructor terms (785 pairs) fit while its
/// longest application spelling weighed 19 and was refused at 20, when the
/// datatype's name grew by one byte (`Option_u8` to `OptionX_u8`): datatype
/// construction did not run, the model gate could not confirm the candidate,
/// and the satisfiable query came back `unknown`.
#[test]
fn congruence_pair_envelope_counts_pairs_not_name_bytes() {
    for weight in [19, 20, 64] {
        let mut budget = OpaqueDtCollectionBudget::new();
        assert!(
            budget.finish(4, 35, 20, weight).is_some(),
            "785 pairs fit the pair envelope at weight {weight}"
        );
    }
}

/// The byte-weighted congruence cost still has a bound: the work envelope.
#[test]
fn congruence_name_bytes_are_charged_to_the_work_envelope() {
    // 785 pairs * 64 rounds = 50,240 visits; at weight 1,000 that is 50.24M of
    // work, over the 32 MiB collection work envelope.
    let mut heavy = OpaqueDtCollectionBudget::new();
    assert!(heavy.finish(4, 35, 20, 1_000).is_none());
}

/// Too many pairs are refused at any weight.
#[test]
fn congruence_pair_envelope_refuses_too_many_pairs() {
    // 200 constructor terms: 19,900 pairs * 64 rounds = 1,273,600 visits.
    let mut wide = OpaqueDtCollectionBudget::new();
    assert!(wide.finish(4, 0, 200, 1).is_none());
    // 176 constructor terms: 15,400 pairs * 64 = 985,600 visits fit.
    let mut fits = OpaqueDtCollectionBudget::new();
    assert!(fits.finish(4, 0, 176, 1).is_some());
}
