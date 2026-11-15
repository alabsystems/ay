// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn vector() -> ModelValue {
    let bv = |value, width| ModelValue::bitvec(BigInt::from(value), width);
    ModelValue::Datatype {
        ctor: "mkVec_bv40".into(),
        args: vec![
            bv(0, 64),
            bv(65, 64),
            bv(66, 64),
            ModelValue::Array(Box::new(ArrayValue {
                default: bv(9, 40),
                store: vec![(bv(33, 64), bv(4, 40)), (bv(33, 64), bv(5, 40))],
            })),
        ],
    }
}

#[test]
fn complete_record_clone_equality_preserves_array_pins_with_shared_headroom() {
    let original = vector();
    let clone = original.clone();
    let mut budget = WitnessBudget {
        value_work: 1000,
        ..WitnessBudget::default()
    };
    assert_eq!(compare(&original, &clone, &mut budget), Some(true));
    let (ModelValue::Datatype { args: left, .. }, ModelValue::Datatype { args: right, .. }) =
        (&original, &clone)
    else {
        panic!("vector values");
    };
    // A separately retained array ancestor must agree as well. The unchanged
    // whole-array semantic comparator still accounts the full product.
    assert_eq!(compare(&left[3], &right[3], &mut budget), Some(true));
    assert!(budget.value_work < MAX_WITNESS_VALUE_WORK);

    let mut conflict = original.clone();
    let ModelValue::Datatype { args, .. } = &mut conflict else {
        panic!("vector");
    };
    args[1] = ModelValue::bitvec(BigInt::from(1u8) << 63, 64);
    assert_eq!(
        compare(&original, &conflict, &mut WitnessBudget::default()),
        Some(false)
    );
    assert!(matches!(value_eq(&original, &conflict), Ok(false)));
}

#[test]
fn componentwise_comparison_preserves_shape_and_undecidable_results() {
    let record = vector();
    let mut different_ctor = record.clone();
    let ModelValue::Datatype { ctor, .. } = &mut different_ctor else {
        panic!("vector");
    };
    *ctor = "other".into();
    let mut different_arity = record.clone();
    let ModelValue::Datatype { args, .. } = &mut different_arity else {
        panic!("vector");
    };
    args.pop();
    let seq = ModelValue::Seq(vec![record.clone(), ModelValue::Bool(true)]);
    let same_seq = seq.clone();
    let shorter = ModelValue::Seq(vec![record.clone()]);
    let mixed = ModelValue::Seq(vec![record.clone(), ModelValue::Int(BigInt::from(1))]);
    for (left, right) in [
        (&record, &different_ctor),
        (&record, &different_arity),
        (&seq, &shorter),
        (&record, &seq),
        (&seq, &mixed),
        (&seq, &same_seq),
    ] {
        assert_eq!(
            compare(left, right, &mut WitnessBudget::default()),
            value_eq(left, right).ok(),
        );
    }
}

#[test]
fn record_comparison_keeps_exact_preflight_and_refuses_a_short_shared_allowance() {
    let record = vector();
    let clone = record.clone();
    let mut measured = WitnessBudget::default();
    assert_eq!(compare(&record, &clone, &mut measured), Some(true));
    for extra in [0, 1] {
        let mut budget = WitnessBudget {
            value_work: MAX_WITNESS_VALUE_WORK - measured.value_work + extra,
            ..WitnessBudget::default()
        };
        assert_eq!(
            compare(&record, &clone, &mut budget),
            (extra == 0).then_some(true)
        );
    }
    // A mismatching constructor does not bypass complete payload admission.
    let malformed = ModelValue::Datatype {
        ctor: "different".into(),
        args: vec![ModelValue::Str("x".repeat(MAX_WITNESS_VALUE_WORK))],
    };
    assert_eq!(
        compare(&record, &malformed, &mut WitnessBudget::default()),
        None
    );
    assert_eq!(
        compare(&record, &clone, &mut WitnessBudget::default()),
        Some(true)
    );
}
