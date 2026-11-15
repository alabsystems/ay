// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn table(width: u32, default: bool, bits: u128) -> Value {
    let mut value = Arc::new(BoolArray::constant(width, default).expect("valid width"));
    for index in 0..(1u128 << width) {
        value = value
            .store(index, bits & (1u128 << index) != 0, &mut Budget::new())
            .expect("small table");
    }
    Value::Array(value)
}

#[test]
fn exhaustive_bv1_bv2_tables_compare_by_total_function_not_default() {
    for width in [1, 2] {
        let tables = 1u128 << (1u32 << width);
        for left in 0..tables {
            for right in 0..tables {
                for left_default in [false, true] {
                    for right_default in [false, true] {
                        let a = table(width, left_default, left);
                        let b = table(width, right_default, right);
                        assert_eq!(
                            a.equivalent(&b, &mut Budget::new()).expect("comparison"),
                            left == right
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn differing_defaults_need_complete_union_coverage() {
    let a = evaluated(&store(
        array(1, false),
        ChcExpr::BitVec(0, 1),
        ChcExpr::Bool(true),
    ));
    let b = evaluated(&store(
        array(1, true),
        ChcExpr::BitVec(1, 1),
        ChcExpr::Bool(false),
    ));
    assert!(a.equivalent(&b, &mut Budget::new()).expect("BV1 equal"));
    let a = evaluated(&store(
        array(2, false),
        ChcExpr::BitVec(0, 2),
        ChcExpr::Bool(true),
    ));
    let b = evaluated(&store(
        array(2, true),
        ChcExpr::BitVec(1, 2),
        ChcExpr::Bool(false),
    ));
    assert!(!a
        .equivalent(&b, &mut Budget::new())
        .expect("BV2 uncovered indices differ"));
}

#[test]
fn newest_write_default_elision_and_index_modulus_preserve_values() {
    let a = store(
        store(array(2, false), ChcExpr::BitVec(7, 2), ChcExpr::Bool(true)),
        ChcExpr::BitVec(3, 2),
        ChcExpr::Bool(false),
    );
    assert!(evaluated(&a)
        .equivalent(&evaluated(&array(2, false)), &mut Budget::new())
        .expect("overwritten"));
    let a = store(
        store(array(2, false), ChcExpr::BitVec(1, 2), ChcExpr::Bool(true)),
        ChcExpr::BitVec(2, 2),
        ChcExpr::Bool(true),
    );
    let b = store(
        store(array(2, false), ChcExpr::BitVec(2, 2), ChcExpr::Bool(true)),
        ChcExpr::BitVec(1, 2),
        ChcExpr::Bool(true),
    );
    assert!(evaluated(&a)
        .equivalent(&evaluated(&b), &mut Budget::new())
        .expect("reordered"));
}

#[test]
fn every_supported_index_width_including_128_is_exact() {
    for width in 1..=128 {
        let index = ground::mask(width).expect("supported width");
        let expr = store(
            array(width, false),
            ChcExpr::BitVec(index, width),
            ChcExpr::Bool(true),
        );
        let value = evaluated(&expr);
        assert!(!value
            .equivalent(&evaluated(&array(width, false)), &mut Budget::new())
            .expect("different"));
        let roundtrip = value
            .to_expr(&mut Budget::new())
            .expect("bounded representation");
        assert!(value
            .equivalent(&evaluated(&roundtrip), &mut Budget::new())
            .expect("roundtrip"));
    }
}

#[test]
fn array_key_extract_concat_and_typed_scalar_pins_are_evaluated_exactly() {
    let concat = ChcExpr::Op(
        ChcOp::BvConcat,
        vec![
            Arc::new(ChcExpr::BitVec(0x42, 32)),
            Arc::new(ChcExpr::BitVec(0, 32)),
        ],
    );
    let index = ChcExpr::Op(ChcOp::BvExtract(63, 32), vec![Arc::new(concat)]);
    let actual = evaluated(&store(array(32, true), index, ChcExpr::Bool(false)));
    let expected = evaluated(&store(
        array(32, true),
        ChcExpr::BitVec(0x42, 32),
        ChcExpr::Bool(false),
    ));
    assert!(actual
        .equivalent(&expected, &mut Budget::new())
        .expect("same cell"));
}
