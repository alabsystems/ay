// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

//! Producer-shaped controls, not executed MODEL_CHECKER_CONSUMER harness results.
//!
//! MODEL_CHECKER_CONSUMER 22278991c4d8e73189117c1f601ca1f4a89d6054:
//! model-checker-consumer-compiler/src/codegen_ay/chc/call/codegen_call_slice_helpers.rs,
//! build_precise_slice_eq (lines 742–762), constructs offset+i on both reads.
//! A fixed &[u32; 4] supplies literal length four and zero backing offsets.
//! Nonzero/subtraction/wraparound cases below are explicit metamorphic controls.

use super::*;

#[derive(Clone, Copy, Debug)]
enum Translation {
    IndexPlusOffset,
    OffsetPlusIndex,
    IndexMinusOffset,
    OffsetMinusIndex,
}

const TRANSLATIONS: [Translation; 4] = [
    Translation::IndexPlusOffset,
    Translation::OffsetPlusIndex,
    Translation::IndexMinusOffset,
    Translation::OffsetMinusIndex,
];

impl Translation {
    fn expression(self, offset: &Expr) -> Expr {
        match self {
            Self::IndexPlusOffset => index().bvadd(offset.clone()),
            Self::OffsetPlusIndex => offset.clone().bvadd(index()),
            Self::IndexMinusOffset => index().bvsub(offset.clone()),
            Self::OffsetMinusIndex => offset.clone().bvsub(index()),
        }
    }

    fn concrete(self, index: u64, offset: u64) -> u64 {
        match self {
            Self::IndexPlusOffset | Self::OffsetPlusIndex => index.wrapping_add(offset),
            Self::IndexMinusOffset => index.wrapping_sub(offset),
            Self::OffsetMinusIndex => offset.wrapping_sub(index),
        }
    }
}

fn bounded(consequent: Expr) -> Expr {
    quantify(index().bvult(Expr::bitvec_const(4, 64)).implies(consequent))
}

fn equalities(output: &Expr) -> &[Expr] {
    let ExprValue::And(items) = output.value() else {
        panic!("translated finite support was not normalized")
    };
    assert_eq!(items.len(), 4);
    items
}

fn sides(equality: &Expr) -> (&Expr, &Expr) {
    let ExprValue::Eq(left, right) = equality.value() else {
        panic!("ground equality")
    };
    (left, right)
}

fn read_parts(read: &Expr) -> (&Expr, &Expr) {
    let ExprValue::Select { array, index } = read.value() else {
        panic!("source read")
    };
    (array, index)
}

fn assert_translation(actual: &Expr, form: Translation, ordinal: usize, offset: &Expr) {
    assert_eq!(actual.sort().bitvec_width(), Some(64));
    let (left, right) = match (form, actual.value()) {
        (Translation::IndexPlusOffset | Translation::OffsetPlusIndex, ExprValue::BvAdd(a, b))
        | (Translation::IndexMinusOffset | Translation::OffsetMinusIndex, ExprValue::BvSub(a, b)) => {
            (a, b)
        }
        _ => panic!("source operator changed: {form:?}"),
    };
    let (ground, retained) = match form {
        Translation::IndexPlusOffset | Translation::IndexMinusOffset => (left, right),
        Translation::OffsetPlusIndex | Translation::OffsetMinusIndex => (right, left),
    };
    assert_eq!(ground, &Expr::bitvec_const(ordinal, 64));
    assert!(Arc::ptr_eq(&retained.value, &offset.value));
    assert_eq!(retained.sort(), offset.sort());
}

fn eval_index(expr: &Expr, offset: u64) -> u64 {
    assert_eq!(expr.sort().bitvec_width(), Some(64));
    match expr.value() {
        ExprValue::BitVecConst { value, width: 64 } => value.to_u64().unwrap(),
        ExprValue::Var { name } if name == "offset" => offset,
        ExprValue::BvAdd(a, b) => eval_index(a, offset).wrapping_add(eval_index(b, offset)),
        ExprValue::BvSub(a, b) => eval_index(a, offset).wrapping_sub(eval_index(b, offset)),
        _ => panic!("unexpected translated index"),
    }
}

fn scalar(expr: &Expr, offset: u64, read: &dyn Fn(&str, u64) -> BigInt) -> BigInt {
    match expr.value() {
        ExprValue::BoolConst(value) => BigInt::from(u8::from(*value)),
        ExprValue::BitVecConst { value, .. } => value.clone(),
        ExprValue::Select { array, index } => {
            let ExprValue::Var { name } = array.value() else {
                panic!("source array variable")
            };
            read(name, eval_index(index, offset))
        }
        _ => panic!("unexpected scalar output"),
    }
}

fn holds(output: &Expr, offset: u64, read: &dyn Fn(&str, u64) -> BigInt) -> bool {
    equalities(output).iter().all(|equality| {
        let (left, right) = sides(equality);
        scalar(left, offset, read) == scalar(right, offset, read)
    })
}

#[test]
fn fixed_four_u32_slice_equality_normalizes_the_actual_zero_plus_index_shape() {
    let a = array("A", Sort::bitvec(32));
    let b = array("B", Sort::bitvec(32));
    let zero = Expr::bitvec_const(0, 64);
    let form = Translation::OffsetPlusIndex;
    let output = bounded(
        a.clone()
            .select(form.expression(&zero))
            .eq(b.clone().select(form.expression(&zero))),
    );
    for (ordinal, equality) in equalities(&output).iter().enumerate() {
        let (left, right) = sides(equality);
        for (read, original) in [(left, &a), (right, &b)] {
            let (source, translated) = read_parts(read);
            assert!(Arc::ptr_eq(&source.value, &original.value));
            assert_eq!(read.sort(), &Sort::bitvec(32));
            assert_translation(translated, form, ordinal, &zero);
        }
    }
    for tail in [0, u32::MAX] {
        assert!(holds(&output, 0, &|name, slot| {
            BigInt::from(if name == "B" && slot >= 4 {
                u64::from(tail)
            } else {
                slot & u64::from(u32::MAX)
            })
        }));
    }
    assert!(!holds(&output, 0, &|name, slot| {
        BigInt::from(if name == "B" && slot == 3 {
            9
        } else {
            slot & u64::from(u32::MAX)
        })
    }));
}

#[test]
fn every_literal_and_free_offset_orientation_retains_source_syntax_and_arc_identity() {
    for offset in [
        Expr::bitvec_const(19, 64),
        Expr::var("offset", Sort::bitvec(64)),
    ] {
        for form in TRANSLATIONS {
            let output = bounded(
                array("A", Sort::bool())
                    .select(form.expression(&offset))
                    .eq(Expr::true_()),
            );
            for (ordinal, equality) in equalities(&output).iter().enumerate() {
                let (read, _) = sides(equality);
                let (_, actual) = read_parts(read);
                assert_translation(actual, form, ordinal, &offset);
                assert_eq!(eval_index(actual, 19), form.concrete(ordinal as u64, 19));
            }
        }
    }
}

#[test]
fn two_source_arrays_keep_independent_offsets_and_only_their_requested_cells() {
    let left = Translation::OffsetPlusIndex;
    let right = Translation::OffsetMinusIndex;
    let five = Expr::bitvec_const(5, 64);
    let seventeen = Expr::bitvec_const(17, 64);
    let output = bounded(
        array("A", Sort::bitvec(32))
            .select(left.expression(&five))
            .eq(array("B", Sort::bitvec(32)).select(right.expression(&seventeen))),
    );
    for (ordinal, equality) in equalities(&output).iter().enumerate() {
        let (a, b) = sides(equality);
        assert_translation(read_parts(a).1, left, ordinal, &five);
        assert_translation(read_parts(b).1, right, ordinal, &seventeen);
    }
    let value = |name: &str, slot: u64| {
        BigInt::from(match name {
            "A" if (5..9).contains(&slot) => slot - 5,
            "B" if (14..18).contains(&slot) => 17 - slot,
            "A" => 31,
            "B" => 99,
            _ => panic!("source name"),
        })
    };
    assert!(holds(&output, 0, &value));
    assert!(!holds(&output, 0, &|name, slot| {
        if name == "B" && slot == 14 {
            BigInt::from(0)
        } else {
            value(name, slot)
        }
    }));
}

fn assert_fill_support(form: Translation, fill: &Expr, offset_value: u64) {
    let offset = Expr::var("offset", Sort::bitvec(64));
    let a = array("A", fill.sort().clone());
    let output = bounded(a.clone().select(form.expression(&offset)).eq(fill.clone()));
    let required: Vec<_> = (0..4).map(|i| form.concrete(i, offset_value)).collect();
    let tail = form.concrete(4, offset_value);
    assert!(!required.contains(&tail));
    let expected = scalar(fill, offset_value, &|_, _| panic!("scalar fill"));
    let wrong = BigInt::from(u8::from(expected == BigInt::from(0)));
    for (ordinal, equality) in equalities(&output).iter().enumerate() {
        let (read, actual_fill) = sides(equality);
        assert!(Arc::ptr_eq(&actual_fill.value, &fill.value));
        assert!(Arc::ptr_eq(&read_parts(read).0.value, &a.value));
        assert_translation(read_parts(read).1, form, ordinal, &offset);
        assert_eq!(read.sort(), fill.sort());
    }
    for tail_value in [&expected, &wrong] {
        assert!(holds(&output, offset_value, &|_, slot| {
            if required.contains(&slot) {
                expected.clone()
            } else if slot == tail {
                tail_value.clone()
            } else {
                wrong.clone()
            }
        }));
    }
    assert!(!holds(&output, offset_value, &|_, slot| {
        if slot == required[3] {
            wrong.clone()
        } else {
            expected.clone()
        }
    }));
}

#[test]
fn translated_bool_and_wide_bv_fills_preserve_exact_values_and_unconstrained_tails() {
    let high = Expr::bitvec_const((BigInt::from(1u8) << 128usize) + 17, 129);
    for fill in [Expr::false_(), Expr::true_(), high] {
        for form in TRANSLATIONS {
            assert_fill_support(form, &fill, 23);
        }
    }
}

#[test]
fn high_u64_wraparound_remains_bv_add_sub_syntax_not_unbounded_integer_indices() {
    for offset in [1, u64::MAX - 1, u64::MAX] {
        for form in TRANSLATIONS {
            let literal = Expr::bitvec_const(offset, 64);
            let output = bounded(
                array("A", Sort::bool())
                    .select(form.expression(&literal))
                    .eq(Expr::true_()),
            );
            let expected: Vec<_> = (0..4).map(|i| form.concrete(i, offset)).collect();
            for (ordinal, equality) in equalities(&output).iter().enumerate() {
                let (read, _) = sides(equality);
                let actual = read_parts(read).1;
                assert_translation(actual, form, ordinal, &literal);
                assert_eq!(eval_index(actual, 0), expected[ordinal]);
            }
            assert!(holds(&output, 0, &|_, slot| BigInt::from(u8::from(
                expected.contains(&slot)
            ))));
            assert!(!holds(&output, 0, &|_, slot| BigInt::from(u8::from(
                slot != expected[3]
            ))));
        }
    }
}
