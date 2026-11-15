// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

type Binary = fn(Expr, Expr) -> ExprValue;

fn translation(operation: Binary, left: Expr, right: Expr, sort: Sort) -> Expr {
    raw(operation(left, right), sort)
}

fn read_at(at: Expr) -> Expr {
    boolean(ExprValue::Select {
        array: array("a", Sort::bool()),
        index: at,
    })
}

fn guarded(equality: Expr, upper: u64) -> Expr {
    index()
        .bvult(Expr::bitvec_const(upper, 64))
        .implies(equality)
}

fn retain_index(at: Expr) {
    for upper in [0, 2] {
        retained(guarded(read_at(at.clone()).eq(Expr::true_()), upper));
    }
}

#[test]
fn translated_result_and_binder_metadata_must_match_the_declared_width() {
    for operation in [ExprValue::BvAdd as Binary, ExprValue::BvSub] {
        for sort in [Sort::bool(), Sort::int(), Sort::bitvec(32)] {
            for reverse in [false, true] {
                let binder = index();
                let offset = Expr::bitvec_const(3, 64);
                let (left, right) = if reverse {
                    (offset, binder)
                } else {
                    (binder, offset)
                };
                retain_index(translation(operation, left, right, sort.clone()));
            }
        }
        for sort in [Sort::bool(), Sort::int(), Sort::bitvec(32)] {
            for reverse in [false, true] {
                let binder = Expr::var("i", sort.clone());
                let offset = Expr::bitvec_const(3, 64);
                let (left, right) = if reverse {
                    (offset, binder)
                } else {
                    (binder, offset)
                };
                retain_index(translation(operation, left, right, Sort::bitvec(64)));
            }
        }
    }
}

#[test]
fn translated_offsets_require_matching_canonical_literal_or_variable_metadata() {
    let literal = |value: BigInt, payload_width, sort| {
        raw(
            ExprValue::BitVecConst {
                value,
                width: payload_width,
            },
            sort,
        )
    };
    let offsets = [
        Expr::var("o", Sort::bool()),
        Expr::var("o", Sort::bitvec(32)),
        raw(ExprValue::BoolConst(true), Sort::bitvec(64)),
        literal(BigInt::from(-1), 64, Sort::bitvec(64)),
        literal(BigInt::from(1u8) << 64usize, 64, Sort::bitvec(64)),
        literal(BigInt::from(3), 63, Sort::bitvec(64)),
        literal(BigInt::from(3), 64, Sort::bitvec(63)),
        literal(BigInt::from(3), 64, Sort::bool()),
    ];
    for operation in [ExprValue::BvAdd as Binary, ExprValue::BvSub] {
        for offset in &offsets {
            retain_index(translation(
                operation,
                index(),
                offset.clone(),
                Sort::bitvec(64),
            ));
            retain_index(translation(
                operation,
                offset.clone(),
                index(),
                Sort::bitvec(64),
            ));
        }
    }
}

#[test]
fn translation_requires_exactly_one_binder_and_one_noncompound_offset() {
    let offset = Expr::var("o", Sort::bitvec(64));
    let zero = Expr::bitvec_const(0, 64);
    let nested = translation(
        ExprValue::BvAdd,
        offset.clone(),
        zero.clone(),
        Sort::bitvec(64),
    );
    let nested_binder = translation(ExprValue::BvSub, index(), zero.clone(), Sort::bitvec(64));
    for operation in [ExprValue::BvAdd as Binary, ExprValue::BvSub] {
        for (left, right) in [
            (index(), index()),
            (offset.clone(), zero.clone()),
            (index(), nested.clone()),
            (nested.clone(), index()),
            (nested_binder.clone(), offset.clone()),
            (offset.clone(), nested_binder.clone()),
        ] {
            retain_index(translation(operation, left, right, Sort::bitvec(64)));
        }
    }
    for operation in [ExprValue::BvMul as Binary, ExprValue::BvXor] {
        retain_index(translation(
            operation,
            index(),
            offset.clone(),
            Sort::bitvec(64),
        ));
    }
    let read_offset = array("offsets", Sort::bitvec(64)).select(zero);
    retain_index(translation(
        ExprValue::BvAdd,
        index(),
        read_offset,
        Sort::bitvec(64),
    ));
}

#[test]
fn translated_reads_still_authenticate_array_and_result_metadata() {
    let translated = index().bvadd(Expr::bitvec_const(1, 64));
    for base in [
        array("a", Sort::bitvec(8)),
        Expr::var("a", Sort::array(Sort::bitvec(32), Sort::bool())),
        Expr::var("a", Sort::bool()),
    ] {
        let read = boolean(ExprValue::Select {
            array: base,
            index: translated.clone(),
        });
        retained(guarded(read.eq(Expr::true_()), 2));
    }
    let read = raw(
        ExprValue::Select {
            array: array("a", Sort::bool()),
            index: translated,
        },
        Sort::bitvec(8),
    );
    retained(guarded(read.eq(Expr::bitvec_const(0, 8)), 2));
}

#[test]
fn offset_name_conflicts_are_rejected_even_in_empty_support_and_both_orders() {
    for upper in [0, 2] {
        let at = index().bvadd(Expr::var("a", Sort::bitvec(64)));
        retained(guarded(read_at(at).eq(Expr::true_()), upper));

        let at = index().bvsub(Expr::var("o", Sort::bitvec(64)));
        let first = guarded(read_at(at).eq(Expr::true_()), upper);
        for sort in [Sort::bool(), Sort::bitvec(8)] {
            let conflicting = guarded(
                array("b", sort.clone())
                    .select(index())
                    .eq(Expr::var("o", sort)),
                upper,
            );
            retained(boolean(ExprValue::And(vec![
                first.clone(),
                conflicting.clone(),
            ])));
            retained(boolean(ExprValue::And(vec![conflicting, first.clone()])));
        }
    }
}

#[test]
fn compatible_offset_names_can_be_shared_with_other_reads_and_scalar_fills() {
    let offset = Expr::var("o", Sort::bitvec(64));
    let first = guarded(
        array("a", Sort::bitvec(64))
            .select(index().bvadd(offset.clone()))
            .eq(offset.clone()),
        2,
    );
    let second = guarded(
        array("b", Sort::bitvec(64))
            .select(offset.clone().bvsub(index()))
            .eq(offset),
        0,
    );
    let result = quantify(boolean(ExprValue::And(vec![first, second])));
    assert!(matches!(result.value(), ExprValue::And(args) if args.len() == 2));
}

#[test]
fn a_later_invalid_translation_preserves_the_whole_original_body_and_triggers() {
    let valid = guarded(
        read_at(index().bvadd(Expr::bitvec_const(3, 64))).eq(Expr::true_()),
        2,
    );
    let invalid = guarded(read_at(index().bvsub(index())).eq(Expr::true_()), 0);
    let body = boolean(ExprValue::And(vec![valid, invalid]));
    retained(body.clone());
    retained_with(
        vec![("i".to_owned(), Sort::bitvec(64))],
        body,
        vec![vec![read_at(index().bvadd(Expr::bitvec_const(3, 64)))]],
    );
    let retry = quantify(guarded(
        read_at(index().bvadd(Expr::bitvec_const(3, 64))).eq(Expr::true_()),
        2,
    ));
    assert!(matches!(retry.value(), ExprValue::And(args) if args.len() == 2));
}
