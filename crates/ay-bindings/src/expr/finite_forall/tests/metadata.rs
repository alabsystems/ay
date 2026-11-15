// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn raw_bv(value: BigInt, literal_width: u32, sort_width: u32) -> Expr {
    raw(
        ExprValue::BitVecConst {
            value,
            width: literal_width,
        },
        Sort::bitvec(sort_width),
    )
}

#[test]
fn malformed_guard_literal_and_index_metadata_are_not_normalized() {
    for bound in [
        raw_bv(BigInt::from(-1), 64, 64),
        raw_bv(BigInt::from(1u8) << 64usize, 64, 64),
        raw_bv(BigInt::from(2), 63, 64),
        raw_bv(BigInt::from(2), 64, 63),
        raw(ExprValue::BoolConst(true), Sort::bitvec(64)),
    ] {
        let guard = boolean(ExprValue::BvULt(index(), bound));
        retained(guard.implies(array("a", Sort::bool()).select(index()).eq(Expr::true_())));
    }
    let guard = boolean(ExprValue::BvULt(
        Expr::var("i", Sort::bitvec(32)),
        Expr::bitvec_const(2, 64),
    ));
    retained(guard.implies(array("a", Sort::bool()).select(index()).eq(Expr::true_())));
}

#[test]
fn every_boolean_operator_must_have_boolean_metadata() {
    let guard = index().bvult(Expr::bitvec_const(2, 64));
    let equality = array("a", Sort::bool()).select(index()).eq(Expr::true_());
    let wrong_guard = Expr {
        sort: Sort::int(),
        value: Arc::clone(&guard.value),
    };
    let wrong_equality = Expr {
        sort: Sort::int(),
        value: Arc::clone(&equality.value),
    };
    retained(boolean(ExprValue::Implies(wrong_guard, equality)));
    retained(boolean(ExprValue::Implies(guard, wrong_equality)));
    let implication = bounded_equality(2);
    let wrong_implication = Expr {
        sort: Sort::int(),
        value: Arc::clone(&implication.value),
    };
    retained(boolean(ExprValue::And(vec![wrong_implication])));
    let wrong_and = raw(ExprValue::And(vec![bounded_equality(0)]), Sort::int());
    retained(boolean(ExprValue::And(vec![wrong_and])));
}

#[test]
fn select_result_index_and_element_sorts_are_all_authenticated() {
    let guard = index().bvult(Expr::bitvec_const(2, 64));
    let bases = [
        array("a", Sort::bitvec(8)),
        Expr::var("a", Sort::array(Sort::bitvec(32), Sort::bool())),
        Expr::var("a", Sort::bool()),
    ];
    for base in bases {
        let read = boolean(ExprValue::Select {
            array: base,
            index: index(),
        });
        retained(guard.clone().implies(read.eq(Expr::true_())));
    }
    let read = boolean(ExprValue::Select {
        array: array("a", Sort::bool()),
        index: Expr::var("i", Sort::bitvec(32)),
    });
    retained(guard.clone().implies(read.eq(Expr::true_())));
    let wrong_read = raw(
        ExprValue::Select {
            array: array("a", Sort::bool()),
            index: index(),
        },
        Sort::bitvec(8),
    );
    retained(guard.implies(wrong_read.eq(Expr::bitvec_const(0, 8))));
}

#[test]
fn malformed_scalar_metadata_and_noncanonical_values_are_retained() {
    let guard = index().bvult(Expr::bitvec_const(2, 64));
    let read = array("a", Sort::bitvec(8)).select(index());
    for value in [
        raw_bv(BigInt::from(-1), 8, 8),
        raw_bv(BigInt::from(256), 8, 8),
        raw_bv(BigInt::from(1), 7, 8),
        raw(ExprValue::BoolConst(true), Sort::bitvec(8)),
    ] {
        retained(guard.clone().implies(read.clone().eq(value)));
    }
    let boolean_read = array("a", Sort::bool()).select(index());
    let false_metadata = raw(
        ExprValue::BitVecConst {
            value: BigInt::from(0),
            width: 8,
        },
        Sort::bool(),
    );
    retained(guard.implies(boolean_read.eq(false_metadata)));
}

#[test]
fn incompatible_free_symbol_sorts_cannot_disappear_with_empty_support() {
    let empty = index().bvult(Expr::bitvec_const(0, 64));
    let bool_array = array("a", Sort::bool());
    retained(
        empty.clone().implies(
            bool_array
                .clone()
                .select(index())
                .eq(Expr::var("a", Sort::bool())),
        ),
    );
    let first = empty
        .clone()
        .implies(bool_array.select(index()).eq(Expr::true_()));
    let different_array = empty.clone().implies(
        array("a", Sort::bitvec(8))
            .select(index())
            .eq(Expr::bitvec_const(0, 8)),
    );
    retained(first.clone().and(different_array));
    let scalar_same_name = empty.clone().implies(
        array("b", Sort::bool())
            .select(index())
            .eq(Expr::var("a", Sort::bool())),
    );
    retained(first.and(scalar_same_name));
    let scalar_bool = empty.clone().implies(
        array("b", Sort::bool())
            .select(index())
            .eq(Expr::var("fill", Sort::bool())),
    );
    let scalar_bv = empty.implies(
        array("c", Sort::bitvec(8))
            .select(index())
            .eq(Expr::var("fill", Sort::bitvec(8))),
    );
    retained(scalar_bool.and(scalar_bv));
}
