// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::SmtValue;
use num_bigint::BigUint;

#[test]
fn wide_free_state_and_small_universal_binders_have_separate_boundaries() {
    for width in [65, 72, 127, 128, 129, 136, 256, crate::MAX_BITVECTOR_WIDTH] {
        let value = if width >= 128 {
            u128::MAX
        } else {
            1u128 << (width - 1)
        };
        let matrix = op(
            ChcOp::Eq,
            vec![var("wide_state", bv(width)), ChcExpr::BitVec(value, width)],
        );
        let source = standalone(vec![premise("i", 64, matrix)]).unwrap();
        let script = source.source_smtlib();
        assert!(script.contains(&format!("(wide_state (_ BitVec {width}))")));
        assert!(script.contains(&format!("(_ bv{value} {width})")));
        assert!(script.contains("(forall ((i (_ BitVec 64)))"));
        assert!(standalone(vec![premise("wide_binder", width, ChcExpr::Bool(true))]).is_err());
    }
}

#[test]
fn full_136_bit_keys_preserve_high_chunks_and_source_store_order() {
    let key = op(
        ChcOp::BvConcat,
        vec![ChcExpr::BitVec(128, 8), ChcExpr::BitVec(u128::MAX, 128)],
    );
    let low = op(
        ChcOp::BvConcat,
        vec![ChcExpr::BitVec(0, 8), ChcExpr::BitVec(u128::MAX, 128)],
    );
    let environment = ay_core::kani_compat::DetHashMap::default();
    let expected = (BigUint::from(128u8) << 128usize) + BigUint::from(u128::MAX);
    assert_eq!(
        crate::expr::evaluate_expr(&key, &environment),
        Some(SmtValue::BigBitVec(Arc::new(expected), 136))
    );
    let table = ChcExpr::ConstArray(bv(136), Arc::new(ChcExpr::BitVec(0, 8)));
    let table = op(
        ChcOp::Store,
        vec![table, low.clone(), ChcExpr::BitVec(7, 8)],
    );
    let table = op(
        ChcOp::Store,
        vec![table, key.clone(), ChcExpr::BitVec(9, 8)],
    );
    for (index, expected) in [(low, 7), (key, 9)] {
        let read = op(ChcOp::Select, vec![table.clone(), index]);
        assert_eq!(
            crate::expr::evaluate_expr(&read, &environment),
            Some(SmtValue::BitVec(expected, 8))
        );
        let matrix = op(ChcOp::Eq, vec![read, ChcExpr::BitVec(expected, 8)]);
        let source = standalone(vec![premise("i", 64, matrix)]).unwrap();
        assert!(source
            .source_smtlib()
            .contains("(Array (_ BitVec 136) (_ BitVec 8))"));
        assert_eq!(source.source_smtlib().matches("(store ").count(), 2);
    }
}

#[test]
fn oversized_intermediate_widths_refuse_even_beneath_a_false_constraint() {
    for expression in [
        ChcExpr::BitVec(0, crate::MAX_BITVECTOR_WIDTH + 1),
        op(
            ChcOp::BvZeroExtend(crate::MAX_BITVECTOR_WIDTH),
            vec![ChcExpr::BitVec(0, 1)],
        ),
        op(ChcOp::BvRepeat(u32::MAX), vec![ChcExpr::BitVec(0, 136)]),
        op(
            ChcOp::BvConcat,
            vec![
                var("x", bv(crate::MAX_BITVECTOR_WIDTH)),
                ChcExpr::BitVec(0, 1),
            ],
        ),
    ] {
        let equality = op(ChcOp::Eq, vec![expression.clone(), expression]);
        let matrix = op(ChcOp::And, vec![ChcExpr::Bool(false), equality]);
        assert!(standalone(vec![premise("i", 64, matrix)]).is_err());
    }
    for (value, width) in [(2u128, 1), (u128::MAX, 127)] {
        let bad = ChcExpr::BitVec(value, width);
        assert!(standalone(vec![premise(
            "i",
            64,
            op(ChcOp::Eq, vec![bad.clone(), bad])
        )])
        .is_err());
    }
}

#[test]
fn wide_unused_declarations_consume_the_shared_source_allowance() {
    let mut declarations = ChcProblem::new();
    for index in 0..129 {
        declarations.declare_predicate(
            format!("unused_{index}"),
            vec![bv(crate::MAX_BITVECTOR_WIDTH)],
        );
    }
    assert!(
        QuantifiedChcProblem::new(declarations, vec![query(ChcExpr::Bool(true), vec![])],).is_err()
    );
}

#[test]
fn computed_wide_results_share_the_declaration_payload_ledger() {
    let expanded = op(
        ChcOp::BvZeroExtend(crate::MAX_BITVECTOR_WIDTH - 1),
        vec![ChcExpr::BitVec(0, 1)],
    );
    let equality = op(ChcOp::Eq, vec![expanded.clone(), expanded]);
    assert!(standalone(vec![premise("i", 64, equality.clone())]).is_ok());
    // No wide declaration or leaf exists: only indexed result sorts account
    // for these 130 million-bit occurrences in a small source expression.
    let matrix = op(ChcOp::And, vec![equality; 65]);
    assert!(standalone(vec![premise("i", 64, matrix)]).is_err());
}
