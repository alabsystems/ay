// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use crate::smt::check_sat::counted_query::convert::scalar::tests::{
    ample, convert, model, op, var,
};
use std::sync::Arc;

#[test]
fn independent_original_evaluation_rejects_false_source_without_read_assignments() {
    let array = ChcExpr::ConstArray(ChcSort::BitVec(2), Arc::new(ChcExpr::BitVec(1, 2)));
    let source = op(
        ChcOp::Eq,
        vec![
            op(ChcOp::Select, vec![array, ChcExpr::BitVec(3, 2)]),
            ChcExpr::BitVec(2, 2),
        ],
    );
    let mut built = convert(&source, &ample()).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            let variables = vec![None; encoding.cnf.terms().len()];
            let mut witness = free::Model::empty();
            witness.reads.push(free::ReadValue {
                index: ScalarValue::BitVec(3, 2),
                value: ScalarValue::BitVec(1, 2),
            });
            assert_eq!(
                original(encoding, &variables, &witness),
                Err(Error::InvalidCandidate)
            );
            Ok(())
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn distinct_symbolic_indices_with_equal_values_hit_the_same_original_store() {
    let array = ChcExpr::ConstArray(ChcSort::BitVec(2), Arc::new(ChcExpr::BitVec(0, 2)));
    let stored = op(
        ChcOp::Store,
        vec![array, var("i", ChcSort::BitVec(2)), ChcExpr::BitVec(2, 2)],
    );
    let source = op(
        ChcOp::And,
        vec![
            op(
                ChcOp::Eq,
                vec![var("i", ChcSort::BitVec(2)), var("j", ChcSort::BitVec(2))],
            ),
            op(
                ChcOp::Eq,
                vec![
                    op(ChcOp::Select, vec![stored, var("j", ChcSort::BitVec(2))]),
                    ChcExpr::BitVec(2, 2),
                ],
            ),
        ],
    );
    let mut built = convert(&source, &ample()).unwrap();
    built
        .with_scalar_encoding(|encoding| {
            let candidate = encoding.check_scalar_candidate(&model(encoding))?;
            encoding.replay_scalar_candidate(&candidate)
        })
        .unwrap();
    built.finish().unwrap();
}

#[test]
fn malformed_persistent_store_links_and_wrong_scalar_types_fail_closed() {
    let original = ample();
    let array = Array {
        shape: Type::Array(0, 0),
        contents: Contents::Store {
            base: 0,
            index: ScalarValue::Bool(false),
            value: ScalarValue::Bool(true),
        },
    };
    assert_eq!(
        read(
            &[array],
            0,
            ScalarValue::Bool(true),
            &free::Model::empty(),
            &original
        ),
        Err(Error::InvalidCandidate)
    );
    assert!(value_type(Value::Array(1), &[array]).is_err());
    assert_eq!(scalar_type(ScalarValue::BitVec(1, 128)), Type::BitVec(128));
    original.check().unwrap();
}
