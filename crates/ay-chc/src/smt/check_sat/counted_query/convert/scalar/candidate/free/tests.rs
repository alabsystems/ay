// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::check_sat::counted_query::convert::scalar::tests::{
    ample, convert, model as sat_model, op, owner, var,
};
use std::sync::Arc;

mod mutations;
mod refusals;
mod resources;
mod semantics;

fn array(name: &str, key: ChcSort, value: ChcSort) -> ChcExpr {
    var(name, ChcSort::Array(Box::new(key), Box::new(value)))
}

fn select(array: ChcExpr, index: ChcExpr) -> ChcExpr {
    op(ChcOp::Select, vec![array, index])
}

fn eq(left: ChcExpr, right: ChcExpr) -> ChcExpr {
    op(ChcOp::Eq, vec![left, right])
}

fn boolean_source() -> ChcExpr {
    let a = array("a", ChcSort::Bool, ChcSort::Bool);
    op(
        ChcOp::And,
        vec![
            eq(select(a.clone(), ChcExpr::Bool(false)), ChcExpr::Bool(true)),
            eq(select(a, ChcExpr::Bool(true)), ChcExpr::Bool(false)),
        ],
    )
}

fn sequence(source: &ChcExpr, original: &CountedAdmission) -> Result<()> {
    let mut built = convert(source, original)?;
    let result = built.with_scalar_encoding(|encoding| {
        let candidate = encoding.check_scalar_candidate(&sat_model(encoding))?;
        encoding.replay_scalar_candidate(&candidate)
    });
    built.finish()?;
    result
}

#[test]
fn zero_observation_arrays_have_typed_total_defaults_not_domain_enumeration() {
    let original = ample();
    for (index, element) in [
        (ScalarSort::Bool, ScalarSort::Bool),
        (ScalarSort::Bool, ScalarSort::BitVec(128)),
        (ScalarSort::BitVec(128), ScalarSort::Bool),
        (ScalarSort::BitVec(128), ScalarSort::BitVec(128)),
    ] {
        let model = Model {
            arrays: vec![Array::empty(TermId(7), index, element)],
            reads: Vec::new(),
        };
        assert!(model.arrays[0].cells.is_empty());
        let keys = match index {
            ScalarSort::Bool => vec![ScalarValue::Bool(false), ScalarValue::Bool(true)],
            ScalarSort::BitVec(width) => vec![
                ScalarValue::BitVec(0, width),
                ScalarValue::BitVec(1u128 << 127, width),
                ScalarValue::BitVec(u128::MAX, width),
            ],
        };
        for key in keys {
            assert_eq!(model.read(0, key, &original).unwrap(), zero(element));
        }
    }
    original.check().unwrap();
}

#[test]
fn duplicate_decoded_keys_are_deduplicated_only_when_values_agree() {
    let original = ample();
    let mut array = Array::empty(TermId(4), ScalarSort::BitVec(2), ScalarSort::Bool);
    let cell = ReadValue {
        index: ScalarValue::BitVec(1, 2),
        value: ScalarValue::Bool(true),
    };
    decode::insert(&mut array, cell, &original).unwrap();
    decode::insert(&mut array, cell, &original).unwrap();
    assert_eq!(array.cells.len(), 1);
    assert_eq!(
        decode::insert(
            &mut array,
            ReadValue {
                index: cell.index,
                value: ScalarValue::Bool(false),
            },
            &original
        ),
        Err(Error::InvalidCandidate)
    );
    assert_eq!(array.cells, vec![cell]);
    assert_eq!(
        decode::insert(
            &mut array,
            ReadValue {
                index: ScalarValue::BitVec(1, 3),
                value: cell.value,
            },
            &original
        ),
        Err(Error::InvalidCandidate)
    );
}
