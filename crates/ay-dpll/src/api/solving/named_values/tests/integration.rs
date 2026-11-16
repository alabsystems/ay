// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::time::Duration;

fn word(value: u64, width: u32) -> ModelValue {
    ModelValue::BitVec {
        value: value.into(),
        width,
    }
}

fn array(default: ModelValue, stores: Vec<(ModelValue, ModelValue)>) -> ModelValue {
    ModelValue::Array {
        default: Box::new(default),
        stores,
    }
}

fn record(name: &str, args: Vec<ModelValue>) -> ModelValue {
    ModelValue::Datatype {
        constructor: name.into(),
        args,
    }
}

#[test]
#[ntest::timeout(10_000)]
fn public_named_values_extract_parsed_scalars_and_reject_stale_models() {
    let mut solver = parsed(
        "(declare-const |x with space| Int)(declare-const y Int)
         (assert (= |x with space| 7))(assert (= y 9))",
    );
    assert!(solver.declared_variables().next().is_none());
    assert!(solver
        .try_check_sat_with_timeout(Duration::from_secs(2))
        .unwrap()
        .is_sat());
    let size = solver.terms().len();
    assert_eq!(
        solver
            .try_get_named_values(&["y", "x with space", "y"])
            .unwrap(),
        vec![
            ModelValue::Int(9.into()),
            ModelValue::Int(7.into()),
            ModelValue::Int(9.into())
        ]
    );
    assert_eq!(solver.terms().len(), size);
    assert_eq!(
        solver.try_get_named_values(&[]).unwrap(),
        [] as [ModelValue; 0]
    );
    assert!(solver.try_get_named_values(&["y", "missing"]).is_err());
    solver.parse_smtlib2("(assert false)").unwrap();
    assert!(matches!(
        solver.try_get_named_values(&["y"]),
        Err(SolverError::NoResult)
    ));
    assert!(solver
        .try_check_sat_with_timeout(Duration::from_secs(2))
        .unwrap()
        .is_unsat());
    assert!(matches!(
        solver.try_get_named_values(&["y"]),
        Err(SolverError::NotSat)
    ));
}

#[test]
#[ntest::timeout(20_000)]
fn public_named_values_keep_complete_nested_record_arrays_and_far_stores() {
    let solver_text = "
        (declare-datatype Row ((row (len (_ BitVec 64))
          (data (Array (_ BitVec 64) (_ BitVec 8))))))
        (declare-datatype Outer ((outer (rows (Array (_ BitVec 64) Row)))))
        (declare-const v Outer)
        (assert (= v (outer (store ((as const (Array (_ BitVec 64) Row))
          (row (_ bv0 64) ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)))
          (_ bv33 64)
          (row (_ bv65 64) (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07)
                                (_ bv64 64) #x09))))))";
    let mut solver = parsed(solver_text);
    assert!(solver.declared_variables().next().is_none());
    assert!(solver
        .try_check_sat_with_timeout(Duration::from_secs(5))
        .unwrap()
        .is_sat());
    let size = solver.terms().len();
    let empty = record("row", vec![word(0, 64), array(word(0, 8), vec![])]);
    let changed = record(
        "row",
        vec![
            word(65, 64),
            array(word(7, 8), vec![(word(64, 64), word(9, 8))]),
        ],
    );
    assert_eq!(
        solver.try_get_named_values(&["v"]).unwrap(),
        vec![record(
            "outer",
            vec![array(empty, vec![(word(33, 64), changed)])]
        )]
    );
    assert_eq!(solver.terms().len(), size);
}
