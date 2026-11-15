// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Public native getters must return the complete witness in either order.

use super::*;
use crate::api::{Logic, ModelValue as NativeValue, Solver};
use std::time::Duration;

enum FirstGetter {
    NamedValues,
    WholeModel,
}

fn checker_value(value: NativeValue) -> ModelValue {
    match value {
        NativeValue::BitVec { value, width } => ModelValue::BitVec { value, width },
        NativeValue::Array { default, stores } => array(
            checker_value(*default),
            stores
                .into_iter()
                .map(|(key, value)| (checker_value(key), checker_value(value)))
                .collect(),
        ),
        NativeValue::Datatype { constructor, args } => ModelValue::Datatype {
            ctor: constructor,
            args: args.into_iter().map(checker_value).collect(),
        },
        other => panic!("expected fully typed nested witness, got {other:?}"),
    }
}

fn public_sort() -> Sort {
    let row = Sort::Datatype(DatatypeSort::new(
        "Row",
        vec![DatatypeConstructor::new(
            "row",
            vec![
                DatatypeField::new("len", Sort::bitvec(64)),
                DatatypeField::new("data", Sort::array(Sort::bitvec(64), Sort::bitvec(8))),
            ],
        )],
    ));
    Sort::Datatype(DatatypeSort::new(
        "Outer",
        vec![DatatypeConstructor::new(
            "outer",
            vec![DatatypeField::new(
                "rows",
                Sort::array(Sort::bitvec(64), row),
            )],
        )],
    ))
}

#[test]
#[ntest::timeout(20_000)]
fn named_values_and_native_whole_model_are_complete_in_both_orders() {
    let checker = ClosedEquality::new(&expected());
    let sort = public_sort();
    let source = format!("{DECLARATIONS}(declare-const v Outer)(assert (= v {WITNESS}))");
    for first in [FirstGetter::NamedValues, FirstGetter::WholeModel] {
        let mut solver = Solver::try_new(Logic::All).unwrap();
        solver.set_term_memory_limit(Some(64 * 1024 * 1024));
        solver.parse_smtlib2(&source).unwrap();
        assert!(solver.declared_variables().next().is_none());
        assert!(solver
            .try_check_sat_with_timeout(Duration::from_secs(5))
            .unwrap()
            .is_sat());
        let (named, model) = match first {
            FirstGetter::NamedValues => {
                let named = solver.try_get_named_values(&["v", "v"]).unwrap();
                (named, solver.try_get_model_str().unwrap())
            }
            FirstGetter::WholeModel => {
                let model = solver.try_get_model_str().unwrap();
                (solver.try_get_named_values(&["v", "v"]).unwrap(), model)
            }
        };
        assert_eq!(named.len(), 2);
        let literal = model_binding(&model, "v");
        let decoded = NativeValue::decode_typed_literals(&[(&literal, &sort)]).unwrap();
        assert_eq!(decoded.len(), 1);
        for value in named.into_iter().chain(decoded) {
            let verdict = checker.check(checker_value(value));
            assert!(matches!(verdict, GateVerdict::ConfirmedSat), "{verdict:?}");
        }
    }
}
