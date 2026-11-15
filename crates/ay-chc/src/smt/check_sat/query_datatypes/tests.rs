// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ChcDtConstructor, ChcDtSelector, ChcOp, ChcVar};

mod solving;

fn datatype() -> ChcSort {
    ChcSort::Datatype {
        name: "OptionInt".into(),
        constructors: crate::ChcDtConstructors::new(vec![
            ChcDtConstructor {
                name: "none".into(),
                selectors: vec![],
            },
            ChcDtConstructor {
                name: "some".into(),
                selectors: vec![ChcDtSelector {
                    name: "value".into(),
                    sort: ChcSort::Int,
                }],
            },
        ]),
    }
}

fn array(key: ChcSort, value: ChcSort) -> ChcSort {
    ChcSort::Array(Box::new(key), Box::new(value))
}

fn variable(sort: ChcSort) -> ChcExpr {
    ChcExpr::Var(ChcVar::new("v", sort))
}

#[test]
fn carried_datatypes_include_nested_array_keys_values_and_function_results() {
    let cases = [
        variable(datatype()),
        variable(array(datatype(), ChcSort::Int)),
        variable(array(ChcSort::Int, datatype())),
        variable(array(ChcSort::Bool, array(datatype(), ChcSort::Int))),
        variable(array(array(ChcSort::Int, datatype()), ChcSort::Bool)),
        ChcExpr::FuncApp("some".into(), datatype(), vec![ChcExpr::Int(7).into()]),
        ChcExpr::FuncApp(
            "array-result".into(),
            array(ChcSort::Int, datatype()),
            vec![],
        ),
        ChcExpr::FuncApp(
            "scalar-selector".into(),
            ChcSort::Int,
            vec![variable(datatype()).into()],
        ),
        ChcExpr::ConstArray(datatype(), ChcExpr::Int(0).into()),
        ChcExpr::ConstArray(ChcSort::Int, variable(datatype()).into()),
        ChcExpr::ConstArrayMarker(array(ChcSort::Int, datatype())),
    ];
    for expr in cases {
        assert_eq!(classify(&expr), DatatypeUse::Present, "{expr:?}");
    }
}

#[test]
fn scalar_ite_and_uninterpreted_names_are_not_datatype_evidence() {
    let ite = ChcExpr::Op(
        ChcOp::Ite,
        vec![
            variable(ChcSort::Bool).into(),
            ChcExpr::Int(1).into(),
            ChcExpr::Int(2).into(),
        ],
    );
    assert!(ite.scan_features().has_ite);
    for expr in [
        ite,
        variable(ChcSort::Uninterpreted("OptionInt".into())),
        ChcExpr::FuncApp("some".into(), ChcSort::Int, vec![ChcExpr::Int(1).into()]),
        ChcExpr::ConstArrayMarker(ChcSort::Int),
        variable(array(ChcSort::BitVec(8), ChcSort::Real)),
        ChcExpr::IsTesterMarker("some".into()),
    ] {
        assert_eq!(classify(&expr), DatatypeUse::Absent);
    }
}

#[test]
fn classification_never_admits_malformed_datatype_metadata_or_markers() {
    let empty = ChcSort::Datatype {
        name: "Empty".into(),
        constructors: crate::ChcDtConstructors::new(vec![]),
    };
    let expr = variable(empty);
    assert_eq!(classify(&expr), DatatypeUse::Present);
    assert!(crate::smt::executor_adapter::collect_dt_declarations_for_expr(&[], &expr).is_err());
    let marker = ChcExpr::ConstArrayMarker(datatype());
    assert_eq!(classify(&marker), DatatypeUse::Present);
    assert!(crate::smt::executor_sort_guard::unsupported_executor_expr_reason(&marker).is_some());
}

#[test]
fn exact_work_frontiers_and_fanout_exhaustion_are_indeterminate() {
    let scalar = ChcExpr::Bool(true);
    assert_eq!(classify_with_limit(&scalar, 0), DatatypeUse::Indeterminate);
    assert_eq!(classify_with_limit(&scalar, 1), DatatypeUse::Absent);
    let scalar_var = variable(ChcSort::Int);
    assert_eq!(
        classify_with_limit(&scalar_var, 1),
        DatatypeUse::Indeterminate
    );
    assert_eq!(classify_with_limit(&scalar_var, 2), DatatypeUse::Absent);
    let array_var = variable(array(ChcSort::Int, ChcSort::Bool));
    assert_eq!(
        classify_with_limit(&array_var, 3),
        DatatypeUse::Indeterminate
    );
    assert_eq!(classify_with_limit(&array_var, 4), DatatypeUse::Absent);
    let dt_array = variable(array(ChcSort::Int, datatype()));
    assert_eq!(
        classify_with_limit(&dt_array, 3),
        DatatypeUse::Indeterminate
    );
    assert_eq!(classify_with_limit(&dt_array, 4), DatatypeUse::Present);
    let shared = Arc::new(ChcExpr::Bool(true));
    let fanout = ChcExpr::Op(ChcOp::And, vec![shared; 128]);
    assert_eq!(
        classify_with_limit(&fanout, 128),
        DatatypeUse::Indeterminate
    );
    assert_eq!(classify_with_limit(&fanout, 129), DatatypeUse::Absent);
    assert!(classify_with_limit(&fanout, 128).needs_datatype_schedule());
}

#[test]
fn shared_expression_dag_expands_each_node_once_without_structural_hashing() {
    let mut expr = Arc::new(ChcExpr::Bool(true));
    for _ in 0..16 {
        expr = Arc::new(ChcExpr::Op(ChcOp::Or, vec![expr.clone(), expr]));
    }
    // Root plus two incoming edges per expanded internal node: 1 + 2*16.
    assert_eq!(classify_with_limit(&expr, 32), DatatypeUse::Indeterminate);
    assert_eq!(classify_with_limit(&expr, 33), DatatypeUse::Absent);
}

#[test]
fn deep_array_sorts_use_iterative_work_and_budgeted_refusal() {
    let mut sort = ChcSort::Int;
    for _ in 0..4096 {
        sort = array(ChcSort::Bool, sort);
    }
    let mut marker = ChcExpr::ConstArrayMarker(sort);
    assert_eq!(classify_with_limit(&marker, 8), DatatypeUse::Indeterminate);
    assert_eq!(classify(&marker), DatatypeUse::Absent);
    // Do not make the test's own recursive Box destructor the depth limit.
    let ChcExpr::ConstArrayMarker(sort) = &mut marker else {
        unreachable!();
    };
    let mut sort = std::mem::replace(sort, ChcSort::Int);
    while let ChcSort::Array(_, value) = sort {
        sort = *value;
    }
}

#[test]
fn query_policy_preserves_none_zero_and_shorter_timeouts() {
    assert!(!DatatypeUse::Absent.needs_datatype_schedule());
    assert_eq!(DatatypeUse::Absent.internal_slice(None), None);
    assert_eq!(
        DatatypeUse::Absent.internal_slice(Some(Duration::from_secs(5))),
        Some(Duration::from_millis(1250))
    );
    assert_eq!(
        DatatypeUse::Absent.internal_slice(Some(Duration::from_secs(60))),
        Some(Duration::from_secs(2))
    );
    for policy in [DatatypeUse::Present, DatatypeUse::Indeterminate] {
        assert!(policy.needs_datatype_schedule());
        assert_eq!(policy.internal_slice(None), Some(Duration::from_millis(25)));
        assert_eq!(
            policy.internal_slice(Some(Duration::from_secs(5))),
            Some(Duration::from_millis(25))
        );
    }
    for policy in [
        DatatypeUse::Absent,
        DatatypeUse::Present,
        DatatypeUse::Indeterminate,
    ] {
        assert_eq!(
            policy.internal_slice(Some(Duration::ZERO)),
            Some(Duration::ZERO)
        );
        assert_eq!(
            policy.internal_slice(Some(Duration::from_millis(40))),
            Some(Duration::from_millis(10))
        );
    }
}
