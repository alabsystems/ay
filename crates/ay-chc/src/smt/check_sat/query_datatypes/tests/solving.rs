// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::model_verify::verify_sat_model_strict;
use crate::smt::types::ModelVerifyResult;
use crate::smt::{SmtContext, SmtResult};
use ay_core::kani_compat::DetHashMap as FxHashMap;

fn scalar_ite_query(value: i128) -> ChcExpr {
    let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let b = ChcExpr::Var(ChcVar::new("b", ChcSort::Bool));
    let ite = ChcExpr::Op(
        ChcOp::Ite,
        vec![b.into(), ChcExpr::Int(1).into(), ChcExpr::Int(2).into()],
    );
    ChcExpr::Op(
        ChcOp::And,
        vec![
            ChcExpr::eq(x.clone(), ite).into(),
            ChcExpr::eq(x, ChcExpr::Int(value)).into(),
        ],
    )
}

#[test]
fn unused_definitions_preserve_scalar_ite_sat_unsat_and_scheduling() {
    let mut definitions = FxHashMap::default();
    definitions.insert("Unused".into(), vec![("unused".into(), vec![])]);
    for declared in [FxHashMap::default(), definitions] {
        for (value, expected_sat) in [(1, true), (3, false)] {
            let query = scalar_ite_query(value);
            assert!(query.scan_features().has_ite);
            let mut context = SmtContext::new();
            context.set_datatype_defs(declared.clone());
            let policy = classify(&query);
            assert_eq!(policy, DatatypeUse::Absent);
            assert_eq!(policy.internal_slice(None), None);
            let result = context.check_sat_with_timeout(&query, Duration::from_secs(3));
            if expected_sat {
                let SmtResult::Sat(model) = result else {
                    panic!("expected scalar SAT, got {result:?}");
                };
                assert!(matches!(
                    verify_sat_model_strict(&query, &model),
                    ModelVerifyResult::Valid
                ));
            } else {
                assert!(result.is_unsat(), "expected scalar UNSAT, got {result:?}");
            }
        }
    }
}

#[test]
fn embedded_constructor_metadata_without_registry_keeps_checked_sat_unsat() {
    let constructor = ChcExpr::FuncApp("some".into(), datatype(), vec![ChcExpr::Int(7).into()]);
    let selected = ChcExpr::FuncApp("value".into(), ChcSort::Int, vec![constructor.into()]);
    for (value, expected_sat) in [(7, true), (8, false)] {
        let x = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
        let query = ChcExpr::Op(
            ChcOp::And,
            vec![
                ChcExpr::eq(x.clone(), selected.clone()).into(),
                ChcExpr::eq(x, ChcExpr::Int(value)).into(),
            ],
        );
        let mut context = SmtContext::new();
        assert!(context.datatype_defs.is_empty());
        assert_eq!(classify(&query), DatatypeUse::Present);
        let result = context.check_sat_with_timeout(&query, Duration::from_secs(3));
        if expected_sat {
            let SmtResult::Sat(model) = result else {
                panic!("expected expression-local DT SAT, got {result:?}");
            };
            assert!(matches!(
                verify_sat_model_strict(&query, &model),
                ModelVerifyResult::Valid
            ));
        } else {
            assert!(
                result.is_unsat(),
                "expected expression-local DT UNSAT, got {result:?}"
            );
        }
    }
}
