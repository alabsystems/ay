// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::SmtValue;
use crate::{ChcExpr, ChcOp};
use ay_core::kani_compat::DetHashMap;

fn vector(constructor: &str, length: u128, data: SmtValue) -> SmtValue {
    SmtValue::Datatype(
        constructor.to_owned(),
        vec![
            SmtValue::BitVec(0, 64),
            SmtValue::BitVec(length, 64),
            SmtValue::BitVec(100, 64),
            data,
        ],
    )
}

fn world(premise: Premise, query: Query) -> SmtValue {
    let data = SmtValue::ArrayMap {
        default: Box::new(SmtValue::BitVec(7, 8)),
        entries: Vec::new(),
    };
    let ordinary = vector("mkInner", 100, data);
    let changed = match (premise, query) {
        (_, Query::ShiftedFill) => ordinary.clone(),
        _ => vector(
            "mkInner",
            if matches!(query, Query::OtherRowLength) {
                1
            } else {
                100
            },
            SmtValue::ArrayMap {
                default: Box::new(SmtValue::BitVec(7, 8)),
                entries: vec![(SmtValue::BitVec(64, 64), SmtValue::BitVec(9, 8))],
            },
        ),
    };
    vector(
        "mkOuter",
        100,
        SmtValue::ArrayMap {
            default: Box::new(ordinary),
            entries: vec![(SmtValue::BitVec(33, 64), changed)],
        },
    )
}

fn variable(expression: &ChcExpr) -> &str {
    let ChcExpr::Var(var) = expression else {
        panic!("source variable")
    };
    &var.name
}

fn operand(expression: &ChcExpr, index: usize) -> &ChcExpr {
    let ChcExpr::Op(_, args) = expression else {
        panic!("source operator")
    };
    &args[index]
}

pub(super) fn check(problem: &QuantifiedChcProblem, premise: Premise, query: Query) {
    let outer = world(premise, query);
    let mut values = DetHashMap::default();
    let fact = &problem.source_problem().clauses()[0];
    let crate::ClauseHead::Predicate(_, arguments) = &fact.head else {
        panic!("fact head")
    };
    values.insert(variable(&arguments[0]).to_owned(), outer.clone());
    values.insert(variable(&arguments[1]).to_owned(), SmtValue::BitVec(7, 8));
    let evaluate = crate::expr::evaluate_expr;
    if let Some(constraint) = &fact.body.constraint {
        assert_eq!(evaluate(constraint, &values), Some(SmtValue::Bool(true)));
    }
    // The only non-default cell is (33,64). It is off every diagonal, or
    // outside row 33's valid length in the wrong-row control. Every remaining
    // cell is 7 by construction. These samples exercise the actual matrices;
    // they are not enumeration of the entire BV64 carrier.
    let indices = [0, 32, 33, 34, 64, 99, 100, u64::MAX as u128];
    for universal in &problem.premises()[0] {
        let binders = universal.binders().collect::<Vec<_>>();
        for row in indices {
            values.insert(binders[0].name.clone(), SmtValue::BitVec(row, 64));
            for col in indices {
                if let Some(binder) = binders.get(1) {
                    values.insert(binder.name.clone(), SmtValue::BitVec(col, 64));
                }
                assert_eq!(
                    evaluate(universal.matrix(), &values),
                    Some(SmtValue::Bool(true))
                );
            }
        }
    }
    let clause = &problem.source_problem().clauses()[1];
    let (_, arguments) = &clause.body.predicates[0];
    values.insert(variable(&arguments[0]).to_owned(), outer);
    values.insert(variable(&arguments[1]).to_owned(), SmtValue::BitVec(7, 8));
    let constraint = clause.body.constraint.as_ref().unwrap();
    let ChcExpr::Op(ChcOp::And, guards) = constraint else {
        panic!("query guards")
    };
    assert_eq!(guards.len(), 5);
    values.insert(
        variable(operand(&guards[0], 0)).to_owned(),
        SmtValue::BitVec(33, 64),
    );
    values.insert(
        variable(operand(&guards[1], 0)).to_owned(),
        SmtValue::BitVec(64, 64),
    );
    if matches!(query, Query::OtherRowLength) {
        let length = operand(&guards[3], 1);
        let ChcExpr::FuncApp(_, _, receiver) = length else {
            panic!("row length")
        };
        let other = operand(&receiver[0], 1);
        values.insert(variable(other).to_owned(), SmtValue::BitVec(34, 64));
    }
    assert_eq!(evaluate(constraint, &values), Some(SmtValue::Bool(true)));
}
