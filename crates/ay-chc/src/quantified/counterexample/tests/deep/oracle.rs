// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Concrete source evaluation independent of search, rendering and native SAT.
//! BV4 transition states are exhaustive; the authenticated BV64 guard is i<10.

use super::*;
use ay_core::kani_compat::DetHashMap;

type Environment = DetHashMap<String, SmtValue>;

fn evaluate(expression: &ChcExpr, environment: &Environment) -> SmtValue {
    crate::expr::evaluate_expr(expression, environment).expect("complete concrete source value")
}

fn argument(expression: &ChcExpr, index: usize) -> &ChcExpr {
    let ChcExpr::Op(_, arguments) = expression else {
        panic!("source operation")
    };
    &arguments[index]
}

fn environment(clause: &HornClause, record: &SmtValue, position: u128) -> Environment {
    let arguments = if let Some((_, arguments)) = clause.body.predicates.first() {
        arguments
    } else {
        let ClauseHead::Predicate(_, arguments) = &clause.head else {
            panic!("fact head")
        };
        arguments
    };
    let mut environment = Environment::default();
    let ChcExpr::Var(record_variable) = &arguments[0] else {
        panic!("record argument")
    };
    environment.insert(record_variable.name.clone(), record.clone());
    if let ChcExpr::Var(position_variable) = &arguments[1] {
        environment.insert(
            position_variable.name.clone(),
            SmtValue::BitVec(position, 4),
        );
    }
    environment
}

fn false_indices(premise: &UniversalPremise, mut environment: Environment) -> Vec<u128> {
    assert_eq!(premise.binder_count(), 1);
    assert_eq!(premise.binder().sort, ChcSort::BitVec(64));
    assert!(matches!(premise.matrix(), ChcExpr::Op(ChcOp::Implies, _)));
    let guard = argument(premise.matrix(), 0);
    assert!(matches!(guard, ChcExpr::Op(ChcOp::BvULt, _)));
    assert_eq!(argument(guard, 0), &ChcExpr::Var(premise.binder().clone()));
    assert_eq!(
        evaluate(argument(guard, 1), &environment),
        SmtValue::BitVec(10, 64)
    );
    let mut failures = Vec::new();
    for index in 0..13 {
        environment.insert(premise.binder().name.clone(), SmtValue::BitVec(index, 64));
        let result = evaluate(premise.matrix(), &environment);
        assert!(matches!(result, SmtValue::Bool(_)));
        if result == SmtValue::Bool(false) {
            failures.push(index);
        }
    }
    // All remaining unsigned BV64 indices are >=10: the exact guard is false.
    failures
}

pub(super) fn check_record(value: &SmtValue) {
    let SmtValue::Datatype(constructor, fields) = value else {
        panic!("complete record value")
    };
    assert_eq!(constructor, "mkVec");
    assert_eq!(fields.len(), 4);
    assert_eq!(
        fields[..3],
        [
            SmtValue::BitVec(0, 64),
            SmtValue::BitVec(10, 64),
            SmtValue::BitVec(10, 64)
        ]
    );
    let SmtValue::ArrayMap { default, entries } = &fields[3] else {
        panic!("complete array default and stores")
    };
    assert_eq!(default.as_ref(), &SmtValue::BitVec(7, 8));
    let mut seen = std::collections::BTreeSet::new();
    for (key, cell) in entries.iter().rev() {
        let SmtValue::BitVec(value, 64) = key else {
            panic!("typed BV64 array key")
        };
        assert!(*value <= u128::from(u64::MAX));
        if seen.insert(*value) {
            assert_eq!(cell, &SmtValue::BitVec(7, 8));
        }
    }
}

pub(super) fn check() {
    for (cells, expected, reachable_query) in [
        (Cells::Filled, 8, true),
        (Cells::CorruptLast, 8, false),
        (Cells::Filled, 7, false),
    ] {
        let source = loop_source(cells, expected);
        let clauses = source.source_problem().clauses();
        assert_eq!(clauses.len(), 3);
        let record = evaluate(
            argument(clauses[0].body.constraint.as_ref().unwrap(), 1),
            &Environment::default(),
        );
        let fact_environment = environment(&clauses[0], &record, 0);
        assert_eq!(
            evaluate(
                clauses[0].body.constraint.as_ref().unwrap(),
                &fact_environment
            ),
            SmtValue::Bool(true)
        );
        let failed = false_indices(&source.premises()[0][0], fact_environment);
        assert_eq!(
            failed,
            match cells {
                Cells::Filled => vec![],
                Cells::CorruptLast => vec![9],
            }
        );
        let mut reachable = vec![false; 16];
        reachable[0] = failed.is_empty();
        let mut query_states = Vec::new();
        for position in 0..16 {
            let step_environment = environment(&clauses[1], &record, position);
            let step = evaluate(
                clauses[1].body.constraint.as_ref().unwrap(),
                &step_environment,
            );
            assert_eq!(step, SmtValue::Bool(position < 9));
            assert_eq!(
                false_indices(&source.premises()[1][0], step_environment.clone()),
                failed
            );
            let ClauseHead::Predicate(_, head) = &clauses[1].head else {
                panic!("step head")
            };
            assert_eq!(
                evaluate(&head[1], &step_environment),
                SmtValue::BitVec((position + 1) % 16, 4)
            );
            if reachable[position as usize] && position < 9 {
                reachable[position as usize + 1] = true;
            }
            let query_environment = environment(&clauses[2], &record, position);
            let query = evaluate(
                clauses[2].body.constraint.as_ref().unwrap(),
                &query_environment,
            );
            if reachable[position as usize] && query == SmtValue::Bool(true) {
                query_states.push(position);
            }
        }
        assert_eq!(query_states, if reachable_query { vec![9] } else { vec![] });
        assert_eq!(
            reachable.iter().filter(|&&value| value).count(),
            if failed.is_empty() { 10 } else { 0 }
        );
    }
}
