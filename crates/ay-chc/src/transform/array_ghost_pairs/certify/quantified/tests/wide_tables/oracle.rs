// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent exact evaluation of the authored table/resize source witness.
//! This fixes arbitrary table values, not IEEE arithmetic. Candidate evaluation
//! separately uses AY's evaluator only after constructing an exact typed input.

use super::*;
use std::collections::BTreeMap;

pub(super) fn lhs(table: Table) -> u128 {
    (1u128 << (table.cell_width() - 1)) + 3
}
pub(super) fn key(table: Table, tag: u128) -> BigUint {
    (BigUint::from(tag) << (2 * table.cell_width()) as usize)
        + (BigUint::from(lhs(table)) << table.cell_width() as usize)
        + BigUint::from(9u8)
}

pub(super) fn candidate_environment(
    table: Table,
    id: PredicateId,
    vars: &[ChcVar],
    tag: u128,
    index: u128,
    table_cell: u128,
    byte: u128,
) -> DetHashMap<String, SmtValue> {
    let (rhs, first, old, new, key_axis, data_axis, table_value, data_value) = if id.index() == 0 {
        (2, 3, 5, 6, 7, 8, 9, 10)
    } else {
        (6, 0, 5, 3, 8, 7, 10, 9)
    };
    let mut env = DetHashMap::default();
    for (position, value, width) in [
        (1, lhs(table), table.cell_width()),
        (rhs, 9, table.cell_width()),
        (first, 7, table.cell_width()),
        (old, 32, 64),
        (new, 65, 64),
        (data_axis, index, 64),
        (table_value, table_cell, table.cell_width()),
        (data_value, byte, 8),
    ] {
        assert_eq!(vars[position].sort, ChcSort::BitVec(width));
        env.insert(vars[position].name.clone(), SmtValue::BitVec(value, width));
    }
    env.insert(
        vars[key_axis].name.clone(),
        SmtValue::try_bitvec_from_biguint(key(table, tag), table.key_width()).unwrap(),
    );
    env
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Value {
    Bool(bool),
    Bv(BigUint, u32),
    Array(Box<Value>, Vec<(BigUint, Value)>),
}
type Environment = BTreeMap<String, Value>;
fn bv(value: u128, width: u32) -> Value {
    Value::Bv(BigUint::from(value), width)
}

fn eval(expr: &ChcExpr, env: &Environment) -> Value {
    match expr {
        ChcExpr::Var(var) => env.get(&var.name).expect("source local assignment").clone(),
        ChcExpr::Bool(value) => Value::Bool(*value),
        ChcExpr::BitVec(value, width) => bv(*value, *width),
        ChcExpr::Op(operator, args) => {
            let args: Vec<_> = args.iter().map(|arg| eval(arg, env)).collect();
            operation(*operator, &args)
        }
        other => panic!("unsupported independent source term: {other:?}"),
    }
}

fn operation(operator: ChcOp, args: &[Value]) -> Value {
    match (operator, args) {
        (ChcOp::Eq, [a, b]) => Value::Bool(a == b),
        (ChcOp::Ne, [a, b]) => Value::Bool(a != b),
        (ChcOp::Not, [Value::Bool(a)]) => Value::Bool(!a),
        (ChcOp::Implies, [Value::Bool(a), Value::Bool(b)]) => Value::Bool(!a || *b),
        (ChcOp::And, args) => Value::Bool(args.iter().all(|arg| {
            let Value::Bool(value) = arg else {
                panic!("and")
            };
            *value
        })),
        (ChcOp::Or, args) => Value::Bool(args.iter().any(|arg| {
            let Value::Bool(value) = arg else {
                panic!("or")
            };
            *value
        })),
        (ChcOp::BvULt, [Value::Bv(a, aw), Value::Bv(b, bw)]) if aw == bw => Value::Bool(a < b),
        (ChcOp::BvUGe, [Value::Bv(a, aw), Value::Bv(b, bw)]) if aw == bw => Value::Bool(a >= b),
        (ChcOp::BvConcat, [Value::Bv(a, aw), Value::Bv(b, bw)]) => {
            Value::Bv((a << *bw as usize) + b, aw + bw)
        }
        (ChcOp::BvExtract(high, low), [Value::Bv(value, width)])
            if low <= high && high < *width =>
        {
            let bits = high - low + 1;
            let mask = (BigUint::from(1u8) << bits as usize) - BigUint::from(1u8);
            Value::Bv((value >> low as usize) & mask, bits)
        }
        (ChcOp::Select, [Value::Array(default, entries), Value::Bv(key, _)]) => entries
            .iter()
            .rev()
            .find(|(index, _)| index == key)
            .map_or_else(|| default.as_ref().clone(), |(_, value)| value.clone()),
        other => panic!("unsupported independent source operation: {other:?}"),
    }
}

fn expected_matrix(source: &QuantifiedChcProblem, table: Table, change: Change) -> ChcExpr {
    let i = ChcExpr::Var(source.premises()[0][0].binder().clone());
    let index = ChcSort::BitVec(64);
    let array = ChcSort::Array(Box::new(index.clone()), Box::new(ChcSort::BitVec(8)));
    let read = |name| ChcExpr::select(variable(name, &array), i.clone());
    let prefix = op(
        ChcOp::Implies,
        vec![
            op(ChcOp::BvULt, vec![i.clone(), variable("old", &index)]),
            op(ChcOp::Eq, vec![read("b"), read("a")]),
        ],
    );
    let mut matrices = vec![prefix];
    if !matches!(change, Change::MissingSuffix) {
        matrices.push(op(
            ChcOp::Implies,
            vec![
                op(
                    ChcOp::And,
                    vec![
                        op(ChcOp::BvUGe, vec![i.clone(), variable("old", &index)]),
                        op(ChcOp::BvULt, vec![i.clone(), variable("new", &index)]),
                    ],
                ),
                op(
                    ChcOp::Eq,
                    vec![
                        read("b"),
                        op(
                            ChcOp::BvExtract(7, 0),
                            vec![variable("first", &ChcSort::BitVec(table.cell_width()))],
                        ),
                    ],
                ),
            ],
        ));
    } else {
        matrices.push(ChcExpr::Bool(true));
    }
    op(ChcOp::And, matrices)
}

pub(super) fn bad_state(source: &QuantifiedChcProblem, table: Table, change: Change) -> bool {
    let cells = Value::Array(
        Box::new(bv(7, 8)),
        if matches!(change, Change::MissingSuffix) {
            vec![(BigUint::from(64u8), bv(9, 8))]
        } else {
            vec![]
        },
    );
    let table_value = Value::Array(
        Box::new(bv(0, table.cell_width())),
        vec![
            (key(table, 4), bv(7, table.cell_width())),
            (key(table, 0), bv(9, table.cell_width())),
        ],
    );
    let mut env: Environment = [
        ("table", table_value),
        (
            "other_table",
            Value::Array(Box::new(bv(9, table.cell_width())), vec![]),
        ),
        ("lhs", bv(lhs(table), table.cell_width())),
        ("rhs", bv(9, table.cell_width())),
        ("first", bv(7, table.cell_width())),
        ("a", Value::Array(Box::new(bv(7, 8)), vec![])),
        ("b", cells),
        ("old", bv(32, 64)),
        ("new", bv(65, 64)),
        ("j", bv(64, 64)),
    ]
    .into_iter()
    .map(|(name, value)| (name.to_owned(), value))
    .collect();
    let clauses = source.source_problem().clauses();
    assert_eq!(clauses.len(), 4);
    assert_eq!(
        eval(clauses[0].body.constraint.as_ref().unwrap(), &env),
        Value::Bool(true)
    );
    let premise = &source.premises()[0][0];
    assert_eq!(premise.binder_count(), 1);
    assert_eq!(premise.binder().sort, ChcSort::BitVec(64));
    assert_eq!(premise.matrix(), &expected_matrix(source, table, change));
    // Every active unsigned index is in 0..65; the authenticated matrix has
    // false prefix/suffix guards at every other BV64 value, not a low-prefix
    // approximation to an unrestricted quantifier.
    for index in (0u128..=65).chain(std::iter::once(u128::from(u64::MAX))) {
        env.insert(premise.binder().name.clone(), bv(index, 64));
        assert_eq!(eval(premise.matrix(), &env), Value::Bool(true));
    }
    let ClauseHead::Predicate(p, fact) = &clauses[0].head else {
        panic!("P fact")
    };
    assert_eq!(clauses[1].body.predicates, vec![(*p, fact.clone())]);
    let ClauseHead::Predicate(q, head) = &clauses[1].head else {
        panic!("Q successor")
    };
    let [(query_pred, query_args)] = clauses[2].body.predicates.as_slice() else {
        panic!("query anchor")
    };
    assert_eq!(q, query_pred);
    let values: Vec<_> = head.iter().map(|arg| eval(arg, &env)).collect();
    assert_eq!(values.len(), query_args.len());
    for (arg, value) in query_args.iter().zip(values) {
        let ChcExpr::Var(var) = arg else {
            panic!("query state formal")
        };
        env.insert(var.name.clone(), value);
    }
    let ClauseHead::Predicate(error, args) = &clauses[2].head else {
        panic!("error")
    };
    assert_eq!(args.as_slice(), []);
    assert_eq!(clauses[3].body.predicates, vec![(*error, vec![])]);
    assert!(clauses[3].is_query());
    eval(clauses[2].body.constraint.as_ref().unwrap(), &env) == Value::Bool(true)
}
