// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent source-AST evaluator for one authored total interpretation:
//! f always returns 7, g always returns 9, matrix_only always returns 0, and
//! arrays are uniform. This is not an enumeration of all possible UF models.

use super::*;
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Value {
    Bool(bool),
    Bv(u128, u32),
    Array(Box<Value>),
    Record(Vec<Value>),
}
type Environment = BTreeMap<String, Value>;

fn eval(expr: &ChcExpr, env: &Environment) -> Value {
    match expr {
        ChcExpr::Bool(value) => Value::Bool(*value),
        ChcExpr::BitVec(value, width) => Value::Bv(*value, *width),
        ChcExpr::Var(var) => env
            .get(&var.name)
            .expect("complete occurrence assignment")
            .clone(),
        ChcExpr::FuncApp(name, _, args) => {
            let values: Vec<_> = args.iter().map(|arg| eval(arg, env)).collect();
            match (name.as_str(), values.as_slice()) {
                ("f", [Value::Bool(_), Value::Bv(_, 8)]) => Value::Bv(7, 8),
                ("g", [Value::Bool(_), Value::Bv(_, 8)]) => Value::Bv(9, 8),
                ("matrix_only", [Value::Bv(_, 64)]) => Value::Bv(0, 1),
                ("mkVec" | "mkInner" | "mkOuter", [_, _, _, _]) => Value::Record(values),
                ("fld_ptr", [Value::Record(fields)]) => fields[0].clone(),
                ("fld_len", [Value::Record(fields)]) => fields[1].clone(),
                ("fld_cap", [Value::Record(fields)]) => fields[2].clone(),
                ("fld_data", [Value::Record(fields)]) => fields[3].clone(),
                other => panic!("unexpected authored function/selector: {other:?}"),
            }
        }
        ChcExpr::Op(operator, args) => {
            let values: Vec<_> = args.iter().map(|arg| eval(arg, env)).collect();
            operation(*operator, &values)
        }
        other => panic!("unexpected source expression: {other:?}"),
    }
}

fn operation(operator: ChcOp, values: &[Value]) -> Value {
    match (operator, values) {
        (ChcOp::Eq, [left, right]) => Value::Bool(left == right),
        (ChcOp::Ne, [left, right]) => Value::Bool(left != right),
        (ChcOp::Not, [Value::Bool(value)]) => Value::Bool(!value),
        (ChcOp::Implies, [Value::Bool(a), Value::Bool(b)]) => Value::Bool(!a || *b),
        (ChcOp::And, values) => Value::Bool(values.iter().all(|value| {
            let Value::Bool(value) = value else {
                panic!("Boolean conjunction")
            };
            *value
        })),
        (ChcOp::BvULt, [Value::Bv(a, width), Value::Bv(b, other)]) if width == other => {
            Value::Bool(a < b)
        }
        (ChcOp::BvUGe, [Value::Bv(a, width), Value::Bv(b, other)]) if width == other => {
            Value::Bool(a >= b)
        }
        (ChcOp::BvAdd, [Value::Bv(a, 8), Value::Bv(b, 8)]) => Value::Bv((a + b) & 255, 8),
        (ChcOp::Select, [Value::Array(default), Value::Bv(_, 64)]) => default.as_ref().clone(),
        other => panic!("unexpected authored operation: {other:?}"),
    }
}

fn bound(expr: &ChcExpr, names: &[&str]) -> bool {
    matches!(expr, ChcExpr::Var(var) if names.contains(&var.name.as_str()))
}

/// Check the exact partition used below: bound values can only be uniform
/// array keys, arguments to a constant total UF, or the left side of `< 65`.
/// Thus 0 and 65 cover all Boolean branches over the entire BV64 domain;
/// 64 and MAX independently exercise the late-cell and unsigned boundaries.
fn check_partition(expr: &ChcExpr, names: &[&str], env: &Environment) {
    match expr {
        ChcExpr::Var(_) => assert!(!bound(expr, names), "unexpected binder dependency"),
        ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 && bound(&args[1], names) => {
            check_partition(&args[0], names, env);
        }
        ChcExpr::Op(ChcOp::BvULt, args) if args.len() == 2 && bound(&args[0], names) => {
            check_partition(&args[1], names, env);
            assert_eq!(eval(&args[1], env), Value::Bv(65, 64));
        }
        ChcExpr::FuncApp(name, _, args)
            if name == "matrix_only" && args.len() == 1 && bound(&args[0], names) => {}
        ChcExpr::FuncApp(_, _, args) | ChcExpr::Op(_, args) => {
            for arg in args {
                check_partition(arg, names, env);
            }
        }
        ChcExpr::Bool(_) | ChcExpr::BitVec(_, _) => {}
        other => panic!("unexpected quantified partition term: {other:?}"),
    }
}

pub(super) fn bad_state(source: &QuantifiedChcProblem, shape: Shape, calls: Calls) -> bool {
    let cell = match calls {
        Calls::Same => 7,
        Calls::Independent => 9,
    };
    let data = Value::Array(Box::new(Value::Bv(cell, 8)));
    let record = |data| {
        Value::Record(vec![
            Value::Bv(0, 64),
            Value::Bv(65, 64),
            Value::Bv(65, 64),
            data,
        ])
    };
    let rows = Value::Array(Box::new(record(data.clone())));
    let mut env: Environment = [
        ("x", Value::Bv(13, 8)),
        ("fill", Value::Bv(7, 8)),
        ("length", Value::Bv(65, 64)),
        ("k", Value::Bv(64, 64)),
        ("row", Value::Bv(33, 64)),
        ("col", Value::Bv(64, 64)),
        ("a", data.clone()),
        ("v", record(data)),
        ("rows", rows.clone()),
        ("outer", record(rows)),
    ]
    .into_iter()
    .map(|(name, value)| (name.to_owned(), value))
    .collect();
    let clauses = source.source_problem().clauses();
    assert_eq!(clauses.len(), 3);
    let ClauseHead::Predicate(p, args) = &clauses[0].head else {
        panic!("fact")
    };
    assert_eq!(clauses[1].body.predicates, vec![(*p, args.clone())]);
    let ClauseHead::Predicate(error, args) = &clauses[1].head else {
        panic!("error relation")
    };
    assert_eq!(args.as_slice(), []);
    assert_eq!(clauses[2].body.predicates, vec![(*error, vec![])]);
    assert!(clauses[2].is_query());
    assert_eq!(
        eval(clauses[0].body.constraint.as_ref().unwrap(), &env),
        Value::Bool(true)
    );
    let premise = &source.premises()[0][0];
    let binders: Vec<_> = premise.binders().collect();
    assert_eq!(binders.len(), 2);
    let names: Vec<_> = binders.iter().map(|var| var.name.as_str()).collect();
    for binder in &binders {
        env.insert(binder.name.clone(), Value::Bv(0, 64));
    }
    check_partition(premise.matrix(), &names, &env);
    for row in [0, 64, 65, u128::from(u64::MAX)] {
        for column in [0, 64, 65, u128::from(u64::MAX)] {
            env.insert(binders[0].name.clone(), Value::Bv(row, 64));
            env.insert(binders[1].name.clone(), Value::Bv(column, 64));
            assert_eq!(eval(premise.matrix(), &env), Value::Bool(true));
        }
    }
    let expected_arity = match shape {
        Shape::Array => 3,
        Shape::Vec | Shape::Nested => 2,
    };
    assert_eq!(
        source.source_problem().predicates()[0].arg_sorts.len(),
        expected_arity
    );
    eval(clauses[1].body.constraint.as_ref().unwrap(), &env) == Value::Bool(true)
}
