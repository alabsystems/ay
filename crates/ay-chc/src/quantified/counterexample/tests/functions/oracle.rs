// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent evaluator of this authored source fragment. UF rows are keyed
//! by complete argument values and shared globally across all occurrences.

use super::*;
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Value {
    Bool(bool),
    Bv(u128, u32),
    Array(u8, Vec<(u128, u8)>),
}

type Environment = BTreeMap<String, Value>;

fn eval(expr: &ChcExpr, env: &Environment, table: &[bool; 3]) -> Value {
    match expr {
        ChcExpr::Bool(value) => Value::Bool(*value),
        ChcExpr::BitVec(value, width) => Value::Bv(*value, *width),
        ChcExpr::Var(var) => env
            .get(&var.name)
            .expect("complete local assignment")
            .clone(),
        ChcExpr::ConstArray(ChcSort::BitVec(64), value) => {
            let Value::Bv(value, 8) = eval(value, env, table) else {
                panic!("byte default")
            };
            Value::Array(value as u8, vec![])
        }
        ChcExpr::FuncApp(name, ChcSort::BitVec(1), args) => {
            let args: Vec<_> = args.iter().map(|arg| eval(arg, env, table)).collect();
            let bit = match (name.as_str(), args.as_slice()) {
                ("uf_call_0_pure", [Value::Bool(true), Value::Bv(7, 8)]) => table[0],
                ("uf_call_0_pure", [Value::Bool(true), Value::Bv(8, 8)]) => table[1],
                ("uf_call_1_other", [Value::Bool(true), Value::Bv(7, 8)]) => table[2],
                ("uf_call_0_pure" | "uf_call_1_other", [Value::Bool(_), Value::Bv(_, 8)]) => false,
                ("uf_range", [Value::Bool(true), Value::Bv(33, 64), Value::Bv(1, 64)]) => table[0],
                ("uf_range", [Value::Bool(true), Value::Bv(_, 64), Value::Bv(_, 64)]) => true,
                _ => panic!("authenticated finite-table signature"),
            };
            Value::Bv(u128::from(bit), 1)
        }
        ChcExpr::Op(operator, args) => {
            let args: Vec<_> = args.iter().map(|arg| eval(arg, env, table)).collect();
            operation(*operator, &args)
        }
        other => panic!("unsupported independent oracle expression: {other:?}"),
    }
}

fn operation(operator: ChcOp, args: &[Value]) -> Value {
    match (operator, args) {
        (ChcOp::Eq, [left, right]) => Value::Bool(left == right),
        (ChcOp::Not, [Value::Bool(value)]) => Value::Bool(!value),
        (ChcOp::Implies, [Value::Bool(left), Value::Bool(right)]) => Value::Bool(!left || *right),
        (ChcOp::And, args) => Value::Bool(args.iter().all(|arg| {
            let Value::Bool(value) = arg else {
                panic!("Boolean conjunction")
            };
            *value
        })),
        (ChcOp::BvAdd, [Value::Bv(left, 8), Value::Bv(right, 8)]) => {
            Value::Bv((left + right) & 255, 8)
        }
        (ChcOp::BvULt, [Value::Bv(left, width), Value::Bv(right, other)]) if width == other => {
            Value::Bool(left < right)
        }
        (ChcOp::Select, [Value::Array(default, entries), Value::Bv(index, 64)]) => {
            let value = entries
                .iter()
                .rev()
                .find(|(key, _)| key == index)
                .map_or(*default, |(_, value)| *value);
            Value::Bv(u128::from(value), 8)
        }
        (
            ChcOp::Store,
            [Value::Array(default, entries), Value::Bv(index, 64), Value::Bv(value, 8)],
        ) => {
            let mut entries = entries.clone();
            entries.push((*index, *value as u8));
            Value::Array(*default, entries)
        }
        other => panic!("unsupported independent oracle operation: {other:?}"),
    }
}

fn environment(arguments: &[ChcExpr], values: &[Value]) -> Environment {
    assert_eq!(arguments.len(), values.len());
    arguments
        .iter()
        .zip(values)
        .map(|(argument, value)| {
            let ChcExpr::Var(var) = argument else {
                panic!("source relation argument")
            };
            (var.name.clone(), value.clone())
        })
        .collect()
}

fn accepts(source: &QuantifiedChcProblem, calls: Calls, cells: Cells, table: &[bool; 3]) -> bool {
    let data = match cells {
        Cells::Filled => Value::Array(7, vec![]),
        Cells::CorruptLast => Value::Array(7, vec![(64, 8)]),
    };
    let first = Value::Bool(table[0]);
    let second = Value::Bool(match calls {
        Calls::Congruent => table[0],
        Calls::DistinctArgument => table[1],
        Calls::DistinctSymbol => table[2],
    });
    let values = [Value::Bool(true), Value::Bv(7, 8), first, second, data];
    let fact_values = [
        values[0].clone(),
        values[1].clone(),
        values[2].clone(),
        values[4].clone(),
    ];
    let clauses = source.source_problem().clauses();
    assert_eq!(clauses.len(), 4);
    let ClauseHead::Predicate(_, fact_args) = &clauses[0].head else {
        panic!("fact")
    };
    let ClauseHead::Predicate(_, step_args) = &clauses[1].head else {
        panic!("step")
    };
    assert_eq!(clauses[1].body.predicates[0].1, *fact_args);
    assert_eq!(clauses[2].body.predicates[0].1, *step_args);
    for index in 1..4 {
        let ClauseHead::Predicate(previous, _) = &clauses[index - 1].head else {
            panic!("linked head")
        };
        assert_eq!(clauses[index].body.predicates.len(), 1);
        assert_eq!(clauses[index].body.predicates[0].0, *previous);
    }
    assert!(clauses[3].body.predicates[0].1.is_empty());
    assert!(clauses[3].is_query());
    let mut fact = environment(fact_args, &fact_values);
    let step = environment(step_args, &values);
    let query = environment(&clauses[2].body.predicates[0].1, &values);
    let mut accepted = true;
    for (clause, env) in [&clauses[0], &clauses[1], &clauses[2]]
        .into_iter()
        .zip([&fact, &step, &query])
    {
        if let Some(constraint) = &clause.body.constraint {
            accepted &= eval(constraint, env, table) == Value::Bool(true);
        }
    }
    let premise = &source.premises()[0][0];
    assert_eq!(premise.binder_count(), 1);
    let ChcExpr::Op(ChcOp::Implies, matrix) = premise.matrix() else {
        panic!("implication")
    };
    let ChcExpr::Op(ChcOp::BvULt, guard) = matrix[0].as_ref() else {
        panic!("range")
    };
    assert_eq!(guard[0].as_ref(), &ChcExpr::Var(premise.binder().clone()));
    assert_eq!(guard[1].as_ref(), &ChcExpr::BitVec(65, 64));
    for index in 0..67 {
        fact.insert(premise.binder().name.clone(), Value::Bv(index, 64));
        accepted &= eval(premise.matrix(), &fact, table) == Value::Bool(true);
    }
    // The exact unsigned guard is false for all other BV64 indices.
    accepted
}

/// Count eight authored total interpretations: three independently chosen
/// table entries and false everywhere else. This is not an enumeration of all
/// mathematically possible total functions over the Bool/BV8 domain.
pub(super) fn model_count(source: &QuantifiedChcProblem, calls: Calls, cells: Cells) -> usize {
    (0u8..8)
        .filter(|bits| {
            let table = [bits & 1 != 0, bits & 2 != 0, bits & 4 != 0];
            accepts(source, calls, cells, &table)
        })
        .count()
}

pub(super) fn grouped_holds(source: &QuantifiedChcProblem, point: bool) -> bool {
    let premise = &source.premises()[0][0];
    let binders: Vec<_> = premise.binders().collect();
    assert_eq!(binders.len(), 2);
    let ChcExpr::Op(ChcOp::Implies, matrix) = premise.matrix() else {
        panic!("joint matrix")
    };
    let ChcExpr::Op(ChcOp::And, guards) = matrix[0].as_ref() else {
        panic!("joint guard")
    };
    assert_eq!(guards.len(), 2);
    for (index, limit) in [34, 2].into_iter().enumerate() {
        let ChcExpr::Op(ChcOp::BvULt, operands) = guards[index].as_ref() else {
            panic!("range")
        };
        assert_eq!(operands[0].as_ref(), &ChcExpr::Var(binders[index].clone()));
        assert_eq!(operands[1].as_ref(), &ChcExpr::BitVec(limit, 64));
    }
    let table = [point, false, false];
    let mut env = Environment::new();
    let mut accepted = source.source_problem().clauses()[0]
        .body
        .constraint
        .as_ref()
        .is_none_or(|constraint| eval(constraint, &env, &table) == Value::Bool(true));
    for row in 0..36 {
        env.insert(binders[0].name.clone(), Value::Bv(row, 64));
        for column in 0..4 {
            env.insert(binders[1].name.clone(), Value::Bv(column, 64));
            accepted &= eval(premise.matrix(), &env, &table) == Value::Bool(true);
        }
    }
    // Every tuple outside the checked rectangle has at least one false guard.
    accepted
}
