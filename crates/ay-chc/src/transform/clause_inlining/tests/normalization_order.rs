// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A compound head argument must reuse any later plain head position. Avoid
//! artificial existentials without losing repeated positions or real locals.

use super::*;
use crate::ChcOp;

fn op(operation: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(
        operation,
        args.into_iter().map(std::sync::Arc::new).collect(),
    )
}

fn normalized(args: Vec<ChcExpr>, body: ChcExpr) -> (Vec<ChcVar>, ChcExpr) {
    let mut problem = ChcProblem::new();
    let predicate = problem.declare_predicate("P", args.iter().map(ChcExpr::sort).collect());
    let clause = HornClause::new(
        ClauseBody::constraint(body),
        ClauseHead::Predicate(predicate, args),
    );
    let result = ClauseInliner::normalize_head_for_back_translation(&clause);
    let ClauseHead::Predicate(_, args) = result.head else {
        panic!("normalization preserves the predicate head")
    };
    let formals: Vec<_> = args
        .iter()
        .map(|arg| match arg {
            ChcExpr::Var(var) => var.clone(),
            _ => panic!("every normalized head argument is a variable"),
        })
        .collect();
    let distinct: FxHashSet<_> = formals.iter().map(|var| &var.name).collect();
    assert_eq!(distinct.len(), formals.len(), "positions stay distinct");
    drop(distinct);
    (formals, result.body.constraint.unwrap())
}

// A deliberately independent evaluator for the tiny BV2 test fragment. It
// does not call the normalizer, equality propagation, or a solver.
fn value(expr: &ChcExpr, env: &[(&ChcVar, u128)]) -> u128 {
    match expr {
        ChcExpr::Bool(value) => u128::from(*value),
        ChcExpr::BitVec(value, 2) => *value,
        ChcExpr::Var(var) => env.iter().find(|(key, _)| *key == var).unwrap().1,
        ChcExpr::Op(operation, args) => {
            let args: Vec<_> = args.iter().map(|arg| value(arg, env)).collect();
            match operation {
                ChcOp::And => u128::from(args.iter().all(|value| *value != 0)),
                ChcOp::Or => u128::from(args.iter().any(|value| *value != 0)),
                ChcOp::Eq => u128::from(args[0] == args[1]),
                ChcOp::BvAdd => (args[0] + args[1]) & 3,
                ChcOp::BvULt => u128::from(args[0] < args[1]),
                _ => panic!("unsupported test operation {operation:?}"),
            }
        }
        _ => panic!("unsupported test expression {expr:?}"),
    }
}

#[test]
fn compound_before_plain_and_repeated_positions_has_no_artificial_locals() {
    let x = ChcVar::new("x", ChcSort::BitVec(2));
    let x_expr = ChcExpr::var(x);
    let compound = op(ChcOp::BvAdd, vec![x_expr.clone(), ChcExpr::BitVec(1, 2)]);
    let body = op(ChcOp::BvULt, vec![x_expr.clone(), ChcExpr::BitVec(3, 2)]);
    let (formals, constraint) = normalized(vec![compound, x_expr.clone(), x_expr], body);
    assert!(constraint.vars().iter().all(|var| formals.contains(var)));
    let mut admitted = 0;
    for output in 0..4 {
        for first in 0..4 {
            for repeated in 0..4 {
                let expected = first < 3 && repeated == first && output == ((first + 1) & 3);
                let actual = value(
                    &constraint,
                    &[
                        (&formals[0], output),
                        (&formals[1], first),
                        (&formals[2], repeated),
                    ],
                ) != 0;
                assert_eq!(actual, expected, "tuple {output},{first},{repeated}");
                admitted += usize::from(actual);
            }
        }
    }
    assert_eq!(admitted, 3);
}

#[test]
fn compound_only_local_is_shared_not_dropped_or_captured() {
    let x = ChcVar::new("x", ChcSort::BitVec(2));
    let y = ChcVar::new("y", ChcSort::BitVec(2));
    let x_expr = ChcExpr::var(x);
    let y_expr = ChcExpr::var(y);
    let sum = op(ChcOp::BvAdd, vec![x_expr.clone(), y_expr.clone()]);
    let next = op(ChcOp::BvAdd, vec![y_expr.clone(), ChcExpr::BitVec(1, 2)]);
    let body = op(ChcOp::BvULt, vec![y_expr, ChcExpr::BitVec(2, 2)]);
    let (formals, constraint) = normalized(vec![sum, next, x_expr.clone(), x_expr], body);
    let locals: Vec<_> = constraint
        .vars()
        .into_iter()
        .filter(|var| !formals.contains(var))
        .collect();
    assert_eq!(locals.len(), 1, "one genuinely existential y, not x");
    assert_eq!(locals[0].sort, ChcSort::BitVec(2));
    let mut admitted = 0;
    for sum in 0..4 {
        for next in 0..4 {
            for first in 0..4 {
                for repeated in 0..4 {
                    let expected = (0..4).any(|y| {
                        y < 2
                            && repeated == first
                            && sum == ((first + y) & 3)
                            && next == ((y + 1) & 3)
                    });
                    let actual = (0..4).any(|y| {
                        value(
                            &constraint,
                            &[
                                (&formals[0], sum),
                                (&formals[1], next),
                                (&formals[2], first),
                                (&formals[3], repeated),
                                (&locals[0], y),
                            ],
                        ) != 0
                    });
                    assert_eq!(actual, expected, "tuple {sum},{next},{first},{repeated}");
                    admitted += usize::from(actual);
                }
            }
        }
    }
    assert_eq!(admitted, 8);
}

#[test]
fn boolean_compound_before_many_layout_formals_keeps_disjunctions_closed() {
    let bases: Vec<_> = (0..7)
        .map(|index| ChcVar::new(format!("stack_base_{index}"), ChcSort::BitVec(8)))
        .collect();
    let observations: Vec<_> = bases
        .iter()
        .map(|base| ChcExpr::eq(ChcExpr::var(base.clone()), ChcExpr::BitVec(0, 8)))
        .collect();
    let mut arguments = vec![op(ChcOp::Or, observations)];
    arguments.extend(bases.iter().cloned().map(ChcExpr::var));
    arguments.push(ChcExpr::var(bases[0].clone()));
    let mut layout = Vec::new();
    for left in 0..6 {
        for right in left + 1..6 {
            layout.push(op(
                ChcOp::Or,
                vec![
                    op(
                        ChcOp::BvULt,
                        vec![
                            ChcExpr::var(bases[left].clone()),
                            ChcExpr::var(bases[right].clone()),
                        ],
                    ),
                    op(
                        ChcOp::BvULt,
                        vec![
                            ChcExpr::var(bases[right].clone()),
                            ChcExpr::var(bases[left].clone()),
                        ],
                    ),
                ],
            ));
        }
    }
    assert_eq!(layout.len(), 15);
    let (formals, constraint) = normalized(arguments, op(ChcOp::And, layout));
    assert_eq!(formals.len(), 9);
    assert!(constraint.vars().iter().all(|var| formals.contains(var)));
}
