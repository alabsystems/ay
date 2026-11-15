// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ChcSort, ChcVar};
use std::sync::Arc;

mod surface;

mod captured;
mod captured22;
mod congruence;
mod congruence_resources;
mod early_congruence;
mod original;
mod resources;
mod selected_constants;
mod store_noop;

fn op(op: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, args.into_iter().map(Arc::new).collect())
}

fn variable(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, sort))
}

fn prove(body: &ChcExpr, head: &ChcExpr) -> Result<bool> {
    entails(body, head, &mut Owner::capture().expect("original owner"))
}

#[test]
fn exact_array_terms_and_renamed_scalar_conjunctions_are_retained() {
    let array = variable(
        "renamed_array",
        ChcSort::Array(Box::new(ChcSort::BitVec(2)), Box::new(ChcSort::Bool)),
    );
    let read = op(ChcOp::Select, vec![array.clone(), ChcExpr::BitVec(1, 2)]);
    let guard = op(
        ChcOp::Or,
        vec![read.clone(), variable("renamed_flag", ChcSort::Bool)],
    );
    let body = op(ChcOp::And, vec![guard.clone(), read.clone()]);
    let head = op(
        ChcOp::And,
        vec![guard, ChcExpr::eq(array.clone(), array), read],
    );
    assert_eq!(prove(&body, &head), Ok(true));
}

#[test]
fn changed_heads_and_or_arm_extraction_are_not_proved() {
    let x = variable("x", ChcSort::Bool);
    let y = variable("y", ChcSort::Bool);
    let disjunction = op(ChcOp::Or, vec![x.clone(), y.clone()]);
    assert_eq!(prove(&disjunction, &x), Ok(false));
    assert_eq!(prove(&x, &ChcExpr::not(x.clone())), Ok(false));
    assert_eq!(prove(&x, &y), Ok(false));
    assert_eq!(
        prove(&ChcExpr::Bool(true), &ChcExpr::Bool(false)),
        Ok(false)
    );
}

#[test]
fn every_dead_arm_is_typed_before_reflexivity_or_true() {
    let invalid = op(
        ChcOp::Store,
        vec![
            ChcExpr::const_array(ChcSort::BitVec(2), ChcExpr::Bool(false)),
            ChcExpr::BitVec(1, 3),
            ChcExpr::Bool(true),
        ],
    );
    let reflexive = ChcExpr::eq(invalid.clone(), invalid);
    let body = op(ChcOp::And, vec![ChcExpr::Bool(false), reflexive.clone()]);
    assert_eq!(prove(&body, &ChcExpr::Bool(true)), Ok(false));
    let head = op(ChcOp::Or, vec![ChcExpr::Bool(true), reflexive]);
    assert_eq!(prove(&ChcExpr::Bool(false), &head), Ok(false));
}

#[test]
fn ill_typed_reflexivity_literals_and_name_collisions_decline() {
    let invalid = [
        ChcExpr::BitVec(4, 2),
        ChcExpr::BitVec(0, 0),
        ChcExpr::Real(1, 0),
        op(
            ChcOp::BvAdd,
            vec![ChcExpr::BitVec(1, 2), ChcExpr::BitVec(1, 3)],
        ),
        op(ChcOp::Eq, vec![ChcExpr::Int(0), ChcExpr::Bool(false)]),
        op(ChcOp::And, vec![]),
    ];
    for term in invalid {
        assert_eq!(
            prove(&ChcExpr::Bool(true), &ChcExpr::eq(term.clone(), term)),
            Ok(false)
        );
    }
    let body = ChcExpr::eq(variable("same", ChcSort::Int), ChcExpr::Int(0));
    let boolean = variable("same", ChcSort::Bool);
    assert_eq!(
        prove(&body, &ChcExpr::eq(boolean.clone(), boolean)),
        Ok(false)
    );
}

#[test]
fn undeclared_function_signatures_never_gain_reflexive_authority() {
    let unknown = ChcExpr::FuncApp("unknown_function".into(), ChcSort::Int, vec![]);
    let reflexive = ChcExpr::eq(unknown.clone(), unknown);
    assert_eq!(prove(&reflexive, &reflexive), Ok(false));
    assert_eq!(prove(&ChcExpr::Bool(true), &reflexive), Ok(false));
}

#[test]
fn accepted_small_bv_implications_hold_for_every_original_assignment() {
    use crate::smt::SmtValue;
    use ay_core::kani_compat::DetHashMap;
    let x = variable("x", ChcSort::BitVec(2));
    let y = variable("y", ChcSort::BitVec(2));
    let atoms = [
        ChcExpr::eq(x.clone(), ChcExpr::BitVec(1, 2)),
        op(ChcOp::BvULt, vec![x.clone(), y.clone()]),
        ChcExpr::eq(x.clone(), y.clone()),
    ];
    for i in 0..atoms.len() {
        for j in 0..atoms.len() {
            let body = op(ChcOp::And, vec![atoms[i].clone(), atoms[j].clone()]);
            let heads = [
                atoms[i].clone(),
                atoms[j].clone(),
                ChcExpr::eq(x.clone(), x.clone()),
            ];
            for head in heads {
                assert_eq!(prove(&body, &head), Ok(true));
                for xv in 0..4 {
                    for yv in 0..4 {
                        let env: DetHashMap<_, _> = [
                            ("x".into(), SmtValue::BitVec(xv, 2)),
                            ("y".into(), SmtValue::BitVec(yv, 2)),
                        ]
                        .into_iter()
                        .collect();
                        let premise = crate::expr::evaluate_expr(&body, &env).unwrap();
                        let conclusion = crate::expr::evaluate_expr(&head, &env).unwrap();
                        assert!(
                            premise == SmtValue::Bool(false) || conclusion == SmtValue::Bool(true)
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn shared_boolean_dag_is_not_expanded_as_a_tree() {
    let mut expression = Arc::new(variable("shared", ChcSort::Bool));
    for _ in 0..40 {
        expression = Arc::new(ChcExpr::Op(
            ChcOp::And,
            vec![Arc::clone(&expression), expression],
        ));
    }
    assert_eq!(prove(&expression, &expression), Ok(true));
}
