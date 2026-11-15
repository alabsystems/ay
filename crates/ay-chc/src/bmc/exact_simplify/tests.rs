// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
#![cfg(test)]

use super::simplify;
use crate::bmc::{AcyclicNames, BmcSolver, FxHashMap, IntInterval};
use crate::expr::evaluate::evaluate_expr;
use crate::smt::SmtValue;
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar};
use std::cell::Cell;
use std::sync::Arc;

mod oracle;
mod progress;
mod routes;

fn variable(name: &str) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, ChcSort::Int))
}

fn contradictory_bounds() -> Vec<ChcExpr> {
    vec![
        ChcExpr::ge(variable("x"), ChcExpr::Int(2)),
        ChcExpr::le(variable("x"), ChcExpr::Int(1)),
    ]
}

fn ordinary_cases() -> Vec<Vec<ChcExpr>> {
    let x = variable("x");
    let y = variable("y");
    let p = ChcExpr::Var(ChcVar::new("p", ChcSort::Bool));
    let stored = ChcExpr::store(
        ChcExpr::const_array(ChcSort::Bool, ChcExpr::Bool(false)),
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
    );
    vec![
        Vec::new(),
        vec![ChcExpr::Bool(true)],
        vec![ChcExpr::Bool(false)],
        contradictory_bounds(),
        vec![ChcExpr::ne(x.clone(), y.clone())],
        vec![
            ChcExpr::eq(x.clone(), y.clone()),
            ChcExpr::eq(y.clone(), ChcExpr::Int(3)),
            ChcExpr::le(x.clone(), ChcExpr::Int(4)),
        ],
        vec![p.clone(), ChcExpr::not(p)],
        vec![ChcExpr::select(stored, ChcExpr::Bool(true))],
        vec![
            ChcExpr::ge(x.clone(), ChcExpr::Int(0)),
            ChcExpr::le(x.clone(), ChcExpr::Int(2)),
            ChcExpr::eq(y, ChcExpr::mul(x.clone(), x)),
        ],
    ]
}

fn live(conjuncts: Vec<ChcExpr>) -> ChcExpr {
    let mut keep_going = || true;
    let mut names = AcyclicNames::new(&ChcProblem::new(), &mut keep_going).unwrap();
    let result = simplify(conjuncts, &mut names).expect("live bounded simplification");
    assert!(!names.stopped());
    result
}

#[test]
fn ordinary_outputs_match_frozen_orchestration_with_current_numeric_helpers() {
    // The oracle freezes the old pipeline, not the old interval-comparison bug.
    // Both lanes deliberately use the independently corrected numeric helpers.
    for conjuncts in ordinary_cases() {
        assert_eq!(live(conjuncts.clone()), oracle::simplify(conjuncts));
    }
}

#[test]
fn empty_truth_and_infeasible_bounds_have_distinct_definitive_results() {
    assert_eq!(live(Vec::new()), ChcExpr::Bool(true));
    assert_eq!(live(vec![ChcExpr::Bool(true)]), ChcExpr::Bool(true));
    assert_eq!(live(vec![ChcExpr::Bool(false)]), ChcExpr::Bool(false));
    assert_eq!(live(contradictory_bounds()), ChcExpr::Bool(false));
}

#[test]
fn an_unconstrained_disequality_keeps_its_concrete_satisfying_source_witness() {
    let source = ChcExpr::ne(variable("x"), variable("y"));
    let output = live(vec![source.clone()]);
    let model = FxHashMap::from_iter([
        ("x".to_owned(), SmtValue::Int(1)),
        ("y".to_owned(), SmtValue::Int(2)),
    ]);
    assert_eq!(evaluate_expr(&source, &model), Some(SmtValue::Bool(true)));
    assert_eq!(evaluate_expr(&output, &model), Some(SmtValue::Bool(true)));
    assert_ne!(output, ChcExpr::Bool(false));
}

#[test]
fn literal_propagation_preserves_full_typed_identity_for_raw_same_name_variables() {
    // This raw AST probes the typed substitution contract, not acceptance of
    // two different SMT declarations with the same source name.
    let boolean = ChcExpr::Var(ChcVar::new("x", ChcSort::Bool));
    let source = ChcExpr::and_all([ChcExpr::eq(variable("x"), ChcExpr::Int(0)), boolean.clone()]);
    let expected = source.propagate_equalities();
    assert_eq!(expected, boolean);
    let mut keep_going = || true;
    let mut names = AcyclicNames::new(&ChcProblem::new(), &mut keep_going).unwrap();
    assert_eq!(super::propagate(source, &mut names), Some(expected));
    assert!(!names.stopped());
}

#[test]
fn a_large_raw_child_is_refused_before_false_can_hide_it() {
    let mut deep = ChcExpr::Var(ChcVar::new("deep", ChcSort::Bool));
    for _ in 0..crate::expr::MAX_EXPR_RECURSION_DEPTH {
        deep = ChcExpr::Op(ChcOp::Not, vec![Arc::new(deep)]);
    }
    let mut keep_going = || true;
    let mut names = AcyclicNames::new(&ChcProblem::new(), &mut keep_going).unwrap();
    assert!(simplify(vec![ChcExpr::Bool(false), deep], &mut names).is_none());
    assert!(names.stopped());
}
