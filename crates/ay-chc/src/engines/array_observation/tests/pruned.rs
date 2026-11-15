// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Owned-clone budget != source registry or proof authority. Frozen pruned
//! clauses retain their old signatures, but their owned syntax must be scanned.

use super::*;
use crate::{ClauseBody, HornClause};

fn frozen_pruned(element: ChcExpr) -> ChcProblem {
    frozen_parts(element, bv(5, 32))
}

fn frozen_parts(element: ChcExpr, historical_initializer: ChcExpr) -> ChcProblem {
    let mut problem = source(9, false);
    let ClauseHead::Predicate(_, arguments) = &mut problem.clauses_mut()[0].head else {
        panic!("fact");
    };
    arguments[0] = ChcExpr::ConstArray(ChcSort::BitVec(64), Arc::new(historical_initializer));
    let body = problem.lookup_predicate("B").unwrap();
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(
            body,
            vec![
                ChcExpr::ConstArray(ChcSort::BitVec(64), Arc::new(element)),
                bv(0, 64),
            ],
        )],
        Some(ChcExpr::Bool(false)),
    )));
    assert_eq!(problem.pruned_false_query_count(), 1);
    problem
        .try_scalarize_const_array_selects_with_map()
        .unwrap();
    // These OWNED old B(array,i) args now have a different registry from the
    // live scalar B(cell,i). The semantic iterator intentionally skips them.
    assert_eq!(
        problem.owned_clauses_for_budget().count(),
        problem.source_clauses().count() + 1
    );
    let array = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let later = problem.declare_predicate("later", vec![array.clone()]);
    problem.add_clause(HornClause::fact(
        ChcExpr::Bool(true),
        later,
        vec![ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::Int(7)))],
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(later, vec![variable("fresh_a", array)])],
        Some(ChcExpr::not(ChcExpr::eq(
            ChcExpr::select(
                variable(
                    "fresh_a",
                    ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
                ),
                ChcExpr::Int(0),
            ),
            ChcExpr::Int(7),
        ))),
    )));
    problem
}

#[test]
fn small_frozen_pruned_source_is_budgeted_without_wrong_registry_typing_or_blanket_refusal() {
    let original = frozen_pruned(bv(5, 32));
    let before = original.clone();
    let projected = project(&original);
    assert_eq!(projected.reduced.pruned_false_query_count(), 1);
    assert_eq!(
        projected.reduced.pruned_false_query_ids(),
        original.pruned_false_query_ids()
    );
    let later = original.lookup_predicate("later").unwrap();
    assert_eq!(
        projected.reduced.get_predicate(later).unwrap().arg_sorts,
        [ChcSort::Int]
    );
    same_source(&before, &original);
}

#[test]
fn deep_owned_frozen_pruned_root_declines_before_clone_and_keeps_original_source() {
    let mut element = bv(5, 32);
    for _ in 0..super::super::admission::MAX_DEPTH {
        element = operation(ChcOp::BvAdd, element, bv(0, 32));
    }
    let original = frozen_pruned(element);
    let before = original.clone();
    assert!(Projection::new(&original, &mut || true).is_none());
    same_source(&before, &original);
}

#[test]
fn large_shared_owned_frozen_pruned_root_cannot_hide_recursive_copy_work() {
    let mut element = bv(5, 32);
    for _ in 0..14 {
        let child = Arc::new(element);
        element = ChcExpr::Op(ChcOp::BvAdd, vec![child.clone(), child]);
    }
    let original = frozen_pruned(element);
    let before = original.clone();
    assert!(Projection::new(&original, &mut || true).is_none());
    same_source(&before, &original);
}

fn assert_owned_roots_fit(problem: &ChcProblem) {
    let mut scan = super::super::admission::Scan::default();
    for clause in problem.owned_clauses_for_budget() {
        for (_, args) in &clause.body.predicates {
            for arg in args {
                scan.expression(arg, &mut || true).unwrap();
            }
        }
        if let Some(constraint) = &clause.body.constraint {
            scan.expression(constraint, &mut || true).unwrap();
        }
        if let ClauseHead::Predicate(_, args) = &clause.head {
            for arg in args {
                scan.expression(arg, &mut || true).unwrap();
            }
        }
    }
}

#[test]
fn deep_historical_source_is_scanned_even_when_every_current_owned_root_is_small() {
    let mut historical = bv(5, 32);
    for _ in 0..super::super::admission::MAX_DEPTH {
        historical = operation(ChcOp::BvAdd, historical, bv(0, 32));
    }
    let original = frozen_parts(bv(5, 32), historical);
    assert_owned_roots_fit(&original);
    assert!(original.frozen_pruned_source_for_budget().is_some());
    let before = original.clone();
    assert!(Projection::new(&original, &mut || true).is_none());
    same_source(&before, &original);
}

#[test]
fn large_shared_historical_source_is_scanned_on_the_same_occurrence_budget() {
    let mut historical = bv(5, 32);
    for _ in 0..14 {
        let child = Arc::new(historical);
        historical = ChcExpr::Op(ChcOp::BvAdd, vec![child.clone(), child]);
    }
    let original = frozen_parts(bv(5, 32), historical);
    assert_owned_roots_fit(&original);
    assert!(original.frozen_pruned_source_for_budget().is_some());
    let before = original.clone();
    assert!(Projection::new(&original, &mut || true).is_none());
    same_source(&before, &original);
}
