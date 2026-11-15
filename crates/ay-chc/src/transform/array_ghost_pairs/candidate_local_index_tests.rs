// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]
#![allow(clippy::unwrap_used, clippy::expect_used)]

use super::*;
use crate::smt::SmtValue;
use crate::{ClauseBody, HornClause};

fn variable(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort))
}

fn array_sort(width: u32) -> ChcSort {
    ChcSort::Array(
        Box::new(ChcSort::BitVec(width)),
        Box::new(ChcSort::BitVec(8)),
    )
}

fn operation(op: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, args.into_iter().map(Arc::new).collect())
}

fn query_problem(args: Vec<ChcExpr>, constraint: ChcExpr) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let predicate = problem.declare_predicate("P", args.iter().map(ChcExpr::sort).collect());
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(predicate, args)],
        Some(constraint),
    )));
    problem
}

fn candidates(problem: &ChcProblem, slots: usize) -> Option<Vec<QueryAnchoredGhostCandidate>> {
    query_anchored_ghost_candidates(problem, &GhostPairSpec::analyze(problem, slots))
}

fn suffix_bad(
    index: ChcExpr,
    old: ChcExpr,
    new: ChcExpr,
    value: ChcExpr,
    fill: ChcExpr,
) -> ChcExpr {
    ChcExpr::and_all([
        operation(ChcOp::BvUGe, vec![index.clone(), ChcExpr::BitVec(32, 64)]),
        operation(ChcOp::BvUGe, vec![index.clone(), old]),
        operation(ChcOp::BvULt, vec![index, new]),
        ChcExpr::ne(value, fill),
    ])
}

#[test]
fn symbolic_resize_local_index_keeps_all_three_bounds_and_exact_guarded_formula() {
    // Synthetic query matching the source resize suffix, deliberately beyond
    // its 32 ground instances. j is NOT added to the predicate signature.
    let array = variable("data", array_sort(64));
    let old = variable("old", ChcSort::BitVec(64));
    let new = variable("new", ChcSort::BitVec(64));
    let fill = variable("fill", ChcSort::BitVec(8));
    let j = variable("j", ChcSort::BitVec(64));
    let bad = suffix_bad(
        j.clone(),
        old.clone(),
        new.clone(),
        ChcExpr::select(array.clone(), j),
        fill.clone(),
    );
    let problem = query_problem(vec![array, old, new, fill], bad);
    let batch = candidates(&problem, 1).expect("local BV64 index has one ghost slot");
    assert_eq!(batch.len(), 1);
    let candidate = &batch[0];
    assert_eq!(candidate.vars.len(), 6);
    let v = |position: usize| ChcExpr::var(candidate.vars[position].clone());
    let expected = ChcExpr::implies(
        ChcExpr::eq(v(4), v(4)),
        ChcExpr::not(suffix_bad(v(4), v(1), v(2), v(5), v(3))),
    );
    assert_eq!(candidate.formula, expected);
    assert!(!candidate.formula.vars().iter().any(|var| var.name == "j"));
    for old in [0u128, 2, 32, 65] {
        for new in [2u128, 65, 66] {
            for j in [0u128, 31, 32, 64, 65, u64::MAX as u128] {
                for value in [0u128, 7] {
                    let values = [
                        (1, old, 64),
                        (2, new, 64),
                        (3, 7, 8),
                        (4, j, 64),
                        (5, value, 8),
                    ];
                    assert_eq!(
                        evaluate(candidate, &values),
                        !(j >= 32 && j >= old && j < new && value != 7)
                    );
                }
            }
        }
    }
}

fn evaluate(candidate: &QueryAnchoredGhostCandidate, values: &[(usize, u128, u32)]) -> bool {
    let env = values
        .iter()
        .map(|(position, value, width)| {
            (
                candidate.vars[*position].name.clone(),
                SmtValue::BitVec(*value, *width),
            )
        })
        .collect();
    match crate::expr::evaluate::evaluate_expr(&candidate.formula, &env) {
        Some(SmtValue::Bool(value)) => value,
        other => panic!("expected a closed Boolean candidate, got {other:?}"),
    }
}

#[test]
fn distinct_local_indices_require_distinct_slots_and_remain_independent() {
    let array = variable("a", array_sort(2));
    let j = variable("j", ChcSort::BitVec(2));
    let k = variable("k", ChcSort::BitVec(2));
    let constraint = ChcExpr::and_all([
        ChcExpr::ne(j.clone(), k.clone()),
        ChcExpr::ne(
            ChcExpr::select(array.clone(), j),
            ChcExpr::select(array.clone(), k),
        ),
    ]);
    let problem = query_problem(vec![array], constraint);
    assert!(candidates(&problem, 1).is_none());
    let batch = candidates(&problem, 2).expect("two independent local indices");
    let candidate = &batch[0];
    assert_eq!(candidate.vars.len(), 5);
    for j in 0u128..4 {
        for k in 0u128..4 {
            for a in 0u128..2 {
                for b in 0u128..2 {
                    assert_eq!(
                        evaluate(candidate, &[(1, j, 2), (2, a, 8), (3, k, 2), (4, b, 8)]),
                        !(j != k && a != b)
                    );
                }
            }
        }
    }
}

#[test]
fn one_local_index_shared_between_arrays_links_their_ghost_indices() {
    let a = variable("a", array_sort(2));
    let b = variable("b", array_sort(2));
    let j = variable("j", ChcSort::BitVec(2));
    let bad = ChcExpr::ne(
        ChcExpr::select(a.clone(), j.clone()),
        ChcExpr::select(b.clone(), j),
    );
    let problem = query_problem(vec![a, b], bad);
    let batch = candidates(&problem, 1).expect("one slot per observed array");
    for i in 0u128..4 {
        for j in 0u128..4 {
            for a in 0u128..2 {
                for b in 0u128..2 {
                    assert_eq!(
                        evaluate(&batch[0], &[(2, i, 2), (3, a, 8), (4, j, 2), (5, b, 8)]),
                        i != j || a == b
                    );
                }
            }
        }
    }
}

#[test]
fn unobserved_or_only_computed_local_indices_remain_unsupported() {
    let a = variable("a", array_sort(64));
    let j = variable("j", ChcSort::BitVec(64));
    let k = variable("k", ChcSort::BitVec(64));
    let computed = operation(ChcOp::BvAdd, vec![j.clone(), ChcExpr::BitVec(1, 64)]);
    for bad in [
        ChcExpr::ne(ChcExpr::select(a.clone(), computed), ChcExpr::BitVec(0, 8)),
        ChcExpr::and(
            ChcExpr::ne(j.clone(), k),
            ChcExpr::ne(ChcExpr::select(a.clone(), j), ChcExpr::BitVec(0, 8)),
        ),
    ] {
        assert!(candidates(&query_problem(vec![a.clone()], bad), 2).is_none());
    }
}

#[test]
fn mixed_sort_names_and_scalar_functions_cannot_capture_local_index() {
    let a = variable("a", array_sort(64));
    let j = variable("j", ChcSort::BitVec(64));
    let read_bad = ChcExpr::ne(ChcExpr::select(a.clone(), j), ChcExpr::BitVec(0, 8));
    for extra in [
        variable("j", ChcSort::Bool),
        variable("a", ChcSort::Bool),
        ChcExpr::FuncApp("opaque".to_string(), ChcSort::Bool, vec![]),
    ] {
        let problem = query_problem(vec![a.clone()], ChcExpr::and(read_bad.clone(), extra));
        assert!(candidates(&problem, 1).is_none());
    }
}

#[test]
fn local_index_census_is_bounded_and_polls_all_guard_occurrences() {
    let a = variable("a", array_sort(64));
    let j = variable("j", ChcSort::BitVec(64));
    let bad = ChcExpr::and(
        operation(ChcOp::BvUGe, vec![j.clone(), ChcExpr::BitVec(32, 64)]),
        ChcExpr::ne(ChcExpr::select(a.clone(), j), ChcExpr::BitVec(0, 8)),
    );
    let problem = query_problem(vec![a], bad.clone());
    let spec = GhostPairSpec::analyze(&problem, 1);
    let clause = &problem.clauses()[0];
    let (predicate, args) = &clause.body.predicates[0];
    let positions =
        query_argument_positions(args, &problem.get_predicate(*predicate).unwrap().arg_sorts)
            .unwrap();
    let layout = &spec.preds[predicate];
    let mut polls = 0;
    assert!(
        local_index_reads(&bad, &positions, layout, 1, &mut 4096, &mut || {
            polls += 1;
            false
        })
        .is_some()
    );
    for stop in 1..=polls {
        let mut calls = 0;
        assert!(
            local_index_reads(&bad, &positions, layout, 1, &mut 4096, &mut || {
                calls += 1;
                calls == stop
            })
            .is_none()
        );
        assert_eq!(calls, stop);
    }
    let mut remaining = 0;
    assert!(
        local_index_reads(&bad, &positions, layout, 1, &mut remaining, &mut || false).is_none()
    );
    assert_eq!(remaining, 0);
    let oversized = ChcExpr::select(
        args[0].clone(),
        variable(&"j".repeat(4097), ChcSort::BitVec(64)),
    );
    let mut remaining = 4096;
    assert!(local_index_reads(
        &oversized,
        &positions,
        layout,
        1,
        &mut remaining,
        &mut || false,
    )
    .is_none());
    assert_eq!(remaining, 0);
}
