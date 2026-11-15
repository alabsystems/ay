// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Identity compatibility, ordering and cooperative refusal controls.
#![cfg(test)]

use super::*;
use crate::{ChcDtConstructor, ChcDtSelector, ChcVar, ClauseBody};
use std::sync::Arc;

mod datatypes;
mod historical_v1;
mod oracle;
mod progress;
mod unary;

fn push_raw(problem: &mut ChcProblem, clause: HornClause) {
    let position = problem.clauses().len();
    problem.add_clause(HornClause::query(ClauseBody::empty()));
    // Identity spelling must work independently of semantic/simplification
    // authority, so retain every deliberately raw expression variant.
    problem.clauses_mut()[position] = clause;
}

fn rich_problem() -> ChcProblem {
    let datatype = ChcSort::Datatype {
        name: "Tree\n\"λ".to_string(),
        constructors: crate::ChcDtConstructors::new(vec![
            ChcDtConstructor {
                name: "Z".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "field\\name".to_string(),
                    sort: ChcSort::Array(
                        Box::new(ChcSort::BitVec(64)),
                        Box::new(ChcSort::Uninterpreted("U\t".to_string())),
                    ),
                }],
            },
            ChcDtConstructor {
                name: "A".to_string(),
                selectors: Vec::new(),
            },
        ]),
    };
    let mut problem = ChcProblem::new();
    problem.set_fixedpoint_format();
    let z = problem.declare_predicate("Z\n", vec![datatype.clone(), ChcSort::Real]);
    let a = problem.declare_predicate("A", vec![ChcSort::Bool, ChcSort::Int]);
    problem.declare_predicate("A", vec![ChcSort::Bool, ChcSort::Int]);
    let action = problem.declare_action("z\"step");
    problem.declare_action("a\nstep");
    problem.add_datatype_def(
        "Z".to_string(),
        vec![(
            "ZCtor".to_string(),
            vec![("selector".to_string(), datatype.clone())],
        )],
    );
    problem.add_datatype_def("A".to_string(), vec![("ACtor".to_string(), Vec::new())]);
    let variants = vec![
        ChcExpr::Bool(false),
        ChcExpr::Int(i128::MIN),
        ChcExpr::Real(-17, -3),
        ChcExpr::BitVec(u128::MAX, 128),
        ChcExpr::Var(ChcVar::new("v\n\"", datatype)),
        ChcExpr::Op(
            ChcOp::Add,
            vec![Arc::new(ChcExpr::Int(4)), Arc::new(ChcExpr::Int(-2))],
        ),
        ChcExpr::Op(
            ChcOp::Sub,
            vec![Arc::new(ChcExpr::Int(4)), Arc::new(ChcExpr::Int(-2))],
        ),
        ChcExpr::PredicateApp("embedded\"".to_string(), z, vec![Arc::new(ChcExpr::Int(1))]),
        ChcExpr::PredicateApp("missing".to_string(), PredicateId::new(31), Vec::new()),
        ChcExpr::FuncApp(
            "uf\\".to_string(),
            ChcSort::Real,
            vec![Arc::new(ChcExpr::Real(1, 0))],
        ),
        ChcExpr::ConstArrayMarker(ChcSort::BitVec(32)),
        ChcExpr::IsTesterMarker("Ctor\t".to_string()),
        ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::Bool(true))),
    ];
    let mut clause = HornClause::new(
        ClauseBody::new(
            vec![
                (z, vec![ChcExpr::Int(9)]),
                (a, Vec::new()),
                (z, vec![ChcExpr::Int(9)]),
            ],
            Some(ChcExpr::FuncApp(
                "all".to_string(),
                ChcSort::Bool,
                variants.into_iter().map(Arc::new).collect(),
            )),
        ),
        ClauseHead::Predicate(PredicateId::new(63), vec![ChcExpr::Int(i128::MAX)]),
    )
    .with_action(action);
    clause.source_query_ordinal = Some(37);
    push_raw(&mut problem, clause);
    push_raw(&mut problem, HornClause::query(ClauseBody::empty()));
    problem
}

fn assert_oracle(problem: &ChcProblem) {
    let expected = oracle::normalized_chc_input(problem);
    assert_eq!(input(problem), expected);
    assert_eq!(
        input_hash(problem),
        oracle::normalized_chc_input_sha256(problem)
    );
    assert_eq!(
        ordered_hash(problem),
        oracle::ordered_chc_clause_sequence_sha256(problem)
    );
    assert_eq!(
        normalized_chc_input_sha256_with_progress(problem, &mut || true),
        Ok(input_hash(problem))
    );
    assert_eq!(
        ordered_chc_clause_sequence_sha256_with_progress(problem, &mut || true),
        Ok(ordered_hash(problem))
    );
}

#[test]
fn empty_input_has_exact_existing_schema_and_lines() {
    let problem = ChcProblem::new();
    assert_eq!(
        input(&problem),
        "ay.chc.normalized-input/v1\nfixedpoint=false\ndatatypes\nactions\npredicates\nclauses\n"
    );
    assert_oracle(&problem);
}

#[test]
fn every_expression_sort_and_raw_scalar_spelling_matches_old_oracle() {
    assert_oracle(&rich_problem());
}

#[test]
fn semantic_hash_sorts_clauses_but_overlay_binds_clause_positions() {
    let first = rich_problem();
    let mut reversed = first.clone();
    reversed.clauses_mut().reverse();
    assert_oracle(&reversed);
    assert_eq!(input_hash(&first), input_hash(&reversed));
    assert_ne!(ordered_hash(&first), ordered_hash(&reversed));
}

#[test]
fn semantic_hash_sorts_body_applications_but_overlay_binds_premises() {
    let first = rich_problem();
    let mut swapped = first.clone();
    swapped.clauses_mut()[0].body.predicates.swap(0, 1);
    assert_oracle(&swapped);
    assert_eq!(input_hash(&first), input_hash(&swapped));
    assert_ne!(ordered_hash(&first), ordered_hash(&swapped));
}

#[test]
fn query_ordinal_is_only_in_the_positional_overlay() {
    let first = rich_problem();
    let mut changed = first.clone();
    changed.clauses_mut()[0].source_query_ordinal = Some(38);
    assert_oracle(&changed);
    assert_eq!(input_hash(&first), input_hash(&changed));
    assert_ne!(ordered_hash(&first), ordered_hash(&changed));
}

#[test]
fn nested_selector_and_action_identity_mutations_remain_observable() {
    let first = rich_problem();
    let mut changed = first.clone();
    changed.add_datatype_def("A".to_string(), vec![("Different".to_string(), Vec::new())]);
    assert_oracle(&changed);
    assert_ne!(input_hash(&first), input_hash(&changed));
    // The overlay spells clause payloads, not unrelated top-level datatype declarations.
    assert_eq!(ordered_hash(&first), ordered_hash(&changed));
    changed = first.clone();
    changed.clauses_mut()[0].action_id = None;
    assert_oracle(&changed);
    assert_ne!(input_hash(&first), input_hash(&changed));
    assert_ne!(ordered_hash(&first), ordered_hash(&changed));
}

#[test]
fn commutative_child_order_is_canonical_and_noncommutative_order_is_not() {
    for op in [ChcOp::Add, ChcOp::Sub] {
        let mut first = ChcProblem::new();
        push_raw(
            &mut first,
            HornClause::query(ClauseBody::constraint(ChcExpr::Op(
                op,
                vec![Arc::new(ChcExpr::Int(1)), Arc::new(ChcExpr::Int(2))],
            ))),
        );
        let mut second = first.clone();
        let Some(ChcExpr::Op(_, args)) = &mut second.clauses_mut()[0].body.constraint else {
            panic!("fixture operation")
        };
        args.reverse();
        assert_oracle(&first);
        assert_oracle(&second);
        assert_eq!(input_hash(&first) == input_hash(&second), op == ChcOp::Add);
        assert_eq!(
            ordered_hash(&first) == ordered_hash(&second),
            op == ChcOp::Add
        );
    }
}

#[test]
fn repeated_wide_argument_edges_preserve_multiplicity_and_bytes() {
    let shared = Arc::new(ChcExpr::Int(7));
    let mut problem = ChcProblem::new();
    push_raw(
        &mut problem,
        HornClause::query(ClauseBody::constraint(ChcExpr::FuncApp(
            "wide".to_string(),
            ChcSort::Bool,
            vec![shared; 4096],
        ))),
    );
    assert_oracle(&problem);
}
