// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

#![cfg(test)]

use super::*;
use crate::{ChcDtConstructor, ChcDtSelector, ChcOp, ChcVar, ClauseBody, HornClause};
use std::sync::Arc;

mod boundaries;
mod oracle;

fn problem_with_expression(expression: ChcExpr) -> ChcProblem {
    let mut problem = ChcProblem::new();
    problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        true,
    ))));
    // Preserve the exact raw source instead of invoking the insertion simplifier.
    problem.clauses_mut()[0].body.constraint = Some(expression);
    problem
}

fn source_fixture() -> ChcProblem {
    let variable = ChcExpr::Var(ChcVar::new("x", ChcSort::Int));
    let mut problem = problem_with_expression(ChcExpr::eq(
        ChcExpr::add(variable, ChcExpr::Int(1)),
        ChcExpr::Int(2),
    ));
    let action = problem.declare_action("advance");
    problem.clauses_mut()[0].action_id = Some(action);
    let datatype = ChcSort::Datatype {
        name: "Packet".to_string(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: "packet".to_string(),
            selectors: vec![ChcDtSelector {
                name: "payload".to_string(),
                sort: ChcSort::Int,
            }],
        }]),
    };
    problem.declare_predicate("Unused", vec![datatype]);
    problem.declare_predicate(
        "ArrayUnused",
        vec![ChcSort::Array(
            Box::new(ChcSort::Bool),
            Box::new(ChcSort::BitVec(8)),
        )],
    );
    problem.add_datatype_def(
        "Packet".to_string(),
        vec![(
            "packet".to_string(),
            vec![("payload".to_string(), ChcSort::Int)],
        )],
    );
    problem
}

fn preflight(
    problem: &ChcProblem,
    progress: &mut dyn FnMut() -> bool,
) -> Result<(), ChcGroundDerivationArtifactError> {
    preflight_problem_source_identity(&mut GroundValidationControl::new(progress), problem)
}

fn check_source(
    problem: &ChcProblem,
    progress: &mut dyn FnMut() -> bool,
) -> Result<(), ChcGroundDerivationArtifactError> {
    super::super::validate_ground_source_problem_with_control(
        problem,
        &mut GroundValidationControl::new(progress),
    )
}

fn rejects_every_callback(
    mut run: impl FnMut(&mut dyn FnMut() -> bool) -> Result<(), ChcGroundDerivationArtifactError>,
) {
    let mut callbacks = 0usize;
    assert_eq!(
        run(&mut || {
            callbacks += 1;
            true
        }),
        Ok(())
    );
    assert!(callbacks > 1);
    for refusal in 1..=callbacks {
        let mut seen = 0usize;
        let failure = run(&mut || {
            seen += 1;
            seen != refusal
        })
        .unwrap_err();
        assert_eq!(
            failure.reason,
            ChcGroundDerivationArtifactErrorReason::Interrupted
        );
        assert_eq!(seen, refusal, "the first refusal is terminal");
    }
    assert_eq!(
        run(&mut || true),
        Ok(()),
        "an independent retry remains valid"
    );
}

#[test]
fn preflight_every_callback_including_final_refuses() {
    let problem = source_fixture();
    rejects_every_callback(|progress| preflight(&problem, progress));
}

#[test]
fn full_source_every_callback_including_final_refuses() {
    // Keep the per-ordinal loop tiny while crossing all semantic phase polls.
    let problem = problem_with_expression(ChcExpr::Bool(true));
    rejects_every_callback(|progress| check_source(&problem, progress));
}

#[test]
fn always_continue_preserves_full_source_results_and_details() {
    let valid = source_fixture();
    assert_eq!(oracle::validate_ground_source_problem(&valid), Ok(()));
    assert_eq!(check_source(&valid, &mut || true), Ok(()));
    let mut wrong_action = problem_with_expression(ChcExpr::Bool(true));
    wrong_action.clauses_mut()[0].action_id = Some(crate::ActionId::new(99));
    let mut wrong_predicate = problem_with_expression(ChcExpr::Bool(true));
    wrong_predicate.clauses_mut()[0]
        .body
        .predicates
        .push((crate::PredicateId(99), vec![]));
    for problem in [
        wrong_action,
        wrong_predicate,
        problem_with_expression(ChcExpr::Int(3)),
    ] {
        assert_eq!(
            check_source(&problem, &mut || true),
            oracle::validate_ground_source_problem(&problem)
        );
    }
}

#[test]
fn pre_cancel_invalid_source_does_not_become_source_error() {
    let problem = problem_with_expression(ChcExpr::Int(3));
    assert_eq!(
        check_source(&problem, &mut || false).unwrap_err().reason,
        ChcGroundDerivationArtifactErrorReason::Interrupted
    );
}

#[test]
fn stopped_control_cannot_resume_in_source_validation() {
    let problem = source_fixture();
    let mut calls = 0usize;
    let mut progress = || {
        calls += 1;
        calls > 1
    };
    let mut control = GroundValidationControl::new(&mut progress);
    for _ in 0..2 {
        assert_eq!(
            super::super::validate_ground_source_problem_with_control(&problem, &mut control)
                .unwrap_err()
                .reason,
            ChcGroundDerivationArtifactErrorReason::Interrupted
        );
    }
    assert_eq!(calls, 1);
}

#[test]
fn wide_expression_edges_are_polled_individually() {
    let problem = problem_with_expression(ChcExpr::Op(
        ChcOp::And,
        (0..64).map(|_| Arc::new(ChcExpr::Bool(true))).collect(),
    ));
    let mut calls = 0usize;
    assert_eq!(
        preflight(&problem, &mut || {
            calls += 1;
            true
        }),
        Ok(())
    );
    assert!(
        calls > 2 * 64,
        "child pushes and popped nodes must both poll"
    );
    assert_eq!(
        preflight(&problem, &mut || true),
        oracle::preflight_problem_source_identity(&problem)
    );
}

#[test]
fn nested_datatype_dag_is_priced_by_reference() {
    // As a tree this sort has 2^40 leaves; the identity spells 40 definitions
    // and one reference per occurrence, and the preflight prices exactly that.
    let mut sort = ChcSort::BitVec(32);
    for level in 1..=40 {
        sort = ChcSort::Datatype {
            name: format!("D{level}"),
            constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
                name: format!("mk{level}"),
                selectors: vec![
                    ChcDtSelector {
                        name: format!("a{level}"),
                        sort: sort.clone(),
                    },
                    ChcDtSelector {
                        name: format!("b{level}"),
                        sort,
                    },
                ],
            }]),
        };
    }
    let mut problem = problem_with_expression(ChcExpr::Var(ChcVar::new("x", sort.clone())));
    problem.declare_predicate("P", vec![sort]);
    rejects_every_callback(|progress| preflight(&problem, progress));
}
