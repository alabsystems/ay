// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

#![cfg(test)]

use super::*;

#[test]
fn exact_work_boundary_and_pre_cancel_leave_counter_unchanged() {
    let mut work = CHC_GROUND_DERIVATION_MAX_SOURCE_WORK - 1;
    let mut progress = || true;
    let mut control = GroundValidationControl::new(&mut progress);
    assert_eq!(
        charge_source_identity_work(&mut control, &mut work, 1),
        Ok(())
    );
    assert_eq!(work, CHC_GROUND_DERIVATION_MAX_SOURCE_WORK);
    assert_eq!(
        charge_source_identity_work(&mut control, &mut work, 1)
            .unwrap_err()
            .reason,
        ChcGroundDerivationArtifactErrorReason::SourceWorkLimitExceeded
    );
    assert_eq!(work, CHC_GROUND_DERIVATION_MAX_SOURCE_WORK);
    let mut refusing = || false;
    assert_eq!(
        charge_source_identity_work(
            &mut GroundValidationControl::new(&mut refusing),
            &mut work,
            0
        )
        .unwrap_err()
        .reason,
        ChcGroundDerivationArtifactErrorReason::Interrupted
    );
    assert_eq!(work, CHC_GROUND_DERIVATION_MAX_SOURCE_WORK);
}

#[test]
fn malformed_width_and_derived_width_match_old_errors() {
    for expression in [
        ChcExpr::Var(ChcVar::new("invalid", ChcSort::BitVec(0))),
        ChcExpr::Op(ChcOp::Int2Bv(0), vec![Arc::new(ChcExpr::Int(0))]),
    ] {
        let problem = problem_with_expression(expression);
        let expected = oracle::preflight_problem_source_identity(&problem);
        assert_eq!(
            expected.as_ref().unwrap_err().reason,
            ChcGroundDerivationArtifactErrorReason::SourceWorkLimitExceeded
        );
        assert_eq!(preflight(&problem, &mut || true), expected);
    }
}

#[test]
fn deep_sort_and_expression_preserve_old_work_refusal() {
    let mut sort = ChcSort::Bool;
    let mut expression = ChcExpr::Bool(true);
    for _ in 0..=CHC_GROUND_DERIVATION_MAX_SOURCE_DEPTH {
        sort = ChcSort::Array(Box::new(ChcSort::Bool), Box::new(sort));
        expression = ChcExpr::Op(ChcOp::Not, vec![Arc::new(expression)]);
    }
    for problem in [
        problem_with_expression(ChcExpr::Var(ChcVar::new("deep", sort))),
        problem_with_expression(expression),
    ] {
        let expected = oracle::preflight_problem_source_identity(&problem);
        assert!(expected.is_err());
        assert_eq!(preflight(&problem, &mut || true), expected);
    }
}

#[test]
fn every_live_clause_is_guarded_before_derived_sorts() {
    let mut problem = problem_with_expression(ChcExpr::Op(
        ChcOp::Int2Bv(0),
        vec![Arc::new(ChcExpr::Int(0))],
    ));
    problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        true,
    ))));
    let mut expression = ChcExpr::Bool(true);
    for _ in 0..=CHC_GROUND_DERIVATION_MAX_SOURCE_DEPTH {
        expression = ChcExpr::Op(ChcOp::Not, vec![Arc::new(expression)]);
    }
    problem.clauses_mut()[1].body.constraint = Some(expression);
    let expected = oracle::preflight_problem_source_identity(&problem).unwrap_err();
    assert!(
        !expected.detail.contains("source bitvector width"),
        "the later unsafe expression must stop the whole iterative preflight first"
    );
    assert_eq!(preflight(&problem, &mut || true).unwrap_err(), expected);
}

#[test]
fn unselected_declarations_are_polled_and_work_bounded() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("P", vec![ChcSort::Uninterpreted("name".to_string())]);
    rejects_every_callback(|progress| preflight(&problem, progress));
    let mut oversized = ChcProblem::new();
    oversized.declare_action("x".repeat(CHC_GROUND_DERIVATION_MAX_SOURCE_WORK / 2));
    assert_eq!(
        preflight(&oversized, &mut || true),
        oracle::preflight_problem_source_identity(&oversized)
    );
    assert!(preflight(&oversized, &mut || true).is_err());
}

#[test]
fn empty_problem_still_polls_before_success() {
    rejects_every_callback(|progress| preflight(&ChcProblem::new(), progress));
}
