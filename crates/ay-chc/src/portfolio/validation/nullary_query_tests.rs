// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::portfolio::accept::AcceptDecision;
use crate::portfolio::PortfolioConfig;
use crate::ChcParser;

// The system is safe, but error=true violates its exact authored query.
// Expanding that query to error_p0=>false can hide the invalid interpretation.
const SOURCE: &str = r#"
(set-logic HORN)
(declare-rel State (Int))
(declare-rel error_p0 ())
(declare-rel error ())
(declare-var x Int)
(declare-var xp Int)
(rule (=> (= x 0) (State x)))
(rule (=> (and (State x) (= xp (+ x 1))) (State xp)))
(rule (=> (and (State x) (< x 0)) error_p0))
(rule (=> error_p0 error))
(query error)
"#;

fn fixture(strict_proofs: bool, error_value: bool) -> (PortfolioSolver, InvariantModel) {
    let problem = ChcParser::parse(SOURCE).unwrap();
    let state = problem.lookup_predicate("State").unwrap();
    let error_p0 = problem.lookup_predicate("error_p0").unwrap();
    let error = problem.lookup_predicate("error").unwrap();
    let queries: Vec<_> = problem.queries().collect();
    assert_eq!(queries.len(), 1);
    assert_eq!(queries[0].body.predicates, vec![(error, Vec::new())]);
    assert_eq!(problem.clauses().len(), 5);
    let original_clauses = format!("{:?}", problem.clauses());
    let solver = PortfolioSolver::new(
        problem,
        PortfolioConfig {
            engines: Vec::new(),
            parallel: false,
            enable_preprocessing: false,
            strict_proofs,
            ..PortfolioConfig::default()
        },
    );
    assert_eq!(
        format!("{:?}", solver.original_problem.clauses()),
        original_clauses
    );
    assert_eq!(format!("{:?}", solver.problem.clauses()), original_clauses);

    let x = ChcVar::new("x", ChcSort::Int);
    let mut model = InvariantModel::new();
    model.set(
        state,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(0)),
        ),
    );
    model.set(
        error_p0,
        PredicateInterpretation::new(Vec::new(), ChcExpr::Bool(false)),
    );
    model.set(
        error,
        PredicateInterpretation::new(Vec::new(), ChcExpr::Bool(error_value)),
    );
    model.individually_inductive = true;
    model.convergence_proven = true;
    (solver, model)
}

#[test]
fn full_validation_preserves_exact_nullary_error_query() {
    for strict_proofs in [false, true] {
        for error_value in [false, true] {
            for mode in [ValidationBudget::Standard, ValidationBudget::PerRule] {
                let (solver, model) = fixture(strict_proofs, error_value);
                let expected = format!("{model:?}");
                let translated = solver.back_translate_safe_model(&model).unwrap();
                assert_eq!(format!("{translated:?}"), expected);
                let result = solver.validate_safe_with_mode_pre_translated(translated, mode);
                if error_value {
                    assert!(
                        result.is_err(),
                        "invalid original query model passed: {result:?}"
                    );
                } else {
                    let checked = result.expect("the exact valid model must still pass");
                    assert_eq!(format!("{checked:?}"), expected);
                }
            }
        }
    }
}

#[test]
fn query_precheck_preserves_exact_nullary_error_query() {
    for strict_proofs in [false, true] {
        for error_value in [false, true] {
            let (solver, model) = fixture(strict_proofs, error_value);
            let translated = solver.back_translate_safe_model(&model).unwrap();
            let result = solver.validate_safe_query_only_pre_translated(&translated);
            if error_value {
                assert!(
                    matches!(result, SafePrecheckResult::Invalid(_)),
                    "got {result:?}"
                );
            } else {
                // error=false is exactly the negation of the unconditional
                // query; the existing guard correctly defers to full checking.
                assert!(
                    matches!(result, SafePrecheckResult::ExactNegatedQuery(_)),
                    "got {result:?}"
                );
                assert!(solver
                    .validate_safe_with_mode_pre_translated(translated, ValidationBudget::PerRule)
                    .is_ok());
            }
        }
    }
}

#[test]
fn acceptance_rejects_nullary_error_model_without_clause_rewriting() {
    for strict_proofs in [false, true] {
        for error_value in [false, true] {
            let (solver, model) = fixture(strict_proofs, error_value);
            let expected = format!("{model:?}");
            // Exercise the common sequential/parallel acceptance boundary;
            // needs_validation=false must not bypass mandatory Safe validation.
            let decision = solver.accept_or_reject(PortfolioResult::Safe(model), false, "PDR", 0);
            if error_value {
                assert!(
                    matches!(decision, AcceptDecision::Reject),
                    "got {decision:?}"
                );
            } else {
                let AcceptDecision::Accept(PortfolioResult::Safe(checked)) = decision else {
                    panic!("expected checked original model, got {decision:?}");
                };
                assert_eq!(format!("{checked:?}"), expected);
            }
        }
    }
}
