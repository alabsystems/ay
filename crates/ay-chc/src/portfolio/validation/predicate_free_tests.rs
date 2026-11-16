// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::engines::{prove_external_invariant_model, validate_external_invariant_model};
use crate::portfolio::accept::AcceptDecision;
use crate::portfolio::{EngineConfig, PortfolioConfig};
use crate::{ChcParser, VerifiedChcResult};

const FALSE_SOURCE: &str = "(set-logic HORN)\n(assert false)\n";
const TRUE_SOURCE: &str = "(set-logic HORN)\n(assert true)\n";
const EMPTY_SOURCE: &str = "(set-logic HORN)\n";
const ARITHMETIC_SAFE: &str = r#"
(set-logic HORN)
(declare-var x Int)
(rule (=> (and (< x 0) (> x 1)) false))
"#;
const ARITHMETIC_UNSAFE: &str = r#"
(set-logic HORN)
(declare-var x Int)
(rule (=> (< x 0) false))
"#;
const CASES: [(&str, bool); 5] = [
    (FALSE_SOURCE, false),
    (TRUE_SOURCE, true),
    (ARITHMETIC_SAFE, true),
    (ARITHMETIC_UNSAFE, false),
    (EMPTY_SOURCE, true),
];

fn solver(source: &str, strict_proofs: bool) -> PortfolioSolver {
    let problem = ChcParser::parse(source).unwrap();
    let original_clauses = format!("{:?}", problem.clauses());
    let solver = PortfolioSolver::new(
        problem,
        PortfolioConfig {
            engines: vec![EngineConfig::Pdr(PdrConfig::default())],
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
    solver
}

#[test]
fn full_validation_checks_predicate_free_clauses_with_empty_interpretations() {
    for strict_proofs in [false, true] {
        for (source, valid) in CASES {
            let solver = solver(source, strict_proofs);
            assert!(solver.original_problem.predicates().is_empty());
            let model = InvariantModel::new();
            // Translation alone is not authority: it can carry an empty model
            // even when the original clauses are invalid.
            assert!(solver.back_translate_safe_model(&model).unwrap().is_empty());
            for mode in [ValidationBudget::Standard, ValidationBudget::PerRule] {
                let checked = solver.validate_safe_with_mode_pre_translated(model.clone(), mode);
                assert_eq!(checked.is_ok(), valid, "source={source}, got {checked:?}");
                assert_eq!(
                    matches!(
                        solver.validate_safe_with_mode(&model, mode),
                        ValidationResult::Valid
                    ),
                    valid,
                    "source={source}",
                );
            }
        }
    }
}

#[test]
fn query_validation_checks_predicate_free_clauses_in_both_entrypoints() {
    for strict_proofs in [false, true] {
        for (source, valid) in CASES {
            let solver = solver(source, strict_proofs);
            let model = InvariantModel::new();
            for result in [
                solver.validate_safe_query_only(&model),
                solver.validate_safe_query_only_pre_translated(&model),
            ] {
                if valid {
                    assert!(
                        matches!(result, SafePrecheckResult::Valid),
                        "got {result:?}"
                    );
                } else {
                    assert!(
                        matches!(result, SafePrecheckResult::Invalid(_)),
                        "got {result:?}"
                    );
                }
            }
        }
    }
}

#[test]
fn actual_acceptance_checks_predicate_free_empty_safe_candidates() {
    for strict_proofs in [false, true] {
        for (source, valid) in CASES {
            let solver = solver(source, strict_proofs);
            let decision = solver.accept_or_reject(
                PortfolioResult::Safe(InvariantModel::new()),
                false,
                "PDR",
                0,
            );
            if valid {
                let AcceptDecision::Accept(PortfolioResult::Safe(checked)) = decision else {
                    panic!("expected checked Safe for {source}, got {decision:?}");
                };
                assert!(checked.is_empty());
            } else {
                assert!(
                    matches!(decision, AcceptDecision::Reject),
                    "got {decision:?}"
                );
            }
        }
    }
}

#[test]
fn public_empty_model_validation_and_proof_check_original_predicate_free_clauses() {
    for strict_proofs in [false, true] {
        for (source, valid) in CASES {
            let problem = ChcParser::parse(source).unwrap();
            let model = InvariantModel::new();
            let config = PdrConfig {
                strict_proofs,
                ..PdrConfig::default()
            };
            assert_eq!(
                validate_external_invariant_model(&problem, &model, &config).unwrap(),
                valid,
            );
            let run = prove_external_invariant_model(problem, model, config).unwrap();
            assert_eq!(
                run.accepted_as_proof(),
                valid,
                "source={source}, got {run:?}"
            );
            if valid {
                let VerifiedChcResult::Safe(checked) = run.result() else {
                    panic!("expected checked Safe, got {run:?}");
                };
                assert!(checked.model().is_empty());
            } else {
                assert!(run.result().is_unknown(), "got {run:?}");
            }
        }
    }
}

#[test]
fn predicate_free_trivial_solving_keeps_true_false_and_arithmetic_results() {
    for strict_proofs in [false, true] {
        for (source, valid) in CASES {
            let solver = solver(source, strict_proofs);
            let result = solver.solve();
            if valid {
                assert!(matches!(result, PortfolioResult::Safe(_)), "got {result:?}");
            } else {
                assert!(
                    matches!(result, PortfolioResult::Unsafe(_)),
                    "got {result:?}"
                );
            }
        }
    }
    // The arithmetic positive has a real variable-bearing original query,
    // not an empty problem or a parser-folded Bool(false) admission shortcut.
    let problem = ChcParser::parse(ARITHMETIC_SAFE).unwrap();
    assert!(problem.predicates().is_empty());
    assert_eq!(problem.clauses().len(), 1);
    let query = problem.queries().next().unwrap();
    let constraint = query.body.constraint.as_ref().unwrap();
    assert_ne!(constraint.vars(), [] as [ChcVar; 0]);
    assert!(!matches!(constraint, ChcExpr::Bool(_)));
    // Constant-false query bodies are pruned by ChcProblem::add_clause:
    // assert-true is a vacuous positive, not evidence of live-clause checking.
    assert!(ChcParser::parse(TRUE_SOURCE).unwrap().clauses().is_empty());
}

#[test]
fn empty_models_still_refuse_declared_predicates() {
    for strict_proofs in [false, true] {
        let solver = solver("(set-logic HORN)\n(declare-rel P (Int))\n", strict_proofs);
        assert_eq!(solver.original_problem.predicates().len(), 1);
        assert!(solver.original_problem.clauses().is_empty());
        let model = InvariantModel::new();
        assert!(solver
            .validate_safe_with_mode_pre_translated(model.clone(), ValidationBudget::PerRule)
            .is_err());
        assert!(matches!(
            solver.validate_safe_query_only(&model),
            SafePrecheckResult::Invalid(_)
        ));
        assert!(!validate_external_invariant_model(
            &solver.original_problem,
            &model,
            &PdrConfig::default(),
        )
        .unwrap());
    }
}

#[test]
fn predicate_free_clause_validation_honors_cancelled_and_expired_boundaries() {
    for strict_proofs in [false, true] {
        let solver = solver(ARITHMETIC_SAFE, strict_proofs);
        assert_eq!(solver.original_problem.clauses().len(), 1);
        let model = InvariantModel::new();
        solver.cancellation_token.cancel();
        assert!(solver
            .validate_safe_with_mode_pre_translated(model.clone(), ValidationBudget::PerRule)
            .is_err());
        assert!(matches!(
            solver.validate_safe_query_only(&model),
            SafePrecheckResult::Invalid(_)
        ));
        assert!(matches!(
            solver.accept_or_reject(PortfolioResult::Safe(model.clone()), false, "PDR", 0),
            AcceptDecision::Reject
        ));
        let cancelled = PdrConfig {
            cancellation_token: Some(solver.cancellation_token.clone()),
            ..PdrConfig::default()
        };
        let expired = PdrConfig {
            solve_timeout: Some(Duration::ZERO),
            ..PdrConfig::default()
        };
        for config in [cancelled, expired] {
            assert!(
                !validate_external_invariant_model(&solver.original_problem, &model, &config,)
                    .unwrap()
            );
            let run = prove_external_invariant_model(
                solver.original_problem.clone(),
                model.clone(),
                config,
            )
            .unwrap();
            assert!(!run.accepted_as_proof());
            assert!(run.result().is_unknown());
        }
        let mut verifier = PdrSolver::new(
            solver.original_problem.clone(),
            PdrConfig {
                preserve_original_clauses: true,
                ..PdrConfig::default()
            },
        );
        verifier.set_validation_deadline(Duration::ZERO);
        assert!(!verifier.verify_model(&model));
        assert!(!verifier.verify_model_query_only(&model));
    }
}
