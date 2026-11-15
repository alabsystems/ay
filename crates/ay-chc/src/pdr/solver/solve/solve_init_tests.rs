// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used)]

use super::*;
use crate::pdr::config::PdrConfig;
use crate::ChcParser;

/// A fact clause whose constraint no state satisfies still reaches
/// `init_must_summaries_from_facts`, which extracts witness instances from it
/// unchecked. Its equalities contradict each other (`x = y`, `x = 5`, `y = 6`);
/// that is an unsatisfiable input, not a propagation bug, and the debug
/// postcondition used to panic on it.
#[test]
fn init_must_summaries_accepts_an_unsatisfiable_fact_constraint() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x y) (= x 5) (= y 6)) (inv x))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"#;
    let mut solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), PdrConfig::default());
    assert!(solver.init_must_summaries_from_facts());
}

#[test]
fn retained_false_queries_survive_constructor_splits_and_validate_original_model() {
    let input = r#"
        (set-logic HORN)
        (declare-fun P (Int) Bool)
        (assert (P 0))
        (assert (forall ((x Int)) (=> (and (P x) (< x 3)) (P (+ x 1)))))
        (assert (forall ((x Int)) (=> (and (P x) (> x 3)) false)))
        (check-sat)
    "#;
    for vacuous in [true, false] {
        let mut original = ChcParser::parse(input).unwrap();
        for clause in original.clauses_mut() {
            if clause.is_query() {
                clause.body.constraint = Some(ChcExpr::Bool(!vacuous));
            }
        }
        let config = PdrConfig {
            strict_proofs: true,
            solve_timeout: Some(std::time::Duration::from_secs(5)),
            ..PdrConfig::default()
        };
        original.validate().expect("retained query is valid input");
        let result = PdrSolver::new(original.clone(), config.clone()).solve();
        match (vacuous, result) {
            (true, PdrResult::Safe(model)) => {
                assert!(PdrSolver::new(original, config).verify_model(&model));
            }
            (false, PdrResult::Unsafe(witness)) => {
                assert!(matches!(
                    PdrSolver::new(original, config).verify_counterexample(&witness),
                    crate::pdr::CexVerificationResult::Valid
                ));
            }
            (_, other) => panic!("query truth and original validation must survive: {other:?}"),
        }
    }
}

#[test]
fn predicate_free_theory_query_has_a_depth_zero_unsafe_witness() {
    let original = ChcParser::parse(
        r#"
        (set-logic HORN)
        (declare-fun P (Int) Bool)
        (assert (P 0))
        (assert (forall ((x Int)) (=> (= x 3) false)))
        (check-sat)
    "#,
    )
    .unwrap();
    let config = PdrConfig {
        strict_proofs: true,
        solve_timeout: Some(std::time::Duration::from_secs(5)),
        ..PdrConfig::default()
    };
    let PdrResult::Unsafe(witness) = PdrSolver::new(original.clone(), config.clone()).solve()
    else {
        panic!("a satisfiable query needs no relation premise");
    };
    assert!(matches!(
        PdrSolver::new(original, config).verify_counterexample(&witness),
        crate::pdr::CexVerificationResult::Valid
    ));
}
