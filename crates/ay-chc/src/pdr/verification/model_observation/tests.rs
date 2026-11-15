// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ChcParser, ChcProblem, PdrConfig};

fn fixture() -> (ChcProblem, InvariantModel, crate::PdrConfig) {
    let problem = ChcParser::parse(
        r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#,
    )
    .unwrap();
    let model =
        InvariantModel::parse_smtlib("(define-fun Inv ((x Int)) Bool (>= x 0))", &problem).unwrap();
    (problem, model, crate::PdrConfig::default())
}

#[test]
fn warm_and_fresh_verifiers_keep_original_instance_and_ambient_caps() {
    let (problem, model, config) = fixture();
    let mut verifier = PdrSolver::new(problem, config.with_memory_budget(Some(1)));
    assert_eq!(verifier.config.memory_budget, Some(1));
    assert!(!verifier.verify_model_fresh(&model));
    assert!(!verifier.verify_model_at_safe_boundary(&model, None));
    assert_eq!(verifier.smt.term_memory_budget, Some(1));
    let mut verifier = PdrSolver::new(
        fixture().0,
        PdrConfig::default().with_memory_budget(Some(usize::MAX)),
    );
    {
        let _ambient = SmtContext::scoped_thread_term_memory_budget(Some(1));
        assert!(!verifier.verify_model(&model));
        assert_eq!(verifier.smt.term_memory_budget, Some(1));
    }
    assert!(!verifier.verify_model(&model));
}

#[test]
fn original_refutation_marker_resets_for_healthy_and_repeated_verification() {
    let (problem, model, config) = fixture();
    let bad =
        InvariantModel::parse_smtlib("(define-fun Inv ((x Int)) Bool true)", &problem).unwrap();
    let mut verifier = PdrSolver::new(problem, config.with_memory_budget(Some(64 * 1024 * 1024)));
    assert!(!verifier.verify_model(&bad));
    assert_eq!(
        verifier.observed_model_validation_failure(),
        Some(ExternalInvariantValidation::Refuted)
    );
    assert!(verifier.verify_model(&model));
    assert_eq!(verifier.observed_model_validation_failure(), None);
    assert!(!verifier.verify_model(&InvariantModel::new()));
    assert_eq!(
        verifier.observed_model_validation_failure(),
        Some(ExternalInvariantValidation::Rejected)
    );
    assert!(!verifier.verify_model(&bad));
    assert_eq!(
        verifier.observed_model_validation_failure(),
        Some(ExternalInvariantValidation::Refuted)
    );
}
