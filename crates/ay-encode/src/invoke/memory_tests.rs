// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn absent_memory_budget_remains_absent_on_both_invocation_profiles() {
    let config = EncodeConfig::new();
    assert_eq!(config.memory_budget, None);
    assert_eq!(config.to_adaptive_config().memory_budget(), None);
    assert_eq!(config.to_pdr_config().memory_budget(), None);
}

#[test]
fn explicit_memory_budget_including_zero_reaches_strict_pdr() {
    for bytes in [0, 1, 64 * 1024 * 1024, usize::MAX] {
        let config = EncodeConfig::new()
            .with_proof_mode(ProofMode::Strict)
            .with_memory_budget(bytes);
        assert_eq!(config.memory_budget, Some(bytes));
        assert_eq!(config.to_adaptive_config().memory_budget(), Some(bytes));
        assert_eq!(config.to_pdr_config().memory_budget(), Some(bytes));
    }
}

#[test]
fn memory_forwarding_preserves_production_profile_and_timeout() {
    let timeout = Duration::from_secs(7);
    let config = EncodeConfig::new()
        .with_timeout(timeout)
        .with_memory_budget(1234);
    let converted = config.to_pdr_config();
    let production = PdrConfig::production(false);
    assert_eq!(converted.memory_budget(), Some(1234));
    assert_eq!(converted.solve_timeout, Some(timeout));
    assert_eq!(converted.max_frames, production.max_frames);
    assert_eq!(converted.max_iterations, production.max_iterations);
    assert_eq!(converted.max_obligations, production.max_obligations);
    assert_eq!(config.memory_budget, Some(1234));
    assert_eq!(config.timeout, Some(timeout));
}

#[test]
fn external_proof_cannot_lose_zero_budget_or_poison_a_fresh_attempt() {
    let source = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (y Int)) (=> (and (Inv x) (= y (+ x 1))) (Inv y))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;
    let fixture = || {
        let problem = ay_chc::ChcParser::parse(source).expect("original counter parses");
        let model =
            InvariantModel::parse_smtlib("(define-fun Inv ((x Int)) Bool (>= x 0))", &problem)
                .expect("original invariant parses");
        (problem, model)
    };
    let (problem, model) = fixture();
    let exhausted = EncodeConfig::new()
        .with_proof_mode(ProofMode::Strict)
        .with_timeout(Duration::from_secs(5))
        .with_memory_budget(0);
    let rejected = prove_with_external_model(problem, model, &exhausted)
        .expect("memory refusal is a non-accepted result");
    assert!(!rejected.accepted_as_proof());
    assert!(rejected.result().is_unknown());

    let (problem, model) = fixture();
    let healthy = exhausted.with_memory_budget(64 * 1024 * 1024);
    let accepted = prove_with_external_model(problem, model, &healthy)
        .expect("fresh full validation completes");
    assert!(accepted.accepted_as_proof());
    assert!(accepted.result().is_safe());
}
