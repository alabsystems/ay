// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn problem(expected: u8) -> ChcProblem {
    ChcParser::parse(&format!(
        "(set-logic HORN)
        (declare-rel inv ((Array (_ BitVec 8) (_ BitVec 8))))
        (declare-rel error ())
        (declare-var a (Array (_ BitVec 8) (_ BitVec 8)))
        (rule (inv (lambda ((i (_ BitVec 8))) (bvadd i #x07))))
        (rule (=> (and (inv a) (not (= (select a #x03) #x{expected:02x}))) error))
        (query error)"
    ))
    .expect("typed scalar lambda problem")
}

#[test]
fn lambda_observation_route_requires_original_model_validation() {
    let original = problem(10);
    let adaptive = AdaptivePortfolio::new(original.clone(), AdaptiveConfig::test_default());
    let result = adaptive.try_array_const_key_cegar_route(None);
    let Some(PortfolioResult::Safe(model)) = result else {
        panic!("lambda observation must produce an original-validated model: {result:?}");
    };
    assert!(crate::engines::validate_external_invariant_model(
        &original,
        &model,
        &PdrConfig {
            strict_proofs: true,
            disable_array_scalarization: true,
            preserve_original_clauses: true,
            ..PdrConfig::default()
        },
    )
    .expect("independent original-array validation must complete"));
}

#[test]
fn lambda_observation_route_cannot_accept_false_property() {
    let adaptive = AdaptivePortfolio::new(problem(9), AdaptiveConfig::test_default());
    assert!(!matches!(
        adaptive.try_array_const_key_cegar_route(None),
        Some(PortfolioResult::Safe(_))
    ));
}
