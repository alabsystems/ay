// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use super::*;
use crate::model::{Model, Sense};
use crate::{BoundSide, FactRef, FarkasCertificate, LpSession, Multiplier, SolveOpts};

fn br(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn objective_model() -> Model {
    let mut model = Model::new();
    let x = model.add_col(0.0, 1.0);
    model.set_objective(&[(x, 1.0)], Sense::Minimize);
    model
}

#[test]
fn checkable_shape_rejects_wrong_point_arity() {
    let model = objective_model();
    let fabricated = Outcome::Feasible {
        model_values: Vec::new(),
        incumbent_only: false,
        dual_bound: None,
    };

    assert_eq!(
        fabricated.evidence_shape(&model),
        EvidenceShape::FieldsPresent,
        "shape classification must remain visibly non-authoritative"
    );
    assert!(matches!(
        fabricated.check_against(&model),
        Err(OutcomeCheckError::PointArity {
            expected: 1,
            actual: 0
        })
    ));
}

#[test]
fn checkable_shape_rejects_an_infeasible_public_point() {
    let model = objective_model();
    let fabricated = Outcome::Feasible {
        model_values: vec![br(2)],
        incumbent_only: false,
        dual_bound: None,
    };

    assert!(fabricated.evidence_shape(&model).has_required_fields());
    assert!(matches!(
        fabricated.check_against(&model),
        Err(OutcomeCheckError::PointRejected { .. })
    ));
}

#[test]
fn checkable_shape_rejects_a_recombined_objective_value() {
    let model = objective_model();
    let fabricated = Outcome::Optimal {
        value: br(1),
        model_values: vec![BigRational::zero()],
        // The bound is shaped to meet the fabricated value. Its invalid
        // multiplier body is immaterial: objective replay must reject first.
        cert: Some(OptimalityCertificate {
            sense: Sense::Minimize,
            objective: vec![(0, BigRational::one())],
            bound: br(1),
            multipliers: Vec::new(),
        }),
    };

    assert!(fabricated.evidence_shape(&model).has_required_fields());
    assert!(matches!(
        fabricated.check_against(&model),
        Err(OutcomeCheckError::ObjectiveMismatch { attained, reported })
            if attained.is_zero() && *reported == br(1)
    ));
}

#[test]
fn checkable_shape_rejects_a_foreign_self_declared_objective_certificate() {
    let model = objective_model();
    // This is a valid certificate for the all-zero objective on any feasible
    // model. `OptimalityCertificate::verify` intentionally verifies the
    // certificate's SELF-DECLARED objective, so exact outcome validation must
    // additionally bind that declaration to `model`'s objective.
    let foreign = OptimalityCertificate {
        sense: Sense::Minimize,
        objective: Vec::new(),
        bound: BigRational::zero(),
        multipliers: Vec::new(),
    };
    foreign
        .verify(&model)
        .expect("the standalone certificate correctly proves its empty objective");
    let fabricated = Outcome::Optimal {
        value: BigRational::zero(),
        model_values: vec![BigRational::zero()],
        cert: Some(foreign),
    };

    assert!(fabricated.evidence_shape(&model).has_required_fields());
    assert!(matches!(
        fabricated.check_against(&model),
        Err(OutcomeCheckError::OptimalityObjectiveMismatch)
    ));
}

#[test]
fn optimality_requires_an_explicit_objective() {
    let outcome = Outcome::Optimal {
        value: BigRational::zero(),
        model_values: Vec::new(),
        cert: Some(OptimalityCertificate {
            sense: Sense::Minimize,
            objective: Vec::new(),
            bound: BigRational::zero(),
            multipliers: Vec::new(),
        }),
    };

    let feasibility_only = Model::new();
    assert!(matches!(
        outcome.check_against(&feasibility_only),
        Err(OutcomeCheckError::OptimalityWithoutObjective)
    ));

    let mut explicit_zero = Model::new();
    explicit_zero.set_objective(&[], Sense::Minimize);
    let checked = outcome
        .check_against(&explicit_zero)
        .expect("an explicit all-zero objective is a genuine objective");
    assert!(checked.is_rim_closed());
}

#[test]
fn a_valid_continuous_session_result_upgrades_to_rim_closed() {
    let mut model = Model::new();
    let x = model.add_col(1.0, 2.0);
    model.set_objective(&[(x, 1.0)], Sense::Minimize);
    let opts = SolveOpts::new().with_require_certificates(true);
    let mut session = LpSession::new(&model, &opts).expect("valid continuous session");
    let outcome = session
        .optimize_model_objective()
        .expect("continuous solve succeeds");

    let checked = outcome
        .check_against(&model)
        .expect("session result revalidates against its source model");
    assert!(matches!(
        checked.outcome(),
        Outcome::Optimal {
            value,
            cert: Some(_),
            ..
        } if value == &br(1)
    ));
    assert!(checked.is_rim_closed());
}

#[test]
fn a_valid_feasible_point_upgrades_to_rim_closed() {
    let model = objective_model();
    let outcome = Outcome::Feasible {
        model_values: vec![BigRational::zero()],
        incumbent_only: false,
        dual_bound: None,
    };

    assert_eq!(outcome.evidence_shape(&model), EvidenceShape::FieldsPresent);
    let checked = outcome
        .check_against(&model)
        .expect("the exact feasible point must seal");
    assert!(matches!(checked.outcome(), Outcome::Feasible { .. }));
    assert!(checked.is_rim_closed());
}

#[test]
fn a_verified_farkas_refutation_upgrades_to_rim_closed() {
    let mut model = Model::new();
    let x = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
    let lower = model.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
    let upper = model.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);
    let outcome = Outcome::Infeasible {
        cert: Some(FarkasCertificate {
            multipliers: vec![
                Multiplier {
                    fact: FactRef::RowBound {
                        row: lower,
                        side: BoundSide::Lower,
                    },
                    coeff: BigRational::one(),
                },
                Multiplier {
                    fact: FactRef::RowBound {
                        row: upper,
                        side: BoundSide::Upper,
                    },
                    coeff: BigRational::one(),
                },
            ],
        }),
        tree_cert: None,
    };

    assert_eq!(outcome.evidence_shape(&model), EvidenceShape::FieldsPresent);
    let checked = outcome
        .check_against(&model)
        .expect("the exact Farkas contradiction must seal");
    assert!(matches!(checked.outcome(), Outcome::Infeasible { .. }));
    assert!(checked.is_rim_closed());
}

#[test]
fn an_uncertified_optimum_never_produces_a_checked_token() {
    let model = objective_model();
    let outcome = Outcome::Optimal {
        value: BigRational::zero(),
        model_values: vec![BigRational::zero()],
        cert: None,
    };

    assert!(matches!(
        outcome.evidence_shape(&model),
        EvidenceShape::MissingFields { why } if why.contains("certificate")
    ));
    assert!(matches!(
        outcome.check_against(&model),
        Err(OutcomeCheckError::MissingEvidence { why }) if why.contains("certificate")
    ));
}

#[test]
fn a_verified_integral_relaxation_gap_remains_search_dependent() {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let row = model.add_row(0.5, f64::INFINITY, &[(x, 1.0)]);
    model.set_objective(&[(x, 1.0)], Sense::Minimize);
    let lp_bound = BigRational::new(BigInt::from(1), BigInt::from(2));
    let outcome = Outcome::Optimal {
        value: br(1),
        model_values: vec![br(1)],
        cert: Some(OptimalityCertificate {
            sense: Sense::Minimize,
            objective: vec![(0, BigRational::one())],
            bound: lp_bound,
            multipliers: vec![Multiplier {
                fact: FactRef::RowBound {
                    row,
                    side: BoundSide::Lower,
                },
                coeff: BigRational::one(),
            }],
        }),
    };

    let shape = outcome.evidence_shape(&model);
    assert!(matches!(
        shape,
        EvidenceShape::MissingFields { why } if why.contains("search")
    ));
    assert!(matches!(
        outcome.check_against(&model),
        Err(OutcomeCheckError::MissingEvidence { why }) if why.contains("search")
    ));
}

#[test]
fn internal_bounds_and_no_verdict_never_look_like_exported_proofs() {
    let model = objective_model();
    for outcome in [
        Outcome::Bound {
            dual_bound: BigRational::zero(),
            rigorous: true,
        },
        Outcome::Bound {
            dual_bound: BigRational::zero(),
            rigorous: false,
        },
        Outcome::Unbounded,
        Outcome::Unknown {
            reason: UnknownReason::Timeout,
        },
    ] {
        let shape = outcome.evidence_shape(&model);
        let EvidenceShape::MissingFields { why } = shape else {
            panic!("{outcome:?} must not look independently checkable")
        };
        assert!(!why.trim().is_empty());
        assert!(matches!(
            outcome.check_against(&model),
            Err(OutcomeCheckError::MissingEvidence { .. })
        ));
    }
}

#[test]
fn an_unexported_infeasibility_claim_stays_search_dependent() {
    let model = objective_model();
    let outcome = Outcome::Infeasible {
        cert: None,
        tree_cert: None,
    };
    assert!(!outcome.evidence_shape(&model).has_required_fields());
    assert!(matches!(
        outcome.check_against(&model),
        Err(OutcomeCheckError::MissingEvidence { .. })
    ));
}
