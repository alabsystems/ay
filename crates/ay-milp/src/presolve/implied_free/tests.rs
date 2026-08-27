// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::time::Duration;

use super::*;
use crate::cert::{BoundSide, FactRef, Multiplier};
use crate::model::Sense;

fn integer(value: i64) -> BigRational {
    BigRational::from_integer(value.into())
}

fn primal_only_certificate() -> (Model, AffineAggregationCertificate) {
    let mut model = Model::new();
    let x = model.add_int_col(0.0, 2.0);
    let y = model.add_int_col(0.0, 2.0);
    model.add_row(0.0, 0.0, &[(x, 1.0), (y, -1.0)]);
    model.set_objective(&[(x, 1.0), (y, 2.0)], Sense::Minimize);

    let (reduced, post) =
        aggregate_implied_free_equalities(&model, None, None).expect("the equality must aggregate");
    let reduced_point = vec![BigRational::zero(); reduced.num_cols()];
    let outcome = Outcome::Optimal {
        value: reduced.objective_value_at(&reduced_point),
        model_values: reduced_point,
        cert: None,
    };
    let certificate = post
        .certificate_for_outcome(&outcome, &reduced, &model, None, None)
        .expect("a checked source primal must produce an artifact");
    (model, certificate)
}

fn optimality_certificate() -> (Model, AffineAggregationCertificate) {
    let mut model = Model::new();
    let x = model.add_int_col(0.0, 3.0);
    model.add_int_col(2.0, 2.0);
    model.set_objective(&[(x, 1.0)], Sense::Minimize);

    let (reduced, post) = aggregate_implied_free_equalities(&model, None, None)
        .expect("the fixed column must project");
    let inner = OptimalityCertificate {
        sense: Sense::Minimize,
        objective: vec![(0, integer(1))],
        bound: integer(0),
        multipliers: vec![Multiplier {
            fact: FactRef::ColBound {
                col: Col(0),
                side: BoundSide::Lower,
            },
            coeff: integer(1),
        }],
    };
    inner
        .verify(&reduced)
        .expect("the reduced lower-bound proof is valid");
    let outcome = Outcome::Optimal {
        value: integer(0),
        model_values: vec![integer(0)],
        cert: Some(inner),
    };
    let certificate = post
        .certificate_for_outcome(&outcome, &reduced, &model, None, None)
        .expect("the exact reduced optimum must produce an artifact");
    (model, certificate)
}

#[test]
fn unsupported_inner_proof_is_explicitly_partial() {
    let (model, certificate) = primal_only_certificate();
    assert!(matches!(
        certificate.claim(),
        AffineAggregationClaim::Optimal { .. }
    ));
    assert!(matches!(
        certificate.inner_proof(),
        AffineAggregationInnerProof::Unsupported
    ));
    assert_eq!(
        certificate.verify(&model),
        Ok(AffineAggregationVerification {
            primal_verified: true,
            infeasibility_verified: false,
            optimality_verified: false,
        })
    );
}

#[test]
fn no_objective_discards_a_vacuous_reduced_optimality_proof() {
    let mut model = Model::new();
    let x = model.add_int_col(0.0, 2.0);
    let y = model.add_int_col(0.0, 2.0);
    model.add_row(0.0, 0.0, &[(x, 1.0), (y, -1.0)]);
    let (reduced, post) =
        aggregate_implied_free_equalities(&model, None, None).expect("the equality must aggregate");
    let reduced_point = vec![integer(1); reduced.num_cols()];
    let outcome = Outcome::Optimal {
        value: integer(0),
        model_values: reduced_point,
        cert: Some(OptimalityCertificate {
            sense: Sense::Minimize,
            objective: Vec::new(),
            bound: integer(0),
            multipliers: Vec::new(),
        }),
    };
    let certificate = post
        .certificate_for_outcome(&outcome, &reduced, &model, None, None)
        .expect("the source point is still useful");
    assert_eq!(certificate.claim(), &AffineAggregationClaim::Feasible);
    assert!(matches!(
        certificate.inner_proof(),
        AffineAggregationInnerProof::Unsupported
    ));
    assert!(certificate.verify(&model).is_ok());
}

#[test]
fn exact_inner_optimality_proves_only_the_model_objective() {
    let (model, certificate) = optimality_certificate();
    assert_eq!(
        certificate.verify(&model),
        Ok(AffineAggregationVerification {
            primal_verified: true,
            infeasibility_verified: false,
            optimality_verified: true,
        })
    );

    // This remains a valid exact dual proof in the reduced frame, but it
    // bounds 2*x rather than the reduced model's x objective.  A wrapper
    // that checked only `OptimalityCertificate::verify` would launder it.
    let mut tampered = certificate;
    let AffineAggregationInnerProof::Optimality(inner) = &mut tampered.inner_proof else {
        panic!("fixture must carry optimality evidence");
    };
    inner.objective[0].1 = integer(2);
    inner.multipliers[0].coeff = integer(2);
    assert_eq!(
        tampered.verify(&model),
        Err(AffineAggregationCertificateError::InnerProof)
    );
}

#[test]
fn aggregation_artifact_rejects_every_tampered_replay_boundary() {
    let (model, certificate) = primal_only_certificate();

    let mut tampered = certificate.clone();
    tampered.analysis.source_digest.push('0');
    assert_eq!(
        tampered.verify(&model),
        Err(AffineAggregationCertificateError::SourceDigest)
    );

    let mut tampered = certificate.clone();
    tampered.analysis.reduced_digest.push('0');
    assert_eq!(
        tampered.verify(&model),
        Err(AffineAggregationCertificateError::ReducedDigest)
    );

    let mut tampered = certificate.clone();
    tampered.analysis.objective_delta += integer(1);
    assert_eq!(
        tampered.verify(&model),
        Err(AffineAggregationCertificateError::ObjectiveDelta)
    );

    let mut tampered = certificate.clone();
    tampered.analysis.caps.version += 1;
    assert_eq!(
        tampered.verify(&model),
        Err(AffineAggregationCertificateError::Caps)
    );

    let mut different_model = model.clone();
    different_model.add_int_col(0.0, 1.0);
    assert_eq!(
        tampered.verify(&different_model),
        Err(AffineAggregationCertificateError::SourceDigest),
        "model binding is checked before any attacker-controlled payload"
    );

    let mut tampered = certificate.clone();
    tampered.source_primal.as_mut().expect("source point")[0] =
        BigRational::from_integer(num_bigint::BigInt::from(1u8) << MAX_RATIONAL_BITS as usize);
    assert_eq!(
        tampered.verify(&model),
        Err(AffineAggregationCertificateError::Caps)
    );

    let mut tampered = certificate.clone();
    let bounds = Arc::make_mut(&mut tampered.analysis.bounds);
    bounds[0].lower = Some(integer(3));
    bounds[0].upper = Some(integer(2));
    assert_eq!(
        tampered.verify(&model),
        Err(AffineAggregationCertificateError::AnalysisBox)
    );

    let mut tampered = certificate.clone();
    let steps = Arc::make_mut(&mut tampered.analysis.steps);
    let AffineRecovery::Equality { constant, .. } = &mut steps[0] else {
        panic!("fixture must begin with an equality recovery");
    };
    *constant += integer(1);
    assert_eq!(
        tampered.verify(&model),
        Err(AffineAggregationCertificateError::Replay)
    );

    let mut tampered = certificate.clone();
    tampered.inner_proof = AffineAggregationInnerProof::Farkas(FarkasCertificate {
        multipliers: Vec::new(),
    });
    assert_eq!(
        tampered.verify(&model),
        Err(AffineAggregationCertificateError::InnerProof)
    );

    let mut tampered = certificate;
    tampered.source_primal.as_mut().expect("source point")[0] = integer(3);
    assert_eq!(
        tampered.verify(&model),
        Err(AffineAggregationCertificateError::Primal)
    );
}

#[test]
fn fixed_column_projects_rows_and_objective_exactly() {
    let mut model = Model::new();
    let fixed = model.add_int_col(3.0, 3.0);
    let survivor = model.add_int_col(0.0, 10.0);
    model.add_row(5.0, f64::INFINITY, &[(fixed, 1.0), (survivor, 1.0)]);
    model.set_objective(&[(fixed, 2.0), (survivor, 1.0)], Sense::Minimize);

    let (reduced, post) =
        aggregate_implied_free_equalities(&model, None, None).expect("fixed projection must fire");
    assert_eq!(reduced.num_cols(), 1);
    assert_eq!(reduced.num_rows(), 1);
    assert_eq!(reduced.row(Row(0)), (&[(0, 1.0)][..], 2.0, f64::INFINITY));
    assert_eq!(*post.const_delta(), integer(6));
    let point = post
        .widen(&[integer(4)], None, None)
        .expect("right reduced width");
    assert_eq!(point, vec![integer(3), integer(4)]);
    assert!(model.check_point(&point).is_ok());
    assert_eq!(
        model.objective_value_at(&point),
        reduced.objective_value_at(&[integer(4)]) + post.const_delta()
    );
}

#[test]
fn affine_integer_chain_recovers_in_reverse_order() {
    let mut model = Model::new();
    let x = model.add_int_col(5.0, 10.0);
    let y = model.add_int_col(0.0, 5.0);
    let z = model.add_int_col(2.0, 7.0);
    model.add_row(5.0, 5.0, &[(x, 1.0), (y, -1.0)]); // x = y+5
    model.add_row(7.0, 7.0, &[(y, 1.0), (z, 1.0)]); // y = 7-z
    model.set_objective(&[(x, 2.0), (y, 3.0), (z, 4.0)], Sense::Minimize);

    let (reduced, post) =
        aggregate_implied_free_equalities(&model, None, None).expect("affine chain must aggregate");
    assert_eq!(reduced.num_cols(), 1);
    assert_eq!(reduced.num_rows(), 0);
    assert_eq!(post.recoveries().len(), 2);
    assert_eq!(*post.const_delta(), integer(45));
    let reduced_point = vec![integer(4)];
    let point = post
        .widen(&reduced_point, None, None)
        .expect("right reduced width");
    assert_eq!(point, vec![integer(8), integer(3), integer(4)]);
    assert!(model.check_point(&point).is_ok());
    assert_eq!(
        model.objective_value_at(&point),
        reduced.objective_value_at(&reduced_point) + post.const_delta()
    );
}

#[test]
fn no_objective_state_survives_the_reduction() {
    let mut model = Model::new();
    let x = model.add_int_col(0.0, 4.0);
    let y = model.add_int_col(0.0, 4.0);
    model.add_row(0.0, 0.0, &[(x, 1.0), (y, -1.0)]);
    assert!(!model.has_objective());

    let (reduced, _) =
        aggregate_implied_free_equalities(&model, None, None).expect("the equality must aggregate");
    assert!(
        !reduced.has_objective(),
        "setting a zero offset must not turn feasibility into optimization"
    );
}

#[test]
fn maximize_offset_and_fixed_objective_constant_compose() {
    let mut model = Model::new();
    let fixed = model.add_int_col(3.0, 3.0);
    let survivor = model.add_int_col(0.0, 4.0);
    model.set_objective(&[(fixed, 2.0), (survivor, 1.0)], Sense::Maximize);
    model.set_objective_offset(7.0);

    let (reduced, post) = aggregate_implied_free_equalities(&model, None, None)
        .expect("the fixed objective column must project");
    assert!(reduced.has_objective());
    assert_eq!(reduced.sense(), Sense::Maximize);
    assert_eq!(reduced.objective_offset(), 7.0);
    assert_eq!(*post.const_delta(), integer(6));
    let reduced_point = vec![integer(4)];
    let full = post
        .widen(&reduced_point, None, None)
        .expect("bounded postsolve");
    assert_eq!(
        model.objective_value_at(&full),
        reduced.objective_value_at(&reduced_point) + post.const_delta()
    );
    assert_eq!(model.objective_value_at(&full), integer(17));
}

#[test]
fn zero_memory_declines_even_a_zero_nnz_projection() {
    let mut model = Model::new();
    model.add_int_col(1.0, 1.0);
    assert!(aggregate_implied_free_equalities(&model, None, Some(0)).is_none());
    assert!(aggregate_implied_free_equalities(&model, None, Some(1)).is_none());
    let (_, post) = aggregate_implied_free_equalities(&model, None, None)
        .expect("the unlimited fixture itself is reducible");
    assert!(post.widen(&[], None, Some(0)).is_none());
    let now = Instant::now();
    let expired = now.checked_sub(Duration::from_millis(1)).unwrap_or(now);
    assert!(post.widen(&[], Some(expired), None).is_none());
}

#[test]
fn inequality_only_integral_model_declines_in_the_metadata_preflight() {
    let mut model = Model::new();
    let columns: Vec<_> = (0..128).map(|_| model.add_binary_col()).collect();
    let row: Vec<_> = columns.iter().map(|&column| (column, 1.0)).collect();
    model.add_row(f64::NEG_INFINITY, 64.0, &row);
    assert!(structural_preflight(&model, None, None).is_none());
    assert!(aggregate_implied_free_equalities(&model, None, None).is_none());
}

fn ternary_points(width: usize) -> Vec<Vec<BigRational>> {
    let count = 3usize.pow(width as u32);
    (0..count)
        .map(|mut code| {
            (0..width)
                .map(|_| {
                    let digit = (code % 3) as i64;
                    code /= 3;
                    integer(digit)
                })
                .collect()
        })
        .collect()
}

#[test]
fn random_small_integer_models_are_exhaustively_bijective() {
    let mut state = 0xA11F_1EE5_D15C_A11Fu64;
    let mut next = || {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        state
    };

    for case in 0..48 {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, 2.0);
        let y = model.add_int_col(0.0, 2.0);
        let z = model.add_int_col(0.0, 2.0);
        if next() & 1 == 0 {
            model.add_row(0.0, 0.0, &[(x, 1.0), (y, -1.0)]);
        } else {
            model.add_row(2.0, 2.0, &[(x, 1.0), (y, 1.0)]);
        }
        let a = (next() % 5) as i64 - 2;
        let b = (next() % 5) as i64 - 2;
        let c = (next() % 5) as i64 - 2;
        let rhs = (next() % 7) as i64 - 1;
        model.add_row(
            f64::NEG_INFINITY,
            rhs as f64,
            &[(x, a as f64), (y, b as f64), (z, c as f64)],
        );
        let ox = (next() % 7) as i64 - 3;
        let oy = (next() % 7) as i64 - 3;
        let oz = (next() % 7) as i64 - 3;
        let sense = if next() & 1 == 0 {
            Sense::Minimize
        } else {
            Sense::Maximize
        };
        model.set_objective(&[(x, ox as f64), (y, oy as f64), (z, oz as f64)], sense);
        model.set_objective_offset((next() % 5) as f64 - 2.0);

        let (reduced, post) = aggregate_implied_free_equalities(&model, None, None)
            .unwrap_or_else(|| panic!("case {case}: admissible equality did not aggregate"));
        assert_eq!(reduced.num_cols(), 2, "case {case}");

        let mut original_values = Vec::new();
        for original_point in ternary_points(model.num_cols()) {
            if model.check_point(&original_point).is_err() {
                continue;
            }
            let mut projected = vec![BigRational::zero(); post.n_reduced];
            for (original, mapped) in post.map.iter().enumerate() {
                if let Some(mapped) = mapped {
                    projected[mapped.index()] = original_point[original].clone();
                }
            }
            assert!(reduced.check_point(&projected).is_ok(), "case {case}");
            assert_eq!(
                post.widen(&projected, None, None),
                Some(original_point.clone()),
                "case {case}: reverse recovery is not the inverse projection"
            );
            assert_eq!(
                model.objective_value_at(&original_point),
                reduced.objective_value_at(&projected) + post.const_delta(),
                "case {case}: objective identity"
            );
            original_values.push(model.objective_value_at(&original_point));
        }

        let mut reduced_values = Vec::new();
        for reduced_point in ternary_points(reduced.num_cols()) {
            if reduced.check_point(&reduced_point).is_err() {
                continue;
            }
            let full = post
                .widen(&reduced_point, None, None)
                .unwrap_or_else(|| panic!("case {case}: bounded recovery declined"));
            assert!(model.check_point(&full).is_ok(), "case {case}");
            reduced_values.push(reduced.objective_value_at(&reduced_point) + post.const_delta());
        }
        original_values.sort();
        reduced_values.sort();
        assert_eq!(original_values, reduced_values, "case {case}");
    }
}

#[test]
fn non_integer_affine_recovery_is_declined() {
    let mut model = Model::new();
    let x = model.add_int_col(0.0, 1.0);
    let y = model.add_int_col(0.0, 1.0);
    model.add_row(0.0, 0.0, &[(x, 2.0), (y, -1.0)]);

    assert!(aggregate_implied_free_equalities(&model, None, None).is_none());
}

#[test]
fn inexact_float_objective_fold_is_declined() {
    let mut model = Model::new();
    let x = model.add_int_col(0.0, 4.0);
    let y = model.add_int_col(0.0, 4.0);
    model.add_row(0.0, 0.0, &[(x, 1.0), (y, -1.0)]);
    model.set_objective(&[(x, 1.0), (y, 2.0f64.powi(-53))], Sense::Minimize);

    assert!(aggregate_implied_free_equalities(&model, None, None).is_none());
}

#[test]
fn expired_deadline_declines_without_partial_output() {
    let mut model = Model::new();
    model.add_int_col(1.0, 1.0);
    let now = Instant::now();
    let deadline = now.checked_sub(Duration::from_millis(1)).unwrap_or(now);
    assert!(aggregate_implied_free_equalities(&model, Some(deadline), None).is_none());
}
