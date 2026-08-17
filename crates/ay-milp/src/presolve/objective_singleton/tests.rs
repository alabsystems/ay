// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_traits::One;

use super::*;

#[test]
fn aggregate_slack_exposes_and_eliminates_a_second_layer() {
    let mut model = Model::new();
    let t = model.add_int_col(5.0, 10.0);
    let slack = model.add_col(0.0, f64::INFINITY);
    let aggregate = model.add_col(0.0, f64::INFINITY);
    model.add_row(f64::NEG_INFINITY, 3.0, &[(t, 1.0), (slack, -1.0)]);
    model.add_row(f64::NEG_INFINITY, 0.0, &[(slack, 1.0), (aggregate, -1.0)]);
    model.set_objective(&[(aggregate, 1.0)], Sense::Minimize);

    let (reduced, post) = substitute_objective_singletons(&model).expect("both layers eliminate");
    assert_eq!(reduced.num_cols(), 1);
    assert_eq!(reduced.num_rows(), 0);
    assert_eq!(post.recover.len(), 2);
    assert_eq!(reduced.obj_coeff(Col(0)), 1.0);
    assert_eq!(*post.const_delta(), BigRational::from_integer((-3).into()));
    let reduced_point = vec![BigRational::from_integer(7.into())];
    let full = post.widen(&reduced_point);
    assert_eq!(
        full,
        vec![
            BigRational::from_integer(7.into()),
            BigRational::from_integer(4.into()),
            BigRational::from_integer(4.into())
        ]
    );
    assert!(model.check_point(&full).is_ok());
    assert_eq!(
        model.objective_value_at(&full),
        reduced.objective_value_at(&reduced_point) + post.const_delta()
    );
}

#[test]
fn rational_fold_stays_available_to_exact_routes() {
    let mut model = Model::new();
    let decision = model.add_binary_col();
    let objective = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
    // 10*objective - decision = 0, hence objective = decision/10.
    // The transform is exact even though its f64 advice coefficient 0.1
    // cannot represent the authoritative rational 1/10.
    model.add_row(0.0, 0.0, &[(objective, 10.0), (decision, -1.0)]);
    model.set_objective(&[(objective, 1.0)], Sense::Minimize);

    let (reduced, post) =
        substitute_objective_singletons(&model).expect("singleton must eliminate");
    assert_eq!(reduced.num_cols(), 1);
    assert_eq!(reduced.num_rows(), 0);
    assert!(
        reduced.has_inexact_objective_coeffs(),
        "the exact 1/10 cost must remain in the side store"
    );
    let reduced_decision = post.map[decision.index()].expect("decision survives");
    assert_eq!(
        reduced.obj_coeff_exact_at(reduced_decision.0, reduced.obj_coeff(reduced_decision)),
        BigRational::new(1.into(), 10.into())
    );

    let reduced_point = vec![BigRational::one()];
    let full = post.widen(&reduced_point);
    assert!(model.check_point(&full).is_ok());
    assert_eq!(
        full[objective.index()],
        BigRational::new(1.into(), 10.into())
    );
    assert_eq!(
        model.objective_value_at(&full),
        reduced.objective_value_at(&reduced_point) + post.const_delta()
    );
}

#[test]
fn a_box_that_can_bind_before_the_row_declines_piecewise_elimination() {
    let mut model = Model::new();
    let t = model.add_int_col(0.0, 10.0);
    let slack = model.add_col(0.0, f64::INFINITY);
    model.add_row(f64::NEG_INFINITY, 3.0, &[(t, 1.0), (slack, -1.0)]);
    model.set_objective(&[(slack, 1.0)], Sense::Minimize);
    // s=max(0,t-3), not one affine expression over t's box.
    assert!(substitute_objective_singletons(&model).is_none());
}

#[test]
fn maximization_uses_the_opposite_oriented_row_side() {
    let mut model = Model::new();
    let t = model.add_int_col(0.0, 5.0);
    let reward = model.add_col(f64::NEG_INFINITY, 10.0);
    model.add_row(0.0, f64::INFINITY, &[(t, -1.0), (reward, -1.0)]);
    model.set_objective(&[(reward, 1.0)], Sense::Maximize);
    let (reduced, post) = substitute_objective_singletons(&model).expect("upper target");
    assert_eq!(post.recover[0].side, ObjectiveSingletonSide::Lower);
    let full = post.widen(&[BigRational::one()]);
    assert_eq!(full[1], BigRational::from_integer((-1).into()));
    assert!(model.check_point(&full).is_ok());
    assert_eq!(reduced.obj_coeff(Col(0)), -1.0);
}

#[test]
fn expired_deadline_declines_without_a_partial_transform() {
    let mut model = Model::new();
    let decision = model.add_binary_col();
    let cost = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
    model.add_row(0.0, 0.0, &[(cost, 1.0), (decision, -2.0)]);
    model.set_objective(&[(cost, 1.0)], Sense::Minimize);

    assert!(substitute_objective_singletons_with_deadline(&model, Some(Instant::now())).is_none());
}
