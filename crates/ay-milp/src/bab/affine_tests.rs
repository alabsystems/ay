// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included to preserve the historical `bab::tests::*` names.

#[test]
fn affine_aggregation_postsolve_seals_point_and_value_in_caller_frame() {
    let mut model = Model::new();
    let x = model.add_int_col(0.0, 5.0);
    let y = model.add_int_col(0.0, 5.0);
    model.add_row(0.0, 0.0, &[(x, 1.0), (y, -1.0)]);
    model.set_objective(&[(x, 2.0), (y, 3.0)], Sense::Minimize);
    let (reduced, post) =
        crate::presolve::aggregate_implied_free_equalities(&model, None, Some(64 << 20))
            .expect("the equality must aggregate");
    let reduced_point = vec![BigRational::from_integer(2.into())];
    let reduced_value = reduced.objective_value_at(&reduced_point);

    match affine::expand_affine_aggregation_outcome(
        &Outcome::Optimal {
            value: reduced_value.clone(),
            model_values: reduced_point.clone(),
            cert: None,
        },
        &post,
        &model,
        None,
        Some(64 << 20),
    ) {
        Outcome::Optimal {
            value,
            model_values,
            cert,
        } => {
            assert_eq!(value, BigRational::from_integer(10.into()));
            assert_eq!(model_values, vec![BigRational::from_integer(2.into()); 2]);
            assert!(cert.is_none(), "a reduced-frame proof must not escape");
            assert!(model.check_point(&model_values).is_ok());
        }
        other => panic!("expected a sealed caller-frame optimum, got {other:?}"),
    }

    assert!(matches!(
        affine::expand_affine_aggregation_outcome(
            &Outcome::Optimal {
                value: reduced_value + BigRational::from_integer(1.into()),
                model_values: reduced_point,
                cert: None,
            },
            &post,
            &model,
            None,
            Some(64 << 20),
        ),
        Outcome::Unknown {
            reason: UnknownReason::WitnessRejected { .. }
        }
    ));
}

#[test]
fn affine_aggregation_keeps_top_level_feasibility_as_feasible() {
    let _env_lock = lock_env();
    let mut model = Model::new();
    let x = model.add_int_col(0.0, 5.0);
    let y = model.add_int_col(0.0, 5.0);
    model.add_row(0.0, 0.0, &[(x, 1.0), (y, -1.0)]);
    model.add_row(2.0, f64::INFINITY, &[(x, 1.0)]);
    assert!(!model.has_objective());

    // Other reductions self-decline or follow this arm in the chain.
    let opts = SolveOpts::new()
        .with_structure_routing(false)
        .with_engine(crate::EngineEconomics::new().with_affine_agg(true));
    let mut session = crate::BabSession::new(model.clone(), &opts).expect("valid model");
    match session.check().expect("solve") {
        Outcome::Feasible { model_values, .. } => {
            assert!(model.check_point(&model_values).is_ok());
        }
        other => panic!("a no-objective caller must receive Feasible, got {other:?}"),
    }
}

#[test]
fn affine_postsolve_maps_infeasible_and_unbounded_without_relabeling() {
    let mut model = Model::new();
    let x = model.add_int_col(f64::NEG_INFINITY, f64::INFINITY);
    let y = model.add_int_col(f64::NEG_INFINITY, f64::INFINITY);
    model.add_row(0.0, 0.0, &[(x, 1.0), (y, -1.0)]);
    model.set_objective(&[(x, 1.0)], Sense::Maximize);
    let (_, post) =
        crate::presolve::aggregate_implied_free_equalities(&model, None, Some(64 << 20))
            .expect("the free affine equality must aggregate");

    assert!(matches!(
        affine::expand_affine_aggregation_outcome(
            &Outcome::Infeasible {
                cert: None,
                tree_cert: None,
            },
            &post,
            &model,
            None,
            Some(64 << 20),
        ),
        Outcome::Infeasible {
            cert: None,
            tree_cert: None
        }
    ));
    assert!(matches!(
        affine::expand_affine_aggregation_outcome(
            &Outcome::Unbounded,
            &post,
            &model,
            None,
            Some(64 << 20),
        ),
        Outcome::Unbounded
    ));
}
