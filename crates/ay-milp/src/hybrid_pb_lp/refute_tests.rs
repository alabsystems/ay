// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn recourse_model() -> Model {
    let mut model = Model::new();
    let choose = model.add_binary_col();
    let recourse = model.add_col(0.0, 4.0);
    model.add_row(4.0, f64::INFINITY, &[(recourse, 1.0), (choose, 3.0)]);
    model.set_objective(&[(choose, 2.0), (recourse, 1.0)], Sense::Minimize);
    model
}

#[test]
fn refutation_stops_on_a_checked_nonoptimal_point() {
    let model = recourse_model();
    let before = crate::simplex::stats::work_local();
    let refutation = try_refute_certified(&model, None).expect("completed probe");
    let refutation_work = crate::simplex::stats::work_local() - before;
    let CertifiedHybridPbLpDecision::Feasible {
        model_values,
        incumbent_only,
    } = refutation
    else {
        panic!("one feasible point disproves infeasibility without optimizing");
    };
    assert!(incumbent_only);
    model.check_point(&model_values).expect("checked witness");
    assert_eq!(
        model.objective_value_at(&model_values),
        BigRational::from_integer(4.into())
    );

    let before = crate::simplex::stats::work_local();
    let optimization = try_solve_certified(&model, None).expect("completed optimization");
    let optimization_work = crate::simplex::stats::work_local() - before;
    let CertifiedHybridPbLpDecision::Optimal {
        value,
        model_values,
    } = optimization
    else {
        panic!("ordinary optimization must retain the full search");
    };
    assert_eq!(value, BigRational::from_integer(3.into()));
    model.check_point(&model_values).expect("optimal witness");
    assert!(
        refutation_work > 0 && refutation_work < optimization_work,
        "probe work {refutation_work} must stop before optimization work {optimization_work}"
    );
}

#[test]
fn refutation_does_not_optimize_the_continuous_subproblem() {
    let mut observations = Vec::new();
    for (coefficient, optimum) in [(3.0, 5), (-3.0, -10)] {
        let mut model = Model::new();
        let choose = model.add_binary_col();
        model.set_col_bounds(choose, 1.0, 1.0);
        let recourse = model.add_col(0.0, 4.0);
        model.add_row(0.0, f64::INFINITY, &[(recourse, 1.0), (choose, -1.0)]);
        model.set_objective(&[(choose, 2.0), (recourse, coefficient)], Sense::Minimize);

        let before = crate::simplex::stats::work_local();
        let CertifiedHybridPbLpDecision::Feasible {
            model_values,
            incumbent_only,
        } = try_refute_certified(&model, None).expect("completed feasibility probe")
        else {
            panic!("refutation must return a checked feasible point");
        };
        let work = crate::simplex::stats::work_local() - before;
        assert!(incumbent_only);
        model
            .check_point(&model_values)
            .expect("exact feasible witness");
        observations.push((model_values, work));

        let CertifiedHybridPbLpDecision::Optimal {
            value,
            model_values,
        } = try_solve_certified(&model, None).expect("completed optimization")
        else {
            panic!("ordinary optimization must retain the recourse objective");
        };
        model
            .check_point(&model_values)
            .expect("exact optimal witness");
        assert_eq!(value, BigRational::from_integer(optimum.into()));
    }
    assert_eq!(
        observations[0], observations[1],
        "opposite continuous objectives must not change a refutation witness or its LP work"
    );
}

#[test]
fn refutation_still_emits_a_model_bound_infeasibility_certificate() {
    let mut model = Model::new();
    let choose = model.add_binary_col();
    let recourse = model.add_col(0.0, 1.0);
    model.add_row(2.0, f64::INFINITY, &[(recourse, 1.0)]);
    model.add_row(f64::NEG_INFINITY, 0.0, &[(recourse, 1.0), (choose, -1.0)]);
    model.set_objective(&[(recourse, 1.0)], Sense::Minimize);
    let CertifiedHybridPbLpDecision::Infeasible(certificate) =
        try_refute_certified(&model, None).expect("completed refutation")
    else {
        panic!("infeasibility must retain its certificate");
    };
    verify_hybrid_pb_lp_infeasibility_certificate(&model, &certificate)
        .expect("independent certificate verification");
    assert!(
        verify_hybrid_pb_lp_infeasibility_certificate(&recourse_model(), &certificate).is_err()
    );
}

#[test]
fn lifted_refutation_stops_without_optimizing_the_integer_master() {
    let mut model = Model::new();
    let choose = model.add_int_col(0.0, 2.0);
    let recourse = model.add_col(0.0, 4.0);
    model.add_row(4.0, f64::INFINITY, &[(recourse, 1.0), (choose, 3.0)]);
    model.set_objective(&[(choose, 2.0), (recourse, 1.0)], Sense::Minimize);
    let crate::hybrid_integer_lift::CertifiedHybridIntegerLiftDecision::Feasible {
        model_values,
        incumbent_only,
    } = crate::hybrid_integer_lift::try_refute_certified(&model, None)
        .expect("completed lifted probe")
    else {
        panic!("lifted probe must return a feasible counterexample");
    };
    assert!(incumbent_only);
    model
        .check_point(&model_values)
        .expect("checked original-model witness");
    assert_eq!(
        model.objective_value_at(&model_values),
        BigRational::from_integer(4.into())
    );
}

#[test]
fn stopped_refutation_never_mints_a_verdict() {
    assert!(
        try_solve_certified_interruptible(&recourse_model(), None, HybridGoal::Refute, || true,)
            .is_none()
    );
}
