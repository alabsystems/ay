// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn a_checked_feasible_projection_does_not_repeat_the_hybrid_search() {
    let mut model = Model::new();
    let choose = model.add_binary_col();
    let recourse = model.add_col(0.0, 4.0);
    model.add_int_col(0.0, f64::INFINITY);
    model.add_row(4.0, f64::INFINITY, &[(recourse, 1.0), (choose, 3.0)]);
    model.set_objective(&[(choose, 2.0), (recourse, 1.0)], Sense::Minimize);
    let projection = MonotoneProjection::try_build(&model, None, || false)
        .expect("the unused open integer has a finite anchor");

    let before = crate::simplex::stats::work_local();
    let direct = crate::hybrid_pb_lp::try_refute_certified(projection.residual(), None)
        .expect("the direct hybrid search completes");
    let direct_work = crate::simplex::stats::work_local() - before;
    let crate::hybrid_pb_lp::CertifiedHybridPbLpDecision::Feasible { model_values, .. } = direct
    else {
        panic!("the projection has a feasible point");
    };
    projection
        .residual()
        .check_point(&model_values)
        .expect("independently checked residual witness");
    assert!(direct_work > 0, "the fixture must exercise the LP solver");

    let before = crate::simplex::stats::work_local();
    assert_eq!(
        try_prove_infeasibility(&model, Instant::now() + Duration::from_secs(30)),
        None,
        "a feasible projection has no infeasibility certificate"
    );
    let route_work = crate::simplex::stats::work_local() - before;
    assert_eq!(
        route_work, direct_work,
        "a checked feasible point must end the probe without a second LP search"
    );
}
