// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded target-objective FSB selection followed by exact tree harvesting.

use std::time::{Duration, Instant};

use ay_milp::{
    CertifiedBinaryTreeHarvest, Col, LpSession, Model, Sense, SolveOpts, TargetFsbOpts,
    MAX_TARGET_FSB_CANDIDATES,
};
use num_rational::BigRational;

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

/// p >= max(x, 1-x) and q >= max(z, 1-z):
///
///   p >= x, p >= 1-x
///   q >= z, q >= 1-z.
///
/// The relaxed target minimum p+q is 1. Fixing either useful binary raises the
/// minimum to 3/2; fixing both raises it to 2. `dummy` changes nothing.
fn target_relaxation() -> (Model, Col, Col, Col, Col, Col) {
    let mut model = Model::new();
    let x = model.add_col(0.0, 1.0);
    let dummy = model.add_col(0.0, 1.0);
    let z = model.add_col(0.0, 1.0);
    let p = model.add_col(0.0, 1.0);
    let q = model.add_col(0.0, 1.0);
    model.add_row(0.0, f64::INFINITY, &[(p, 1.0), (x, -1.0)]);
    model.add_row(1.0, f64::INFINITY, &[(p, 1.0), (x, 1.0)]);
    model.add_row(0.0, f64::INFINITY, &[(q, 1.0), (z, -1.0)]);
    model.add_row(1.0, f64::INFINITY, &[(q, 1.0), (z, 1.0)]);
    (model, x, dummy, z, p, q)
}

fn target_decision() -> (Model, Col, Col, Col, ay_milp::Row) {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let dummy = model.add_binary_col();
    let z = model.add_binary_col();
    let p = model.add_col(0.0, 1.0);
    let q = model.add_col(0.0, 1.0);
    model.add_row(0.0, f64::INFINITY, &[(p, 1.0), (x, -1.0)]);
    model.add_row(1.0, f64::INFINITY, &[(p, 1.0), (x, 1.0)]);
    model.add_row(0.0, f64::INFINITY, &[(q, 1.0), (z, -1.0)]);
    model.add_row(1.0, f64::INFINITY, &[(q, 1.0), (z, 1.0)]);
    let decision = model.add_row(f64::NEG_INFINITY, 1.75, &[(p, 1.0), (q, 1.0)]);
    (model, x, dummy, z, decision)
}

fn test_fsb_opts() -> TargetFsbOpts {
    TargetFsbOpts::new()
        .with_max_probe_pivots_per_call(64)
        .with_probe_time_limit(Duration::from_secs(2))
}

#[test]
fn target_fsb_rejects_a_static_distractor_and_certifies_the_selected_pair() {
    assert_eq!(MAX_TARGET_FSB_CANDIDATES, 8);
    let (relaxation, x, dummy, z, p, q) = target_relaxation();
    let objective = [(p, 1.0), (q, 1.0)];
    let threshold = rat(7, 4);

    let mut static_prefix = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    assert!(
        static_prefix
            .harvest_cut_or_binary_assignment_tree_stronger_than(
                &objective,
                Sense::Minimize,
                &[x, dummy],
                &threshold,
            )
            .is_none(),
        "x plus the distractor leaves z=1/2 and proves only 3/2"
    );

    let mut fused = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    let (harvest, report) = fused
        .harvest_cut_or_target_fsb_assignment_tree_stronger_than(
            &objective,
            Sense::Minimize,
            &[x, dummy, z],
            &threshold,
            &test_fsb_opts(),
        )
        .expect("target FSB must replace the distractor with z");
    let CertifiedBinaryTreeHarvest::Tree(tree) = harvest else {
        panic!("the relaxed target is 1, so this proof must use a tree")
    };
    assert_eq!(report.candidate_count(), 3);
    assert_eq!(report.probe_calls(), 14);
    assert_eq!(report.selected_splits(), &[x, z]);
    assert_eq!(tree.split_cols(), &[x, z]);
    assert_eq!(tree.num_leaves(), 4);
    assert!(report.first_worst_lower_bound().unwrap() > 1.49);
    assert!(report.joint_worst_lower_bound().unwrap() > 1.99);

    let (decision_model, decision_x, _decision_dummy, decision_z, decision) = target_decision();
    assert_eq!(
        [decision_x.index(), decision_z.index()],
        [x.index(), z.index()]
    );
    let cert = tree
        .into_farkas_against_row_upper(&decision_model, decision)
        .expect("the four exact p+q>=2 leaves must close p+q<=7/4");
    cert.verify(&decision_model)
        .expect("the fused selector may not alter exact tree replay");
    assert_eq!(cert.num_leaves(), 4);
}

#[test]
fn target_fsb_root_fast_path_spends_no_advice_calls() {
    let (relaxation, x, dummy, z, p, q) = target_relaxation();
    let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    let (harvest, report) = session
        .harvest_cut_or_target_fsb_assignment_tree_stronger_than(
            &[(p, 1.0), (q, 1.0)],
            Sense::Minimize,
            &[x, dummy, z],
            &rat(3, 4),
            &TargetFsbOpts::new()
                .with_max_probe_calls(0)
                .with_max_probe_pivots_per_call(0)
                .with_probe_time_limit(Duration::ZERO)
                .with_max_probe_scratch_bytes(0),
        )
        .expect("the exact root row clears 3/4 without consulting probe caps");
    let CertifiedBinaryTreeHarvest::Root(row) = harvest else {
        panic!("a sufficient root must return before target FSB")
    };
    row.verify(&relaxation).unwrap();
    assert_eq!(report.probe_calls(), 0);
    assert!(report.selected_splits().is_empty());
}

#[test]
fn target_fsb_resource_caps_and_deadline_fail_closed() {
    let (relaxation, x, dummy, z, p, q) = target_relaxation();
    let objective = [(p, 1.0), (q, 1.0)];
    let candidates = [x, dummy, z];
    let threshold = rat(7, 4);

    for opts in [
        test_fsb_opts().with_max_probe_calls(13),
        test_fsb_opts().with_max_probe_pivots_per_call(0),
        test_fsb_opts().with_probe_time_limit(Duration::ZERO),
        test_fsb_opts().with_max_probe_scratch_bytes(0),
    ] {
        let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
        assert!(
            session
                .harvest_cut_or_target_fsb_assignment_tree_stronger_than(
                    &objective,
                    Sense::Minimize,
                    &candidates,
                    &threshold,
                    &opts,
                )
                .is_none(),
            "an incomplete bounded scan must not select from a partial ranking"
        );
    }

    let expired = Instant::now()
        .checked_sub(Duration::from_millis(1))
        .expect("monotonic clock supports a one-millisecond subtraction");
    let mut expired_session =
        LpSession::new(&relaxation, &SolveOpts::new().with_deadline(expired)).unwrap();
    assert!(
        expired_session
            .harvest_cut_or_target_fsb_assignment_tree_stronger_than(
                &objective,
                Sense::Minimize,
                &candidates,
                &threshold,
                &test_fsb_opts(),
            )
            .is_none(),
        "an expired outer deadline must decline before the cold target root"
    );
}
