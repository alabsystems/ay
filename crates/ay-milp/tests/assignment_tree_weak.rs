// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Complete, bounded binary-assignment harvesting and exact tree composition.

use std::time::{Duration, Instant};

use ay_milp::{
    CertifiedBinaryTreeHarvest, Col, FixedAssignmentTreeWarmStart, LpSession, Model, Sense,
    SolveOpts, MAX_CERTIFIED_BINARY_ASSIGNMENT_TREE_LEAVES,
};
use num_rational::BigRational;

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

/// The relaxed epigraph
///
///   z >= x + y - 1/2
///   z >= 1/2 - x - y
///
/// has root minimum zero. Splitting only x is insufficient because the x=0
/// child can choose y=1/2, but every complete binary assignment to x,y has
/// z>=1/2 (and x=y=1 has z>=3/2).
fn two_split_relaxation() -> (Model, Col, Col, Col) {
    let mut model = Model::new();
    let x = model.add_col(0.0, 1.0);
    let y = model.add_col(0.0, 1.0);
    let z = model.add_col(0.0, 2.0);
    model.add_row(-0.5, f64::INFINITY, &[(z, 1.0), (x, -1.0), (y, -1.0)]);
    model.add_row(0.5, f64::INFINITY, &[(z, 1.0), (x, 1.0), (y, 1.0)]);
    (model, x, y, z)
}

fn two_split_decision(decision_coeff: f64) -> (Model, Col, Col, Col, ay_milp::Row) {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let y = model.add_binary_col();
    let z = model.add_col(0.0, 2.0);
    model.add_row(-0.5, f64::INFINITY, &[(z, 1.0), (x, -1.0), (y, -1.0)]);
    model.add_row(0.5, f64::INFINITY, &[(z, 1.0), (x, 1.0), (y, 1.0)]);
    let decision = model.add_row(f64::NEG_INFINITY, 0.25, &[(z, decision_coeff)]);
    (model, x, y, z, decision)
}

fn one_infeasible_leaf_relaxation() -> (Model, Col, Col, Col) {
    let (mut model, x, y, z) = two_split_relaxation();
    model.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0), (y, 1.0)]);
    (model, x, y, z)
}

fn one_infeasible_leaf_decision(assignment_upper: f64) -> (Model, Col, Col, Col, ay_milp::Row) {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let y = model.add_binary_col();
    let z = model.add_col(0.0, 2.0);
    model.add_row(-0.5, f64::INFINITY, &[(z, 1.0), (x, -1.0), (y, -1.0)]);
    model.add_row(0.5, f64::INFINITY, &[(z, 1.0), (x, 1.0), (y, 1.0)]);
    model.add_row(f64::NEG_INFINITY, assignment_upper, &[(x, 1.0), (y, 1.0)]);
    let decision = model.add_row(f64::NEG_INFINITY, 0.25, &[(z, 1.0)]);
    (model, x, y, z, decision)
}

#[test]
fn depth_two_is_necessary_and_composes_in_canonical_assignment_order() {
    let (relaxation, x, y, z) = two_split_relaxation();
    let threshold = rat(1, 4);

    let mut one_split = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    assert!(
        one_split
            .harvest_cut_or_binary_split_stronger_than(&[(z, 1.0)], Sense::Minimize, x, &threshold,)
            .is_none(),
        "x=0 still admits x+y=1/2, so one split cannot prove z>1/4"
    );

    let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    let CertifiedBinaryTreeHarvest::Tree(tree) = session
        .harvest_cut_or_binary_assignment_tree_stronger_than(
            &[(z, 1.0)],
            Sense::Minimize,
            &[x, y],
            &threshold,
        )
        .expect("all four complete assignments prove z>1/4")
    else {
        panic!("the root minimum is zero, so the proof must use the tree")
    };
    assert_eq!(tree.split_cols(), &[x, y]);
    assert_eq!(tree.num_leaves(), 4);

    let (decision_model, decision_x, decision_y, _decision_z, decision) = two_split_decision(1.0);
    assert_eq!(
        [decision_x.index(), decision_y.index()],
        [x.index(), y.index()]
    );
    let cert = tree
        .clone()
        .into_farkas_against_row_upper(&decision_model, decision)
        .expect("assignment rows must close against z<=1/4");
    cert.verify(&decision_model)
        .expect("whole-tree verification re-prices every Gray-solved leaf");
    assert_eq!(cert.num_leaves(), 4);

    let mut continuous_decision = relaxation.clone();
    let continuous_row = continuous_decision.add_row(f64::NEG_INFINITY, 0.25, &[(z, 1.0)]);
    assert!(
        tree.clone()
            .into_farkas_against_row_upper(&continuous_decision, continuous_row)
            .is_none(),
        "continuous splits do not cover the caller's domain"
    );

    let (tampered_model, _, _, _, tampered_decision) = two_split_decision(2.0);
    assert!(
        tree.into_farkas_against_row_upper(&tampered_model, tampered_decision)
            .is_none(),
        "changing the decision row's linear form must invalidate composition"
    );
}

#[test]
fn progressive_prefix_and_stopped_root_probe_remain_proof_neutral() {
    let (relaxation, x, y, z) = two_split_relaxation();
    let threshold = rat(1, 4);
    for warm_start in [
        FixedAssignmentTreeWarmStart::ProgressivePrefix {
            prefix_time_limit: Duration::ZERO,
            start_assignment: 1,
        },
        FixedAssignmentTreeWarmStart::RootProbeThenProgressivePrefix {
            root_time_limit: Duration::ZERO,
            prefix_time_limit: Duration::ZERO,
            start_assignment: 1,
        },
    ] {
        let opts = SolveOpts::new()
            .with_deadline(Instant::now() + Duration::from_secs(30))
            .with_fixed_assignment_tree_warm_start(Some(warm_start));
        let mut session = LpSession::new(&relaxation, &opts).unwrap();
        let CertifiedBinaryTreeHarvest::Tree(tree) = session
            .harvest_cut_or_binary_assignment_tree_stronger_than(
                &[(z, 1.0)],
                Sense::Minimize,
                &[x, y],
                &threshold,
            )
            .expect("advice-only start must still produce exact complete leaves")
        else {
            panic!("the relaxed root cannot prove the threshold")
        };

        let (decision_model, _, _, _, decision) = two_split_decision(1.0);
        let cert = tree
            .into_farkas_against_row_upper(&decision_model, decision)
            .expect("every canary leaf must compose independently");
        cert.verify(&decision_model)
            .expect("warm-start advice must not enter exact verification");
        assert_eq!(cert.num_leaves(), 4);
    }
}

#[test]
fn an_infeasible_complete_assignment_becomes_an_exact_farkas_leaf() {
    let (relaxation, x, y, z) = one_infeasible_leaf_relaxation();
    let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    let CertifiedBinaryTreeHarvest::Tree(tree) = session
        .harvest_cut_or_binary_assignment_tree_stronger_than(
            &[(z, 1.0)],
            Sense::Minimize,
            &[x, y],
            &rat(1, 4),
        )
        .expect("00, 01, and 10 prove the row while 11 is exactly infeasible")
    else {
        panic!("the root minimum is zero, so the proof must use the tree")
    };
    assert_eq!(tree.num_leaves(), 4);

    let (decision_model, decision_x, decision_y, _, decision) = one_infeasible_leaf_decision(1.0);
    assert_eq!(
        [decision_x.index(), decision_y.index()],
        [x.index(), y.index()]
    );
    let cert = tree
        .clone()
        .into_farkas_against_row_upper(&decision_model, decision)
        .expect("the direct 11 Farkas leaf and three conditional rows must compose");
    cert.verify(&decision_model)
        .expect("the completed tree must independently reverify");
    assert_eq!(cert.num_leaves(), 4);

    let (relaxed_decision, _, _, _, relaxed_row) = one_infeasible_leaf_decision(2.0);
    assert!(
        tree.into_farkas_against_row_upper(&relaxed_decision, relaxed_row)
            .is_none(),
        "the stored 11 Farkas witness must be re-priced against the decision model"
    );
}

#[test]
fn root_fast_path_and_invalid_requests_fail_closed() {
    assert_eq!(MAX_CERTIFIED_BINARY_ASSIGNMENT_TREE_LEAVES, 16);
    let (relaxation, x, y, z) = two_split_relaxation();

    let mut root_session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    let CertifiedBinaryTreeHarvest::Root(root) = root_session
        .harvest_cut_or_binary_assignment_tree_stronger_than(
            &[(z, 1.0)],
            Sense::Minimize,
            &[x, y],
            &rat(-1, 4),
        )
        .expect("the root lower bound zero strictly clears -1/4")
    else {
        panic!("a sufficient root row must return before assignment solves")
    };
    root.verify(&relaxation).unwrap();

    let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    for splits in [&[][..], &[x, x][..]] {
        assert!(session
            .harvest_cut_or_binary_assignment_tree_stronger_than(
                &[(z, 1.0)],
                Sense::Minimize,
                splits,
                &rat(1, 4),
            )
            .is_none());
    }
    assert!(
        session
            .harvest_cut_or_binary_assignment_tree_stronger_than(
                &[(z, 1.0), (z, -1.0)],
                Sense::Minimize,
                &[x, y],
                &rat(1, 4),
            )
            .is_none(),
        "duplicate objective columns must decline"
    );
    assert!(
        session
            .harvest_cut_or_binary_assignment_tree_stronger_than(
                &[(z, f64::NAN)],
                Sense::Minimize,
                &[x, y],
                &rat(1, 4),
            )
            .is_none(),
        "non-finite objectives must decline"
    );

    let mut other = Model::new();
    for _ in 0..5 {
        other.add_col(0.0, 1.0);
    }
    let outside = other.col_at(4).unwrap();
    assert!(
        session
            .harvest_cut_or_binary_assignment_tree_stronger_than(
                &[(z, 1.0)],
                Sense::Minimize,
                &[x, outside],
                &rat(1, 4),
            )
            .is_none(),
        "a split handle outside the session model must decline"
    );

    let mut five = Model::new();
    let split_cols: Vec<_> = (0..5).map(|_| five.add_col(0.0, 1.0)).collect();
    let objective = five.add_col(0.0, 1.0);
    let mut five_session = LpSession::new(&five, &SolveOpts::new()).unwrap();
    assert!(
        five_session
            .harvest_cut_or_binary_assignment_tree_stronger_than(
                &[(objective, 1.0)],
                Sense::Minimize,
                &split_cols,
                &rat(0, 1),
            )
            .is_none(),
        "depth above four must decline before solving"
    );

    let mut wrong_box = Model::new();
    let wide = wrong_box.add_col(0.0, 2.0);
    let wrong_objective = wrong_box.add_col(0.0, 1.0);
    let mut wrong_box_session = LpSession::new(&wrong_box, &SolveOpts::new()).unwrap();
    assert!(
        wrong_box_session
            .harvest_cut_or_binary_assignment_tree_stronger_than(
                &[(wrong_objective, 1.0)],
                Sense::Minimize,
                &[wide],
                &rat(0, 1),
            )
            .is_none(),
        "a split without the exact relaxed box [0,1] must decline"
    );

    let invalid_start = SolveOpts::new().with_fixed_assignment_tree_warm_start(Some(
        FixedAssignmentTreeWarmStart::ProgressivePrefix {
            prefix_time_limit: Duration::ZERO,
            start_assignment: 4,
        },
    ));
    let mut invalid_start_session = LpSession::new(&relaxation, &invalid_start).unwrap();
    assert!(
        invalid_start_session
            .harvest_cut_or_binary_assignment_tree_stronger_than(
                &[(z, 1.0)],
                Sense::Minimize,
                &[x, y],
                &rat(1, 4),
            )
            .is_none(),
        "a Gray start outside the depth-two assignment domain must decline"
    );

    let expired = Instant::now()
        .checked_sub(Duration::from_millis(1))
        .expect("monotonic clock supports a one-millisecond subtraction");
    let opts = SolveOpts::new().with_deadline(expired);
    let mut expired_session = LpSession::new(&relaxation, &opts).unwrap();
    assert!(
        expired_session
            .harvest_cut_or_binary_assignment_tree_stronger_than(
                &[(z, 1.0)],
                Sense::Minimize,
                &[x, y],
                &rat(-1, 4),
            )
            .is_none(),
        "an already-expired assignment probe must fail closed"
    );
}
