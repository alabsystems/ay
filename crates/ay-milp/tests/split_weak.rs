// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact composition of node-local weak objective rows into Farkas leaves.

use ay_milp::{
    BoundSide, CertifiedSplitHarvest, Col, LpSession, MilpInfeasibilityCertificate, Model, Row,
    Sense, SolveOpts, TreeNode,
};
use num_rational::BigRational;
use std::time::{Duration, Instant};

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

/// Base relaxation:
///
///   z >= x
///   z >= 1 - x
///
/// has minimum z=1/2 over x in [0,1], but minimum z=1 under either integer
/// child x=0 or x=1. Thus the decision row z<=3/4 has a genuine integrality
/// gap at the root and is refuted by a weak objective row in each child.
fn decision_model() -> (Model, Col, Col, Row) {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let z = model.add_col(0.0, 2.0);
    model.add_row(0.0, f64::INFINITY, &[(z, 1.0), (x, -1.0)]);
    model.add_row(1.0, f64::INFINITY, &[(z, 1.0), (x, 1.0)]);
    let decision = model.add_row(f64::NEG_INFINITY, 0.75, &[(z, 1.0)]);
    (model, x, z, decision)
}

/// Rebuild the base rows as a continuous relaxation, with x fixed to one
/// branch. Row/column handles intentionally match `decision_model`; the
/// decision row itself is absent while deriving the objective lower row.
fn child_relaxation(x_value: f64) -> (Model, Col, Col) {
    let mut model = Model::new();
    let x = model.add_col(0.0, 1.0);
    let z = model.add_col(0.0, 2.0);
    model.add_row(0.0, f64::INFINITY, &[(z, 1.0), (x, -1.0)]);
    model.add_row(1.0, f64::INFINITY, &[(z, 1.0), (x, 1.0)]);
    model.fix_col(x, x_value);
    (model, x, z)
}

fn child_lower_row(value: f64) -> ay_milp::CertifiedRow {
    let (model, _x, z) = child_relaxation(value);
    let mut session = LpSession::new(&model, &SolveOpts::new()).unwrap();
    let row = session
        .harvest_cut(&[(z, 1.0)], Sense::Minimize)
        .expect("fixed child has a certified objective lower row");
    row.verify(&model).unwrap();
    assert_eq!(row.lb, rat(1, 1));
    row
}

/// The same integrality-gap shape scaled by three and padded above the exact
/// basis cap. Each child has exact minimum z=1/3, while the large-model weak
/// lane snaps its 1/3 row dual to the 2^-30 grid and proves a slightly weaker
/// (but still decision-refuting) lower row.
fn weak_decision_model() -> (Model, Col, Col, Row) {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let z = model.add_col(0.0, 1.0);
    model.add_row(0.0, f64::INFINITY, &[(z, 3.0), (x, -1.0)]);
    model.add_row(1.0, f64::INFINITY, &[(z, 3.0), (x, 1.0)]);
    for _ in 0..601 {
        let dummy = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        model.add_row(0.0, 0.0, &[(dummy, 1.0)]);
    }
    let decision = model.add_row(f64::NEG_INFINITY, 0.25, &[(z, 1.0)]);
    (model, x, z, decision)
}

fn weak_relaxation_model() -> (Model, Col, Col) {
    let mut model = Model::new();
    let x = model.add_col(0.0, 1.0);
    let z = model.add_col(0.0, 1.0);
    model.add_row(0.0, f64::INFINITY, &[(z, 3.0), (x, -1.0)]);
    model.add_row(1.0, f64::INFINITY, &[(z, 3.0), (x, 1.0)]);
    for _ in 0..601 {
        let dummy = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        model.add_row(0.0, 0.0, &[(dummy, 1.0)]);
    }
    (model, x, z)
}

#[test]
fn child_weak_rows_compose_into_a_verifying_split_tree() {
    let (model, x, _z, decision) = decision_model();

    let lo = child_lower_row(0.0)
        .into_farkas_against_row_upper(&model, decision, &[(x, BoundSide::Upper, rat(0, 1))])
        .expect("z>=1 and z<=3/4 contradict in the x<=0 child");
    let hi = child_lower_row(1.0)
        .into_farkas_against_row_upper(&model, decision, &[(x, BoundSide::Lower, rat(1, 1))])
        .expect("z>=1 and z<=3/4 contradict in the x>=1 child");

    let cert = MilpInfeasibilityCertificate {
        root: TreeNode::Split {
            col: x,
            cut: rat(0, 1),
            lo: Box::new(TreeNode::Leaf { farkas: lo }),
            hi: Box::new(TreeNode::Leaf { farkas: hi }),
        },
    };
    cert.verify(&model)
        .expect("the independent tree checker re-prices both child leaves");
    assert_eq!(cert.num_leaves(), 2);
}

#[test]
fn large_child_weak_duals_compose_into_a_verifying_split_tree() {
    let (model, x, _z, decision) = weak_decision_model();
    let (relaxation, relaxed_x, z) = weak_relaxation_model();
    let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    let CertifiedSplitHarvest::Split { zero, one } = session
        .harvest_cut_or_binary_split_stronger_than(
            &[(z, 1.0)],
            Sense::Minimize,
            relaxed_x,
            &rat(1, 4),
        )
        .expect("root is insufficient but both warm children clear 1/4")
    else {
        panic!("the root LP minimum is only 1/6, so this must need a split")
    };
    for row in [&zero, &one] {
        assert!(
            row.lb > rat(1, 4) && row.lb < rat(1, 3),
            "the test must exercise a snapped child weak row, got {}",
            row.lb
        );
    }
    let lo = zero
        .into_farkas_against_row_upper(&model, decision, &[(x, BoundSide::Upper, rat(0, 1))])
        .expect("snapped weak row still strictly refutes z<=1/4");
    let hi = one
        .into_farkas_against_row_upper(&model, decision, &[(x, BoundSide::Lower, rat(1, 1))])
        .expect("snapped weak row still strictly refutes z<=1/4");
    let cert = MilpInfeasibilityCertificate {
        root: TreeNode::Split {
            col: x,
            cut: rat(0, 1),
            lo: Box::new(TreeNode::Leaf { farkas: lo }),
            hi: Box::new(TreeNode::Leaf { farkas: hi }),
        },
    };
    cert.verify(&model)
        .expect("whole-tree verification accepts both weak-dual leaves");
}

#[test]
fn combined_harvest_returns_root_first_and_fails_closed_if_children_are_weak() {
    let (relaxation, x, z) = weak_relaxation_model();
    let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    let CertifiedSplitHarvest::Root(root) = session
        .harvest_cut_or_binary_split_stronger_than(&[(z, 1.0)], Sense::Minimize, x, &rat(0, 1))
        .expect("the root minimum 1/6 strictly clears zero")
    else {
        panic!("a sufficient root row must return before child solves")
    };
    root.verify(&relaxation).unwrap();
    assert!(root.lb > rat(0, 1));

    let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    assert!(
        session
            .harvest_cut_or_binary_split_stronger_than(&[(z, 1.0)], Sense::Minimize, x, &rat(1, 3),)
            .is_none(),
        "snapped child bounds are below the strict exact threshold 1/3"
    );
}

#[test]
fn combined_harvest_handles_maximize_orientation_and_expired_deadline() {
    let (relaxation, x, z) = weak_relaxation_model();
    let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    let CertifiedSplitHarvest::Split { zero, one } = session
        .harvest_cut_or_binary_split_stronger_than(&[(z, -1.0)], Sense::Maximize, x, &rat(1, 4))
        .expect("max -z must re-orient to the same lower row z>=lb")
    else {
        panic!("the root maximum of -z is only -1/6, so this must need a split")
    };
    for (value, row) in [(0.0, zero), (1.0, one)] {
        let mut child = relaxation.clone();
        child.fix_col(x, value);
        row.verify(&child).unwrap();
        assert_eq!(
            row.coeffs,
            vec![(u32::try_from(z.index()).unwrap(), rat(1, 1))]
        );
        assert!(row.lb > rat(1, 4));
    }

    let expired = Instant::now()
        .checked_sub(Duration::from_millis(1))
        .expect("monotonic clock supports a one-millisecond subtraction");
    let opts = SolveOpts::new().with_deadline(expired);
    let mut session = LpSession::new(&relaxation, &opts).unwrap();
    assert!(
        session
            .harvest_cut_or_binary_split_stronger_than(&[(z, 1.0)], Sense::Minimize, x, &rat(0, 1),)
            .is_none(),
        "an already-expired proof probe must fail closed"
    );
}

#[test]
fn child_composition_fails_closed_on_wrong_or_missing_assumptions() {
    let (mut model, x, z, decision) = decision_model();
    let lo_row = child_lower_row(0.0);

    assert!(
        lo_row
            .clone()
            .into_farkas_against_row_upper(&model, decision, &[])
            .is_none(),
        "a child proof must not transfer to the root box"
    );
    assert!(
        lo_row
            .clone()
            .into_farkas_against_row_upper(&model, decision, &[(x, BoundSide::Lower, rat(1, 1))],)
            .is_none(),
        "a low-child proof must not transfer to the opposite child"
    );

    let equal = model.add_row(f64::NEG_INFINITY, 1.0, &[(z, 1.0)]);
    assert!(
        lo_row
            .clone()
            .into_farkas_against_row_upper(&model, equal, &[(x, BoundSide::Upper, rat(0, 1))],)
            .is_none(),
        "q>=gamma plus q<=gamma is not a contradiction"
    );

    let wrong_form = model.add_row(f64::NEG_INFINITY, 0.75, &[(z, 2.0)]);
    assert!(
        lo_row
            .into_farkas_against_row_upper(&model, wrong_form, &[(x, BoundSide::Upper, rat(0, 1))],)
            .is_none(),
        "the final exact Farkas check rejects coefficient mismatch"
    );
}
