// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adaptive three-leaf target-FSB selection and exact asymmetric-tree replay.

use std::time::{Duration, Instant};

use ay_milp::{
    CertifiedAdaptiveThreeLeafHarvest, Col, LpSession, Model, Sense, SolveOpts, TargetFsbOpts,
};
use num_rational::BigRational;

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

/// `p >= max(z, 1-z)` supplies the hard branch. The root split adds
/// `p >= x` when hard=0, or `p >= 1-x` when hard=1, so the opposite root child
/// is an easy `p >= 1` leaf. The hard child has relaxed minimum 1/2 and reaches
/// one only after splitting `z`. `dummy` is a stable-ranking distractor.
fn adaptive_relaxation(hard_value: bool, infeasible_easy: bool) -> (Model, Col, Col, Col, Col) {
    let mut model = Model::new();
    let x = model.add_col(0.0, 1.0);
    let dummy = model.add_col(0.0, 1.0);
    let z = model.add_col(0.0, 1.0);
    let p = model.add_col(0.0, 2.0);
    if hard_value {
        model.add_row(1.0, f64::INFINITY, &[(p, 1.0), (x, 1.0)]);
    } else {
        model.add_row(0.0, f64::INFINITY, &[(p, 1.0), (x, -1.0)]);
    }
    model.add_row(0.0, f64::INFINITY, &[(p, 1.0), (z, -1.0)]);
    model.add_row(1.0, f64::INFINITY, &[(p, 1.0), (z, 1.0)]);
    if infeasible_easy {
        if hard_value {
            model.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
        } else {
            model.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);
        }
    }
    (model, x, dummy, z, p)
}

fn adaptive_decision(
    hard_value: bool,
    infeasible_easy: bool,
    decision_coeff: f64,
) -> (Model, Col, Col, Col, Col, ay_milp::Row) {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let dummy = model.add_binary_col();
    let z = model.add_binary_col();
    let p = model.add_col(0.0, 2.0);
    if hard_value {
        model.add_row(1.0, f64::INFINITY, &[(p, 1.0), (x, 1.0)]);
    } else {
        model.add_row(0.0, f64::INFINITY, &[(p, 1.0), (x, -1.0)]);
    }
    model.add_row(0.0, f64::INFINITY, &[(p, 1.0), (z, -1.0)]);
    model.add_row(1.0, f64::INFINITY, &[(p, 1.0), (z, 1.0)]);
    if infeasible_easy {
        if hard_value {
            model.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
        } else {
            model.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);
        }
    }
    let decision = model.add_row(f64::NEG_INFINITY, 0.75, &[(p, decision_coeff)]);
    (model, x, dummy, z, p, decision)
}

fn test_opts() -> TargetFsbOpts {
    TargetFsbOpts::new()
        .with_max_probe_pivots_per_call(64)
        .with_probe_time_limit(Duration::from_secs(2))
}

#[test]
fn selects_a_nonprefix_partner_and_verifies_both_hard_orientations() {
    for hard_value in [false, true] {
        let (relaxation, x, dummy, z, p) = adaptive_relaxation(hard_value, false);
        let candidates = [x, dummy, z];
        let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
        let (harvest, report) = session
            .harvest_cut_or_adaptive_three_leaf_target_fsb_stronger_than(
                &[(p, 1.0)],
                Sense::Minimize,
                &candidates,
                0,
                hard_value,
                &rat(3, 4),
                &test_opts(),
            )
            .expect("the easy child and both selected hard grandchildren prove p>3/4");
        let CertifiedAdaptiveThreeLeafHarvest::Tree(tree) = harvest else {
            panic!("the root minimum is 1/2, so this proof must use three leaves")
        };

        assert_eq!(report.candidate_count(), 3);
        assert_eq!(report.probe_calls(), 2 * (candidates.len() - 1));
        assert_eq!(report.root_candidate_index(), 0);
        assert_eq!(report.root_split(), x);
        assert_eq!(report.hard_value(), hard_value);
        assert_eq!(report.second_candidate_index(), Some(2));
        assert_eq!(report.second_split(), Some(z));
        assert!(report
            .hard_grandchild_lower_bounds()
            .unwrap()
            .into_iter()
            .all(|bound| bound > 0.99));
        assert_eq!(tree.root_split(), x);
        assert_eq!(tree.hard_value(), hard_value);
        assert_eq!(tree.second_split(), z);
        assert_eq!(tree.num_leaves(), 3);

        let (decision_model, decision_x, _decision_dummy, decision_z, _, decision) =
            adaptive_decision(hard_value, false, 1.0);
        assert_eq!(
            [decision_x.index(), decision_z.index()],
            [x.index(), z.index()]
        );
        let cert = tree
            .clone()
            .into_farkas_against_row_upper(&decision_model, decision)
            .expect("the arbitrary three-leaf shape must compose exactly");
        cert.verify(&decision_model)
            .expect("the completed asymmetric tree must independently verify");
        assert_eq!(cert.num_leaves(), 3);

        let mut continuous_decision = relaxation.clone();
        let continuous_row = continuous_decision.add_row(f64::NEG_INFINITY, 0.75, &[(p, 1.0)]);
        assert!(
            tree.clone()
                .into_farkas_against_row_upper(&continuous_decision, continuous_row)
                .is_none(),
            "continuous root and second splits do not cover the decision domain"
        );

        let (tampered_model, _, _, _, _, tampered_decision) =
            adaptive_decision(hard_value, false, 2.0);
        assert!(
            tree.into_farkas_against_row_upper(&tampered_model, tampered_decision)
                .is_none(),
            "changing the decision row's linear form must invalidate composition"
        );
    }
}

#[test]
fn an_infeasible_easy_child_is_retained_as_an_exact_farkas_leaf() {
    let hard_value = false;
    let (relaxation, x, dummy, z, p) = adaptive_relaxation(hard_value, true);
    let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    let (harvest, report) = session
        .harvest_cut_or_adaptive_three_leaf_target_fsb_stronger_than(
            &[(p, 1.0)],
            Sense::Minimize,
            &[x, dummy, z],
            0,
            hard_value,
            &rat(3, 4),
            &test_opts(),
        )
        .expect("x=1 is exactly infeasible while x=0,z=0/1 prove p>=1");
    let CertifiedAdaptiveThreeLeafHarvest::Tree(tree) = harvest else {
        panic!("the relaxation root remains p=1/2")
    };
    assert_eq!(report.probe_calls(), 4);
    assert_eq!(report.second_split(), Some(z));

    let (decision_model, _, _, _, _, decision) = adaptive_decision(hard_value, true, 1.0);
    let cert = tree
        .into_farkas_against_row_upper(&decision_model, decision)
        .expect("the direct easy-child Farkas witness must compose with two rows");
    cert.verify(&decision_model).unwrap();
    assert_eq!(cert.num_leaves(), 3);
}

#[test]
fn insufficient_easy_child_and_invalid_requests_fail_closed() {
    let (relaxation, x, dummy, z, p) = adaptive_relaxation(false, false);
    let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    assert!(
        session
            .harvest_cut_or_adaptive_three_leaf_target_fsb_stronger_than(
                &[(p, 1.0)],
                Sense::Minimize,
                &[x, dummy, z],
                0,
                false,
                &rat(5, 4),
                &test_opts(),
            )
            .is_none(),
        "the unsplit x=1 sibling proves only p>=1 and must fail closed"
    );

    for (candidates, root_index) in [
        (&[x, dummy, z][..], 3usize),
        (&[x, x, z][..], 0usize),
        (&[x][..], 0usize),
    ] {
        assert!(session
            .harvest_cut_or_adaptive_three_leaf_target_fsb_stronger_than(
                &[(p, 1.0)],
                Sense::Minimize,
                candidates,
                root_index,
                false,
                &rat(3, 4),
                &test_opts(),
            )
            .is_none());
    }
    assert!(
        session
            .harvest_cut_or_adaptive_three_leaf_target_fsb_stronger_than(
                &[(p, 1.0), (p, -1.0)],
                Sense::Minimize,
                &[x, dummy, z],
                0,
                false,
                &rat(3, 4),
                &test_opts(),
            )
            .is_none(),
        "duplicate objective columns must decline"
    );
}

#[test]
fn root_fast_path_and_all_probe_caps_obey_the_fail_closed_contract() {
    let (relaxation, x, dummy, z, p) = adaptive_relaxation(false, false);
    let candidates = [x, dummy, z];

    let mut root_session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    let (harvest, report) = root_session
        .harvest_cut_or_adaptive_three_leaf_target_fsb_stronger_than(
            &[(p, 1.0)],
            Sense::Minimize,
            &candidates,
            0,
            false,
            &rat(1, 4),
            &TargetFsbOpts::new()
                .with_max_probe_calls(0)
                .with_max_probe_pivots_per_call(0)
                .with_probe_time_limit(Duration::ZERO)
                .with_max_probe_scratch_bytes(0),
        )
        .expect("the root row p>=1/2 returns without consulting advice caps");
    let CertifiedAdaptiveThreeLeafHarvest::Root(row) = harvest else {
        panic!("a sufficient root must not build a tree")
    };
    row.verify(&relaxation).unwrap();
    assert_eq!(report.probe_calls(), 0);
    assert_eq!(report.root_candidate_index(), 0);
    assert_eq!(report.root_split(), x);
    assert!(!report.hard_value());
    assert_eq!(report.second_candidate_index(), None);
    assert_eq!(report.second_split(), None);
    assert_eq!(report.hard_grandchild_lower_bounds(), None);

    for opts in [
        test_opts().with_max_probe_calls(3),
        test_opts().with_max_probe_pivots_per_call(0),
        test_opts().with_probe_time_limit(Duration::ZERO),
        test_opts().with_max_probe_scratch_bytes(0),
    ] {
        let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
        assert!(
            session
                .harvest_cut_or_adaptive_three_leaf_target_fsb_stronger_than(
                    &[(p, 1.0)],
                    Sense::Minimize,
                    &candidates,
                    0,
                    false,
                    &rat(3, 4),
                    &opts,
                )
                .is_none(),
            "an incomplete bounded scan may not select from a partial ranking"
        );
    }

    let expired = Instant::now()
        .checked_sub(Duration::from_millis(1))
        .expect("monotonic clock supports a one-millisecond subtraction");
    let mut expired_session =
        LpSession::new(&relaxation, &SolveOpts::new().with_deadline(expired)).unwrap();
    assert!(
        expired_session
            .harvest_cut_or_adaptive_three_leaf_target_fsb_stronger_than(
                &[(p, 1.0)],
                Sense::Minimize,
                &candidates,
                0,
                false,
                &rat(3, 4),
                &test_opts(),
            )
            .is_none(),
        "an expired outer deadline must decline before the cold target root"
    );
}
