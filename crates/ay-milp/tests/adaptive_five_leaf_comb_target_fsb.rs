// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Three-stage target-FSB selection and exact five-leaf comb replay.

use std::time::{Duration, Instant};

use ay_milp::{Col, LpSession, Model, Sense, SolveOpts, TargetFsbOpts, TreeNode};
use num_rational::BigRational;
use num_traits::Zero;

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

fn candidate(model: &mut Model, binary: bool) -> Col {
    if binary {
        model.add_binary_col()
    } else {
        model.add_col(0.0, 1.0)
    }
}

/// Add `p >= constant + sum(weight * hard_literal(col))`.
fn add_p_ge_literals(model: &mut Model, p: Col, constant: f64, literals: &[(Col, bool, f64)]) {
    let mut lower = constant;
    let mut coeffs = vec![(p, 1.0)];
    for &(col, hard_value, weight) in literals {
        if hard_value {
            coeffs.push((col, -weight));
        } else {
            // hard_literal(false) = 1-col.
            lower += weight;
            coeffs.push((col, weight));
        }
    }
    model.add_row(lower, f64::INFINITY, &coeffs);
}

struct CombFixture {
    model: Model,
    root: Col,
    dummy1: Col,
    second: Col,
    dummy2: Col,
    third: Col,
    dummy3: Col,
    fourth: Col,
    p: Col,
    decision: Option<ay_milp::Row>,
}

/// A dyadic comb with candidates
/// `[root, dummy1, second, dummy2, third, dummy3, fourth]`.
///
/// Below root-hard, fixing `second` yields bounds 1/2 and 1 over a 1/3
/// relaxation. Below second-hard, `third` yields 3/4 and 1 over a 1/2
/// prefix bound. Below third-hard, both fixed values of `fourth` yield 1
/// over a 3/4 prefix bound.
fn comb_model(
    root_hard: bool,
    second_hard: bool,
    third_hard: bool,
    infeasible_root_easy: bool,
    binary: bool,
    decision_upper: Option<f64>,
) -> CombFixture {
    let mut model = Model::new();
    let root = candidate(&mut model, binary);
    let dummy1 = candidate(&mut model, binary);
    let second = candidate(&mut model, binary);
    let dummy2 = candidate(&mut model, binary);
    let third = candidate(&mut model, binary);
    let dummy3 = candidate(&mut model, binary);
    let fourth = candidate(&mut model, binary);
    let p = model.add_col(0.0, 2.0);

    // Root easy: p >= 1-hard(root).
    add_p_ge_literals(&mut model, p, 1.0, &[(root, root_hard, -1.0)]);

    // Second fixed hard/easy: p >= 1/2 and p >= 1 respectively.
    add_p_ge_literals(&mut model, p, 0.0, &[(second, second_hard, 0.5)]);
    add_p_ge_literals(&mut model, p, 1.0, &[(second, second_hard, -1.0)]);

    // Under second-hard, third fixed hard/easy: p >= 3/4 and p >= 1.
    add_p_ge_literals(
        &mut model,
        p,
        -1.0,
        &[(second, second_hard, 1.0), (third, third_hard, 0.75)],
    );
    add_p_ge_literals(
        &mut model,
        p,
        0.0,
        &[(second, second_hard, 1.0), (third, third_hard, -1.0)],
    );

    // Under both hard values, fourth=0/1 each imply p >= 1, while the
    // relaxed fourth value permits p=1/2.
    add_p_ge_literals(
        &mut model,
        p,
        -2.0,
        &[
            (second, second_hard, 1.0),
            (third, third_hard, 1.0),
            (fourth, true, 1.0),
        ],
    );
    add_p_ge_literals(
        &mut model,
        p,
        -1.0,
        &[
            (second, second_hard, 1.0),
            (third, third_hard, 1.0),
            (fourth, true, -1.0),
        ],
    );

    if infeasible_root_easy {
        if root_hard {
            model.add_row(1.0, f64::INFINITY, &[(root, 1.0)]);
        } else {
            model.add_row(f64::NEG_INFINITY, 0.0, &[(root, 1.0)]);
        }
    }
    let decision = decision_upper.map(|upper| model.add_row(f64::NEG_INFINITY, upper, &[(p, 1.0)]));
    CombFixture {
        model,
        root,
        dummy1,
        second,
        dummy2,
        third,
        dummy3,
        fourth,
        p,
        decision,
    }
}

struct FourCandidateFixture {
    model: Model,
    root: Col,
    second: Col,
    third: Col,
    fourth: Col,
    p: Col,
    decision: Option<ay_milp::Row>,
}

fn tie_model(binary: bool, decision: bool) -> FourCandidateFixture {
    let mut model = Model::new();
    let root = candidate(&mut model, binary);
    let second = candidate(&mut model, binary);
    let third = candidate(&mut model, binary);
    let fourth = candidate(&mut model, binary);
    let p = model.add_col(0.0, 2.0);
    model.add_row(1.0, f64::INFINITY, &[(p, 1.0)]);
    let decision = decision.then(|| model.add_row(f64::NEG_INFINITY, 0.75, &[(p, 1.0)]));
    FourCandidateFixture {
        model,
        root,
        second,
        third,
        fourth,
        p,
        decision,
    }
}

fn all_farkas_model(binary: bool) -> FourCandidateFixture {
    let mut model = Model::new();
    let root = candidate(&mut model, binary);
    let second = candidate(&mut model, binary);
    let third = candidate(&mut model, binary);
    let fourth = candidate(&mut model, binary);
    let p = model.add_col(0.0, 1.0);
    // root-hard=0 is fractionally feasible, but root-easy and every 0/1
    // assignment to a selected deeper split are infeasible.
    model.add_row(f64::NEG_INFINITY, 0.0, &[(root, 1.0)]);
    model.add_row(0.5, 0.5, &[(second, 1.0)]);
    model.add_row(0.5, 0.5, &[(third, 1.0)]);
    model.add_row(0.5, 0.5, &[(fourth, 1.0)]);
    FourCandidateFixture {
        model,
        root,
        second,
        third,
        fourth,
        p,
        decision: None,
    }
}

fn test_opts() -> TargetFsbOpts {
    TargetFsbOpts::new()
        .with_max_probe_pivots_per_call(64)
        .with_probe_time_limit(Duration::from_secs(2))
}

fn split_branches(node: &TreeNode, expected: Col) -> (&TreeNode, &TreeNode) {
    match node {
        TreeNode::Split { col, cut, lo, hi } => {
            assert_eq!(*col, expected);
            assert!(cut.is_zero());
            (lo.as_ref(), hi.as_ref())
        }
        TreeNode::Leaf { .. } => panic!("expected split on column {}", expected.index()),
    }
}

fn assert_leaf(node: &TreeNode) {
    assert!(matches!(node, TreeNode::Leaf { .. }));
}

#[allow(clippy::too_many_arguments)]
fn assert_exact_topology(
    root_node: &TreeNode,
    root: Col,
    root_hard: bool,
    second: Col,
    second_hard: bool,
    third: Col,
    third_hard: bool,
    fourth: Col,
) {
    let (root_lo, root_hi) = split_branches(root_node, root);
    let (root_easy, root_deep) = if root_hard {
        (root_lo, root_hi)
    } else {
        (root_hi, root_lo)
    };
    assert_leaf(root_easy);

    let (second_lo, second_hi) = split_branches(root_deep, second);
    let (second_easy, second_deep) = if second_hard {
        (second_lo, second_hi)
    } else {
        (second_hi, second_lo)
    };
    assert_leaf(second_easy);

    let (third_lo, third_hi) = split_branches(second_deep, third);
    let (third_easy, third_deep) = if third_hard {
        (third_lo, third_hi)
    } else {
        (third_hi, third_lo)
    };
    assert_leaf(third_easy);

    let (fourth_zero, fourth_one) = split_branches(third_deep, fourth);
    assert_leaf(fourth_zero);
    assert_leaf(fourth_one);
}

#[test]
fn selects_three_nonprefix_partners_and_verifies_all_orientations() {
    for root_hard in [false, true] {
        for second_hard in [false, true] {
            for third_hard in [false, true] {
                let relaxation = comb_model(root_hard, second_hard, third_hard, false, false, None);
                let candidates = [
                    relaxation.root,
                    relaxation.dummy1,
                    relaxation.second,
                    relaxation.dummy2,
                    relaxation.third,
                    relaxation.dummy3,
                    relaxation.fourth,
                ];
                let mut session = LpSession::new(&relaxation.model, &SolveOpts::new()).unwrap();
                let (comb, report) = session
                    .harvest_adaptive_five_leaf_comb_target_fsb_stronger_than(
                        &[(relaxation.p, 1.0)],
                        Sense::Minimize,
                        &candidates,
                        0,
                        root_hard,
                        &rat(7, 8),
                        &test_opts(),
                    )
                    .expect("all five exact leaves prove p>7/8");

                assert_eq!(report.candidate_count(), 7);
                assert_eq!(report.second_stage_probe_calls(), 12);
                assert_eq!(report.third_stage_probe_calls(), 10);
                assert_eq!(report.fourth_stage_probe_calls(), 8);
                assert_eq!(report.probe_calls(), 6 * candidates.len() - 12);
                assert_eq!(report.root_candidate_index(), 0);
                assert_eq!(report.root_split(), relaxation.root);
                assert_eq!(report.root_hard_value(), root_hard);
                assert_eq!(report.second_candidate_index(), 2);
                assert_eq!(report.second_split(), relaxation.second);
                assert_eq!(report.second_hard_value(), second_hard);
                assert_eq!(report.third_candidate_index(), 4);
                assert_eq!(report.third_split(), relaxation.third);
                assert_eq!(report.third_hard_value(), third_hard);
                assert_eq!(report.fourth_candidate_index(), 6);
                assert_eq!(report.fourth_split(), relaxation.fourth);

                let second_bounds = report.second_child_lower_bounds();
                if second_hard {
                    assert!(second_bounds[1] < second_bounds[0]);
                } else {
                    assert!(second_bounds[0] < second_bounds[1]);
                }
                assert!(second_bounds.into_iter().all(|bound| bound > 0.49));
                let third_bounds = report.third_child_lower_bounds();
                if third_hard {
                    assert!(third_bounds[1] < third_bounds[0]);
                } else {
                    assert!(third_bounds[0] < third_bounds[1]);
                }
                assert!(third_bounds.into_iter().all(|bound| bound > 0.74));
                assert!(report
                    .fourth_child_lower_bounds()
                    .into_iter()
                    .all(|bound| bound > 0.99));

                assert_eq!(comb.root_split(), relaxation.root);
                assert_eq!(comb.root_hard_value(), root_hard);
                assert_eq!(comb.second_split(), relaxation.second);
                assert_eq!(comb.second_hard_value(), second_hard);
                assert_eq!(comb.third_split(), relaxation.third);
                assert_eq!(comb.third_hard_value(), third_hard);
                assert_eq!(comb.fourth_split(), relaxation.fourth);
                assert_eq!(comb.num_leaves(), 5);

                let decision =
                    comb_model(root_hard, second_hard, third_hard, false, true, Some(0.875));
                let cert = comb
                    .clone()
                    .into_farkas_against_row_upper(&decision.model, decision.decision.unwrap())
                    .expect("the exact five-leaf comb must compose");
                cert.verify(&decision.model).unwrap();
                assert_eq!(cert.num_leaves(), 5);
                assert_exact_topology(
                    &cert.root,
                    decision.root,
                    root_hard,
                    decision.second,
                    second_hard,
                    decision.third,
                    third_hard,
                    decision.fourth,
                );

                let mut continuous = relaxation.model.clone();
                let upper = continuous.add_row(f64::NEG_INFINITY, 0.875, &[(relaxation.p, 1.0)]);
                assert!(
                    comb.into_farkas_against_row_upper(&continuous, upper)
                        .is_none(),
                    "continuous split columns cannot prove integer coverage"
                );
            }
        }
    }
}

#[test]
fn minimum_scan_and_exact_ties_preserve_caller_order() {
    let relaxation = tie_model(false, false);
    let candidates = [
        relaxation.second,
        relaxation.fourth,
        relaxation.root,
        relaxation.third,
    ];
    let mut session = LpSession::new(&relaxation.model, &SolveOpts::new()).unwrap();
    let (comb, report) = session
        .harvest_adaptive_five_leaf_comb_target_fsb_stronger_than(
            &[(relaxation.p, 1.0)],
            Sense::Minimize,
            &candidates,
            2,
            false,
            &rat(3, 4),
            &test_opts(),
        )
        .expect("all isolated branches prove p>=1");

    assert_eq!(report.second_stage_probe_calls(), 6);
    assert_eq!(report.third_stage_probe_calls(), 4);
    assert_eq!(report.fourth_stage_probe_calls(), 2);
    assert_eq!(report.probe_calls(), 12);
    assert_eq!(report.root_candidate_index(), 2);
    assert_eq!(report.second_candidate_index(), 0);
    assert_eq!(report.third_candidate_index(), 1);
    assert_eq!(report.fourth_candidate_index(), 3);
    assert_eq!(report.second_split(), relaxation.second);
    assert_eq!(report.third_split(), relaxation.fourth);
    assert_eq!(report.fourth_split(), relaxation.third);
    assert_eq!(
        report.second_child_lower_bounds()[0],
        report.second_child_lower_bounds()[1]
    );
    assert_eq!(
        report.third_child_lower_bounds()[0],
        report.third_child_lower_bounds()[1]
    );
    assert!(!report.second_hard_value());
    assert!(!report.third_hard_value());

    let decision = tie_model(true, true);
    let cert = comb
        .into_farkas_against_row_upper(&decision.model, decision.decision.unwrap())
        .expect("the tie-oriented comb remains complete");
    cert.verify(&decision.model).unwrap();
    assert_exact_topology(
        &cert.root,
        decision.root,
        false,
        decision.second,
        false,
        decision.fourth,
        false,
        decision.third,
    );
}

#[test]
fn a_root_easy_farkas_leaf_mixes_with_four_conditional_rows() {
    let relaxation = comb_model(false, true, false, true, false, None);
    let candidates = [
        relaxation.root,
        relaxation.dummy1,
        relaxation.second,
        relaxation.dummy2,
        relaxation.third,
        relaxation.dummy3,
        relaxation.fourth,
    ];
    let mut session = LpSession::new(&relaxation.model, &SolveOpts::new()).unwrap();
    let (comb, report) = session
        .harvest_adaptive_five_leaf_comb_target_fsb_stronger_than(
            &[(relaxation.p, 1.0)],
            Sense::Minimize,
            &candidates,
            0,
            false,
            &rat(7, 8),
            &test_opts(),
        )
        .expect("root-easy is infeasible and the remaining leaves prove p>=1");
    assert_eq!(report.probe_calls(), 30);

    let decision = comb_model(false, true, false, true, true, Some(0.875));
    let cert = comb
        .into_farkas_against_row_upper(&decision.model, decision.decision.unwrap())
        .expect("the mixed Farkas/conditional-row carrier must compose");
    cert.verify(&decision.model).unwrap();
    assert_eq!(cert.num_leaves(), 5);
}

#[test]
fn an_all_farkas_carrier_still_rejects_a_stale_upper_row() {
    let relaxation = all_farkas_model(false);
    let candidates = [
        relaxation.root,
        relaxation.second,
        relaxation.third,
        relaxation.fourth,
    ];
    let mut session = LpSession::new(&relaxation.model, &SolveOpts::new()).unwrap();
    let (comb, report) = session
        .harvest_adaptive_five_leaf_comb_target_fsb_stronger_than(
            &[(relaxation.p, 1.0)],
            Sense::Minimize,
            &candidates,
            0,
            false,
            &rat(0, 1),
            &test_opts(),
        )
        .expect("all five exact branches have direct infeasibility witnesses");
    assert_eq!(report.probe_calls(), 12);

    let mut augmented = all_farkas_model(true);
    let upper_row = augmented
        .model
        .add_row(f64::NEG_INFINITY, 0.5, &[(augmented.p, 1.0)]);
    let cert = comb
        .clone()
        .into_farkas_against_row_upper(&augmented.model, upper_row)
        .expect("a present upper row remains a valid replay parameter");
    cert.verify(&augmented.model).unwrap();

    let stale_target = all_farkas_model(true);
    assert!(upper_row.index() >= stale_target.model.num_rows());
    assert!(
        comb.into_farkas_against_row_upper(&stale_target.model, upper_row)
            .is_none(),
        "an all-Farkas carrier must not ignore an out-of-model upper row"
    );
}

#[test]
fn an_infeasible_root_hard_box_declines_without_an_anchor() {
    let mut relaxation = tie_model(false, false);
    relaxation
        .model
        .add_row(1.0, f64::INFINITY, &[(relaxation.root, 1.0)]);
    let mut session = LpSession::new(&relaxation.model, &SolveOpts::new()).unwrap();
    assert!(session
        .harvest_adaptive_five_leaf_comb_target_fsb_stronger_than(
            &[(relaxation.p, 1.0)],
            Sense::Minimize,
            &[
                relaxation.root,
                relaxation.second,
                relaxation.third,
                relaxation.fourth,
            ],
            0,
            false,
            &rat(3, 4),
            &test_opts(),
        )
        .is_none());
}

#[test]
fn complete_scan_caps_deadline_and_malformed_requests_fail_closed() {
    let relaxation = comb_model(false, false, false, false, false, None);
    let candidates = [
        relaxation.root,
        relaxation.dummy1,
        relaxation.second,
        relaxation.dummy2,
        relaxation.third,
        relaxation.dummy3,
        relaxation.fourth,
    ];
    let threshold = rat(7, 8);
    for opts in [
        test_opts().with_max_probe_calls(29),
        test_opts().with_max_probe_pivots_per_call(0),
        test_opts().with_probe_time_limit(Duration::ZERO),
        test_opts().with_probe_time_limit(Duration::MAX),
        test_opts().with_max_probe_scratch_bytes(0),
    ] {
        let mut session = LpSession::new(&relaxation.model, &SolveOpts::new()).unwrap();
        assert!(session
            .harvest_adaptive_five_leaf_comb_target_fsb_stronger_than(
                &[(relaxation.p, 1.0)],
                Sense::Minimize,
                &candidates,
                0,
                false,
                &threshold,
                &opts,
            )
            .is_none());
    }

    let mut session = LpSession::new(&relaxation.model, &SolveOpts::new()).unwrap();
    for (bad_candidates, root_index) in [
        (&candidates[..3], 0usize),
        (
            &[
                relaxation.root,
                relaxation.dummy1,
                relaxation.second,
                relaxation.second,
            ][..],
            0,
        ),
        (&candidates[..4], 4),
        (
            &[
                relaxation.root,
                relaxation.dummy1,
                relaxation.second,
                relaxation.p,
            ][..],
            0,
        ),
    ] {
        assert!(session
            .harvest_adaptive_five_leaf_comb_target_fsb_stronger_than(
                &[(relaxation.p, 1.0)],
                Sense::Minimize,
                bad_candidates,
                root_index,
                false,
                &threshold,
                &test_opts(),
            )
            .is_none());
    }
    for objective in [
        [(relaxation.p, 1.0), (relaxation.p, -1.0)],
        [(relaxation.p, f64::NAN), (relaxation.root, 0.0)],
    ] {
        assert!(session
            .harvest_adaptive_five_leaf_comb_target_fsb_stronger_than(
                &objective,
                Sense::Minimize,
                &candidates,
                0,
                false,
                &threshold,
                &test_opts(),
            )
            .is_none());
    }

    let mut too_many_model = relaxation.model.clone();
    let extra1 = too_many_model.add_col(0.0, 1.0);
    let extra2 = too_many_model.add_col(0.0, 1.0);
    let too_many_candidates = [
        candidates[0],
        candidates[1],
        candidates[2],
        candidates[3],
        candidates[4],
        candidates[5],
        candidates[6],
        extra1,
        extra2,
    ];
    let mut too_many_session = LpSession::new(&too_many_model, &SolveOpts::new()).unwrap();
    assert!(too_many_session
        .harvest_adaptive_five_leaf_comb_target_fsb_stronger_than(
            &[(relaxation.p, 1.0)],
            Sense::Minimize,
            &too_many_candidates,
            0,
            false,
            &threshold,
            &test_opts(),
        )
        .is_none());

    let expired = Instant::now()
        .checked_sub(Duration::from_millis(1))
        .expect("monotonic clock supports subtraction");
    let mut expired_session =
        LpSession::new(&relaxation.model, &SolveOpts::new().with_deadline(expired)).unwrap();
    assert!(expired_session
        .harvest_adaptive_five_leaf_comb_target_fsb_stronger_than(
            &[(relaxation.p, 1.0)],
            Sense::Minimize,
            &candidates,
            0,
            false,
            &threshold,
            &test_opts(),
        )
        .is_none());
}
