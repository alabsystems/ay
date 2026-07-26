// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Two-stage target-FSB selection and exact four-leaf comb replay.

use std::time::{Duration, Instant};

use ay_milp::{Col, LpSession, Model, Sense, SolveOpts, TargetFsbOpts};
use num_rational::BigRational;

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

/// A dyadic comb with candidates `[root, dummy1, second, dummy2, third]`.
///
/// The root-easy leaf proves `p>=1`. Below root-hard, splitting `second`
/// yields bounds 3/4 and 1, with `second_hard` selecting which value is the
/// 3/4 child. Below both hard values, splitting `third` yields 1 on both
/// sides. The dummy candidates retain the current relaxed bound.
#[allow(clippy::type_complexity)]
fn comb_model(
    root_hard: bool,
    second_hard: bool,
    infeasible_root_easy: bool,
    binary: bool,
    decision: Option<(f64, f64)>,
) -> (Model, Col, Col, Col, Col, Col, Col, Option<ay_milp::Row>) {
    let mut model = Model::new();
    let root = candidate(&mut model, binary);
    let dummy1 = candidate(&mut model, binary);
    let second = candidate(&mut model, binary);
    let dummy2 = candidate(&mut model, binary);
    let third = candidate(&mut model, binary);
    let p = model.add_col(0.0, 2.0);

    if root_hard {
        // Easy root=0: p >= 1-root.
        model.add_row(1.0, f64::INFINITY, &[(p, 1.0), (root, 1.0)]);
    } else {
        // Easy root=1: p >= root.
        model.add_row(0.0, f64::INFINITY, &[(p, 1.0), (root, -1.0)]);
    }

    if second_hard {
        // Easy second=0, hard second=1.
        model.add_row(1.0, f64::INFINITY, &[(p, 1.0), (second, 1.0)]);
        model.add_row(0.0, f64::INFINITY, &[(p, 1.0), (second, -0.75)]);
        model.add_row(
            -1.0,
            f64::INFINITY,
            &[(p, 1.0), (third, -1.0), (second, -1.0)],
        );
        model.add_row(
            0.0,
            f64::INFINITY,
            &[(p, 1.0), (third, 1.0), (second, -1.0)],
        );
    } else {
        // Easy second=1, hard second=0.
        model.add_row(0.0, f64::INFINITY, &[(p, 1.0), (second, -1.0)]);
        model.add_row(0.75, f64::INFINITY, &[(p, 1.0), (second, 0.75)]);
        model.add_row(
            0.0,
            f64::INFINITY,
            &[(p, 1.0), (third, -1.0), (second, 1.0)],
        );
        model.add_row(1.0, f64::INFINITY, &[(p, 1.0), (third, 1.0), (second, 1.0)]);
    }

    if infeasible_root_easy {
        if root_hard {
            model.add_row(1.0, f64::INFINITY, &[(root, 1.0)]);
        } else {
            model.add_row(f64::NEG_INFINITY, 0.0, &[(root, 1.0)]);
        }
    }
    let decision_row = decision
        .map(|(coefficient, upper)| model.add_row(f64::NEG_INFINITY, upper, &[(p, coefficient)]));
    (model, root, dummy1, second, dummy2, third, p, decision_row)
}

fn tie_model(binary: bool, decision: bool) -> (Model, Col, Col, Col, Col, Option<ay_milp::Row>) {
    let mut model = Model::new();
    let root = candidate(&mut model, binary);
    let second = candidate(&mut model, binary);
    let third = candidate(&mut model, binary);
    let p = model.add_col(0.0, 2.0);
    // All three split columns are deliberately isolated, so every probe sees
    // the identical p>=1 relaxation and the selected second bounds are a
    // bit-for-bit tie rather than merely mathematically symmetric.
    model.add_row(1.0, f64::INFINITY, &[(p, 1.0)]);
    let row = decision.then(|| model.add_row(f64::NEG_INFINITY, 0.75, &[(p, 1.0)]));
    (model, root, second, third, p, row)
}

fn all_farkas_model(binary: bool) -> (Model, Col, Col, Col, Col) {
    let mut model = Model::new();
    let root = candidate(&mut model, binary);
    let second = candidate(&mut model, binary);
    let third = candidate(&mut model, binary);
    let p = model.add_col(0.0, 1.0);
    // root-hard=0 has a feasible fractional advice anchor, but root-easy=1
    // and every 0/1 value of either remaining split are infeasible. Thus all
    // four exact leaves are Farkas while the required hard anchor is Optimal.
    model.add_row(f64::NEG_INFINITY, 0.0, &[(root, 1.0)]);
    model.add_row(0.5, 0.5, &[(second, 1.0)]);
    model.add_row(0.5, 0.5, &[(third, 1.0)]);
    (model, root, second, third, p)
}

fn test_opts() -> TargetFsbOpts {
    TargetFsbOpts::new()
        .with_max_probe_pivots_per_call(64)
        .with_probe_time_limit(Duration::from_secs(2))
}

#[test]
fn selects_two_nonprefix_partners_and_verifies_all_orientations() {
    for root_hard in [false, true] {
        for second_hard in [false, true] {
            let (relaxation, root, dummy1, second, dummy2, third, p, _) =
                comb_model(root_hard, second_hard, false, false, None);
            let candidates = [root, dummy1, second, dummy2, third];
            let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
            let (comb, report) = session
                .harvest_adaptive_four_leaf_comb_target_fsb_stronger_than(
                    &[(p, 1.0)],
                    Sense::Minimize,
                    &candidates,
                    0,
                    root_hard,
                    &rat(7, 8),
                    &test_opts(),
                )
                .expect("the four exact comb leaves prove p>7/8");

            assert_eq!(report.candidate_count(), 5);
            assert_eq!(report.second_stage_probe_calls(), 8);
            assert_eq!(report.third_stage_probe_calls(), 6);
            assert_eq!(report.probe_calls(), 4 * candidates.len() - 6);
            assert_eq!(report.root_candidate_index(), 0);
            assert_eq!(report.root_split(), root);
            assert_eq!(report.root_hard_value(), root_hard);
            assert_eq!(report.second_candidate_index(), 2);
            assert_eq!(report.second_split(), second);
            assert_eq!(report.second_hard_value(), second_hard);
            let second_bounds = report.second_child_lower_bounds();
            if second_hard {
                assert!(second_bounds[1] < second_bounds[0]);
            } else {
                assert!(second_bounds[0] < second_bounds[1]);
            }
            assert!(second_bounds.into_iter().all(|bound| bound > 0.74));
            assert_eq!(report.third_candidate_index(), 4);
            assert_eq!(report.third_split(), third);
            assert!(report
                .third_child_lower_bounds()
                .into_iter()
                .all(|bound| bound > 0.99));

            assert_eq!(comb.root_split(), root);
            assert_eq!(comb.root_hard_value(), root_hard);
            assert_eq!(comb.second_split(), second);
            assert_eq!(comb.second_hard_value(), second_hard);
            assert_eq!(comb.third_split(), third);
            assert_eq!(comb.num_leaves(), 4);

            let (decision_model, decision_root, _, decision_second, _, decision_third, _, row) =
                comb_model(root_hard, second_hard, false, true, Some((1.0, 0.875)));
            assert_eq!(
                [
                    decision_root.index(),
                    decision_second.index(),
                    decision_third.index()
                ],
                [root.index(), second.index(), third.index()]
            );
            let decision = row.unwrap();
            let cert = comb
                .clone()
                .into_farkas_against_row_upper(&decision_model, decision)
                .expect("the asymmetric four-leaf comb must compose exactly");
            cert.verify(&decision_model)
                .expect("the completed arbitrary tree must independently verify");
            assert_eq!(cert.num_leaves(), 4);

            let mut continuous_decision = relaxation.clone();
            let continuous_row = continuous_decision.add_row(f64::NEG_INFINITY, 0.875, &[(p, 1.0)]);
            assert!(
                comb.clone()
                    .into_farkas_against_row_upper(&continuous_decision, continuous_row)
                    .is_none(),
                "continuous comb splits do not cover the decision domain"
            );

            let (feasible_model, _, _, _, _, _, _, feasible_row) =
                comb_model(root_hard, second_hard, false, true, Some((1.0, 1.25)));
            assert!(
                comb.into_farkas_against_row_upper(&feasible_model, feasible_row.unwrap())
                    .is_none(),
                "a changed upper row that admits p=1 must invalidate the proof"
            );
        }
    }
}

#[test]
fn a_nonzero_root_index_preserves_caller_order_and_exact_paths() {
    let (relaxation, root, dummy1, second, dummy2, third, p, _) =
        comb_model(false, false, false, false, None);
    let candidates = [dummy1, second, dummy2, root, third];
    let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    let (comb, report) = session
        .harvest_adaptive_four_leaf_comb_target_fsb_stronger_than(
            &[(p, 1.0)],
            Sense::Minimize,
            &candidates,
            3,
            false,
            &rat(7, 8),
            &test_opts(),
        )
        .expect("a non-prefix root must not disturb either adaptive selection");
    assert_eq!(report.root_candidate_index(), 3);
    assert_eq!(report.root_split(), root);
    assert_eq!(report.second_candidate_index(), 1);
    assert_eq!(report.second_split(), second);
    assert_eq!(report.third_candidate_index(), 4);
    assert_eq!(report.third_split(), third);
    assert_eq!(report.probe_calls(), 14);

    let (decision_model, _, _, _, _, _, _, decision) =
        comb_model(false, false, false, true, Some((1.0, 0.875)));
    let cert = comb
        .into_farkas_against_row_upper(&decision_model, decision.unwrap())
        .expect("the reordered caller surface must preserve exact branch paths");
    cert.verify(&decision_model).unwrap();
}

#[test]
fn lower_score_selects_hard_second_and_an_exact_tie_selects_false() {
    let (relaxation, root, second, third, p, _) = tie_model(false, false);
    let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    let (comb, report) = session
        .harvest_adaptive_four_leaf_comb_target_fsb_stronger_than(
            &[(p, 1.0)],
            Sense::Minimize,
            &[root, second, third],
            0,
            false,
            &rat(3, 4),
            &test_opts(),
        )
        .expect("both values of the selected second split prove p>=1");
    assert_eq!(report.second_split(), second);
    let bounds = report.second_child_lower_bounds();
    assert_eq!(bounds[0], bounds[1]);
    assert!(!report.second_hard_value(), "false must win an exact tie");
    assert_eq!(report.probe_calls(), 6);

    let (decision_model, _, _, _, _, decision) = tie_model(true, true);
    let cert = comb
        .into_farkas_against_row_upper(&decision_model, decision.unwrap())
        .expect("the tie-oriented comb remains a complete proof");
    cert.verify(&decision_model).unwrap();
}

#[test]
fn an_all_farkas_carrier_still_rejects_a_stale_upper_row() {
    let (relaxation, root, second, third, p) = all_farkas_model(false);
    let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    let (comb, report) = session
        .harvest_adaptive_four_leaf_comb_target_fsb_stronger_than(
            &[(p, 1.0)],
            Sense::Minimize,
            &[root, second, third],
            0,
            false,
            &rat(0, 1),
            &test_opts(),
        )
        .expect("every exact leaf has a direct branch infeasibility witness");
    assert_eq!(report.probe_calls(), 6);

    let (mut augmented, _, _, _, augmented_p) = all_farkas_model(true);
    let upper_row = augmented.add_row(f64::NEG_INFINITY, 0.5, &[(augmented_p, 1.0)]);
    let cert = comb
        .clone()
        .into_farkas_against_row_upper(&augmented, upper_row)
        .expect("a present row remains a valid replay parameter");
    cert.verify(&augmented).unwrap();

    let (stale_target, _, _, _, _) = all_farkas_model(true);
    assert!(upper_row.index() >= stale_target.num_rows());
    assert!(
        comb.into_farkas_against_row_upper(&stale_target, upper_row)
            .is_none(),
        "an all-Farkas carrier must not silently ignore an out-of-model row"
    );
}

#[test]
fn tree_only_surface_runs_the_full_scan_even_when_the_unfixed_root_is_sufficient() {
    let (relaxation, root, second, third, p, _) = tie_model(false, false);
    let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    let (comb, report) = session
        .harvest_adaptive_four_leaf_comb_target_fsb_stronger_than(
            &[(p, 1.0)],
            Sense::Minimize,
            &[root, second, third],
            0,
            false,
            &rat(3, 4),
            &test_opts(),
        )
        .expect("tree-only diagnostics must not return through an unfixed-root fast path");
    assert_eq!(report.probe_calls(), 6);
    assert_eq!(comb.num_leaves(), 4);
}

#[test]
fn an_infeasible_root_easy_child_becomes_an_exact_farkas_leaf() {
    let (relaxation, root, dummy1, second, dummy2, third, p, _) =
        comb_model(false, false, true, false, None);
    let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    let (comb, report) = session
        .harvest_adaptive_four_leaf_comb_target_fsb_stronger_than(
            &[(p, 1.0)],
            Sense::Minimize,
            &[root, dummy1, second, dummy2, third],
            0,
            false,
            &rat(7, 8),
            &test_opts(),
        )
        .expect("root=1 is exactly infeasible and the other three leaves prove p>=1");
    assert_eq!(report.probe_calls(), 14);

    let (decision_model, _, _, _, _, _, _, decision) =
        comb_model(false, false, true, true, Some((1.0, 0.875)));
    let cert = comb
        .into_farkas_against_row_upper(&decision_model, decision.unwrap())
        .expect("the direct root-easy Farkas leaf must compose with three rows");
    cert.verify(&decision_model).unwrap();
    assert_eq!(cert.num_leaves(), 4);
}

#[test]
fn an_infeasible_root_hard_box_declines_without_an_advice_anchor() {
    let (mut relaxation, root, second, third, p, _) = tie_model(false, false);
    relaxation.add_row(1.0, f64::INFINITY, &[(root, 1.0)]);
    let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    assert!(
        session
            .harvest_adaptive_four_leaf_comb_target_fsb_stronger_than(
                &[(p, 1.0)],
                Sense::Minimize,
                &[root, second, third],
                0,
                false,
                &rat(3, 4),
                &test_opts(),
            )
            .is_none(),
        "the root-hard box must solve to Optimal before it can seed probes"
    );
}

#[test]
fn full_scan_caps_deadline_and_malformed_requests_fail_closed() {
    let (relaxation, root, dummy1, second, dummy2, third, p, _) =
        comb_model(false, false, false, false, None);
    let candidates = [root, dummy1, second, dummy2, third];
    let threshold = rat(7, 8);
    for opts in [
        test_opts().with_max_probe_calls(13),
        test_opts().with_max_probe_pivots_per_call(0),
        test_opts().with_probe_time_limit(Duration::ZERO),
        test_opts().with_probe_time_limit(Duration::MAX),
        test_opts().with_max_probe_scratch_bytes(0),
    ] {
        let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
        assert!(
            session
                .harvest_adaptive_four_leaf_comb_target_fsb_stronger_than(
                    &[(p, 1.0)],
                    Sense::Minimize,
                    &candidates,
                    0,
                    false,
                    &threshold,
                    &opts,
                )
                .is_none(),
            "the complete 14-call work must be preflighted before solving"
        );
    }

    let mut session = LpSession::new(&relaxation, &SolveOpts::new()).unwrap();
    for (bad_candidates, root_index) in [
        (&[root, dummy1][..], 0usize),
        (&[root, root, second][..], 0usize),
        (&[root, dummy1, second][..], 3usize),
        (&[root, dummy1, p][..], 0usize),
    ] {
        assert!(session
            .harvest_adaptive_four_leaf_comb_target_fsb_stronger_than(
                &[(p, 1.0)],
                Sense::Minimize,
                bad_candidates,
                root_index,
                false,
                &threshold,
                &test_opts(),
            )
            .is_none());
    }
    for objective in [[(p, 1.0), (p, -1.0)], [(p, f64::NAN), (root, 0.0)]] {
        assert!(session
            .harvest_adaptive_four_leaf_comb_target_fsb_stronger_than(
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

    let expired = Instant::now()
        .checked_sub(Duration::from_millis(1))
        .expect("monotonic clock supports a one-millisecond subtraction");
    let mut expired_session =
        LpSession::new(&relaxation, &SolveOpts::new().with_deadline(expired)).unwrap();
    assert!(expired_session
        .harvest_adaptive_four_leaf_comb_target_fsb_stronger_than(
            &[(p, 1.0)],
            Sense::Minimize,
            &candidates,
            0,
            false,
            &threshold,
            &test_opts(),
        )
        .is_none());
}
