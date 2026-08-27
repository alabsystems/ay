// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// One ordinary `check()` under an explicit certificate posture.
#[cfg(test)]
fn solve_under_posture(m: &Model, require_certificates: bool) -> Outcome {
    let _env_lock = lock_env();
    BabSession::new(
        m.clone(),
        &opts().with_require_certificates(require_certificates),
    )
    .expect("session")
    .check()
    .expect("check")
}

/// The reframe verdict must match plain feasibility under both certificate
/// postures. Certificate policy is a filter on the finished original verdict,
/// not a work switch for the nested optimization.
#[cfg(test)]
fn assert_reframe_matches_plain(with_mark: &Model, plain: &Model, want_sat: bool) {
    for require_certificates in [false, true] {
        let reframed = solve_under_posture(with_mark, require_certificates);
        let feas = solve_under_posture(plain, require_certificates);
        assert_eq!(
            is_sat(&reframed),
            want_sat,
            "reframe verdict {} disagrees with the expected {} \
             (require_certificates={require_certificates})",
            tag(&reframed),
            if want_sat { "SAT" } else { "INFEASIBLE" }
        );
        assert_eq!(
            is_sat(&reframed),
            is_sat(&feas),
            "reframe verdict {} != plain feasibility verdict {} \
             (require_certificates={require_certificates})",
            tag(&reframed),
            tag(&feas)
        );
        if want_sat {
            assert!(
                !reframed.is_infeasible(),
                "reframe wrongly INFEASIBLE (require_certificates={require_certificates})"
            );
            assert!(
                !feas.is_infeasible(),
                "plain wrongly INFEASIBLE (require_certificates={require_certificates})"
            );
        } else {
            assert!(
                reframed.is_infeasible(),
                "reframe failed to prove INFEASIBLE (got {}, \
                 require_certificates={require_certificates})",
                tag(&reframed)
            );
        }
    }
}

/// Integral infeasibility whose LP relaxation remains feasible. A strict
/// margin crossing can therefore be certified only by the whole-tree cover.
#[cfg(test)]
fn integral_cover_shape() -> (Model, Model) {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_binary_col();
    m.add_row(f64::NEG_INFINITY, 3.0, &[(x, 2.0), (y, 2.0)]);
    let vrow = m.add_row(1.5, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
    let plain = m.clone();
    m.mark_margin_row(vrow).expect("one-sided margin row");
    (m, plain)
}

#[test]
fn integral_cover_crossing_matches_plain_under_both_postures() {
    let (mark, plain) = integral_cover_shape();
    assert_reframe_matches_plain(&mark, &plain, false);
}

#[test]
fn auto_path_exports_an_original_frame_tree_with_no_prefix() {
    let _env_lock = lock_env();
    let (model, _plain) = integral_cover_shape();
    let outcome = BabSession::new(
        model.clone(),
        &opts()
            .with_require_certificates(true)
            .with_tree_cert_leaves(64),
    )
    .expect("session")
    .check()
    .expect("check");

    match outcome {
        Outcome::Infeasible {
            cert: None,
            tree_cert: Some(tree),
        } => {
            tree.verify(&model)
                .expect("the Auto lane's tree must verify in the ORIGINAL model frame");
            assert!(
                tree.num_leaves() >= 2,
                "a case-split cover of this shape needs at least two leaves, got {}",
                tree.num_leaves()
            );
        }
        other => panic!("expected an original-frame tree-certified Infeasible, got {other:?}"),
    }
}

#[test]
fn auto_path_insufficient_leaf_cap_fails_closed_after_bound_crossing() {
    let _env_lock = lock_env();
    let (model, _plain) = integral_cover_shape();
    let outcome = BabSession::new(
        model,
        &opts()
            .with_require_certificates(true)
            .with_tree_cert_leaves(1),
    )
    .expect("session")
    .check()
    .expect("check");

    assert!(
        matches!(outcome, Outcome::Unknown { .. }),
        "a leaf cap too small to cover the crossing must fail CLOSED: {outcome:?}"
    );
}

#[test]
fn auto_path_equality_at_the_margin_never_triggers_bound_proof() {
    let _env_lock = lock_env();
    let (model, _prefix) = fractional_margin(true, 1.5);
    let outcome = BabSession::new(
        model,
        &opts()
            .with_require_certificates(true)
            .with_tree_cert_leaves(8)
            .with_engine(EngineEconomics::new().with_cuts(false).with_max_nodes(0)),
    )
    .expect("session")
    .check()
    .expect("check");

    assert!(
        matches!(outcome, Outcome::Unknown { .. }),
        "root bound == closed-row threshold is not exclusion: {outcome:?}"
    );
}

#[test]
fn auto_path_reachable_band_is_sat_with_a_point_that_meets_the_original_row() {
    let (mark, _plain) = build(true, 1.0, 2.0, true, 1.0);
    let outcome = solve_under_posture(&mark, true);
    match outcome {
        Outcome::Feasible { model_values, .. } | Outcome::Optimal { model_values, .. } => {
            mark.check_point(&model_values)
                .expect("the mapped witness must satisfy the ORIGINAL model incl. the band row");
        }
        other => panic!("a reachable band must stay SAT under strict policy, got {other:?}"),
    }
}

#[test]
fn auto_path_root_crossing_exports_the_same_root_farkas_as_the_unmarked_solve() {
    let _env_lock = lock_env();
    let mut model = Model::new();
    let x = model.add_binary_col();
    model.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
    let margin = model.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);
    let unmarked = model.clone();
    model.mark_margin_row(margin).expect("one-sided margin");

    // Disable tree capture so this fixture pins the checked root-Farkas arm.
    let solve_opts = opts()
        .with_require_certificates(true)
        .with_tree_cert_leaves(0);
    let marked_outcome = BabSession::new(model.clone(), &solve_opts)
        .expect("marked session")
        .check()
        .expect("marked check");
    let control = BabSession::new(unmarked.clone(), &solve_opts)
        .expect("unmarked session")
        .check()
        .expect("unmarked check");

    match marked_outcome {
        Outcome::Infeasible {
            cert: Some(farkas),
            tree_cert: None,
        } => farkas
            .verify(&model)
            .expect("the root witness must verify against the ORIGINAL model"),
        other => panic!("marking a row must not lose the root witness, got {other:?}"),
    }
    assert!(
        control.is_infeasible(),
        "the unmarked control decides this shape at the root: {control:?}"
    );
}
