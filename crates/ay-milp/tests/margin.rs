// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness of the MARGIN REFRAME (opt-in via `Model::mark_margin_row`).
//!
//! The reframe turns an objective-≡0 feasibility problem `R ∧ (violation row)`
//! into a margin OPTIMIZATION and maps the optimum back to the ORIGINAL
//! feasibility verdict. The contract these tests pin down:
//!
//! 1. The reframed verdict EQUALS the plain feasibility verdict on the same
//!    model — for BOTH a property that HOLDS (original infeasible = the band is
//!    unreachable) and one that is VIOLATED (original feasible = the band is
//!    reached), across `<=` and `>=` rows, continuous and integral.
//! 2. An exported Farkas certificate independently verifies against the
//!    ORIGINAL model.
//! 3. The reframe is FAIL-SAFE: the kill switch and every ill-fitting shape
//!    fall back to the plain feasibility solve with an identical verdict.

use ay_milp::{BabSession, Col, Model, Outcome, SolveOpts, TargetFsbPrefixOpts, TreeNode};
use ay_test_support::env::{lock_env, ScopedEnvVar};

fn opts() -> SolveOpts {
    SolveOpts::new().with_time_limit(std::time::Duration::from_secs(30))
}

fn solve_unlocked(m: &Model) -> Outcome {
    BabSession::new(m.clone(), &opts())
        .expect("session")
        .check()
        .expect("check")
}

fn solve(m: &Model) -> Outcome {
    // Every solver path reads process-global tuning variables. Serialize those
    // reads with this binary's mutation tests so a temporary node cap cannot
    // interrupt an unrelated margin solve.
    let _env_lock = lock_env();
    solve_unlocked(m)
}

/// True for a satisfiable verdict (`Optimal`/`Feasible`).
fn is_sat(o: &Outcome) -> bool {
    o.is_sat()
}

/// A verdict class label, so a mismatch prints usefully.
fn tag(o: &Outcome) -> &'static str {
    match o {
        Outcome::Optimal { .. } => "OPTIMAL",
        Outcome::Feasible { .. } => "FEASIBLE",
        Outcome::Infeasible { .. } => "INFEASIBLE",
        Outcome::Unbounded => "UNBOUNDED",
        Outcome::Bound { .. } => "BOUND",
        Outcome::Unknown { .. } => "UNKNOWN",
        _ => "OTHER",
    }
}

/// Build `R ∧ (margin row)` where `R` is a single row `sum_x in [rest_lo,
/// rest_hi]` over two `[0,1]` variables (continuous unless `integral`), and the
/// margin row is `sum_x <= band` (`le`) or `sum_x >= band` (`ge`).
///
/// Returns `(with_mark, plain)`: identical models, but `with_mark` names the
/// margin row (reframe path) and `plain` leaves it a normal constraint
/// (feasibility path). Both must reach the same verdict.
fn build(integral: bool, rest_lo: f64, rest_hi: f64, le: bool, band: f64) -> (Model, Model) {
    let mut m = Model::new();
    let x = if integral {
        m.add_int_col(0.0, 1.0)
    } else {
        m.add_col(0.0, 1.0)
    };
    let y = if integral {
        m.add_int_col(0.0, 1.0)
    } else {
        m.add_col(0.0, 1.0)
    };
    // R: rest_lo <= x + y <= rest_hi
    m.add_row(rest_lo, rest_hi, &[(x, 1.0), (y, 1.0)]);
    // violation row: x + y <= band (le) or x + y >= band (ge)
    let vrow = if le {
        m.add_row(f64::NEG_INFINITY, band, &[(x, 1.0), (y, 1.0)])
    } else {
        m.add_row(band, f64::INFINITY, &[(x, 1.0), (y, 1.0)])
    };
    let plain = m.clone();
    m.mark_margin_row(vrow).expect("one-sided margin row");
    (m, plain)
}

/// Four binaries constrained to a half-integral sum. The integer model is
/// contradictory, but either side of a one-column prefix remains LP-feasible,
/// so a zero-node budget interrupts a genuinely open shared-prefix frontier.
/// The margin objective `x0+x1+x2+x3` is exactly `3/2` throughout.
fn fractional_margin(le: bool, band: f64) -> (Model, [Col; 4]) {
    let mut model = Model::new();
    let cols = [
        model.add_binary_col(),
        model.add_binary_col(),
        model.add_binary_col(),
        model.add_binary_col(),
    ];
    let sum = [
        (cols[0], 1.0),
        (cols[1], 1.0),
        (cols[2], 1.0),
        (cols[3], 1.0),
    ];
    model.add_row(1.5, 1.5, &sum);
    let margin = if le {
        model.add_row(f64::NEG_INFINITY, band, &sum)
    } else {
        model.add_row(band, f64::INFINITY, &sum)
    };
    model
        .mark_margin_row(margin)
        .expect("fixture has a one-sided nonempty margin");
    (model, cols)
}

fn solve_marked_prefix_unlocked(model: &Model, prefix: &[Col], tree_leaves: usize) -> Outcome {
    let opts = opts()
        .with_tree_cert_leaves(tree_leaves)
        .with_require_certificates(true);
    BabSession::new(model.clone(), &opts)
        .expect("marked-prefix session")
        .check_marked_margin_shared_binary_prefix(prefix)
        .expect("marked-prefix check")
}

fn solve_marked_prefix(model: &Model, prefix: &[Col], tree_leaves: usize) -> Outcome {
    let _env_lock = lock_env();
    solve_marked_prefix_unlocked(model, prefix, tree_leaves)
}

fn solve_marked_prefix_capped(model: &Model, prefix: &[Col], tree_leaves: usize) -> Outcome {
    let _env_lock = lock_env();
    let _node_cap = ScopedEnvVar::set("AY_MILP_MAX_NODES", "0");
    let _cuts = ScopedEnvVar::set("AY_MILP_NO_CUTS", "1");
    solve_marked_prefix_unlocked(model, prefix, tree_leaves)
}

#[test]
fn target_fsb_prefix_resource_decline_matches_the_fixed_fallback_api() {
    let _env_lock = lock_env();
    let _node_cap = ScopedEnvVar::set("AY_MILP_MAX_NODES", "0");
    let _cuts = ScopedEnvVar::set("AY_MILP_NO_CUTS", "1");
    let (mut model, fallback) = fractional_margin(true, 1.0);
    let candidates: [Col; 4] = std::array::from_fn(|_| model.add_binary_col());
    assert!(
        fallback.iter().all(|col| !candidates.contains(col)),
        "candidate and fallback pools must be independent in this regression"
    );
    let solve_opts = opts()
        .with_tree_cert_leaves(32)
        .with_require_certificates(true);

    let fixed = BabSession::new(model.clone(), &solve_opts)
        .expect("fixed fallback session")
        .check_marked_margin_shared_binary_prefix(&fallback)
        .expect("fixed fallback check");
    let declined = BabSession::new(model.clone(), &solve_opts)
        .expect("target-FSB session")
        .check_marked_margin_target_fsb_shared_binary_prefix(
            &fallback,
            &candidates,
            &TargetFsbPrefixOpts::new().with_max_probe_calls(0),
        )
        .expect("resource-declined target-FSB check");

    let certified_leaf_count = |outcome: Outcome| match outcome {
        Outcome::Infeasible {
            tree_cert: Some(tree),
            ..
        } => {
            tree.verify(&model)
                .expect("fallback tree must verify in the original model frame");
            tree.num_leaves()
        }
        other => panic!("expected caller-frame tree-certified Infeasible, got {other:?}"),
    };
    assert_eq!(
        certified_leaf_count(declined),
        certified_leaf_count(fixed),
        "a preflight decline must execute the same complete fallback partition"
    );
}

#[test]
fn target_fsb_prefix_selected_path_is_visible_and_verifies_in_caller_frame() {
    let _env_lock = lock_env();
    let _node_cap = ScopedEnvVar::set("AY_MILP_MAX_NODES", "0");
    let _cuts = ScopedEnvVar::set("AY_MILP_NO_CUTS", "1");
    let mut model = Model::new();
    let fallback: [Col; 4] = std::array::from_fn(|_| model.add_binary_col());
    let candidates: [Col; 4] = std::array::from_fn(|_| model.add_binary_col());
    let fallback_sum = fallback.map(|col| (col, 1.0));
    let candidate_sum = candidates.map(|col| (col, 1.0));
    // Both pools are independently half-integral. Either complete prefix can
    // certify the model, so inspect the public tree skeleton to distinguish a
    // completed candidate selection from a silent fallback.
    model.add_row(1.5, 1.5, &fallback_sum);
    model.add_row(1.5, 1.5, &candidate_sum);
    let margin = model.add_row(f64::NEG_INFINITY, 1.0, &fallback_sum);
    model
        .mark_margin_row(margin)
        .expect("fixture has a one-sided nonempty margin");
    let solve_opts = opts()
        .with_tree_cert_leaves(32)
        .with_require_certificates(true);

    let outcome = BabSession::new(model.clone(), &solve_opts)
        .expect("selected target-FSB session")
        .check_marked_margin_target_fsb_shared_binary_prefix(
            &fallback,
            &candidates,
            &TargetFsbPrefixOpts::new(),
        )
        .expect("completed target-FSB check");
    let tree = match outcome {
        Outcome::Infeasible {
            tree_cert: Some(tree),
            ..
        } => tree,
        other => panic!("expected selected tree-certified Infeasible, got {other:?}"),
    };
    tree.verify(&model)
        .expect("selected tree must verify in the original model frame");
    assert!(tree.num_leaves() > 1);
    let TreeNode::Split { col, .. } = &tree.root else {
        panic!("selected prefix must expose a split at the public tree root");
    };
    assert_eq!(
        *col, candidates[0],
        "equal/missing candidate scores must select in caller order"
    );
    assert!(
        !fallback.contains(col),
        "a fallback prefix would expose its disjoint first column at the root"
    );
}

/// The reframe verdict must MATCH the plain feasibility verdict, and both must
/// have the expected satisfiability. This is the core soundness property.
fn assert_reframe_matches_plain(with_mark: &Model, plain: &Model, want_sat: bool) {
    let reframed = solve(with_mark);
    let feas = solve(plain);
    assert_eq!(
        is_sat(&reframed),
        want_sat,
        "reframe verdict {} disagrees with the expected {}",
        tag(&reframed),
        if want_sat { "SAT" } else { "INFEASIBLE" }
    );
    assert_eq!(
        is_sat(&reframed),
        is_sat(&feas),
        "reframe verdict {} != plain feasibility verdict {}",
        tag(&reframed),
        tag(&feas)
    );
    // Neither path may EVER answer the opposite of the truth.
    if want_sat {
        assert!(!reframed.is_infeasible(), "reframe wrongly INFEASIBLE");
        assert!(!feas.is_infeasible(), "plain wrongly INFEASIBLE");
    } else {
        assert!(
            reframed.is_infeasible(),
            "reframe failed to prove INFEASIBLE (got {})",
            tag(&reframed)
        );
    }
}

// ---- property HOLDS: original INFEASIBLE (band unreachable) ----

#[test]
fn le_row_property_holds_is_infeasible_continuous() {
    // R forces x+y >= 1.5; the band asks x+y <= 1.0 -> min(x+y)=1.5 > 1.0.
    let (mark, plain) = build(false, 1.5, 2.0, true, 1.0);
    assert_reframe_matches_plain(&mark, &plain, false);
}

#[test]
fn le_row_property_holds_is_infeasible_integral() {
    // Binaries: R forces x+y >= 2 (both 1); band asks x+y <= 1 -> infeasible.
    let (mark, plain) = build(true, 2.0, 2.0, true, 1.0);
    assert_reframe_matches_plain(&mark, &plain, false);
}

#[test]
fn ge_row_property_holds_is_infeasible_continuous() {
    // R forces x+y <= 0.5; the band asks x+y >= 2.0 -> max(x+y)=0.5 < 2.0.
    let (mark, plain) = build(false, 0.0, 0.5, false, 2.0);
    assert_reframe_matches_plain(&mark, &plain, false);
}

// ---- property VIOLATED: original FEASIBLE (band reached) ----

#[test]
fn le_row_property_violated_is_feasible_continuous() {
    // R allows x+y in [0.5, 2]; band asks x+y <= 1.0 -> min=0.5 <= 1.0 -> SAT.
    let (mark, plain) = build(false, 0.5, 2.0, true, 1.0);
    assert_reframe_matches_plain(&mark, &plain, true);
}

#[test]
fn le_row_property_violated_is_feasible_integral() {
    // Binaries: R allows x+y in [1,2]; band asks x+y <= 1 -> x+y=1 -> SAT.
    let (mark, plain) = build(true, 1.0, 2.0, true, 1.0);
    assert_reframe_matches_plain(&mark, &plain, true);
}

#[test]
fn ge_row_property_violated_is_feasible_continuous() {
    // R allows x+y in [0, 0.6]; band asks x+y >= 0.3 -> max=0.6 >= 0.3 -> SAT.
    let (mark, plain) = build(false, 0.0, 0.6, false, 0.3);
    assert_reframe_matches_plain(&mark, &plain, true);
}

/// The reframe's FEASIBLE witness must actually satisfy the ORIGINAL model,
/// violation row included (the reframe returns the point; `finish` re-checks
/// it, so a wrong point would surface as `Unknown`, never a false SAT).
#[test]
fn feasible_witness_satisfies_the_original_model() {
    let (mark, _plain) = build(false, 0.5, 2.0, true, 1.0);
    match solve(&mark) {
        Outcome::Feasible { model_values, .. } | Outcome::Optimal { model_values, .. } => {
            mark.check_point(&model_values)
                .expect("reframe witness must satisfy the original model incl. the band row");
        }
        other => panic!("expected a witnessed SAT verdict, got {}", tag(&other)),
    }
}

// ---- certificate export ----

/// On an infeasible-because-band-unreachable instance the reframe should EXPORT
/// a Farkas certificate that independently verifies against the ORIGINAL model.
#[test]
fn infeasible_exports_verifiable_farkas() {
    let (mark, _plain) = build(false, 1.5, 2.0, true, 1.0);
    match solve(&mark) {
        Outcome::Infeasible { cert, tree_cert } => {
            // At least one exact witness, and it must verify against the model.
            let farkas = cert.expect("a continuous margin reframe exports a Farkas witness");
            farkas
                .verify(&mark)
                .expect("Farkas certificate must verify against the ORIGINAL model");
            assert!(tree_cert.is_none() || tree_cert.unwrap().verify(&mark).is_ok());
        }
        other => panic!("expected INFEASIBLE, got {}", tag(&other)),
    }
}

/// `>=` direction: same, with the LOWER-side fact composed in.
#[test]
fn ge_infeasible_exports_verifiable_farkas() {
    let (mark, _plain) = build(false, 0.0, 0.5, false, 2.0);
    match solve(&mark) {
        Outcome::Infeasible { cert, .. } => {
            let farkas = cert.expect("Farkas witness");
            farkas.verify(&mark).expect("verifies against original");
        }
        other => panic!("expected INFEASIBLE, got {}", tag(&other)),
    }
}

// ---- explicit marked-margin + shared-prefix composition ----

#[test]
fn marked_margin_shared_prefix_maps_a_feasible_witness_back() {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let y = model.add_binary_col();
    model.add_row(1.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
    let margin = model.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0), (y, 1.0)]);
    model.mark_margin_row(margin).expect("one-sided margin");

    match solve_marked_prefix(&model, &[x], 16) {
        Outcome::Feasible { model_values, .. } => model
            .check_point(&model_values)
            .expect("mapped witness must satisfy the original margin row"),
        other => panic!("expected mapped Feasible, got {other:?}"),
    }
}

#[test]
fn explicit_shared_margin_never_returns_bare_infeasible_under_default_policy() {
    let _env_lock = lock_env();
    let mut model = Model::new();
    let x = model.add_binary_col();
    // R fixes x=1, while the marked closed row asks for x<=0. The reframed
    // integer optimum excludes the margin, but with tree capture disabled it
    // has no original-frame MILP certificate.
    model.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
    let margin = model.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);
    model.mark_margin_row(margin).expect("one-sided margin");
    let opts = opts().with_tree_cert_leaves(0);
    assert!(
        !opts.require_certificates,
        "the regression must exercise the default generic certificate policy"
    );

    let outcome = BabSession::new(model, &opts)
        .expect("marked-prefix session")
        .check_marked_margin_shared_binary_prefix(&[x])
        .expect("marked-prefix check");
    assert!(
        matches!(
            outcome,
            Outcome::Unknown {
                reason: ay_milp::UnknownReason::CertificateUnavailable
            }
        ),
        "the explicit API must not map an uncertified reframed optimum to UNSAT: {outcome:?}"
    );
}

#[test]
fn interrupted_upper_margin_bound_exports_an_original_frame_tree() {
    let (model, prefix) = fractional_margin(true, 1.0);
    let outcome = solve_marked_prefix_capped(&model, &prefix[..1], 8);

    match outcome {
        Outcome::Infeasible {
            cert: None,
            tree_cert: Some(tree),
        } => {
            assert_eq!(tree.num_leaves(), 2, "one prefix split covers two regions");
            tree.verify(&model)
                .expect("bound-triggered tree must verify against the ORIGINAL row");
        }
        other => panic!("expected original-frame tree-certified Infeasible, got {other:?}"),
    }
}

#[test]
fn interrupted_lower_margin_bound_exports_an_original_frame_tree() {
    let (model, prefix) = fractional_margin(false, 2.0);
    let outcome = solve_marked_prefix_capped(&model, &prefix[..1], 8);

    match outcome {
        Outcome::Infeasible {
            tree_cert: Some(tree),
            ..
        } => tree
            .verify(&model)
            .expect("maximize-frame strict crossing must replay in the original frame"),
        other => panic!("expected original-frame tree-certified Infeasible, got {other:?}"),
    }
}

/// An unlimited solve must not launch live replay from inside the node loop.
/// This tiny fractional integer tree therefore exhausts first; its strict
/// margin crossing is recognized at the terminal quiescent boundary and the
/// real capture is finalized there.
#[test]
fn exhausted_terminal_margin_crossing_exports_an_original_frame_tree() {
    let _env_lock = lock_env();
    let (model, prefix) = fractional_margin(true, 1.0);
    let opts = SolveOpts::new()
        .with_tree_cert_leaves(64)
        .with_require_certificates(true);
    let outcome = BabSession::new(model.clone(), &opts)
        .expect("unlimited marked-prefix session")
        .check_marked_margin_shared_binary_prefix(&prefix[..1])
        .expect("unlimited terminal solve");

    match outcome {
        Outcome::Infeasible {
            cert: None,
            tree_cert: Some(tree),
        } => tree
            .verify(&model)
            .expect("terminal replay must verify against the original margin model"),
        other => {
            panic!("expected terminal original-frame tree-certified Infeasible, got {other:?}")
        }
    }
}

#[test]
fn equality_at_the_margin_never_triggers_bound_proof() {
    let (model, prefix) = fractional_margin(true, 1.5);
    let outcome = solve_marked_prefix_capped(&model, &prefix[..1], 8);

    assert!(
        matches!(outcome, Outcome::Unknown { .. }),
        "root bound == closed-row threshold is not exclusion: {outcome:?}"
    );
}

#[test]
fn insufficient_tree_leaf_cap_fails_closed_after_bound_crossing() {
    let (model, prefix) = fractional_margin(true, 1.0);
    let outcome = solve_marked_prefix_capped(&model, &prefix[..1], 1);

    assert!(
        matches!(outcome, Outcome::Unknown { .. }),
        "two prefix regions cannot produce authority under a one-leaf cap: {outcome:?}"
    );
}

#[test]
fn explicit_shared_margin_rejects_a_missing_mark_before_search() {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let mut session = BabSession::new(model, &opts()).expect("native session");
    let error = session
        .check_marked_margin_shared_binary_prefix(&[x])
        .expect_err("the explicit API requires a marked margin");
    assert!(error.to_string().contains("marked-margin shared prefix"));
}

#[test]
fn expired_shared_margin_deadline_returns_unknown_without_authority() {
    use std::time::{Duration, Instant};

    let (model, prefix) = fractional_margin(true, 1.0);
    let expired = Instant::now()
        .checked_sub(Duration::from_secs(1))
        .expect("monotonic clock supports a one-second lookback");
    let opts = SolveOpts::new()
        .with_deadline(expired)
        .with_tree_cert_leaves(8)
        .with_require_certificates(true);
    let outcome = BabSession::new(model, &opts)
        .expect("marked-prefix session")
        .check_marked_margin_shared_binary_prefix(&prefix[..1])
        .expect("deadline is an outcome, not an API error");

    assert!(matches!(outcome, Outcome::Unknown { .. }));
}

// ---- multiple inequality rows: folding ONE is still sound ----

/// `R` itself contains several inequality rows; the margin row is just one of
/// them. Folding it into the objective while the others stay as constraints
/// must still give the correct feasibility verdict.
#[test]
fn multiple_inequality_rows_fold_one_soundly() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 10.0);
    let y = m.add_col(0.0, 10.0);
    // Several ordinary inequality rows in R.
    m.add_row(3.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]); // x+y >= 3
    m.add_row(f64::NEG_INFINITY, 8.0, &[(x, 1.0)]); //        x   <= 8
    m.add_row(1.0, f64::INFINITY, &[(y, 1.0)]); //            y   >= 1
                                                // The band: x <= 0.5. With x+y>=3, y>=1, x can still be 0 (y=3), so min x=0
                                                // <= 0.5 -> the band IS reachable -> original FEASIBLE.
    let vrow = m.add_row(f64::NEG_INFINITY, 0.5, &[(x, 1.0)]);
    let plain = m.clone();
    m.mark_margin_row(vrow).expect("one-sided");
    assert_reframe_matches_plain(&m, &plain, true);

    // Now make the band unreachable: x >= 6 while x <= 8, but also x+y>=3 and a
    // tightening row x+y <= 5 with y>=1 forces x <= 4 -> x >= 6 unreachable.
    let mut m2 = Model::new();
    let x = m2.add_col(0.0, 10.0);
    let y = m2.add_col(0.0, 10.0);
    m2.add_row(3.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]); // x+y >= 3
    m2.add_row(f64::NEG_INFINITY, 5.0, &[(x, 1.0), (y, 1.0)]); // x+y <= 5
    m2.add_row(1.0, f64::INFINITY, &[(y, 1.0)]); // y >= 1 -> x <= 4
    let vrow2 = m2.add_row(6.0, f64::INFINITY, &[(x, 1.0)]); // band: x >= 6 (unreachable)
    let plain2 = m2.clone();
    m2.mark_margin_row(vrow2).expect("one-sided");
    assert_reframe_matches_plain(&m2, &plain2, false);
}

// ---- fail-safe: kill switch and ill-fitting shapes fall back ----

/// With the kill switch set, the reframe declines and the plain feasibility
/// solve decides — same verdict.
#[test]
fn kill_switch_falls_back_to_plain() {
    let (mark, plain) = build(false, 1.5, 2.0, true, 1.0);
    let _env_lock = lock_env();
    let _kill_switch = ScopedEnvVar::set("AY_MILP_NO_MARGIN_REFRAME", "1");
    let (reframed, feas) = (solve_unlocked(&mark), solve_unlocked(&plain));
    assert_eq!(
        is_sat(&reframed),
        is_sat(&feas),
        "kill-switched reframe must equal plain feasibility ({} vs {})",
        tag(&reframed),
        tag(&feas)
    );
    assert!(
        reframed.is_infeasible(),
        "still the correct INFEASIBLE verdict"
    );
}

/// A two-sided (range) or equality row is not a single margin: `mark_margin_row`
/// must reject it, so the reframe can never fire on an ambiguous shape.
#[test]
fn non_one_sided_rows_are_rejected() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 10.0);
    let range = m.add_row(1.0, 5.0, &[(x, 1.0)]); // two-sided
    assert!(
        m.mark_margin_row(range).is_err(),
        "range row must be rejected"
    );
    let eq = m.add_row(3.0, 3.0, &[(x, 1.0)]); // equality
    assert!(
        m.mark_margin_row(eq).is_err(),
        "equality row must be rejected"
    );
    let empty = m.add_row(f64::NEG_INFINITY, 1.0, &[]); // no coefficients
    assert!(
        m.mark_margin_row(empty).is_err(),
        "empty row must be rejected"
    );
    assert!(
        m.margin_row().is_none(),
        "no margin should be set after failures"
    );
}

/// A model that names a margin but also carries a REAL objective is a misuse:
/// the reframe declines (objective ≢ 0) and the plain optimization runs.
#[test]
fn nonzero_objective_declines_reframe() {
    use ay_milp::Sense;
    let mut m = Model::new();
    let x = m.add_col(0.0, 10.0);
    let y = m.add_col(0.0, 10.0);
    m.add_row(3.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
    let vrow = m.add_row(f64::NEG_INFINITY, 0.5, &[(x, 1.0)]);
    m.set_objective(&[(x, 1.0), (y, 1.0)], Sense::Minimize); // real objective
    m.mark_margin_row(vrow).expect("one-sided");
    // The reframe gate declines (objective ≢ 0): the plain optimization runs and
    // returns the genuine optimum of the model WITH the band row as a constraint.
    match solve(&m) {
        Outcome::Optimal { value, .. } => {
            // min x+y s.t. x+y>=3, x<=0.5 -> x=0.5, y=2.5 -> 3. The band is a
            // hard constraint here (not folded away), so the optimum is 3.
            assert_eq!(value, num_rational::BigRational::from_integer(3.into()));
        }
        other => panic!("expected OPTIMAL 3, got {}", tag(&other)),
    }
}

// ---- AUTO-DETECTED margin (`AY_MILP_AUTO_MARGIN=1`) ----
//
// `mark_margin_row`'s only non-test callers require the CALLER to name the row,
// so the whole reframe is unreachable from an ordinary `check()` — i.e. from
// every model that arrives as a file, which is every ny W1 model, the class this
// module was written for. The arm closes that, and it is DEFAULT-OFF because it
// was measured on those models and lost: it gains SAT witnesses and loses UNSAT
// proofs, and UNSAT is the deliverable (numbers at `margin::auto_margin_row`).
// These tests pin the contract it keeps while firing: the same verdict as the
// plain feasibility solve, caller-frame-verifiable evidence, no reach into a
// model with a real objective — and, first, that it stays off unless asked.

/// The ny W1 shape: an objective-≡0 model whose network row defines a FREE slack
/// column, asserted one-sided by its own singleton row. `capped` adds the row
/// that makes the band unreachable (the property HOLDS => original INFEASIBLE).
fn auto_w1_shape(capped: bool) -> Model {
    let mut m = Model::new();
    let a = m.add_binary_col();
    let b = m.add_binary_col();
    let s = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
    // The "network": s = a + b.
    m.add_row(0.0, 0.0, &[(a, 1.0), (b, 1.0), (s, -1.0)]);
    if capped {
        m.add_row(f64::NEG_INFINITY, 1.0, &[(a, 1.0), (b, 1.0)]);
    }
    // The violation assertion: s >= 2. Detected, not marked.
    m.add_row(2.0, f64::INFINITY, &[(s, 1.0)]);
    m
}

fn solve_auto(m: &Model) -> Outcome {
    let _env_lock = lock_env();
    let _on = ScopedEnvVar::set("AY_MILP_AUTO_MARGIN", "1");
    solve_unlocked(m)
}

/// The core soundness property for auto-firing: an UNMARKED model must reach the
/// same verdict it reaches with the arm off, in both directions.
#[test]
fn auto_detected_margin_matches_the_marked_only_verdict() {
    for capped in [true, false] {
        let m = auto_w1_shape(capped);
        let auto = solve_auto(&m);
        let plain = solve(&m);
        assert_eq!(
            is_sat(&auto),
            !capped,
            "auto-detected reframe verdict {} is wrong for capped={capped}",
            tag(&auto)
        );
        assert_eq!(
            is_sat(&auto),
            is_sat(&plain),
            "auto {} != default (arm off) {} for capped={capped}",
            tag(&auto),
            tag(&plain)
        );
    }
}

/// Auto-firing must not weaken the evidence: the composed Farkas has to verify
/// against the ORIGINAL model, band row included, exactly as it does when a
/// caller named the row by hand. Continuous, so the reframed optimum carries the
/// LP dual the composition needs — the same shape as
/// `infeasible_exports_verifiable_farkas` above, with the row DETECTED instead of
/// marked.
#[test]
fn auto_detected_margin_exports_a_caller_frame_farkas() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 1.0);
    let y = m.add_col(0.0, 1.0);
    let s = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
    m.add_row(0.0, 0.0, &[(x, 1.0), (y, 1.0), (s, -1.0)]);
    m.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0), (y, 1.0)]);
    m.add_row(2.0, f64::INFINITY, &[(s, 1.0)]);
    match solve_auto(&m) {
        Outcome::Infeasible { cert, .. } => {
            let farkas = cert.expect("a detected margin exports the same Farkas a marked one does");
            farkas
                .verify(&m)
                .expect("Farkas must verify against the ORIGINAL model");
        }
        other => panic!("expected INFEASIBLE, got {}", tag(&other)),
    }
}

/// The SAT witness comes back in the caller's frame and satisfies the band row —
/// the reframe relaxed it, so this is the assertion that the map is honest.
#[test]
fn auto_detected_margin_returns_a_witness_for_the_original() {
    let m = auto_w1_shape(false);
    match solve_auto(&m) {
        Outcome::Feasible { model_values, .. } | Outcome::Optimal { model_values, .. } => m
            .check_point(&model_values)
            .expect("witness must satisfy the ORIGINAL model incl. the detected band row"),
        other => panic!("expected a witnessed SAT verdict, got {}", tag(&other)),
    }
}

/// THE BYTE-IDENTITY GUARD. Detection requires an objective identically zero, so
/// a model carrying the very same row shape AND a real objective is untouched
/// even with the arm ON: the plain optimization runs and the band row stays a
/// hard constraint.
#[test]
fn a_real_objective_is_never_auto_reframed() {
    use ay_milp::Sense;
    let mut m = Model::new();
    let a = m.add_binary_col();
    let b = m.add_binary_col();
    let s = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
    m.add_row(0.0, 0.0, &[(a, 1.0), (b, 1.0), (s, -1.0)]);
    m.add_row(2.0, f64::INFINITY, &[(s, 1.0)]);
    m.set_objective(&[(a, 1.0), (b, 3.0)], Sense::Minimize);
    // s >= 2 forces a = b = 1, so the optimum is 4 — and it is 4 only because the
    // band row was honored as a CONSTRAINT rather than folded into the objective.
    match solve_auto(&m) {
        Outcome::Optimal { value, .. } => assert_eq!(
            value,
            num_rational::BigRational::from_integer(4.into()),
            "the band row must remain a hard constraint on an optimization model"
        ),
        other => panic!("expected OPTIMAL 4, got {}", tag(&other)),
    }
}
