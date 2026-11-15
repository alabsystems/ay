// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual marked-margin/native entry and original caller-frame evidence.
//! Authored externally against 24dadd896f5f4438ecfd56e706e964c07a6c2ac0;
//! execution and qualification belong to the applying owner.

use super::{take_test_reports, Report, MAX_CALLS, MAX_VISITS};
use crate::{BabSession, EngineEconomics, Model, Outcome, SolveOpts, TreeNode};
use ay_test_support::env::lock_env;
use num_rational::BigRational;
use std::time::Duration;

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

// The continuous columns are genuine affine network riders, not unused columns
// added only to pass the mixed gate: x=2a+b and y=b+3c occur in the marked row.
fn fixture(sum: (f64, f64), band: f64, integral: bool) -> Model {
    let mut model = Model::new();
    let mut bit = || {
        if integral {
            model.add_binary_col()
        } else {
            model.add_col(0.0, 1.0)
        }
    };
    let [a, b, c] = [bit(), bit(), bit()];
    let x = model.add_col(0.0, 3.0);
    let y = model.add_col(0.0, 4.0);
    model.add_row(sum.0, sum.1, &[(a, 1.0), (b, 1.0), (c, 1.0)]);
    model.add_row(0.0, 0.0, &[(x, 1.0), (a, -2.0), (b, -1.0)]);
    model.add_row(0.0, 0.0, &[(y, 1.0), (b, -1.0), (c, -3.0)]);
    let margin = model.add_row(f64::NEG_INFINITY, band, &[(x, 1.0), (y, 1.0)]);
    model
        .mark_margin_row(margin)
        .expect("one-sided caller margin");
    model
}

fn opts(node_prop: Option<bool>) -> SolveOpts {
    // Keep this tiny mechanism control on the native node-entry path. None
    // deliberately leaves propagation at its real marked/mixed default.
    let mut engine = EngineEconomics::new()
        .with_presolve(false)
        .with_root_probe(false)
        .with_cuts(false)
        .with_root_floor(false)
        .with_node_cuts(false)
        .with_sb_total(0)
        .with_sb_cands(0)
        .with_gub_branch(false)
        .with_sym(false)
        .with_auto_margin(false)
        .with_lattice(false)
        .with_dedup_cols(false)
        .with_binary_complement_sub(false)
        .with_pump_restarts(0)
        .with_max_nodes(128)
        .with_heur_share(0.0)
        .expect("zero heuristic share");
    if let Some(enabled) = node_prop {
        engine = engine.with_node_prop(enabled);
    }
    SolveOpts::new()
        .with_structure_routing(false)
        .with_require_certificates(true)
        .with_tree_cert_leaves(64)
        .with_time_limit(Duration::from_secs(10))
        .with_engine(engine)
}

fn solve(model: &Model, node_prop: Option<bool>) -> (Outcome, Vec<Report>) {
    // Drain observations from earlier work on this thread, never global node
    // counters. These records come only from the actual native state drop.
    let _ = take_test_reports();
    let outcome = BabSession::new(model.clone(), &opts(node_prop))
        .expect("caller session")
        .check()
        .expect("actual marked-margin/native check");
    (outcome, take_test_reports())
}

fn assert_tree(model: &Model, outcome: Outcome) -> crate::MilpInfeasibilityCertificate {
    let Outcome::Infeasible { cert, tree_cert } = outcome else {
        panic!("expected caller-frame Infeasible, got {outcome:?}");
    };
    assert!(cert.is_none(), "the caller LP has an exact feasible point");
    let tree = tree_cert.expect("native closure must export a complete tree");
    tree.verify(model)
        .expect("certificate verifies the original caller model");
    assert!(matches!(&tree.root, TreeNode::Split { .. }));
    assert!((2..=64).contains(&tree.num_leaves()));
    tree
}

#[test]
fn early_marked_native_conflict_before_1024_exports_original_caller_tree() {
    let _guard = lock_env();
    let caller = fixture((1.5, 1.5), 100.0, true);
    let lp = fixture((1.5, 1.5), 100.0, false);
    lp.check_point(&[rat(1, 2), rat(1, 2), rat(1, 2), rat(3, 2), rat(2, 1)])
        .expect("the original relaxation is inhabited; no root refutation exists");
    assert!(super::super::mixed_model_gate(&caller));
    for mask in 0..8 {
        let (a, b, c) = (mask & 1, (mask >> 1) & 1, (mask >> 2) & 1);
        let point = [a, b, c, 2 * a + b, b + 3 * c].map(|n| rat(n, 1));
        assert!(caller.check_point(&point).is_err());
    }

    let (outcome, reports) = solve(&caller, None);
    let tree = assert_tree(&caller, outcome);
    let active: Vec<_> = reports.iter().filter(|r| r.attempts > 0).collect();
    assert!(
        !active.is_empty(),
        "must observe actual native early work: {reports:?}"
    );
    assert!(
        active
            .iter()
            .any(|r| r.conflicts > 0 && r.accepted_prunes > 0),
        "a live strict conflict accepted by native search is mandatory"
    );
    for report in active {
        assert!(report.eligible);
        assert!((1..=MAX_CALLS).contains(&report.attempts));
        assert!((1..=MAX_VISITS).contains(&report.visits));
        assert!(report.terms > 0);
        assert!(report.tightenings > 0);
        assert!(report.first_node.is_some_and(|n| n > 0 && n < 1024));
        assert!(report.last_node.is_some_and(|n| n < 1024));
        if report.conflicts > 0 {
            assert!(report
                .first_conflict_node
                .is_some_and(|n| n > 0 && n < 1024));
        }
        assert_eq!(report.deadline_limits, 0);
        assert_eq!(report.memory_declines, 0);
    }

    let feasible_caller = fixture((1.5, 2.5), 100.0, true);
    feasible_caller
        .check_point(&[rat(1, 1), rat(1, 1), rat(0, 1), rat(3, 1), rat(1, 1)])
        .expect("the different caller frame is genuinely feasible");
    assert!(
        tree.verify(&feasible_caller).is_err(),
        "never relabel the old tree"
    );
}

#[test]
fn early_marked_native_bound_exclusion_exports_original_caller_tree() {
    let _guard = lock_env();
    let caller = fixture((1.5, 2.5), 3.5, true);
    let lp = fixture((1.5, 2.5), 3.5, false);
    lp.check_point(&[rat(1, 1), rat(1, 2), rat(0, 1), rat(5, 2), rat(1, 2)])
        .expect("the original caller LP reaches x+y=3 below the marked band");
    let prepared = crate::margin::prepare(&caller).expect("actual marked-margin preparation");
    let witness = [rat(1, 1), rat(1, 1), rat(0, 1), rat(3, 1), rat(1, 1)];
    prepared
        .reframed_model
        .check_point(&witness)
        .expect("the optimization base is integer-feasible; only the band is empty");
    assert!(caller.check_point(&witness).is_err());
    // Integer sum in [1.5,2.5] is 2, and x+y=2(a+b)+3c=4+c.
    // Hence this original margin is UNSAT, while band4 is its closed SAT tie.
    let (outcome, reports) = solve(&caller, None);
    let _tree = assert_tree(&caller, outcome);
    let active: Vec<_> = reports.iter().filter(|r| r.attempts > 0).collect();
    assert!(
        !active.is_empty(),
        "must exercise the actual early native lane: {reports:?}"
    );
    assert!(active.iter().any(|r| r.tightenings > 0));
    for report in active {
        assert!(report.eligible && report.terms > 0);
        assert!((1..=MAX_CALLS).contains(&report.attempts));
        assert!((1..=MAX_VISITS).contains(&report.visits));
        assert!(report.first_node.is_some_and(|n| n > 0 && n < 1024));
        assert!(report.last_node.is_some_and(|n| n < 1024));
        assert_eq!(report.deadline_limits, 0);
    }
    // No raw propagation conflict is required: the marked row is absent from
    // the inner optimization, whose caller-frame proof is checked above.
}

#[test]
fn early_marked_native_explicit_disable_and_unmarked_keep_original_certificates() {
    let _guard = lock_env();
    let marked = fixture((1.5, 1.5), 100.0, true);
    let mut unmarked = marked.clone();
    unmarked.clear_margin();
    for (caller, node_prop) in [(&marked, Some(false)), (&unmarked, None)] {
        let (outcome, reports) = solve(caller, node_prop);
        let _tree = assert_tree(caller, outcome);
        assert!(!reports.is_empty(), "must reach the actual native state");
        assert!(reports
            .iter()
            .all(|r| !r.eligible && r.attempts == 0 && r.conflicts == 0));
        assert!(reports
            .iter()
            .all(|r| r.first_node.is_none() && r.first_conflict_node.is_none()));
    }
}

#[test]
fn early_marked_native_unsafe_and_closed_tie_keep_exact_original_witnesses() {
    let _guard = lock_env();
    // Network min(x+y)=4 over integer sum in [1.5,2.5]. Thus 4.25 is
    // strictly unsafe and 4 is its closed equality boundary, both SAT.
    let witness = [rat(1, 1), rat(1, 1), rat(0, 1), rat(3, 1), rat(1, 1)];
    for band in [4.25, 4.0] {
        let caller = fixture((1.5, 2.5), band, true);
        caller
            .check_point(&witness)
            .expect("exact original unsafe/tie witness");
        let (outcome, reports) = solve(&caller, None);
        let values = match outcome {
            Outcome::Optimal { model_values, .. } | Outcome::Feasible { model_values, .. } => {
                model_values
            }
            other => panic!("unsafe/tie caller must stay SAT at band {band}: {other:?}"),
        };
        caller
            .check_point(&values)
            .expect("replay returned point in original caller frame");
        assert_eq!(values.len(), witness.len());
        assert_eq!(&values[3] + &values[4], rat(4, 1));
        let active: Vec<_> = reports.iter().filter(|r| r.attempts > 0).collect();
        assert!(
            !active.is_empty(),
            "unsafe/tie must exercise actual early work: {reports:?}"
        );
        for report in active {
            assert!(report.eligible && report.attempts <= MAX_CALLS && report.visits <= MAX_VISITS);
            assert!(report.visits > 0 && report.terms > 0);
            assert!(report.last_node.is_some_and(|n| n < 1024));
        }
    }
}
