// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn blocked_public_solves_keep_deadlines_clear_evidence_and_allow_fresh_requests() {
    if !ay_test_support::isolated_test::run_alone(
        module_path!(),
        "blocked_public_solves_keep_deadlines_clear_evidence_and_allow_fresh_requests",
    )
    .expect("fresh process")
    {
        return;
    }
    let mut model = Model::new();
    let x = model.add_col(0.0, 0.0);
    let opts = SolveOpts::new().with_time_limit(Duration::from_millis(20));
    let mut mip = BabSession::new(model.clone(), &opts).expect("MIP session");
    let mut lp = LpSession::new(&model, &opts).expect("LP session");
    mip.replay_claims.push(replay_claim("previous request"));
    mip.last_deferred = Some(("previous", "request"));

    let (ready, ready_rx) = std::sync::mpsc::sync_channel(0);
    let (release, release_rx) = std::sync::mpsc::channel::<()>();
    let blocker = thread::spawn(move || {
        let caller = ay_sys::compute_budget::ComputeScope::enter().expect("actual base");
        let mut extras = Vec::new();
        while let Some(extra) = caller.try_extra().expect("actual spare") {
            extras.push(extra);
        }
        ready.send(()).expect("ready");
        let _ = release_rx.recv();
        drop(extras);
        drop(caller);
    });
    ready_rx.recv().expect("all actual capacity held");
    assert!(matches!(
        mip.check().expect("bounded MIP wait"),
        Outcome::Unknown {
            reason: UnknownReason::Timeout,
        }
    ));
    assert!(mip.replay_claims.is_empty());
    assert!(mip.last_deferred.is_none());
    assert!(mip.deferred_claim.is_none());
    assert_eq!(mip.opts.time_limit, opts.time_limit);
    assert_eq!(mip.opts.deadline, opts.deadline);
    assert!(matches!(
        lp.optimize_model_objective().expect("bounded LP wait"),
        Outcome::Unknown {
            reason: UnknownReason::Timeout,
        }
    ));
    assert!(lp
        .float_dual_for_expr(&[(x, 1.0)], Sense::Minimize)
        .expect("bounded dual wait")
        .is_none());
    for outcome in [
        lp.rigorous_bound(x, Sense::Minimize)
            .expect("bounded column wait"),
        lp.rigorous_bound_expr(&[(x, 1.0)], Sense::Minimize)
            .expect("bounded expression wait"),
    ] {
        assert!(matches!(
            outcome,
            Outcome::Unknown {
                reason: UnknownReason::Timeout
            }
        ));
    }
    assert!(
        lp.lp.is_none(),
        "no exact LP was constructed while capacity was held"
    );
    assert!(lp.implied_box.is_none());

    drop(release);
    blocker.join().expect("original units released");
    mip.opts = SolveOpts::new().with_time_limit(Duration::from_secs(10));
    lp.opts = mip.opts.clone();
    match mip.check().expect("fresh MIP") {
        Outcome::Optimal { model_values, .. } | Outcome::Feasible { model_values, .. } => {
            model
                .check_point(&model_values)
                .expect("fresh exact witness");
        }
        other => panic!("fresh feasibility request did not decide: {other:?}"),
    }
    assert!(matches!(
        lp.optimize_model_objective().expect("fresh LP"),
        Outcome::Optimal { .. }
    ));
}
