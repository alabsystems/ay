// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof-gate predicates (#proof-capability B2): the routing predicate, the
//! best-effort rebuild meter, and the dormant-lane predicate, exercised on
//! real executors in every proof posture.

/// `checked_certificate_demanded()` is FALSE for the synthesized best-effort
/// artifact and for a shedding solve (both route to the eager arms, exactly
/// alike), and TRUE for every explicit checked-certificate demand.
#[test]
fn routing_predicate_tracks_checked_certificate_demand_not_the_tracker() {
    use super::Executor;

    // Bare executor: no demand.
    let mut exec = Executor::new();
    assert!(!exec.checked_certificate_demanded());
    // The certified public path arms the tracker (mandatory certificate)
    // WITHOUT any user demand: routing must not be demoted by that.
    exec.begin_public_solve(false);
    assert!(exec.produce_proofs_enabled());
    assert!(!exec.checked_certificate_demanded());

    // Synthesized best-effort sidecar: `is_producing_proofs()` is true, but
    // no checked certificate is demanded — routing stays eager.
    let mut exec = Executor::new();
    exec.set_best_effort_produce_proofs(1_000);
    exec.begin_public_solve(false);
    assert!(exec.is_producing_proofs());
    assert!(!exec.checked_certificate_demanded());

    // Competition shedding: identical routing answer to the best-effort case.
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec.begin_public_solve(false);
    assert!(exec.competition_shedding_active());
    assert!(!exec.checked_certificate_demanded());

    // Explicit artifact demand (`--proof`, API set_produce_proofs).
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    assert!(exec.checked_certificate_demanded());

    // `--self-check` (mandatory collection without an artifact demand).
    let mut exec = Executor::new();
    exec.set_self_check(true);
    exec.set_mandatory_proof_collection();
    assert!(exec.checked_certificate_demanded());

    // In-script `(set-option :produce-proofs true)` is an explicit demand,
    // and so is `(set-option :check-proofs-strict true)`.
    for script in [
        "(set-option :produce-proofs true)",
        "(set-option :check-proofs-strict true)",
    ] {
        let commands = ay_frontend::parse(script).expect("valid SMT-LIB option script");
        let mut exec = Executor::new();
        exec.execute_all(&commands)
            .expect("set-option must execute");
        assert!(
            exec.checked_certificate_demanded(),
            "{script} must demand a checked certificate"
        );
    }

    // Shedding + explicit demand: the demand wins, exactly as for the tracker.
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec.set_produce_proofs(true);
    exec.begin_public_solve(false);
    assert!(!exec.competition_shedding_active());
    assert!(exec.checked_certificate_demanded());
}

/// The trust-leaf rebuild's theory-refutation meter is bounded ONLY for the
/// synthesized best-effort artifact; every explicit proof demand keeps it
/// unbounded, so certification behaviour there is byte-identical.
#[test]
fn best_effort_rebuild_refutation_meter_is_bounded_only_for_the_best_effort_artifact() {
    use super::Executor;

    // No proof policy at all (library default / mandatory certificate):
    // budget None, so the meter admits everything.
    let mut exec = Executor::new();
    assert_eq!(exec.best_effort_rebuild_refutation_budget(), None);
    assert!(exec.charge_best_effort_rebuild_refutation(u64::MAX));

    // Best-effort artifact: budget = step budget / 64, then the meter refuses
    // the first refutation that would overrun it and stays refused.
    let mut exec = Executor::new();
    exec.set_best_effort_produce_proofs(6_400);
    assert_eq!(exec.best_effort_rebuild_refutation_budget(), Some(100));
    assert!(exec.charge_best_effort_rebuild_refutation(60));
    assert!(!exec.charge_best_effort_rebuild_refutation(41));
    assert!(exec.charge_best_effort_rebuild_refutation(40));
    assert!(!exec.charge_best_effort_rebuild_refutation(1));
    // A refused charge must not have been debited.
    assert_eq!(exec.best_effort_rebuild_refutation_spent, 100);

    // Explicit API/CLI artifact demand: unbounded, whatever budget was set.
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    exec.set_proof_reconstruction_step_budget(Some(6_400));
    assert_eq!(exec.best_effort_rebuild_refutation_budget(), None);
    assert!(exec.charge_best_effort_rebuild_refutation(u64::MAX));

    // In-script `(set-option :produce-proofs true)` is an explicit demand even
    // on an executor that was configured best-effort by the CLI.
    let commands =
        ay_frontend::parse("(set-option :produce-proofs true)").expect("valid option script");
    let mut exec = Executor::new();
    exec.set_best_effort_produce_proofs(6_400);
    exec.execute_all(&commands)
        .expect("set-option must execute");
    assert_eq!(exec.best_effort_rebuild_refutation_budget(), None);

    // Self-check's mandatory collection clears the budget: unbounded.
    let mut exec = Executor::new();
    exec.set_best_effort_produce_proofs(6_400);
    exec.set_self_check(true);
    exec.set_mandatory_proof_collection();
    assert_eq!(exec.best_effort_rebuild_refutation_budget(), None);
}

/// `unvetted_no_proof_lane_allowed()` equals the old `!produce_proofs_enabled()`
/// whenever competition shedding is inactive, and is additionally FALSE
/// under active shedding.
#[test]
fn unvetted_lane_predicate_is_dead_under_shedding_and_proofs() {
    use super::Executor;

    // Non-competition, tracker off (the internal/nested-solve config where
    // the lanes run today): allowed — byte-identical to the old gates.
    let mut exec = Executor::new();
    assert!(!exec.produce_proofs_enabled());
    assert!(exec.unvetted_no_proof_lane_allowed());

    // Certified public path: begin_public_solve arms the tracker — dead,
    // exactly like the old `!produce_proofs_enabled()` gates.
    exec.begin_public_solve(false);
    assert!(exec.produce_proofs_enabled());
    assert!(!exec.unvetted_no_proof_lane_allowed());

    // Competition shedding: tracker disarmed, produce_proofs_enabled()
    // false — the OLD gates would have gone live; the named predicate keeps
    // the lanes dead.
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec.begin_public_solve(false);
    assert!(!exec.produce_proofs_enabled());
    assert!(exec.competition_shedding_active());
    assert!(!exec.unvetted_no_proof_lane_allowed());

    // Competition mode + explicit proof demand (precedence): certified
    // lanes restored, tracker armed — dead via produce_proofs_enabled().
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec.set_produce_proofs(true);
    exec.begin_public_solve(false);
    assert!(!exec.competition_shedding_active());
    assert!(exec.produce_proofs_enabled());
    assert!(!exec.unvetted_no_proof_lane_allowed());

    // Explicit proof demand without competition mode: dead, as always.
    let mut exec = Executor::new();
    exec.set_produce_proofs(true);
    assert!(!exec.unvetted_no_proof_lane_allowed());
}
