// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::executor_adapter::ReplayLimit;
use std::{cell::Cell, time::Duration};

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn exported(progress: &mut RetainedReplayProgress<'_>) -> super::super::RetainedProofBundle {
    let mut solver = Solver::try_new(ay_dpll::api::Logic::All).unwrap();
    solver.set_produce_proofs(true);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .unwrap();
    let binding = solver
        .parse_smtlib2_with_exact_query_binding(
            "(declare-const p Bool) (assert p) (assert (not p))",
        )
        .unwrap();
    assert!(solver.check_sat().is_unsat());
    solver
        .export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
            &binding,
            progress.deadline(),
            &mut |work, bytes| progress.charge(work, bytes),
        )
        .unwrap()
        .unwrap()
}

#[test]
fn mandatory_third_replay_independently_verifies_nonempty_live_export_inventory() {
    let mut callback = || true;
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    let artifact = exported(&mut progress);
    assert_eq!(artifact.schema(), "ay.proofbundle/v6");
    assert_eq!(artifact.obligation_assertions().len(), 2);
    let verdict = verified_third_replay(&artifact, &mut progress).unwrap();
    assert!(
        matches!(verdict, ay_dpll::api::StrictProofVerdict::Verified(quality)
        if quality.is_complete())
    );
    drop(artifact);
    progress.check().unwrap();
}

#[test]
fn prior_live_export_success_cannot_bypass_a_refused_third_replay() {
    let allow = Cell::new(true);
    let mut callback = || allow.get();
    let mut progress =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    let artifact = exported(&mut progress);
    allow.set(false);
    assert!(verified_third_replay(&artifact, &mut progress).is_err());
    allow.set(true);
    assert!(progress.check().is_err());
}
