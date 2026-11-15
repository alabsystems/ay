// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PROBE, NOT PRE-EMPT: a declined lane must leave the legacy path every
//! verdict it had without the lane.
//!
//! Review repro (differential fuzz, `--z3-mode`): the lane's refutation of the
//! fixture below is not certifiable by the consequence replay, so the lane
//! declines on the shedding first pass AND on its memo retry. Each declined
//! replay call consumed one of the per-query `MAX_REPLAY_ATTEMPTS = 2`
//! attempts, so the legacy replay then refused with "replay attempt budget
//! exhausted" and a problem base publishes `unsat` came back `unknown`. The
//! lane now hands the attempt ledger back on every decline.

use super::{run_with, LaneRun};

/// The fixture is a DEPTH-1 refutation the consequence replay cannot certify;
/// with the nested search on (the default) M3a's expansion certificate
/// publishes it instead, so the declined-replay tests run with it off.
fn run_depth1_only(smt: &str, z3_mode: bool) -> LaneRun {
    let _nested_off = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_qlra_nested: true,
        ..ay_core::misc_cli_flags().clone()
    });
    run_with(smt, z3_mode)
}

/// `(3c + b <= b - 2c - 1)` is the ground `c <= -1/5` under vacuous binders;
/// `c + 2a < a/2 + 2·x10` for ALL `x10` is refuted by any small `x10`.
const LOST2: &str = "(set-logic LRA)\
     (declare-fun a () Real)(declare-fun b () Real)(declare-fun c () Real)\
     (assert (forall ((x00 Real) (x01 Bool)) (<= (+ (* 3 c) b) (+ b (* (- 2) c) (- 1)))))\
     (assert (forall ((x10 Real)) (< (+ c (* 2 a)) (+ (/ a 2) (* 2 x10)))))\
     (check-sat)";

fn assert_legacy_keeps_unsat(z3_mode: bool) {
    let run = run_depth1_only(LOST2, z3_mode);
    assert!(
        run.recognized,
        "the lane must see the fixture (z3_mode={z3_mode})"
    );
    assert_eq!(
        run.verdict, "unsat",
        "z3_mode={z3_mode}: a declined lane must not cost the legacy \
         path its refutation (cert={:?}, decline={:?})",
        run.cert, run.decline
    );
}

#[test]
fn declined_lane_leaves_the_legacy_replay_its_attempts_under_z3_mode() {
    let run = run_depth1_only(LOST2, true);
    assert_eq!(
        run.cert.as_deref(),
        Some("declined"),
        "the fixture must exercise the lane's DECLINED replay, or this test is vacuous"
    );
    assert!(
        run.retried,
        "the memo retry is the second declined replay that exhausted the ledger"
    );
    assert_legacy_keeps_unsat(true);
}

#[test]
fn declined_lane_leaves_the_legacy_replay_its_attempts_in_the_library_default_posture() {
    assert_legacy_keeps_unsat(false);
}

/// Risk R11: a declined pass rolls its scratch terms back, so the legacy path
/// runs on exactly the store it would have seen without the lane. Measured
/// before the rollback: leftover lane terms fed the legacy path's whole-store
/// scans and turned a 1.5 s `unsat` into a 20 s timeout (fuzz f7_118).
#[test]
fn declined_pass_rolls_its_scratch_terms_back() {
    let _nested_off = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_qlra_nested: true,
        ..ay_core::misc_cli_flags().clone()
    });
    let with_lane = run_with(LOST2, true);
    assert_eq!(
        with_lane.cert.as_deref(),
        Some("declined"),
        "the fixture must exercise a declined replay, or this test is vacuous"
    );
    assert_eq!(
        with_lane.rollback.as_deref(),
        Some("rolled-back"),
        "a declined UNSAT pass with no installed proof must roll back"
    );
    let without_lane = {
        let flags = ay_core::MiscCliFlags {
            no_qlra_cegqi: true,
            ..ay_core::misc_cli_flags().clone()
        };
        let _guard = ay_core::misc_test_override::set(flags);
        run_with(LOST2, true)
    };
    assert!(!without_lane.recognized, "the kill switch removes the lane");
    assert_eq!(with_lane.verdict, without_lane.verdict);
    assert_eq!(
        with_lane.terms_len, without_lane.terms_len,
        "after every declined pass rolled back, the legacy path must end on \
         the same term store as a run without the lane"
    );
}

/// The rollback must not cost the lane its own retry: under `--z3-mode` the
/// shedding first pass cannot certify p7's refutation and rolls back, and the
/// trace-armed retry re-runs the search and publishes it.
#[test]
fn rolled_back_verdict_is_republished_on_the_retry() {
    let run = run_with(
        "(set-logic LRA)(declare-const c Real)\
         (assert (forall ((x Real)) (and (> c 0) (< c 0) (> x 0))))(check-sat)",
        true,
    );
    assert_eq!(run.verdict, "unsat", "p7 (decline={:?})", run.decline);
    assert!(run.retried, "p7 publishes on the retry under --z3-mode");
    assert_eq!(
        run.cert.as_deref(),
        Some("installed"),
        "the lane itself must publish on the retry"
    );
}

/// The default posture (nested search on): the depth-1 refutation the replay
/// declines publishes `unsat` through the M3a expansion certificate.
#[test]
fn default_posture_certifies_the_fixture_through_the_expansion_certificate() {
    let run = run_with(LOST2, true);
    assert_eq!(run.verdict, "unsat");
    assert_eq!(run.cert.as_deref(), Some("expansion-installed"));
}
