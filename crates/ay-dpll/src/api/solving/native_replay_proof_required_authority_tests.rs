// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::api::{Logic, Sort};

fn strict_boolean_unsat_details() -> crate::api::types::SolveDetails {
    let mut solver = Solver::try_new(Logic::QfUf).expect("solver");
    solver.set_produce_proofs(true);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .expect("strict proof option");
    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);
    solver.check_sat_with_details()
}

#[test]
fn proof_required_authority_rejects_holes_and_checker_failures() {
    let details = strict_boolean_unsat_details();
    assert!(details.verification.unsat_proof_strictly_verified);
    let _ = Solver::require_native_replay_proof_authority(details.clone())
        .expect("strict complete Boolean proof must carry authority");
    let assert_rejected = |details| {
        assert!(matches!(
            Solver::require_native_replay_proof_authority(details),
            Err(SolverError::InvalidArgument {
                operation: "native_replay_with_proofs",
                ..
            })
        ));
    };

    let total = details
        .statistics
        .get_int("proof_checker_total_steps")
        .expect("strict checker total");
    assert!(total > 0);

    let mut ordinary_authority = details.clone();
    ordinary_authority
        .verification
        .unsat_proof_strictly_verified = false;
    assert_rejected(ordinary_authority);

    // Model the partial checker's intentional Hole behavior: it can report
    // zero failures while skipping one step. The proof-required boundary
    // must reject that evidence even though the summary failure count is 0.
    let mut holey = details.clone();
    holey.statistics.proof_complete = false;
    holey.statistics.set_int("proof_checker_failures", 0);
    holey
        .statistics
        .set_int("proof_checker_skipped_hole_steps", 1);
    holey
        .statistics
        .set_int("proof_checker_checked_steps", total - 1);
    assert_rejected(holey);

    let mut checker_failed = details.clone();
    checker_failed
        .statistics
        .set_int("proof_checker_failures", 1);
    checker_failed.verification.unsat_proof_checker_failures = 1;
    assert_rejected(checker_failed);

    let mut missing_raw_stats = details.clone();
    for key in [
        "proof_checker_failures",
        "proof_checker_checked_steps",
        "proof_checker_total_steps",
        "proof_checker_skipped_hole_steps",
    ] {
        missing_raw_stats.statistics.extra.remove(key);
    }
    assert_rejected(missing_raw_stats);

    let mut trusted = details.clone();
    trusted.statistics.set_int("proof_trust", 1);
    assert_rejected(trusted);

    let mut incomplete = details.clone();
    incomplete.statistics.proof_complete = false;
    assert_rejected(incomplete);

    let mut empty = details.clone();
    empty.statistics.set_int("proof_checker_total_steps", 0);
    empty.statistics.set_int("proof_checker_checked_steps", 0);
    assert_rejected(empty);

    let mut unavailable = details;
    unavailable.verification.unsat_proof_available = false;
    assert_rejected(unavailable);
}
