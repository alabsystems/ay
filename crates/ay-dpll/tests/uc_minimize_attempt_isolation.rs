// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! The unsat-core minimizer's subset solves must not publish their own
//! budget expiry as the outer decision's timeout (#uc-core-minimize,
//! `Executor::minimize_assumption_core`).
//!
//! Embedder posture (deductive-checks, `encoder/mod.rs` `with_limits`): unsat cores
//! ON, proofs OFF, a 30 s command deadline. The named-core redirect proves
//! the `:named` assertions unsat in ~1 s, certification accepts, and the
//! deletion minimizer then re-solves subsets under a narrowed per-attempt
//! `solve_deadline`. A subset attempt's expiry used to land on the entry
//! decision's evaluation attempt (subset solves never begin a decision of
//! their own), every later attempt was dead on arrival, and
//! `emit_sat_verdict` published `Unknown(Timeout)` over the certified UNSAT
//! — measured at 8-10 s under the 30 s wall, i.e. an internal stop, on
//! every `*_push_*` loop obligation deductive-checks encodes. z3 answers `unsat` on
//! both fixtures.

use std::time::{Duration, Instant};

use ay_dpll::api::{Logic, SolveResult, Solver};
use ay_dpll::UnknownReason;
use ntest::timeout;

const EMBEDDER_WALL: Duration = Duration::from_secs(30);

fn embedder_solver(wall: Duration) -> Solver {
    let mut solver = Solver::try_new(Logic::All).expect("solver constructs");
    solver.set_produce_unsat_cores(true);
    solver.set_timeout(Some(wall));
    solver
}

fn assert_certified_unsat_at_the_embedder_wall(name: &str, input: &str) {
    let mut solver = embedder_solver(EMBEDDER_WALL);
    solver.parse_smtlib2(input).expect("fixture parses");
    let started = Instant::now();
    let details = solver.check_sat_with_details();
    let elapsed = started.elapsed();
    let verdict = details
        .result
        .accept_for_consumer()
        .unwrap_or_else(|error| panic!("{name}: consumer acceptance failed: {error:?}"))
        .clone();
    assert!(
        matches!(verdict, SolveResult::Unsat(_)),
        "{name}: expected the certified unsat, got {verdict:?} (reason {:?}) after {elapsed:?}",
        details.unknown_reason
    );
    assert_eq!(details.unknown_reason, None, "{name}");
    // The published UNSAT is the one the entry decision certified BEFORE the
    // minimizer ran — the strict checker's claim, not a subset solve's.
    assert!(
        details.verification.unsat_proof_strictly_verified,
        "{name}: the published unsat must carry the strict certification: {:?}",
        details.verification
    );
    assert!(
        elapsed < EMBEDDER_WALL,
        "{name}: verdict must arrive inside the command deadline, took {elapsed:?}"
    );
    let core = solver
        .try_get_unsat_core()
        .unwrap_or_else(|error| panic!("{name}: core must be readable after unsat: {error:?}"));
    assert!(!core.is_empty(), "{name}: the named core must not be empty");
}

#[test]
#[timeout(120_000)]
fn replay_push_db_grows_stays_unsat_through_the_core_minimizer() {
    assert_certified_unsat_at_the_embedder_wall(
        "replay_push_db_grows",
        include_str!("fixtures/deductive_checks_replay_push_db_grows_named_core.smt2"),
    );
}

#[test]
#[timeout(120_000)]
fn floor_push_appends_stays_unsat_through_the_core_minimizer() {
    assert_certified_unsat_at_the_embedder_wall(
        "floor_push_appends",
        include_str!("fixtures/deductive_checks_floor_push_appends_named_core.smt2"),
    );
}

/// Control: a GENUINE command-deadline expiry is still published as a
/// timeout. Parking discards subset-attempt stops only; the entry decision's
/// own envelope is untouched.
#[test]
#[timeout(60_000)]
fn a_genuine_command_deadline_expiry_still_publishes_timeout() {
    let mut solver = embedder_solver(Duration::ZERO);
    solver
        .parse_smtlib2(include_str!(
            "fixtures/deductive_checks_replay_push_db_grows_named_core.smt2"
        ))
        .expect("fixture parses");
    let details = solver.check_sat_with_details();
    let verdict = details
        .result
        .accept_for_consumer()
        .expect("an Unknown is always consumer-acceptable")
        .clone();
    assert!(
        matches!(verdict, SolveResult::Unknown),
        "an already-expired deadline must fail closed, got {verdict:?}"
    );
    assert_eq!(details.unknown_reason, Some(UnknownReason::Timeout));
}
