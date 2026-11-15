// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The deductive-checks set-fold obligation (`sets_rs::test_set_fold_singleton`,
//! captured as `C_sets/87167-00066` in the 2026-09-16 solver-fix round)
//! replayed through the Rust API in the posture deductive-checks's encoder installs:
//! `Readable` counterexamples, unsat cores ON, proofs OFF, a 30 s command
//! deadline and the 400 000 conflict budget. z3 answers `unsat` on every
//! `unsat` fixture here and `sat` on the control.
//!
//! Measured history in this posture: `unknown (quantifier-unhandled)` at
//! 36-40 s after the alpha-quantifier-sharing merge; `unsat` in ~48 s (so a
//! 30 s `Timeout` inside deductive-checks) once E-matching stopped binding pattern
//! variables through binder-mentioning model classes; `unsat` in ~17 s once
//! the LIA affine-implication accelerator stopped re-eliminating the same
//! equation rows for every disequality on every theory check
//! (#affine-rref-hoist — it was ~95% of the BV/LIA bridge lane's time).

use std::time::{Duration, Instant};

use ay_dpll::api::{Logic, SolveResult, Solver};
use ay_dpll::CounterexampleStyle;

/// deductive-checks's wall backstop (`encoder/mod.rs` `with_limits`).
const DEDUCTIVE_CHECKS_DEADLINE: Duration = Duration::from_secs(30);

fn solve_in_deductive_checks_posture(
    input: &str,
    deadline: Duration,
) -> (Result<SolveResult, String>, Duration) {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver.set_counterexample_style(CounterexampleStyle::Readable);
    solver.set_produce_unsat_cores(true);
    solver.set_timeout(Some(deadline));
    solver
        .try_set_option("rlimit", "400000")
        .expect("deductive-checks installs a conflict budget");
    solver.parse_smtlib2(input).expect("fixture parses");
    let started = Instant::now();
    let details = solver.check_sat_with_details();
    let elapsed = started.elapsed();
    (
        details
            .accept_for_consumer()
            .cloned()
            .map_err(|error| format!("{error:?} / {:?}", details.unknown_reason)),
        elapsed,
    )
}

fn is_unsat(result: &Result<SolveResult, String>) -> bool {
    matches!(result, Ok(SolveResult::Unsat(_)))
}

/// The reduced two-universal frame (the fixture behind
/// `executor_tests::smt::set_fold_pinned_read_proof_fold`): `unsat` in the
/// embedder posture too.
#[test]
fn quantified_frame_is_unsat_in_deductive_checks_posture() {
    let (result, elapsed) = solve_in_deductive_checks_posture(
        include_str!("fixtures/deductive_checks_set_fold_quantified_frame.smt2"),
        DEDUCTIVE_CHECKS_DEADLINE,
    );
    assert!(
        is_unsat(&result),
        "z3: unsat; got {result:?} after {elapsed:?}"
    );
}

/// Sat control (z3: `sat`): the goal cell is unconstrained. Failing closed to
/// `unknown` is acceptable; `unsat` never is.
#[test]
fn quantified_frame_sat_control_is_never_unsat_in_deductive_checks_posture() {
    let (result, elapsed) = solve_in_deductive_checks_posture(
        include_str!("fixtures/deductive_checks_set_fold_quantified_frame_sat.smt2"),
        DEDUCTIVE_CHECKS_DEADLINE,
    );
    assert!(
        !is_unsat(&result),
        "sat control refuted: {result:?} after {elapsed:?}"
    );
}

/// The complete captured obligation (four universals, 60+ assertions) must
/// be decided `unsat` INSIDE deductive-checks's 30 s deadline (was a `Timeout`: the
/// solve needed ~48 s before #affine-rref-hoist, ~17 s after, release).
#[test]
fn captured_obligation_is_unsat_within_the_deductive_checks_deadline() {
    // The 30 s pin is a release-build property; an unoptimized-assertion
    // build keeps the verdict pin with a wider deadline so load cannot flake
    // it.
    let deadline = if cfg!(debug_assertions) {
        Duration::from_secs(180)
    } else {
        DEDUCTIVE_CHECKS_DEADLINE
    };
    let (result, elapsed) = solve_in_deductive_checks_posture(
        include_str!("fixtures/deductive_checks_set_fold_singleton_obligation.smt2"),
        deadline,
    );
    assert!(
        is_unsat(&result),
        "z3: unsat; got {result:?} after {elapsed:?}"
    );
}
