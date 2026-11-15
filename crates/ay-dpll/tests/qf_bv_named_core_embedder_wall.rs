// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Bit-blasted QF_BV / QF_UFBV named-core obligations must certify `unsat`
//! inside an embedder's 30 s wall without paying for re-solves the verdict
//! does not need (#uc-minimize-entry-cost, `Executor::new_derived_query_executor`).
//!
//! Embedder posture (deductive-checks, `encoder/mod.rs` `with_logic` + `with_limits`):
//! unsat cores ON, proofs OFF, a 30 s command deadline. Each fixture is a
//! query deductive-checks's regression harnesses raised and z3 answers `unsat` on
//! (`B_return_position_overflow`, `B_bitvector`, `B_nonlinear`,
//! `B_z3_restart`, `B_exec_spec_verified`). Before the two fixes the
//! verdict was decided in 0.3-1 s and then re-solved up to seven more times:
//! by the deletion minimizer's subset attempts (an adoption paying a fresh
//! solve plus its strict re-verification, a churner paying its whole cap),
//! and by the certification funnel's nested corroboration, whose cloned
//! context re-ran the named-core redirect, harvest recheck and minimizer of
//! its own. Measured at release under load: `return_position_overflow`
//! 8.8 s, `udiv_self` 23.2 s, `exec_spec` 29.1 s, `z3_restart`
//! `Unknown(Timeout)` at the wall.
//!
//! The wall assertion is made only in optimized builds; a debug build of the
//! bit-blaster is not what the embedder runs — measured at release the
//! `exec_spec` and `z3_restart` fixtures decide in ~22-26 s under load, and
//! the debug profile runs them past 30 s, so the debug build gives the solver
//! a wider command deadline and asserts only the certified verdict.

use std::time::{Duration, Instant};

use ay_dpll::api::{Logic, SolveResult, Solver};
use ntest::timeout;

const EMBEDDER_WALL: Duration = Duration::from_secs(30);
/// The command deadline handed to the solver: the embedder's wall at
/// release, a wide one for the debug profile (module docs).
const SOLVER_WALL: Duration = if cfg!(debug_assertions) {
    Duration::from_mins(5)
} else {
    EMBEDDER_WALL
};

fn embedder_solver(wall: Duration) -> Solver {
    let mut solver = Solver::try_new(Logic::All).expect("solver constructs");
    solver.set_produce_unsat_cores(true);
    solver.set_timeout(Some(wall));
    solver
}

fn assert_certified_unsat_at_the_embedder_wall(name: &str, input: &str) {
    let mut solver = embedder_solver(SOLVER_WALL);
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
    // The funnel certifies these bit-blasted refutations one of two ways: a
    // strict-checked proof, or — when the proof carries a `Generic`
    // bit-blast lemma the per-clause lane declines — the fresh-executor
    // corroboration plus complete trust-step discharge that
    // `unsat_corroborated` records (evidence E1; before 2026-10-02 it was
    // filed under `unsat_independently_verified`). Either is an admitted
    // verdict; the consumer acceptance above already refused anything
    // else.
    assert!(
        details.verification.unsat_proof_strictly_verified
            || details.verification.unsat_independently_verified
            || details.verification.unsat_corroborated,
        "{name}: the published unsat must carry a certification: {:?}",
        details.verification
    );
    if !cfg!(debug_assertions) {
        assert!(
            elapsed < EMBEDDER_WALL,
            "{name}: verdict must arrive inside the command deadline, took {elapsed:?}"
        );
    }
    let core = solver
        .try_get_unsat_core()
        .unwrap_or_else(|error| panic!("{name}: core must be readable after unsat: {error:?}"));
    assert!(!core.is_empty(), "{name}: the named core must not be empty");
}

/// 64-bit `a * b` with both operands below 1000: the 128-bit product's high
/// half is zero (`audit2_probes::return_position_overflow_checked`).
#[test]
#[timeout(600_000)]
fn return_position_overflow_certifies_unsat_inside_the_embedder_wall() {
    assert_certified_unsat_at_the_embedder_wall(
        "return_position_overflow",
        include_str!("fixtures/deductive_checks_qfbv_return_position_overflow_named_core.smt2"),
    );
}

/// `y != 0` refutes `y udiv y != 1` (`bitvector_rs` harness; the restoring
/// divider makes every re-solve expensive).
#[test]
#[timeout(600_000)]
fn udiv_self_certifies_unsat_inside_the_embedder_wall() {
    assert_certified_unsat_at_the_embedder_wall(
        "udiv_self",
        include_str!("fixtures/deductive_checks_qfbv_udiv_self_named_core.smt2"),
    );
}

/// Three 16-bit-bounded operands, two signed-bound products, one 64-bit
/// overflow check (`nonlinear_rs` harness).
#[test]
#[timeout(600_000)]
fn nonlinear_certifies_unsat_inside_the_embedder_wall() {
    assert_certified_unsat_at_the_embedder_wall(
        "nonlinear",
        include_str!("fixtures/deductive_checks_qfbv_nonlinear_named_core.smt2"),
    );
}

/// Multiplier distributivity and commutativity as named premises beside the
/// overflow check (`z3_restart_rs` harness): the premises are true but
/// expensive to re-prove, which is exactly what made every subset attempt
/// a churner.
#[test]
#[timeout(600_000)]
fn z3_restart_certifies_unsat_inside_the_embedder_wall() {
    assert_certified_unsat_at_the_embedder_wall(
        "z3_restart",
        include_str!("fixtures/deductive_checks_qfufbv_z3_restart_named_core.smt2"),
    );
}

/// The same harness's bit-vector by-assert with the earlier nonlinear facts as
/// overflow-guarded premises. The refutation needs only the bound and the `&`
/// atom, but the independent Bool/BV lane lowers every premise, 64-bit
/// multipliers included; when its replay stops at the lane's fixed deadline
/// the lane must decline, so the discharge lane still certifies the verdict.
#[test]
#[timeout(600_000)]
fn z3_restart_guarded_premises_certify_unsat_inside_the_embedder_wall() {
    assert_certified_unsat_at_the_embedder_wall(
        "z3_restart_guarded_premises",
        include_str!(
            "fixtures/deductive_checks_qfufbv_z3_restart_guarded_premises_named_core.smt2"
        ),
    );
}

/// `x <= 0xffff` refutes a 64-bit overflow of `x * x` beside uninterpreted
/// datatype carriers (`exec_spec_verified_rs` harness).
#[test]
#[timeout(600_000)]
fn exec_spec_certifies_unsat_inside_the_embedder_wall() {
    assert_certified_unsat_at_the_embedder_wall(
        "exec_spec",
        include_str!("fixtures/deductive_checks_qfufbv_exec_spec_named_core.smt2"),
    );
}
