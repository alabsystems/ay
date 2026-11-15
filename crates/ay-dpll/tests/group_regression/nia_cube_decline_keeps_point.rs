// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #cube-decline-no-trace: a satisfiable QF_NIA product-overflow query must
//! reach `sat`, not walk into the split loop's oscillation guard.
//!
//! `0 <= a < 1000, 0 <= b <= 2^64 - 1, a * b > 2^64 - 1` (the integer
//! component of a deductive verifier multiplication-overflow obligation; the
//! pinned z3 5.3.3 answers `sat`). From 4e96ceb505, whose cube test began to
//! re-solve under its tightened bounds, a DECLINED cube step left the LP at
//! the point it had chosen and rejected (`pop` restores bounds, not values).
//! The NIA refinement read that point after a rejected tentative patch, cut
//! at it, and forwarded the inner LIA's split every round; the DPLL took the
//! floor branch each time, walking `a` down from 999 one unit per round until
//! the oscillation guard ended the search `unknown (incomplete)` in ~12 s.
//! A declined cube test now restores the assignment it was called on
//! (`LraSolver::try_cube_test`); deleting those restores turns all four
//! assertions below back into `unknown`.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

const OBLIGATION: &str =
    include_str!("../../../../benchmarks/smt/QF_NIA/u64_product_overflow_cube_decline_sat.smt2");
const MINIMAL: &str = include_str!(
    "../../../../benchmarks/smt/QF_NIA/u64_product_overflow_min_cube_decline_sat.smt2"
);

fn solve(input: &str, shed_proof_cycle: bool) -> String {
    let commands = parse(input).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    exec.set_competition_mode(shed_proof_cycle);
    exec.set_timeout(Some(Duration::from_secs(30)));
    exec.set_memory_limit(Some(8 << 30));
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"));
    // The corpus files end in `(exit)`: the verdict is the `(check-sat)`
    // answer.
    outputs
        .iter()
        .rev()
        .find(|out| matches!(out.as_str(), "sat" | "unsat" | "unknown"))
        .cloned()
        .unwrap_or_else(|| panic!("no check-sat answer in {outputs:?}"))
}

#[test]
#[timeout(120_000)]
fn u64_product_overflow_reaches_sat_default_posture() {
    assert_eq!(solve(OBLIGATION, false), "sat");
}

#[test]
#[timeout(120_000)]
fn u64_product_overflow_reaches_sat_z3_posture() {
    assert_eq!(solve(OBLIGATION, true), "sat");
}

#[test]
#[timeout(120_000)]
fn minimal_u64_product_overflow_reaches_sat_default_posture() {
    assert_eq!(solve(MINIMAL, false), "sat");
}

#[test]
#[timeout(120_000)]
fn minimal_u64_product_overflow_reaches_sat_z3_posture() {
    assert_eq!(solve(MINIMAL, true), "sat");
}
