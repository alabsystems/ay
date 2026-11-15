// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #split-walk-sat-fallback: a satisfiable QF_NIA problem whose DPLL split
//! walk runs into the oscillation guard must still reach its `sat`.
//!
//! VeryMax `Ex2.04_false-termination.c__p21079` (z3 5.1.0 `sat`): since the
//! NIA soundness landing every NIA check forwards the inner LIA's `NeedSplit`
//! at once, the split loop walks one integer variable downwards and the
//! oscillation guard ended the search `unknown` within ~30 ms of a 30 s
//! budget (both postures). The split loop now offers the theory's SAT-only
//! lane first (`TheorySolver::try_sat_before_split_giveup`); the NIA's clausal
//! local search finds a witness the exact evaluator accepts on every
//! assertion, and the executor's model validation accepts it too. Reverting
//! the offer in `pipeline_incremental_split_lazy_macros.rs` turns both
//! assertions below back into `unknown`.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

const P21079: &str =
    include_str!("../../../../benchmarks/smt/QF_NIA/verymax_ex2_04_p21079_split_walk_sat.smt2");

fn solve(input: &str, shed_proof_cycle: bool) -> String {
    let commands = parse(input).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    exec.set_competition_mode(shed_proof_cycle);
    exec.set_timeout(Some(Duration::from_secs(30)));
    exec.set_memory_limit(Some(8 << 30));
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"));
    // The corpus file ends in `(exit)`, which has an output of its own: the
    // verdict is the `(check-sat)` answer.
    outputs
        .iter()
        .rev()
        .find(|out| matches!(out.as_str(), "sat" | "unsat" | "unknown"))
        .cloned()
        .unwrap_or_else(|| panic!("no check-sat answer in {outputs:?}"))
}

#[test]
#[timeout(120_000)]
fn verymax_p21079_split_walk_reaches_sat_default_posture() {
    assert_eq!(solve(P21079, false), "sat");
}

#[test]
#[timeout(120_000)]
fn verymax_p21079_split_walk_reaches_sat_z3_posture() {
    assert_eq!(solve(P21079, true), "sat");
}
