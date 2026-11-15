// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #nia-split-probe: a satisfiable QF_NIA problem whose witness the factor
//! split only reaches through a long walk of full-set conflicts must still be
//! decided once the split conflicts are precise.
//!
//! AProVE `aproveSMT3478322092999958257` (`:status sat`, z3 5.1.0 `sat`, main
//! `sat` in ~3 s): main runs 404 split rounds whose every conflict is the
//! 282-literal full set, and the 406th factor split finds the witness "every
//! variable 1" in branch [1, 1]. With the factor split's congruence scope the
//! split conflicts are smaller, the SAT search goes elsewhere (2,418 rounds,
//! most of them short LRA conflicts) and the search ended `unknown` at 30 s.
//! When the solve's first factor split is about to enumerate, the NIA now runs
//! one short clausal local search over the original assertions (the split
//! refutes the current assignment and nothing after it offers the search); it
//! finds the witness. Removing the probe's call in `factor_split.rs` (or the
//! executor's per-solve flag) turns the assertion below back into `unknown`.
//!
//! The executor is configured as the CLI's DEFAULT posture configures it for a
//! file input (best-effort proof production), as in `nia_stale_accept_sat`.

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

const APROVE_3478: &str = include_str!(
    "../../../../benchmarks/smt/QF_NIA/aprove_3478322092999958257_split_probe_sat.smt2"
);

/// The CLI's synthesized-default proof reconstruction budget (`crates/ay/src/run.rs`).
const CLI_DEFAULT_PROOF_STEP_BUDGET: u64 = 1_000_000;

fn solve_like_cli_default(input: &str) -> String {
    let commands = parse(input).unwrap_or_else(|err| panic!("parse failed: {err}"));
    let mut exec = Executor::new();
    exec.set_best_effort_produce_proofs(CLI_DEFAULT_PROOF_STEP_BUDGET);
    exec.set_timeout(Some(Duration::from_secs(30)));
    exec.set_memory_limit(Some(8 << 30));
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}"));
    outputs
        .iter()
        .rev()
        .find(|out| matches!(out.as_str(), "sat" | "unsat" | "unknown"))
        .cloned()
        .unwrap_or_else(|| panic!("no check-sat answer in {outputs:?}"))
}

#[test]
#[timeout(120_000)]
fn aprove_3478_split_probe_reaches_sat_default_posture() {
    assert_eq!(solve_like_cli_default(APROVE_3478), "sat");
}
