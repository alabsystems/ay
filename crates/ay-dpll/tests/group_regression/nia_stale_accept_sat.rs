// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #stale-accept-sat-lane: a satisfiable QF_NIA problem whose last split
//! round is a STALE model-equality request must still reach its `sat`.
//!
//! AProVE `aproveSMT2467769011678516224` (`:status sat`, z3 5.1.0 `sat`):
//! the NIA forwards the inner LIA's model equalities because its point
//! violates an asserted disequality (#nia-diseq-model-eq); once every one of
//! them is encoded with its triangle axioms the split loop's #1771 fallback
//! accepts the round as `Sat`, and the model gate rejected the point —
//! `unknown` in ~2 s. The split loop now offers the theory's SAT-only lane
//! there first (`TheorySolver::try_sat_before_stale_accept`); the NIA runs
//! its clausal local search because the point it would report provably
//! falsifies a root assertion, and the witness passes exact evaluation and
//! the executor's model validation. Removing the offer from
//! `pipeline_incremental_split_lazy_shared_macros.rs` turns the assertion
//! below back into `unknown`.
//!
//! The executor is configured as the CLI's DEFAULT posture configures it for a
//! file input: best-effort proof production (`ProofConfig::new_default` →
//! `set_best_effort_produce_proofs`, budget 1,000,000 steps). That is the
//! search that ends on the stale round; without proof production (`--no-proof`,
//! a bare `Executor::new()`) the search takes another path to `sat` with or
//! without the lane (measured: the pin without this setting survived the
//! removal of every offer).

use std::time::Duration;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

const APROVE_2467: &str = include_str!(
    "../../../../benchmarks/smt/QF_NIA/aprove_2467769011678516224_stale_accept_sat.smt2"
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
fn aprove_2467_stale_model_equality_round_reaches_sat_default_posture() {
    assert_eq!(solve_like_cli_default(APROVE_2467), "sat");
}
