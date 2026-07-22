// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use ay_chc::{
    testing, ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PdrConfig,
    PdrResult,
};
use ay_sat::TlaTraceable;
use ay_tla_bridge::find_tla2_binary;
use std::path::{Path, PathBuf};

pub(crate) fn specs_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("..")
        .join("specs")
}

pub(crate) fn pdr_spec_path() -> PathBuf {
    specs_dir().join("pdr_test.tla")
}

/// Returns true if the TLA2 binary is available, false otherwise.
/// When unavailable, prints a message so the caller can return early.
/// Build: `cd ~/tla2 && cargo build --release -p tla-cli`
pub(crate) fn require_tla2_binary() -> bool {
    if let Err(err) = find_tla2_binary() {
        eprintln!(
            "tla2 binary not available: {err}. \
             Build it: cd ~/tla2 && cargo build --release -p tla-cli. \
             Skipping tla2-dependent test."
        );
        return false;
    }
    true
}

/// Build a trivially unsafe CHC problem: Inv(x) with x=0, query Inv(x) /\ x=0 => false.
pub(crate) fn unsafe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // Fact: x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    // Query: Inv(x) /\ x = 0 => false (immediately unsafe)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));
    problem
}

/// Solve a CHC problem with PDR and write a trace to the given path.
pub(crate) fn solve_with_trace(problem: ChcProblem, trace_path: &Path) -> PdrResult {
    let mut solver = testing::new_pdr_solver(problem, PdrConfig::default());
    solver.enable_tla_trace(
        trace_path.to_str().unwrap(),
        "pdr_test",
        &[
            "frames",
            "obligations",
            "currentLevel",
            "result",
            "lemmaCount",
            "activePredicate",
            "activeLevel",
            "obligationDepth",
        ],
    );
    solver.solve()
}
