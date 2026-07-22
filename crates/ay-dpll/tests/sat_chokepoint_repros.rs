// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! SAT-emission-chokepoint soundness fences (#sat-chokepoint).
//!
//! These pin that a wrong array model driven through the two verdict paths that
//! historically SKIPPED the independent model-check gate —
//! `check-sat-assuming` and `optimize` (`(maximize ...)`) — is caught by the
//! single `emit_sat_verdict` funnel and is NEVER reported `sat`. Both repros are
//! declared/z3 UNSAT, so the only sound AY outcomes are `unsat` or `unknown`.

mod common;

use common::SolverOutcome;
use ntest::timeout;

fn assert_never_sat(rel_path: &str) {
    let path = common::workspace_path(rel_path);
    assert!(
        path.is_file(),
        "missing chokepoint repro: {}",
        path.display()
    );
    let outcome = common::run_executor_file_with_timeout(&path, 30)
        .unwrap_or_else(|err| panic!("solver error on {rel_path}: {err}"));
    assert_ne!(
        outcome,
        SolverOutcome::Sat,
        "SOUNDNESS BUG (#sat-chokepoint): AY reported SAT on {rel_path}, which is UNSAT \
         (z3: unsat). A wrong model bypassed the emit_sat_verdict funnel via this path. \
         Sound outcomes are unsat or unknown (fail-closed)."
    );
}

/// check-sat-assuming path must funnel through the independent gate.
#[test]
#[timeout(120_000)]
fn qf_ax_read_over_write_via_assuming_never_sat() {
    assert_never_sat(
        "benchmarks/smt/regression/soundness_sat_chokepoint/\
         qf_ax_read_over_write_via_assuming.smt2",
    );
}

/// optimize (maximize) path must funnel through the independent gate.
#[test]
#[timeout(120_000)]
fn qf_alia_read_over_store_via_maximize_never_sat() {
    assert_never_sat(
        "benchmarks/smt/regression/soundness_sat_chokepoint/\
         qf_alia_read_over_store_via_maximize.smt2",
    );
}
