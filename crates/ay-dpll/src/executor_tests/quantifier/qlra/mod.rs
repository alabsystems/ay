// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Nested-CEGQI quantified-LRA lane (#qlra-nested-cegqi) end-to-end tests.
//!
//! Every publishing assertion also reads the lane's own `qlra.*` statistics,
//! so a verdict the legacy path happened to reach cannot satisfy a test that
//! is about the lane (the dead-route trap `prepass_reachability.rs`
//! documents).
//!
//! The QSAT route decides every fixture here first and the lane never runs
//! behind it, so these tests run under `--no-qsat`, where the lane is the
//! fallback; `quantifier/qsat.rs` runs the same fixtures through the route.

use std::time::Duration;

use crate::Executor;
use ay_frontend::parse;

mod decline_is_free;
mod firewalls;
mod m1_single_block;
mod m2_nested;
mod m3_sat_gate;
mod m3_unsat_cert;
mod m4_incremental;
mod query_scope;

/// Wall cap per test query; generous so load cannot flip a verdict.
const QUERY_TIMEOUT: Duration = Duration::from_secs(30);

/// Run `smt` and return (last output line, `qlra.cert`, `qlra.gate`,
/// `qlra.decline`).
pub(super) struct LaneRun {
    pub(super) verdict: String,
    pub(super) cert: Option<String>,
    pub(super) gate: Option<String>,
    pub(super) decline: Option<String>,
    pub(super) recognized: bool,
    /// An internal retry re-attempted publication from the lane memo.
    pub(super) retried: bool,
    /// `qlra.rollback` of the last lane pass.
    pub(super) rollback: Option<String>,
    /// `qlra.shadow_verdict` of the lane's search.
    pub(super) shadow: Option<String>,
    /// Term-store size after the whole script.
    pub(super) terms_len: usize,
    /// `qlra.gate_xp_consulted` / `qlra.gate_xp_confirmed`: how often the
    /// lane's gate arm consulted / was confirmed by the expansion route.
    pub(super) xp_consulted: u64,
    pub(super) xp_confirmed: u64,
}

pub(super) fn run(smt: &str) -> LaneRun {
    run_with(smt, false)
}

/// As [`run`], optionally under the CLI's `--z3-mode` posture: proof-cycle
/// shedding plus no parsed-assertion retention (`run.rs` turns retention off
/// when no proof can be emitted, which also closes the certification
/// cascade's authored-surface route). The shedding first pass cannot certify,
/// so the lane's memo retry runs a second publication attempt in the same
/// public solve.
pub(super) fn run_with(smt: &str, z3_mode: bool) -> LaneRun {
    let _no_qsat = without_qsat();
    let commands = parse(smt).expect("parse");
    let mut exec = Executor::new();
    exec.set_timeout(Some(QUERY_TIMEOUT));
    if z3_mode {
        exec.set_competition_mode(true);
        exec.set_retain_parsed_assertions(false);
    }
    let outputs = exec.execute_all(&commands).expect("execute");
    let stats = exec.statistics();
    let text = |key: &str| stats.get_string(key).map(str::to_string);
    LaneRun {
        verdict: outputs
            .iter()
            .rev()
            .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
            .cloned()
            .unwrap_or_default(),
        cert: text("qlra.cert"),
        gate: text("qlra.gate"),
        decline: text("qlra.decline"),
        recognized: stats.extra.contains_key("qlra.recognized"),
        retried: stats.extra.contains_key("qlra.retry"),
        rollback: text("qlra.rollback"),
        shadow: text("qlra.shadow_verdict"),
        terms_len: exec.ctx.terms.len(),
        xp_consulted: stats.get_int("qlra.gate_xp_consulted").unwrap_or(0),
        xp_confirmed: stats.get_int("qlra.gate_xp_confirmed").unwrap_or(0),
    }
}

/// `--no-qsat` for the rest of the scope: the lane is the fallback there.
pub(super) fn without_qsat() -> ay_core::misc_test_override::Guard {
    ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_qsat: true,
        ..ay_core::misc_cli_flags().clone()
    })
}

/// The lane itself published `unsat` through the consequence replay.
pub(super) fn assert_lane_unsat(name: &str, smt: &str) {
    let run = run(smt);
    assert_eq!(
        run.verdict, "unsat",
        "{name}: verdict (decline={:?})",
        run.decline
    );
    assert_eq!(
        run.cert.as_deref(),
        Some("installed"),
        "{name}: the lane must be the publisher (decline={:?})",
        run.decline
    );
}

/// The lane itself published `sat` through the quantified model gate.
pub(super) fn assert_lane_sat(name: &str, smt: &str) {
    let run = run(smt);
    assert_eq!(
        run.verdict, "sat",
        "{name}: verdict (decline={:?})",
        run.decline
    );
    assert_eq!(
        run.gate.as_deref(),
        Some("confirmed"),
        "{name}: the lane must be the publisher (decline={:?})",
        run.decline
    );
}
