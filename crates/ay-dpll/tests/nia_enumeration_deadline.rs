// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PUBLICATION pin: the obligation that hung `compiler_consumer` for 7h12m must return
//! inside its declared `:timeout`.
//!
//! ## What was measured
//!
//! 2026-09-11. `offline deductive checker check --allow-l0-gaps -p ay-sat` under
//! a 15-second per-function verification budget ran for 8 hours. Its last
//! diagnostic named `ay_sat::symmetry::detector::cc_vertex_classes`; the
//! following 7h12m were one rustc thread at 100% CPU with no output. Every
//! stack sample landed in ONE activation of
//! `ay_nia::bounded_enum::try_capped_model_search`, called from
//! `nia_check_loop_inner` on a `NeedSplit`, under a live and unexpired
//! `NiaSolver::deadline` that nothing on that path ever read.
//!
//! The fixture here is that obligation: VC #6 of the 22 the native bridge sent
//! for `cc_vertex_classes`, from `crates/ay-sat/src/symmetry/detector/
//! clique_colouring_aux_free_sr.rs:175:26-175:37` — the `n * (n - 1)` multiply
//! inside `k * (n * (n - 1) / 2)`. It is a byte-exact capture of
//! `trust_router`'s `problem_smt2` for that VC, minus its `:timeout` line,
//! which the helper below re-installs so the budget is explicit here.
//!
//! ## What this file pins, and what it does NOT
//!
//! It pins the CLASS, not a red-before-green regression. Two distinct defects
//! made that thread spin, and only one of them was still live on `main` when
//! this file was written:
//!
//! * the odometer overflow in the two `bounded_enum.rs` searches — `+= 1`
//!   before the `> hi` test, which WRAPS inside `compiler_consumer` (built with overflow
//!   checks off) and turns a 10k-point box into a ~2^64-point walk. Fixed on
//!   `main` by `6ee065bfea`, which is why this fixture already returns at its
//!   budget there;
//! * the absence of ANY deadline poll inside those enumerations, so the budget
//!   was only consulted between whole calls. Fixed alongside this file.
//!
//! So this test is green at both revisions. Its job is forward-looking: inside
//! `compiler_consumer` the solve runs in-process with NO watchdog — the `ay` CLI's wall
//! is a CLI feature, not a solver one — so any future enumeration that walks
//! long without polling shows up HERE as a wall-clock overrun rather than as
//! another 8-hour compile. The red-before-green pins for the two defects are
//! the unit tests in `ay-nia` (`bounded_enum.rs` and `factor_split.rs`).
//!
//! MEASURED at the fixing revision: `unknown` in ~5.0 s against the 5 s
//! budget, in-process, `Executor::execute_all` returning on its own.

use std::path::PathBuf;
use std::time::Instant;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// The declared solve budget for the replay, in milliseconds.
const BUDGET_MS: u64 = 5_000;

/// How far past `BUDGET_MS` the answer may arrive before this is a stall.
///
/// The deadline is polled at loop boundaries and every 256 enumerated points,
/// so the honest overshoot is milliseconds; 10 s of slack is for a loaded box
/// and for the parse/encode work that runs outside the budget at all. The
/// failure this pins is unbounded — hours — so a wide slack costs nothing.
const SLACK_S: f64 = 10.0;

#[test]
#[timeout(120_000)]
fn cc_vertex_classes_vc06_returns_within_its_timeout() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/nia_enumeration_deadline/cc_vertex_classes_vc06.smt2");
    let fixture =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let script = format!("(set-option :timeout {BUDGET_MS})\n{fixture}");
    let commands = parse(&script).unwrap_or_else(|e| panic!("parse: {e}"));

    let mut executor = Executor::new();
    let started = Instant::now();
    let outputs = executor
        .execute_all(&commands)
        .unwrap_or_else(|e| panic!("execute: {e}"));
    let elapsed = started.elapsed().as_secs_f64();

    let verdict = outputs
        .iter()
        .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .map(|line| line.trim().to_string())
        .unwrap_or_else(|| "<no verdict>".into());
    let reason = executor.unknown_reason().map(|r| format!("{r:?}"));
    eprintln!("vc-06: {verdict} ({reason:?}) in {elapsed:.2}s");

    assert!(
        matches!(verdict.as_str(), "sat" | "unsat" | "unknown"),
        "the solve must produce a verdict line; got {verdict:?} after {elapsed:.2}s"
    );
    assert!(
        elapsed <= BUDGET_MS as f64 / 1000.0 + SLACK_S,
        "the obligation overran its {BUDGET_MS} ms budget by more than {SLACK_S}s \
         ({elapsed:.2}s, verdict {verdict} {reason:?}). Inside compiler_consumer this path \
         runs with no watchdog, so an overrun here is an unbounded compile — the \
         enumeration loops in ay-nia must poll the deadline."
    );
}
