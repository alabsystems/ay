// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! WRONG-`unsat` canaries — QF_NRA meti-tarski scaled-monomial defect (P0, 2026-07-30).
//!
//! Every benchmark here is **satisfiable** — the file's own `(set-info :status sat)` and
//! z3 5.0.0 agree. AY answered `unsat` on all of them, which is a *false theorem*, not a
//! completeness gap.
//!
//! # The defect these pin
//!
//! `NraSolver::collect_nonlinear_terms` filtered the constant factors out of a flattened
//! `*` node to build the monomial key, but registered the **whole** node — constant
//! included — as that monomial's `aux_var`. That asserts `aux_var == product(vars)` for a
//! term whose value is really `c * product(vars)`. With `c < 0` the sign machinery then
//! read the atom `-2·m <= 0` as the fact `m <= 0`, the exact opposite of its content, and
//! `check_sign_consistency` closed the search against `m > 0`.
//!
//! The sibling NIA solver already carried this guard (`nia/src/tangent_add.rs`, whose
//! comment warns that registering a scaled term "yields a WRONG-UNSAT (false theorem)");
//! NRA never got it.
//!
//! # Why this canary is one-sided
//!
//! Asserted as `!= Unsat`, **not** `== Sat`. These need irrational (cube-root) witnesses,
//! so `unknown` is the honest fail-closed answer until the NRA engine can produce
//! algebraic models for them; `sat` with a validated model is the eventual goal. Tightening
//! to `== Sat` is welcome the day the engine earns it — but **never weaken this to allow
//! `unsat`**. A wrong `unsat` cannot be caught by any gate AY has, because every gate
//! validates a *model*, and a model exists only on the `sat` side.
//!
//! The full end-to-end reproducer is embedded below so the canary cannot become
//! silently vacuous when an optional benchmark corpus is absent.

mod common;

use ntest::timeout;
use std::io::Read;
use std::path::Path;
use std::process::{Command, Stdio};
use std::time::Duration;
use wait_timeout::ChildExt;

/// Solve one benchmark by driving the built **CLI**, not the in-process `Executor`.
///
/// This is deliberate, and the reason is itself a finding worth keeping.
///
/// The in-process paths cannot bound these searches. `common::run_executor_*_with_timeout`
/// installs only `Executor::set_interrupt`, and installing `set_timeout`/`set_deadline`
/// directly fares no better: both were measured overshooting a 10 s budget by **>10x** on
/// these fail-closed NRA solves (a 3-file gate blew a 300 s test timeout twice). The NRA
/// search evidently does not poll either cancellation signal on this path. The CLI *looks*
/// prompt (`-T:5` returns in 7.1 s, `-T:10` in 12.0 s) only because its watchdog thread
/// terminates the process — so the reliable way to bound this is a child process we can
/// kill, exactly as `common::run_z3_file` already does for z3.
///
/// Consequence beyond this test: an **embedded/library consumer cannot cancel this NRA
/// solve promptly**. That cancellation gap remains separate from the soundness fix here.
fn solve_via_cli(path: &Path, budget_secs: u64) -> Option<String> {
    let release = common::workspace_path("target/release/ay");
    let debug = common::workspace_path("target/debug/ay");
    let bin = if release.is_file() {
        release
    } else if debug.is_file() {
        debug
    } else {
        return None; // no CLI built in this checkout — caller skips
    };
    let mut child = Command::new(&bin)
        .arg("--competition")
        .arg(format!("-T:{budget_secs}"))
        .arg(path)
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .spawn()
        .unwrap_or_else(|e| panic!("failed to spawn {}: {e}", bin.display()));

    // Hard bound: the CLI watchdog fires ~2 s after the deadline; allow generous slack,
    // then kill. A killed child yields no verdict, which this gate treats as "not unsat".
    if child
        .wait_timeout(Duration::from_secs(budget_secs + 20))
        .expect("failed waiting for ay")
        .is_none()
    {
        let _ = child.kill();
        let _ = child.wait();
        return Some("unknown".to_string());
    }

    let mut out = String::new();
    if let Some(mut h) = child.stdout.take() {
        let _ = h.read_to_string(&mut out);
    }
    Some(
        out.lines()
            .map(str::trim)
            .filter(|l| matches!(*l, "sat" | "unsat" | "unknown"))
            .next_back()
            .unwrap_or("unknown")
            .to_string(),
    )
}

/// Self-contained satisfiable reproducer for the wrong-UNSAT. A witness is
/// `skoX = 3`, `skoC = cubert(3)`, `skoCM1 = cubert(2)`, and
/// `skoCP1 = cubert(4)`, all positive. The high-degree inequality contains the
/// scaled product whose dropped `-2` coefficient used to invert its sign.
const MINIMAL_REPRO: &str = r#"
(set-logic QF_NRA)
(set-info :status sat)
(declare-fun skoC () Real)
(declare-fun skoCM1 () Real)
(declare-fun skoCP1 () Real)
(declare-fun skoX () Real)
(assert (and
  (<= (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1
       (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1 (* skoCM1
       (* skoCM1 (* skoCM1 (* skoCM1 (- 2)))))))))))))))) 0)
  (= (* skoC (* skoC skoC)) skoX)
  (= (+ 1 (* skoCM1 (* skoCM1 skoCM1))) skoX)
  (= (+ (- 1) (* skoCP1 (* skoCP1 skoCP1))) skoX)
  (not (<= skoX 2))
  (not (<= 10 skoX))
  (not (<= skoC 0))
  (not (<= skoCM1 0))
  (not (<= skoCP1 0))))
(check-sat)
"#;

/// Per-file solver budget, in seconds.
///
/// Deliberately SHORT. Post-fix these benchmarks are fail-closed and burn their whole
/// deadline before answering `unknown` (measured: ~60 s at a 60 s cap), so a generous
/// budget would make this gate cost minutes for no extra signal. The defect being pinned
/// produced its wrong `unsat` in **well under a second** — a regression announces itself
/// immediately — so a short budget catches it just as reliably and keeps the gate cheap.
const BUDGET_SECS: u64 = 10;

#[test]
#[timeout(300_000)]
fn metitarski_scaled_monomial_canaries_are_never_unsat() {
    let dir = tempfile::tempdir().expect("temporary canary directory");
    let path = dir.path().join("scaled-monomial-wrong-unsat.smt2");
    std::fs::write(&path, MINIMAL_REPRO).expect("write embedded wrong-UNSAT canary");
    let Some(verdict) = solve_via_cli(&path, BUDGET_SECS) else {
        eprintln!("skipping wrong-UNSAT canary: no target/{{release,debug}}/ay is built");
        return;
    };

    assert_ne!(
        verdict, "unsat",
        "WRONG-UNSAT CANARY TRIPPED. This embedded formula is SATISFIABLE, so `unsat` \
         is a false theorem and a soundness regression. The known cause is a scaled \
         monomial being registered as the aux var of its constant-free key, breaking \
         the `aux_var == product(vars)` invariant every consumer assumes. Do not \
         weaken this assertion; find the defect."
    );
}
