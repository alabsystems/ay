// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Automated guard for the `storeinv_t3_np_nf_10_wrong_sat` wrong-SAT canary.
//!
//! the development design notes:33` lists this benchmark as a standing
//! gate — "`storeinv_t3_np_nf_10_wrong_sat` canary never sat". Until now that
//! gate existed ONLY as prose: `grep -rn storeinv_t3_np_nf_10 .` returned exactly
//! one hit, the handoff document itself. No test, script, or CI step referenced
//! the benchmark or its directory, so nothing enforced it.
//!
//! That mattered — and the drift turned out to have a different cause than a
//! solver regression. **The benchmark file was MALFORMED, and had been since the
//! commit that added it** (`7ad8c2951`): the `(set-info :source |` line opening a
//! multi-line quoted symbol was missing, leaving bare prose at top level and an
//! orphaned `|)`. z3 rejects it outright ("invalid command, '(' expected"). AY,
//! by contrast, silently recovered and emitted a verdict — `unsat` before
//! 2026-07-25, `unknown` after. So the "regression" was a change in
//! error-recovery behaviour on unparseable input, and the canary had never once
//! tested the wrong-SAT it was created to guard.
//!
//! The file is now repaired. z3 and AY both answer `unsat`, matching its own
//! `(set-info :status unsat)`.
//!
//! (An earlier revision of this header claimed AY "silently recovered" from the
//! malformed input. That was WRONG, and the error was in the observation, not the
//! solver: it came from reading `ay ... 2>/dev/null | tail -1`, which discards
//! stderr and every line but the last. AY in fact emits a precise diagnostic
//! cascade — `stray token 'Benchmarks' at line 10 column 1 ... (skipped 6
//! consecutive stray tokens)`, then `unknown sort 'Index'` for each downstream
//! casualty — and on a well-formed file with trailing garbage it reports
//! `(error ...)` and then the verdict, exactly as z3 does. There is no defect
//! here.)
//!
//! WHAT THIS TEST ASSERTS
//!
//! Two-sided, deliberately:
//!   * `!= Sat`  — the soundness invariant, and what the prose gate said. A `sat`
//!     here is a wrong answer.
//!   * `== Unsat` — the completeness half. The one-sided form the handoff doc
//!     specified is satisfied by `unknown`, which is exactly why the drift went
//!     unnoticed for a day. Pinning `unsat` is only defensible because the file
//!     now parses and both AY and z3 agree on it.
//!
//! See the development design notes §7.

mod common;

use common::SolverOutcome;
use ntest::timeout;

const CANARY: &str =
    "benchmarks/smt/regression/soundness_qf_ax_storechain/storeinv_t3_np_nf_10_wrong_sat.smt2";

/// The canary must NEVER be reported `sat`. A `sat` here is a wrong answer.
#[test]
#[timeout(120_000)]
fn storeinv_t3_np_nf_10_canary_is_never_sat() {
    let path = common::workspace_path(CANARY);
    if !path.is_file() {
        eprintln!(
            "skipping wrong-SAT canary, benchmark not present in this checkout: {}",
            path.display()
        );
        return;
    }

    let outcome = common::run_executor_file_with_timeout(&path, 60)
        .unwrap_or_else(|err| panic!("solver error on the wrong-SAT canary: {err}"));

    assert_ne!(
        outcome,
        SolverOutcome::Sat,
        "WRONG-SAT CANARY TRIPPED: {CANARY} was reported `sat`. This benchmark is \
         unsatisfiable; a `sat` answer here is a soundness regression, not a \
         completeness one. Do not weaken this assertion — find the defect."
    );
    // Two-sided: the benchmark declares `(set-info :status unsat)` and z3 agrees,
    // so `unknown` is a completeness regression and must also fail. This is only
    // assertable because the file now parses — see the header.
    assert_eq!(
        outcome,
        SolverOutcome::Unsat,
        "canary completeness regression: expected `unsat` (declared status, and \
         z3 agrees); got {outcome:?}"
    );
}

/// Logs the answer for post-hoc diagnosis when the assertion above fails.
/// Never fails itself; purely observational.
#[test]
#[timeout(120_000)]
fn storeinv_t3_np_nf_10_canary_answer_is_reported() {
    let path = common::workspace_path(CANARY);
    if !path.is_file() {
        eprintln!("skipping canary observation, benchmark absent");
        return;
    }
    match common::run_executor_file_with_timeout(&path, 60) {
        Ok(outcome) => eprintln!(
            "[canary] storeinv_t3_np_nf_10_wrong_sat => {outcome:?} \
             (was `unsat` before 2026-07-25, `unknown` after; both are sound)"
        ),
        Err(err) => eprintln!("[canary] solver error: {err}"),
    }
}
