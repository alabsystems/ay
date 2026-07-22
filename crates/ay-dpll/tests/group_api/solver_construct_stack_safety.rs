// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression test: `Solver` construction must not overflow small thread
//! stacks (2026-07-18 deductive-checks embedder crash).
//!
//! deductive-checks's test binary crashed with EXC_BAD_ACCESS at a stack guard
//! region, overflowing inside `Executor::execute` during `Solver::try_new`,
//! on libtest's default 2 MiB test threads. There is no deep input here —
//! `set-logic` elaborates no terms. The overflow was constant-per-profile
//! frame bulk: `Executor` is ~56 KB, and the construction chain
//! (`try_new` -> `try_new_with_config` -> `Executor::new` -> `execute`)
//! moved it by value through several unelided frames on top of the giant
//! dispatch/elaboration frames of `execute`/`process_command`. Measured on
//! this host (2026-07-18): construction needed 256–384 KiB of stack at
//! opt-level 1 and 512–768 KiB at opt-level 0 — an embedder's default dev
//! profile compiles ay-dpll at opt-level 0 with MORE frame bulk than that
//! (its third-party deps are opt 0 too), and its own test frames sit above
//! the call, so a 2 MiB test thread overflowed.
//!
//! Fixed by (1) extending the executor's `stacker::maybe_grow` guard
//! (#6783) to `Executor::new`, top-level `Executor::execute`, and
//! `Solver::try_new_with_config`, and (2) boxing the `Executor` inside
//! `Solver` so the value escaping to the caller's stack is ~0.5 KB.
//!
//! The 192 KiB case is a genuine pre-fix-failing reproducer at this repo's
//! own test profile (pre-fix threshold: fails at <= 256 KiB, passes at
//! 384 KiB; post-fix: passes at 48 KiB). The 2 MiB case documents the
//! embedder scenario verbatim. A pre-fix overflow aborts this whole test
//! binary with "thread ... has overflowed its stack" (SIGABRT), which is
//! the intended loud failure mode, matching the other *_stack_safety tests.

use std::sync::mpsc;
use std::time::Duration;

use ay_dpll::api::{Logic, SolveResult, Solver};

/// Construct a `Solver` (Logic::All — deductive-checks's choice), run a trivial
/// check-sat, and confirm completion from a thread with `stack` bytes.
fn construct_on_small_stack(name: &str, stack: usize) {
    let (tx, rx) = mpsc::channel();

    let handle = std::thread::Builder::new()
        .name(name.into())
        .stack_size(stack)
        .spawn(move || {
            let mut solver =
                Solver::try_new(Logic::All).expect("Solver::try_new(Logic::All) must construct");
            // Trivial solve: no assertions => Sat. Exercises the guarded
            // check-sat entry from the same small thread.
            let result = solver.check_sat();
            let _ = tx.send(result);
        })
        .expect("spawn small-stack thread");

    let result = rx
        .recv_timeout(Duration::from_mins(1))
        .unwrap_or_else(|e| panic!("{name}: construction thread did not complete: {e:?}"));
    handle.join().expect("join small-stack thread");
    assert_eq!(
        result,
        SolveResult::Sat,
        "trivial empty-assertion check-sat must stay Sat"
    );
}

/// The embedder scenario verbatim: libtest's default 2 MiB test thread.
#[test]
fn solver_construction_on_2mib_libtest_stack() {
    construct_on_small_stack("construct-2mib", 2 * 1024 * 1024);
}

/// Pre-fix-failing reproducer at this repo's own test profile (opt-level 1):
/// 192 KiB is below the measured pre-fix threshold (<= 256 KiB fails) with
/// 4x margin over the measured post-fix requirement (48 KiB passes).
#[test]
fn solver_construction_on_192kib_stack() {
    construct_on_small_stack("construct-192kib", 192 * 1024);
}

/// Direct-`Executor` embedders (no `api::Solver` layer) get the same
/// protection from the guards on `Executor::new`/`Executor::execute`.
/// 192 KiB fails pre-fix; post-fix threshold is 128 KiB (the ~56 KB
/// `Executor` local plus its unelided by-value return copies are inherent
/// to the public by-value `Executor::new` API and stay on this thread).
#[test]
fn executor_construction_on_192kib_stack() {
    let (tx, rx) = mpsc::channel();

    let handle = std::thread::Builder::new()
        .name("executor-192kib".into())
        .stack_size(192 * 1024)
        .spawn(move || {
            let mut exec = ay_dpll::Executor::new();
            let cmds = ay_frontend::parse("(set-logic ALL)").expect("parse");
            for cmd in &cmds {
                exec.execute(cmd).expect("set-logic ALL must execute");
            }
            let _ = tx.send(());
        })
        .expect("spawn small-stack thread");

    rx.recv_timeout(Duration::from_mins(1))
        .expect("executor construction thread did not complete");
    handle.join().expect("join small-stack thread");
}
