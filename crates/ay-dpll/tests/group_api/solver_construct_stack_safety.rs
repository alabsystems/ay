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
//!
//! The caller's thread still pays for the `Executor` VALUE, twice: the
//! by-value `Executor::new` holds one copy in its own frame (stacker's return
//! slot) on top of the caller's. The direct-`Executor` case needs about
//! `2 * size_of::<Executor>() + 10 KiB` (measured 2026-09-30, aarch64 Linux,
//! opt-level 1: 150,408 B fails at 300 KiB and passes at 304 KiB; 92,552 B
//! fails at 188 KiB and passes at 192 KiB). 0027a7b70 put a 57,864 B
//! `ScopedWindowLanes` inline (91,592 -> 150,408 B) and the 192 KiB case
//! aborted this binary. The fields that embed an `ay_sat::Solver`
//! (`scoped_window_lanes`, `incr_bv_state`, `incr_fp_state`) are boxed now,
//! about 54 KB, and [`EXECUTOR_INLINE_SIZE_CEILING`] makes the next growth a
//! test failure that names its cause instead of an abort.

use std::sync::mpsc;
use std::time::Duration;

use ay_dpll::api::{Logic, SolveResult, Solver};

/// Ceiling on `size_of::<ay_dpll::Executor>()` for the small-stack cases
/// below. Measured 53,968-54,432 B across main on 2026-09-30 (dev profile; release drops the
/// debug-only fields). At the ceiling the direct-`Executor` case needs about
/// 2 * 64 KiB + 10 KiB = 138 KiB of its 192 KiB thread, so this fails well
/// before an overflow would abort the binary. A new field that crosses it is
/// boxed, not accommodated by raising the ceiling: the incremental lanes each
/// embed an ~19 KB `ay_sat::Solver`, and `RUSTC_BOOTSTRAP=1 cargo rustc -p
/// ay-dpll --lib -- -Zprint-type-sizes` lists `executor::Executor`'s fields
/// by size.
const EXECUTOR_INLINE_SIZE_CEILING: usize = 64 * 1024;

fn assert_executor_inline_size_within_ceiling() {
    let size = size_of::<ay_dpll::Executor>();
    assert!(
        size <= EXECUTOR_INLINE_SIZE_CEILING,
        "size_of::<Executor>() is {size} B, over the {EXECUTOR_INLINE_SIZE_CEILING} B \
         small-stack ceiling: the by-value Executor::new pays every inline byte twice \
         on the caller's thread, so box the field that grew it"
    );
}

/// The ceiling on its own, so a growth is reported by name even when no
/// small-stack case runs.
#[test]
fn executor_inline_size_stays_under_small_stack_ceiling() {
    assert_executor_inline_size_within_ceiling();
}

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
    assert_executor_inline_size_within_ceiling();
    construct_on_small_stack("construct-192kib", 192 * 1024);
}

/// Direct-`Executor` embedders (no `api::Solver` layer) get the same
/// protection from the guards on `Executor::new`/`Executor::execute`.
/// 192 KiB fails pre-fix; post-fix threshold is 128 KiB (the ~56 KB
/// `Executor` local plus its unelided by-value return copies are inherent
/// to the public by-value `Executor::new` API and stay on this thread).
/// Re-measured 2026-09-30 at about 54 KB: passes at 128 KiB, which is also the
/// smallest stack this aarch64 host grants (`PTHREAD_STACK_MIN`).
#[test]
fn executor_construction_on_192kib_stack() {
    assert_executor_inline_size_within_ceiling();
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
