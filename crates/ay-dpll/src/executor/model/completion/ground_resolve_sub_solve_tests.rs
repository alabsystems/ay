// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Phase-0 residual sub-solve is decided by counts, not by the clock.
//!
//! `seq_theory_5841::test_seq_replace_decomposition_5841` (and its twin in
//! `seq_soundness_5841`) answered `unknown` in up to 72 of 72 runs under 24
//! concurrent copies, because a 150 ms wall on this sub-solve fired before the
//! sub-solve finished. These tests pin the replacement without timing
//! anything: the envelope the sub-solver is armed with, the stop reason of a
//! counted refusal, and identical outcomes across repeated and concurrent
//! solves.

use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::Duration;

use ay_core::time::Instant;
use ay_frontend::parse;

use super::{
    override_sub_solve_budget_for_test, SubSolveBudget, SUB_SOLVE_HANG_GUARD,
    SUB_SOLVE_MAX_CONFLICTS, SUB_SOLVE_MAX_DECISIONS,
};
use crate::executor::Executor;

/// The regression problem: sat, and its model is completed through the
/// residual sub-solve (18 ground-constrained absent length atoms).
const REPLACE_DECOMPOSITION: &str = "(set-logic QF_SEQLIA)
 (declare-const u (Seq Int))
 (declare-const src (Seq Int))
 (declare-const dst (Seq Int))
 (declare-const r (Seq Int))
 (assert (= r (seq.replace u src dst)))
 (assert (seq.contains u src))
 (assert (not (= src (as seq.empty (Seq Int)))))
 (assert (not (= u (as seq.empty (Seq Int)))))
 (assert (not (= src dst)))
 (assert (not (= r u)))
 (check-sat)";

/// What one solve of [`REPLACE_DECOMPOSITION`] published, including how its
/// residual sub-solve ended.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Observed {
    verdict: String,
    sub_outcome: Option<String>,
    sub_conflicts: Option<u64>,
    sub_decisions: Option<u64>,
}

fn solve_replace_decomposition() -> Observed {
    let commands = parse(REPLACE_DECOMPOSITION).expect("fixture parses");
    let mut exec = Executor::new();
    let verdict = exec
        .execute_all(&commands)
        .expect("fixture executes")
        .join("\n");
    let stats = exec.statistics();
    Observed {
        verdict,
        sub_outcome: stats
            .get_string("model_completion.ground_resolve_sub")
            .map(str::to_string),
        sub_conflicts: stats.get_int("model_completion.ground_resolve_sub_conflicts"),
        sub_decisions: stats.get_int("model_completion.ground_resolve_sub_decisions"),
    }
}

/// The sub-solver carries the counted caps, and its only wall is the hang
/// guard (or the caller's own, earlier, deadline) — never a short verdict
/// budget of its own.
#[test]
fn sub_solve_is_armed_with_counted_caps_and_only_a_hang_guard() {
    let outer = Executor::new();
    let mut sub = Executor::new();
    let before = Instant::now();
    outer.arm_ground_resolve_sub_solve(&mut sub);
    let after = Instant::now();

    assert_eq!(sub.resource_limit(), Some(SUB_SOLVE_MAX_CONFLICTS));
    assert_eq!(sub.decision_limit(), Some(SUB_SOLVE_MAX_DECISIONS));
    let deadline = sub
        .solve_deadline
        .get()
        .expect("the hang guard is always armed");
    assert!(deadline >= before + SUB_SOLVE_HANG_GUARD);
    assert!(deadline <= after + SUB_SOLVE_HANG_GUARD);
    assert_eq!(sub.certification_deadline.get(), Some(deadline));
}

/// A caller's earlier deadline and its interrupt flag bound the sub-solve, so
/// the hang guard can never stretch a command past its own budget.
#[test]
fn sub_solve_never_outlives_the_callers_stop_controls() {
    let mut outer = Executor::new();
    let flag = Arc::new(AtomicBool::new(false));
    let caller = Instant::now() + Duration::from_secs(1);
    outer.set_solve_controls(Some(Arc::clone(&flag)), Some(caller));
    let mut sub = Executor::new();

    outer.arm_ground_resolve_sub_solve(&mut sub);

    assert_eq!(sub.solve_deadline.get(), Some(caller));
    let shared = sub
        .solve_interrupt
        .as_ref()
        .expect("the caller's interrupt flag is shared");
    assert!(Arc::ptr_eq(shared, &flag));
}

// The production envelope sits above everything the retired 150 ms wall let
// a sub-solve finish with, and the guard far above the slowest sub-solve
// measured under load: the largest per-call totals over the calibration set
// and the slowest call (see the module docs of `ground_resolve_sub_solve`).
// Checked at compile time, so a cap cannot drop below them unnoticed.
const CALIBRATED_MAX_CONFLICTS: u64 = 29;
const CALIBRATED_MAX_DECISIONS: u64 = 1_201;
const CALIBRATED_SLOWEST_CALL_MS: u128 = 1_830;
const _: () = assert!(SUB_SOLVE_MAX_CONFLICTS >= 4 * CALIBRATED_MAX_CONFLICTS);
const _: () = assert!(SUB_SOLVE_MAX_DECISIONS >= 4 * CALIBRATED_MAX_DECISIONS);
const _: () = assert!(SUB_SOLVE_HANG_GUARD.as_millis() >= 10 * CALIBRATED_SLOWEST_CALL_MS);

/// With the production caps the sub-solve runs to its own end, and every
/// repetition publishes the same verdict, the same sub-solve outcome and the
/// same counters. Since ae8cb6ed5 detached the sub-solve's memo, the verdict
/// no longer borrows the sub-solve's model values; the positional sequence
/// witness (`completion/seq_witness.rs`) builds its `sat` from the outer
/// model. What this pins is that it is the same on every run and never
/// `unsat`.
#[test]
fn replace_decomposition_is_decided_identically_on_every_run() {
    let first = solve_replace_decomposition();
    assert_ne!(first.verdict, "unsat", "{first:?}");
    let outcome = first.sub_outcome.as_deref().expect("sub-solve ran");
    assert!(
        !outcome.contains("timeout") && !outcome.contains("resourceout"),
        "the production envelope must not stop this sub-solve: {first:?}"
    );
    for _ in 0..3 {
        assert_eq!(solve_replace_decomposition(), first);
    }
}

/// Force the counted caps below what the sub-solve needs, under a guard that
/// cannot fire: the refusal is `resourceout`, never `timeout`, and it is the
/// same on every run. This is the stop a slow machine used to take at random.
#[test]
fn a_counted_refusal_is_resourceout_and_repeatable() {
    let _budget = override_sub_solve_budget_for_test(SubSolveBudget {
        max_conflicts: 1,
        max_decisions: 1,
        hang_guard: Duration::from_secs(3600),
    });
    let first = solve_replace_decomposition();
    assert_eq!(
        first.sub_outcome.as_deref(),
        Some("unknown:resourceout"),
        "{first:?}"
    );
    for _ in 0..3 {
        assert_eq!(solve_replace_decomposition(), first);
    }
}

/// Oversubscribe the host with concurrent solves of the regression problem:
/// every one publishes the same observation as a solve run alone. Nothing
/// here waits on time; the only wall left on the path is the hang guard.
#[test]
fn concurrent_solves_publish_the_single_solve_observation() {
    const SOLVERS: usize = 24;
    let alone = solve_replace_decomposition();
    let handles: Vec<_> = (0..SOLVERS)
        .map(|index| {
            std::thread::Builder::new()
                .name(format!("ground-resolve-contender-{index}"))
                .stack_size(64 * 1024 * 1024)
                .spawn(solve_replace_decomposition)
                .expect("spawn contender")
        })
        .collect();
    for handle in handles {
        assert_eq!(handle.join().expect("contender finished"), alone);
    }
}
