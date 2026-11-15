// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded EAGER validation of witness-less `Unsafe` results in the parallel
//! receive loop (CHC-COMP 2026 LRA-Lin, `kbfiltr_simpl2`-class).
//!
//! Before this change a witness-less Unsafe was deferred unconditionally to
//! the loop's exit, where the enclosing solve/SMT deadlines had expired
//! (every replay query answered Unknown at once) and the boundary gate
//! discarded whatever validated late — a correct refutation available at 2 s
//! of a 60 s window was published as `unknown`. These tests pin:
//!
//! * a VALID witness-less Unsafe arriving late in the window is validated and
//!   accepted INSIDE the window (eager slice, or the reserve drain when it
//!   arrives inside the reserved tail);
//! * a SPURIOUS witness-less Unsafe is still rejected — validation is
//!   reordered, never skipped or weakened.

use super::*;
use crate::pdr::{Counterexample, CounterexampleStep};
use std::sync::{Arc, Mutex};

/// Skeleton counterexample the interpolation / k-induction engines emit: no
/// derivation witness, `depth + 1` steps with no assignments.
fn skeleton_unsafe(depth: usize) -> PortfolioResult {
    let steps = (0..=depth)
        .map(|_| CounterexampleStep::new(crate::PredicateId(0), FxHashMap::default()))
        .collect();
    PortfolioResult::Unsafe(Counterexample::new(steps))
}

fn two_lane_parallel_config(window: Duration) -> PortfolioConfig {
    PortfolioConfig {
        external_cancellation: None,
        engines: vec![
            EngineConfig::Pdr(PdrConfig::default()),
            EngineConfig::Bmc(BmcConfig::default()),
        ],
        parallel: true,
        timeout: None,
        parallel_timeout: Some(window),
        verbose: false,
        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    }
}

/// Lane 0 publishes `result` once `publish_at` has passed; lane 1 idles until
/// cancelled and answers Unknown, like a sibling engine that never finishes.
fn solver_with_late_publisher(
    problem: ChcProblem,
    window: Duration,
    publish_at: ay_core::time::Instant,
    result: PortfolioResult,
) -> PortfolioSolver {
    let published = Arc::new(Mutex::new(Some(result)));
    PortfolioSolver::new(problem, two_lane_parallel_config(window))
        .with_parallel_worker_limit(2)
        .with_sequential_test_engine(move |idx, cancellation| {
            if idx == 0 {
                while ay_core::time::Instant::now() < publish_at && !cancellation.is_cancelled() {
                    thread::sleep(Duration::from_millis(5));
                }
                let result = published
                    .lock()
                    .unwrap()
                    .take()
                    .unwrap_or(PortfolioResult::Unknown);
                EngineResult::Unified(result, "TEST_WITNESSLESS_LANE")
            } else {
                while !cancellation.is_cancelled() {
                    thread::sleep(Duration::from_millis(5));
                }
                EngineResult::Unified(PortfolioResult::Unknown, "TEST_IDLE_SIBLING")
            }
        })
}

#[test]
#[serial]
#[timeout(30_000)]
fn late_witnessless_unsafe_is_validated_eagerly_inside_the_window() {
    // `create_unsafe_problem`: x=0 -> Inv, Inv(x) -> Inv(x+1), Inv(x) /\ x>=5 -> false.
    // A skeleton of depth 5 replays as init /\ T^5 /\ query, which is SAT.
    let window = Duration::from_secs(4);
    let start = ay_core::time::Instant::now();
    let deadline = start + window;
    // Mirror the embedding: the whole-solve thread deadline the adaptive layer
    // installs. At the boundary it zeroes every validation query, which is
    // exactly why a deferred-to-exit validation could never succeed.
    let _solve_deadline = crate::smt::ScopedSolveDeadline::new(Some(deadline));

    let solver = solver_with_late_publisher(
        create_unsafe_problem(),
        window,
        start + window.mul_f64(0.55),
        skeleton_unsafe(5),
    );
    let result = solver.solve_parallel();
    let elapsed = start.elapsed();

    assert!(
        matches!(result, PortfolioResult::Unsafe(_)),
        "a valid witness-less Unsafe published at 55 % of the window must be accepted, got {result:?}"
    );
    assert!(
        elapsed < window,
        "acceptance must happen inside the window (eager slice), not at its boundary: {elapsed:?}"
    );
}

#[test]
#[serial]
#[timeout(30_000)]
fn witnessless_unsafe_inside_the_reserve_tail_is_validated_before_the_boundary() {
    // Published with ~150 ms left: too little for an eager slice
    // (remaining/4 < 50 ms), so it goes to the stash, and the reserve drain
    // (10 % of the window, >= 500 ms) validates it before the deadline.
    let window = Duration::from_secs(4);
    let start = ay_core::time::Instant::now();
    let deadline = start + window;
    let _solve_deadline = crate::smt::ScopedSolveDeadline::new(Some(deadline));

    let solver = solver_with_late_publisher(
        create_unsafe_problem(),
        window,
        deadline - Duration::from_millis(150),
        skeleton_unsafe(5),
    );
    let result = solver.solve_parallel();
    let elapsed = start.elapsed();

    assert!(
        matches!(result, PortfolioResult::Unsafe(_)),
        "a valid witness-less Unsafe published inside the reserve tail must still be accepted, got {result:?}"
    );
    assert!(
        elapsed < window + Duration::from_millis(250),
        "the reserve drain must not overrun the window materially: {elapsed:?}"
    );
}

#[test]
#[serial]
#[timeout(30_000)]
fn spurious_witnessless_unsafe_is_never_accepted() {
    // `create_safe_problem`: Inv(x) /\ x<5 -> Inv(x+1), Inv(x) /\ x>=10 -> false
    // is SAFE; a skeleton of any depth replays UNSAT and must be rejected.
    let window = Duration::from_secs(4);
    let start = ay_core::time::Instant::now();
    let _solve_deadline = crate::smt::ScopedSolveDeadline::new(Some(start + window));

    let solver = solver_with_late_publisher(
        create_safe_problem(),
        window,
        start + window.mul_f64(0.3),
        skeleton_unsafe(6),
    );
    let result = solver.solve_parallel();

    assert!(
        !matches!(result, PortfolioResult::Unsafe(_)),
        "a spurious witness-less Unsafe must not be accepted by the eager slice, got {result:?}"
    );
}
