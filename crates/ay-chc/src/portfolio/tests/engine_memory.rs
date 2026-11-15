// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! WP-F lane memory shares: a lane that outgrows its share is stopped ALONE —
//! cancelled at its soft share, unwound at its hard share when it does not
//! poll — while a sibling lane still delivers its verdict.
//!
//! The mock lanes charge their memory group through the same entry the
//! global counting allocator uses (`ay_sys` charges the calling thread's
//! group from `add_live_bytes`); unit-test binaries do not install the
//! counting allocator, so the charge is made explicitly.

use super::*;
use crate::pdr::{Counterexample, CounterexampleStep};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

fn skeleton_unsafe(depth: usize) -> PortfolioResult {
    let steps = (0..=depth)
        .map(|_| CounterexampleStep::new(crate::PredicateId(0), FxHashMap::default()))
        .collect();
    PortfolioResult::Unsafe(Counterexample::new(steps))
}

fn two_lanes(window: Duration) -> PortfolioConfig {
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

/// Sibling lane: waits until `hog_done` (bounded), records whether its own
/// token was cancelled meanwhile, then answers a valid skeleton `Unsafe`.
fn sibling(hog_done: &AtomicBool, sibling_cancelled: &AtomicBool) -> EngineResult {
    let start = ay_core::time::Instant::now();
    while !hog_done.load(Ordering::SeqCst) && start.elapsed() < Duration::from_secs(10) {
        thread::sleep(Duration::from_millis(5));
    }
    EngineResult::Unified(
        if sibling_cancelled.load(Ordering::SeqCst) {
            PortfolioResult::Unknown
        } else {
            skeleton_unsafe(5)
        },
        "TEST_SIBLING",
    )
}

#[test]
#[serial]
#[timeout(30_000)]
fn lane_over_its_soft_share_is_cancelled_alone() {
    let hog_cancelled = Arc::new(AtomicBool::new(false));
    let sibling_cancelled = Arc::new(AtomicBool::new(false));
    let (hog, sib) = (Arc::clone(&hog_cancelled), Arc::clone(&sibling_cancelled));
    let solver = PortfolioSolver::new(create_unsafe_problem(), two_lanes(Duration::from_secs(20)))
        .with_parallel_worker_limit(2)
        .with_engine_memory_limits(64 << 20, 1 << 40)
        .with_sequential_test_engine(move |idx, cancellation| {
            if idx == 0 {
                // Grows 1 MiB per step and polls its token like any engine loop.
                for _ in 0..100_000 {
                    if cancellation.is_cancelled() {
                        hog.store(true, Ordering::SeqCst);
                        break;
                    }
                    ay_sys::charge_current_for_testing(1 << 20);
                }
                EngineResult::Unified(PortfolioResult::Unknown, "TEST_MEMORY_HOG")
            } else {
                let result = sibling(&hog, &AtomicBool::new(false));
                sib.store(cancellation.is_cancelled(), Ordering::SeqCst);
                result
            }
        });
    let result = solver.solve_parallel();
    assert!(
        hog_cancelled.load(Ordering::SeqCst),
        "the lane past its soft share is cancelled"
    );
    assert!(
        !sibling_cancelled.load(Ordering::SeqCst),
        "the sibling lane is not cancelled by another lane's memory"
    );
    assert!(
        matches!(result, PortfolioResult::Unsafe(_)),
        "the sibling's verdict is still delivered, got {result:?}"
    );
}

/// Sets its flag when dropped during an unwind (the forced lane unwind).
struct UnwindWitness(Arc<AtomicBool>);

impl Drop for UnwindWitness {
    fn drop(&mut self) {
        if std::thread::panicking() {
            self.0.store(true, Ordering::SeqCst);
        }
    }
}

#[test]
#[serial]
#[timeout(30_000)]
fn lane_past_its_hard_share_is_unwound_at_an_expression_walk() {
    let unwound = Arc::new(AtomicBool::new(false));
    let finished_normally = Arc::new(AtomicBool::new(false));
    let (flag, normal) = (Arc::clone(&unwound), Arc::clone(&finished_normally));
    let solver = PortfolioSolver::new(create_unsafe_problem(), two_lanes(Duration::from_secs(20)))
        .with_parallel_worker_limit(2)
        .with_engine_memory_limits(32 << 20, 64 << 20)
        .with_sequential_test_engine(move |idx, cancellation| {
            if idx == 0 {
                let _witness = UnwindWitness(Arc::clone(&flag));
                // A burst past the hard share, then work that never polls
                // its token: only the forced unwind can stop it.
                ay_sys::charge_current_for_testing(128 << 20);
                let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
                let expr = ChcExpr::le(ChcExpr::add(x.clone(), ChcExpr::int(1)), x);
                let start = ay_core::time::Instant::now();
                while start.elapsed() < Duration::from_secs(10) {
                    std::hint::black_box(expr.vars());
                }
                normal.store(true, Ordering::SeqCst);
                EngineResult::Unified(PortfolioResult::Unknown, "TEST_NON_POLLING_HOG")
            } else {
                let _ = &cancellation;
                sibling(&flag, &AtomicBool::new(false))
            }
        });
    let result = solver.solve_parallel();
    assert!(
        unwound.load(Ordering::SeqCst),
        "the non-polling lane was unwound"
    );
    assert!(
        !finished_normally.load(Ordering::SeqCst),
        "the non-polling lane must not run to completion"
    );
    assert!(
        matches!(result, PortfolioResult::Unsafe(_)),
        "the sibling's verdict is still delivered, got {result:?}"
    );
}

/// The process memory governor sheds the lane holding the heap although it
/// is under its own share: that lane stops at its next poll, the sibling
/// keeps running and still delivers its verdict.
#[test]
#[serial]
#[timeout(30_000)]
fn governor_sheds_the_fattest_lane_and_the_sibling_answers() {
    // Far above anything a concurrently running test's group holds, so the
    // shed below can only pick this test's hog.
    const HOG_BYTES: usize = 1 << 50;
    let hog_charged = Arc::new(AtomicBool::new(false));
    let hog_stopped = Arc::new(AtomicBool::new(false));
    let shed_label = Arc::new(std::sync::Mutex::new(None));
    let (charged, stopped, label) = (
        Arc::clone(&hog_charged),
        Arc::clone(&hog_stopped),
        Arc::clone(&shed_label),
    );
    let solver = PortfolioSolver::new(create_unsafe_problem(), two_lanes(Duration::from_secs(20)))
        .with_parallel_worker_limit(2)
        .with_engine_memory_limits(1 << 52, 1 << 53)
        .with_sequential_test_engine(move |idx, cancellation| {
            if idx == 0 {
                ay_sys::charge_current_for_testing(HOG_BYTES);
                charged.store(true, Ordering::SeqCst);
                let start = ay_core::time::Instant::now();
                while start.elapsed() < Duration::from_secs(10) {
                    if cancellation.is_cancelled() {
                        stopped.store(true, Ordering::SeqCst);
                        break;
                    }
                    thread::sleep(Duration::from_millis(2));
                }
                EngineResult::Unified(PortfolioResult::Unknown, "TEST_SHED_HOG")
            } else {
                let start = ay_core::time::Instant::now();
                while !charged.load(Ordering::SeqCst) && start.elapsed() < Duration::from_secs(10) {
                    thread::sleep(Duration::from_millis(2));
                }
                // What the governor does once the process nears its budget.
                let shed = ay_sys::shed_fattest_memory_group(HOG_BYTES, 1);
                *label
                    .lock()
                    .unwrap_or_else(std::sync::PoisonError::into_inner) =
                    shed.map(|usage| usage.label);
                let result = sibling(&stopped, &AtomicBool::new(false));
                assert!(
                    !cancellation.is_cancelled(),
                    "the sibling is not cancelled by the shed"
                );
                result
            }
        });
    let result = solver.solve_parallel();
    assert_eq!(
        *shed_label
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner),
        Some("PDR"),
        "the lane holding the heap (engine 0, PDR) is the one shed"
    );
    assert!(
        hog_stopped.load(Ordering::SeqCst),
        "the shed lane stops at its next poll"
    );
    assert!(
        matches!(result, PortfolioResult::Unsafe(_)),
        "the sibling's verdict is still delivered, got {result:?}"
    );
}
