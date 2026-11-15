// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reaping the worker threads of one BV multi-lane route invocation.

use std::time::Duration;

use ay_core::time::Instant;

/// Reap the (already cancelled) BV lane workers of one route invocation.
///
/// Rust cannot safely kill a thread. Every BV lane receives linked cooperative
/// cancellation and the absolute deadline. Without a verdict every worker is
/// joined synchronously: no solver worker outlives the route, even while one
/// finishes a transform stage that has no cancellation boundary.
///
/// With a VALIDATED verdict — this route's own winner (`verdict`), or a
/// ladder race this thread participates in that is already decided
/// ([`crate::adaptive_ladder_race::race_settled`], re-checked while waiting) —
/// the losers get [`crate::portfolio::VERDICT_REAP_BOUND`] to exit and are then
/// detached, the policy of the parallel portfolio's `reap_after_verdict`: a
/// detached lane owns only clones of the problem, its cancelled token answers
/// every SMT check `Unknown`, and its channel has no receiver. Measured on
/// graham-scan-full.31: a race member certified Safe while this join waited on
/// a BvToBool lane inside a 40 s constant-resimplification pass, and the run
/// printed `unknown` at the 62 s hard exit.
pub(super) fn join_bv_lanes<I>(handles: I, verdict: bool)
where
    I: IntoIterator<Item = std::thread::JoinHandle<()>>,
{
    let mut pending: Vec<std::thread::JoinHandle<()>> = handles.into_iter().collect();
    let mut give_up_at: Option<Instant> = None;
    loop {
        let mut index = 0;
        while index < pending.len() {
            if pending[index].is_finished() {
                let _ = pending.swap_remove(index).join();
            } else {
                index += 1;
            }
        }
        if pending.is_empty() {
            return;
        }
        let now = Instant::now();
        if give_up_at.is_none() && (verdict || crate::adaptive_ladder_race::race_settled()) {
            give_up_at = Some(now + crate::portfolio::VERDICT_REAP_BOUND);
        }
        if give_up_at.is_some_and(|give_up_at| now >= give_up_at) {
            tracing::info!(
                "Adaptive: detaching {} cancelled BV lane(s) still running after a verdict",
                pending.len()
            );
            // Dropping the handles detaches the cancelled workers.
            return;
        }
        std::thread::sleep(Duration::from_millis(2));
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    use super::*;

    #[test]
    fn bv_dual_lane_cancellation_is_linked_and_workers_are_reaped() {
        let route = crate::CancellationToken::new();
        let worker_cancellation = route.child();
        let finished = Arc::new(AtomicBool::new(false));
        let worker_finished = finished.clone();
        let handle = std::thread::spawn(move || {
            while !worker_cancellation.is_cancelled() {
                std::thread::yield_now();
            }
            worker_finished.store(true, Ordering::Release);
        });

        route.cancel();
        join_bv_lanes([handle], false);
        assert!(finished.load(Ordering::Acquire));
    }

    #[test]
    fn bv_dual_lane_verdict_detaches_a_lane_that_ignores_cancellation() {
        let release = Arc::new(AtomicBool::new(false));
        let worker_release = release.clone();
        // A lane stuck in a stage with no cancellation boundary.
        let handle = std::thread::spawn(move || {
            while !worker_release.load(Ordering::Acquire) {
                std::thread::sleep(Duration::from_millis(1));
            }
        });
        let started = Instant::now();
        join_bv_lanes([handle], true);
        let waited = started.elapsed();
        release.store(true, Ordering::Release);
        assert!(
            waited >= crate::portfolio::VERDICT_REAP_BOUND,
            "the straggler gets the reap bound first"
        );
        assert!(
            waited < Duration::from_secs(10),
            "a verdict is not held back by a straggler: waited {waited:?}"
        );
    }
}
