// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The bounded BMC replay the kind2 durationThm back-translation tests draw
//! their ground derivation from: run over a window sized for its work, and
//! held to the replaying thread's CPU instead of to a wall budget.

#![cfg(test)]

use std::time::Duration;

use super::*;
use crate::ground_derivation::GroundDerivation;

/// The replay's own window, sized for its work. It is no production budget.
///
/// On the condensed durationThm system the persistent transition-system lane
/// decides depths 0-2 UNSAT. Depth 2, mostly its UNSAT certificate's
/// reconfirmation, takes 7.0 s of an idle X925 core and 14.2 s of an A725.
/// The lane runs depth 3 to a deterministic resource limit (14.6 s / 31 s),
/// and the fresh path then decides depth 3 SAT in 0.1 s: 21.8 s and 45.8 s of
/// the thread's CPU in all (05f65bd3e and b9818f6c4 alike).
/// `BmcSolver::ts_depth_cap` grants a depth at least twice the WALL the
/// previous depth took when that prediction fits what is left, and half of
/// what is left when it does not. It used to grant everything left in the
/// second case, so a stretched depth 2 handed depth 3 the whole remaining
/// window and the fresh path never ran: under the former 45 s window an X925
/// shared with two busy loops failed, depth 2 taking 20.9 s of wall for 7.1 s
/// of CPU and depth 3 the remaining 23.6 s. A narrow band remains where the
/// doubled prediction only just fits: with W the window and c2 depth 2's CPU,
/// the fresh path keeps about W - 3 c2 x stretch, close to nothing near a
/// stretch of W / (3 c2). Under 45 s that is 1.05x of an A725 core and 2.1x
/// of an X925; under 300 s, 7.0x and 14x.
const REPLAY_WINDOW: Duration = Duration::from_mins(5);

/// The work the window no longer bounds, on the replaying thread's own CPU,
/// which contention does not inflate: 45-46 s on an A725 core, idle or shared
/// with a busy loop. The ceiling is 1.75x that and 3.7x the X925 measurement,
/// so a change that doubles the replay's work fails on the slowest core and
/// one that quadruples it fails on every core.
const REPLAY_CPU_CEILING: Duration = Duration::from_secs(80);

/// A ground derivation of the transformed problem's Unsafe from the bounded
/// BMC replay over [`REPLAY_WINDOW`], its work held under
/// [`REPLAY_CPU_CEILING`].
pub(super) fn bounded_bmc_ground_derivation(
    problem: &ChcProblem,
    depth_hint: usize,
) -> GroundDerivation {
    let clock = ay_sys::thread_clock::ThreadCpuClock::current();
    let before = clock.and_then(|clock| clock.elapsed());
    let started = std::time::Instant::now();
    let cex = crate::bmc::BmcSolver::replay_confirm_unsafe_on_problem(
        problem,
        depth_hint,
        REPLAY_WINDOW,
        None,
        false,
    );
    let spent = clock
        .and_then(|clock| clock.elapsed())
        .zip(before)
        .map(|(after, before)| after.saturating_sub(before));
    if let Some(spent) = spent {
        assert!(
            spent < REPLAY_CPU_CEILING,
            "the bounded BMC replay spent {spent:?} of its thread's CPU, over \
             {REPLAY_CPU_CEILING:?}"
        );
    }
    let cex = cex.unwrap_or_else(|| {
        panic!(
            "the transformed problem is Unsafe at bounded depth (the replay gave up after {:?} \
             of wall and {spent:?} of its thread's CPU)",
            started.elapsed()
        )
    });
    cex.ground_derivation
        .clone()
        .expect("bounded BMC replay attaches a ground derivation")
}
