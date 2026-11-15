// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! M2 (the development design notes §8): what `tick(1)` and `should_stop()`
//! cost on a GuardTree node at depths 1 to 4, against `ResourceGuard` as it
//! was before S0 (a frozen copy below).
//!
//! A MEASUREMENT, WITH NO BOUND. `targo --unverified bench -p ay-core --bench
//! guard_tree` measures and prints the costs and their ratios to the old
//! guard's; run without `--bench` (as `test --benches` runs it), it takes a
//! short smoke pass. It exits 0 either way and states no pass line. Until
//! 2026-10-15 it held `tick` at depth 3 to at most twice the old guard's,
//! and that bound is DELETED, not kept as a printed reading beside the
//! numbers. A cost in nanoseconds is a clock, and the host's load moves it on
//! its own: the old and new series are timed in turn, round by round, each
//! keeping its best round, and still a loaded host widens the ratio (1.5x to
//! 1.9x at load 14 to 16 and 2.0x at 54, against 1.3x idle), so the 2x bound
//! failed trees whose ticks had not changed. A verdict is decided
//! by counts, with a clock only as a hang backstop (Trust BUDGET-1,
//! the development design notes DR-37), and no count is this cost: instructions retired
//! would be another bound, one nobody has measured (by the shape of the tick
//! path, about 2.5x to 3x the old guard's at depth 3 where the nanoseconds read
//! 1.45x). What keeps `tick` cheap is decided by counts in M1: the stride
//! (`TICKS_PER_CLOCK_READ`) on which a node reads the clock and flushes its
//! ledger (`guard_tree/tests/count.rs`). A person reads the numbers on an
//! idle host, as a profile, not as a verdict.
//!
//! Depth counts the nodes from the measured one up to, and including, the
//! one under the root. Every node carries the same limits as the old guard:
//! a cancel flag, a deadline an hour away and an rlimit that is never
//! reached, so both sides read the same conditions.

use std::hint::black_box;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::Duration;

use ay_core::resource::{ChildSpec, DeadlineSource, Guard, NodeLabel};
use ay_core::time::Instant;

/// `ResourceGuard` at origin/main `da447f9a6d`, the reference M2 measures
/// against.
mod baseline {
    use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
    use std::sync::Arc;

    use ay_core::resource::{process_cancelled, Exhausted};
    use ay_core::time::Instant;

    const TICKS_PER_CLOCK_READ: u64 = 1024;

    #[derive(Clone, Debug, Default)]
    pub(crate) struct ResourceGuard {
        pub(crate) deadline: Option<Instant>,
        pub(crate) cancel: Option<Arc<AtomicBool>>,
        pub(crate) rlimit: Option<u64>,
        pub(crate) ticks: Arc<AtomicU64>,
    }

    impl ResourceGuard {
        fn ticks(&self) -> u64 {
            self.ticks.load(Ordering::Relaxed)
        }

        pub(crate) fn tick(&self, cost: u64) -> Result<(), Exhausted> {
            let before = self.ticks.fetch_add(cost, Ordering::Relaxed);
            let after = before.saturating_add(cost);
            if self.cancelled() {
                return Err(Exhausted::Cancelled);
            }
            if self.rlimit.is_some_and(|limit| after >= limit) {
                return Err(Exhausted::Rlimit);
            }
            if before / TICKS_PER_CLOCK_READ != after / TICKS_PER_CLOCK_READ {
                if let Some(why) = self.exhausted() {
                    return Err(why);
                }
            }
            Ok(())
        }

        pub(crate) fn exhausted(&self) -> Option<Exhausted> {
            if self.cancelled() {
                return Some(Exhausted::Cancelled);
            }
            if self.rlimit.is_some_and(|limit| self.ticks() >= limit) {
                return Some(Exhausted::Rlimit);
            }
            if self
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
            {
                return Some(Exhausted::Deadline);
            }
            if ay_sys::process_memory_exceeded() {
                return Some(Exhausted::Memory);
            }
            None
        }

        pub(crate) fn should_stop(&self) -> bool {
            self.exhausted().is_some()
        }

        fn cancelled(&self) -> bool {
            process_cancelled()
                || self
                    .cancel
                    .as_ref()
                    .is_some_and(|flag| flag.load(Ordering::Relaxed))
        }
    }
}

const ROUNDS: usize = 9;
const DEPTHS: usize = 4;

/// One timing of `iterations` calls, in ns per call.
fn per_call(iterations: u64, mut call: impl FnMut()) -> f64 {
    let start = Instant::now();
    for _ in 0..iterations {
        call();
    }
    start.elapsed().as_secs_f64() * 1e9 / iterations as f64
}

/// A node `depth` levels below the root, each level with the same limits.
fn node_at(depth: usize, flag: &Arc<AtomicBool>, deadline: Instant) -> Guard {
    let spec = || {
        ChildSpec::new(NodeLabel::Check)
            .with_external(Arc::clone(flag))
            .with_deadline(DeadlineSource::Fixed(deadline))
            .with_rlimit(Some(u64::MAX))
    };
    (1..depth).fold(Guard::root_child(spec()), |node, _| node.child(spec()))
}

fn main() {
    let measure = std::env::args().any(|arg| arg == "--bench");
    let (ticks, polls) = if measure {
        (4_000_000, 400_000)
    } else {
        (2_000, 200)
    };
    let flag = Arc::new(AtomicBool::new(false));
    let deadline = Instant::now() + Duration::from_secs(3600);
    let old = baseline::ResourceGuard {
        deadline: Some(deadline),
        cancel: Some(Arc::clone(&flag)),
        rlimit: Some(u64::MAX),
        ..baseline::ResourceGuard::default()
    };
    let nodes: Vec<Guard> = (1..=DEPTHS)
        .map(|depth| node_at(depth, &flag, deadline))
        .collect();
    // Best round of each series: [old, depth 1..=4], for tick and for poll.
    let mut tick = [f64::INFINITY; DEPTHS + 1];
    let mut poll = [f64::INFINITY; DEPTHS + 1];
    for _ in 0..ROUNDS {
        let round_tick = per_call(ticks, || {
            let _ = black_box(black_box(&old).tick(1));
        });
        let round_poll = per_call(polls, || {
            black_box(black_box(&old).should_stop());
        });
        tick[0] = tick[0].min(round_tick);
        poll[0] = poll[0].min(round_poll);
        for (at, node) in nodes.iter().enumerate() {
            let round_tick = per_call(ticks, || {
                let _ = black_box(black_box(node).tick(1));
            });
            let round_poll = per_call(polls, || {
                black_box(black_box(node).should_stop());
            });
            tick[at + 1] = tick[at + 1].min(round_tick);
            poll[at + 1] = poll[at + 1].min(round_poll);
        }
    }
    println!(
        "M2 baseline ResourceGuard: tick(1) {:.2} ns, should_stop() {:.2} ns",
        tick[0], poll[0]
    );
    for depth in 1..=DEPTHS {
        println!(
            "M2 GuardTree depth {depth}: tick(1) {:.2} ns ({:.2}x), should_stop() {:.2} ns ({:.2}x)",
            tick[depth],
            tick[depth] / tick[0],
            poll[depth],
            poll[depth] / poll[0]
        );
    }
    if !measure {
        println!("M2: smoke run (no --bench); the numbers above are not a measurement");
    }
}
