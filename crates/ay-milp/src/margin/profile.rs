// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `margin` so the public diagnostic keeps its API path.

// ------------------------------------------------------------------ telemetry
//
// THE MARGIN DUAL, MADE READABLE FROM OUTSIDE THE CRATE.
//
// [`ReframeInfo`] already carries the number the whole module exists to produce
// — the reframed dual bound, next to the trivial 0 of the zero objective — but
// it is crate-private and [`BabSession::check`] drops it, so an embedding
// consumer sees the mapped verdict and nothing else. That is precisely what
// makes an ENGAGED null unclassifiable from outside: a reframe that spent its
// whole deadline creeping toward the band and one that never moved off the root
// both return `Unknown`.
//
// Same shape the crate already uses for `sb_profile_line`: process-global
// atomics written at ONE site, a public one-liner reader, empty until something
// is sampled, and never read by the engine. Recording is unconditional because
// it is six relaxed stores per reframed SOLVE (not per node), and a diagnostic
// that must be armed in advance is not available on the run that surprises you.
// It is a process-global LAST-WRITE snapshot, not a per-call return value:
// concurrent reframes overwrite each other, which is why the reader is a
// diagnostic line rather than an API.

static REFRAMES: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static STATUS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static SENSE_IS_MAX: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
static DECIDED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
static BOUND_BITS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static THRESHOLD_BITS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static WALL_NANOS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// The statuses [`map_reframed`] can stamp, in a fixed order so the atomic
/// carries an index rather than a pointer. Index 0 is "nothing sampled".
const STATUSES: [&str; 8] = [
    "-",
    "OPTIMAL",
    "INFEASIBLE",
    "FEASIBLE_INCUMBENT",
    "FEASIBLE_UNDECIDED",
    "UNKNOWN",
    "UNBOUNDED",
    "BOUND",
];

/// One margin-reframe snapshot, as plain values.
#[derive(Debug, Clone, Copy, PartialEq)]
struct Snapshot {
    reframes: u64,
    status: &'static str,
    sense_is_max: bool,
    decided: bool,
    /// `NaN` when the outcome shape carried no bound at all.
    bound: f64,
    threshold: f64,
    wall_secs: f64,
}

/// Record one completed reframe. Never fails, never blocks, never branches on
/// anything the engine can observe.
///
/// `pub(crate)` because the reframed solve no longer runs only from
/// [`reframe`]: the session's shared nested helper drives the same solve for
/// BOTH marked-margin entries, and the profile line has to stay a fact about
/// whichever one ran rather than about the one that happened to keep the call.
pub(crate) fn record(
    sense: Sense,
    threshold: &BigRational,
    info: &ReframeInfo,
    wall: std::time::Duration,
) {
    use num_traits::ToPrimitive;
    use std::sync::atomic::Ordering::Relaxed;
    let status = STATUSES
        .iter()
        .position(|&name| name == info.reframed_status)
        .unwrap_or(0) as u64;
    let bound = info
        .reframed_bound
        .as_ref()
        .and_then(BigRational::to_f64)
        .unwrap_or(f64::NAN);
    STATUS.store(status, Relaxed);
    SENSE_IS_MAX.store(sense == Sense::Maximize, Relaxed);
    DECIDED.store(info.decided, Relaxed);
    BOUND_BITS.store(bound.to_bits(), Relaxed);
    THRESHOLD_BITS.store(threshold.to_f64().unwrap_or(f64::NAN).to_bits(), Relaxed);
    WALL_NANOS.store(wall.as_nanos().min(u128::from(u64::MAX)) as u64, Relaxed);
    // Published LAST: a nonzero count is the reader's signal that every other
    // field above belongs to a completed reframe.
    REFRAMES.fetch_add(1, Relaxed);
}

fn snapshot() -> Snapshot {
    use std::sync::atomic::Ordering::Relaxed;
    Snapshot {
        reframes: REFRAMES.load(Relaxed),
        status: STATUSES
            .get(STATUS.load(Relaxed) as usize)
            .copied()
            .unwrap_or("-"),
        sense_is_max: SENSE_IS_MAX.load(Relaxed),
        decided: DECIDED.load(Relaxed),
        bound: f64::from_bits(BOUND_BITS.load(Relaxed)),
        threshold: f64::from_bits(THRESHOLD_BITS.load(Relaxed)),
        wall_secs: WALL_NANOS.load(Relaxed) as f64 / 1e9,
    }
}

/// `distance` is signed TOWARD EXCLUSION: how far the dual still has to travel
/// to put the band out of reach, negative while it is still inside.
fn line_from(snapshot: Snapshot) -> String {
    if snapshot.reframes == 0 {
        return String::new();
    }
    let sense = if snapshot.sense_is_max {
        "maximize"
    } else {
        "minimize"
    };
    let distance = if snapshot.sense_is_max {
        snapshot.threshold - snapshot.bound
    } else {
        snapshot.bound - snapshot.threshold
    };
    let render = |value: f64| {
        if value.is_nan() {
            "-".to_owned()
        } else {
            format!("{value:.9}")
        }
    };
    format!(
        "MARGINREFRAME reframes={} status={} sense={sense} threshold={} bound={} \
         distance={} decided={} wall={:.3}s",
        snapshot.reframes,
        snapshot.status,
        render(snapshot.threshold),
        render(snapshot.bound),
        render(distance),
        snapshot.decided,
        snapshot.wall_secs,
    )
}

/// Machine-readable one-liner for the LAST margin reframe this process ran
/// through the ordinary [`BabSession::check`] entry. Empty when no reframe has
/// completed.
///
/// Diagnostics only, and a process-global last-write snapshot rather than a
/// per-call value: it can be contaminated by a concurrent or detached solve,
/// exactly like [`crate::sb_profile_line`], and it can never affect a verdict.
#[must_use]
pub fn margin_profile_line() -> String {
    line_from(snapshot())
}
