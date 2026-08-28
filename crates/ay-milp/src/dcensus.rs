// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DECISION CENSUS — an instrument for MECHANISM D, node-rate steering.
//!
//! # Why limit-invariance cannot see this
//!
//! the development design notes classified four ways the
//! branch-and-bound reads the clock, and measured two of them with a LOAD-FREE instrument
//! (`scripts/milp_limit_invariance.py`): solve one model at two `--limit` values, and if it
//! PROVES inside both, neither run was budget-bound, so the trees must match. That instrument
//! is blind to mechanism D **by construction**. D is not budget-coupled — it is
//! *rate*-coupled. `slow_tree`, `rins_rescue`, the node-cut `repay` and the two `on_pace`
//! sites all divide a node or bound count by ELAPSED WALL and branch on the quotient. Both
//! arms of a limit-invariance pair run on the same box at the same speed, so both see the
//! same rate and the instrument reads INVARIANT however hard the site is steering. The census
//! said so in its own residue section, and this module is the answer.
//!
//! # The instrument, and the false negative it is built to refuse
//!
//! The census REJECTED a firing counter, for a reason worth restating:
//!
//! > a counter that covers 12 of 258 steering sites reports 0 on a model it simply does not
//! > watch, and a 0 that reads as "reproducible" is precisely the instrument artifact this
//! > campaign exists to kill.
//!
//! That objection is fatal to a counter that records only FIRINGS, and this one does not.
//! Every site carries TWO counters:
//!
//!   * `evals` — how many times the predicate was REACHED and computed, and
//!   * `fires` — how many times it came out true (or, for a value-carrying site, how many
//!     times it changed the schedule).
//!
//! so `fires = 0` is never ambiguous. `evals = 0, fires = 0` means *this site is not on this
//! model's path* — the instrument is silent because there is nothing to see. `evals = N > 0,
//! fires = 0` means *the site ran N times and steered nothing* — that is evidence. The dump
//! prints EVERY site on EVERY run, `evals = 0` rows included, so a site that never ran is
//! visible as a blank rather than absent. A reader can therefore always tell "not watched"
//! from "watched and quiet", which is the exact distinction the rejected design could not make.
//!
//! # Coverage, stated so a clean census is not over-read
//!
//! This module watches SIX sites, and they are not a sample — they are the complete set of
//! NODE-RATE reads in `bab.rs`, enumerated structurally rather than by memory. The search
//! that produces them is:
//!
//! ```text
//! grep -n "nodes as f64 / \|/ solve_start.elapsed()\|/ t_start.elapsed()\|pace_rate\|proof_on_pace" \
//!     crates/ay-milp/src/bab.rs
//! ```
//!
//! which returns the two rate HELPERS (`proof_on_pace`, `pace_rate`) and exactly six call
//! sites, every one of which is instrumented here. That is the coverage claim: complete over
//! *rate* reads, and silent about the other three mechanisms (A anytime-stop, B share-of-
//! remaining, C multiple-of-observed-wall), which are the limit-invariance instrument's job
//! and are not re-measured here. It is NOT a claim to cover all 258 steering sites.
//!
//! Two of the six do not have a boolean verdict — the node-cut `repay` and the RINS
//! `wide_interval` compute a NUMBER from the rate and use it as a schedule offset — so those
//! carry a third counter, `steer`, the running sum of the value they produced. A `steer` sum
//! that moves between two runs at a fixed budget is the same kind of evidence a changed
//! `fires` count is.
//!
//! # Cost
//!
//! Zero when the feature is off. Every function below is `#[cfg]`-erased to a `const fn` with
//! an empty body in a default build, exactly as `acensus` is, because `rins_rescue` and
//! `slow_tree` sit in the node loop and a runtime-checked branch there is not free. Only a
//! measurement build asks for `--features dcensus`.

/// The node-rate steering sites. Keep in sync with `NAMES`.
#[derive(Clone, Copy)]
pub(crate) enum Site {
    /// `bab.rs` node-cut dry round: `repay = NODE_CUT_DRY_REPAY * sep_secs * (nodes/elapsed)`,
    /// then `next_cut_node = nodes + cut_every.max(repay)`. Value-carrying; `fires` counts the
    /// rounds where `repay` EXCEEDED the node ladder and therefore actually moved the schedule.
    NodeCutRepay = 0,
    /// `bab.rs` endgame gate: `pace_rate(&bound_hist, ...)` → `on_pace`. `fires` = on pace
    /// (which VETOES the endgame's Hamming-ball commitment).
    EndgameOnPace = 1,
    /// `bab.rs` RINS rescue: `(nodes + rate*remaining) < next_rins` — the cadence is
    /// unreachable at the current rate, so pull the fire in to now.
    RinsRescue = 2,
    /// `bab.rs` `slow_tree`: `(nodes/elapsed)*1.2 < rins_cadence/8`. Gates the ball arms
    /// (`tree_is_proof`), the polish re-fire, and the pull-chain `links`.
    SlowTree = 3,
    /// `bab.rs` RINS cadence gate: `proof_on_pace(...)` → `on_pace`, feeding
    /// `primal_bound_narrow` and the dry-pull backoff.
    RinsOnPace = 4,
    /// `bab.rs` RINS wide-gap rung: `wide_interval = clamp((nodes/elapsed)*1.2, 512, cad/8)`.
    /// Value-carrying; `fires` counts the evaluations where the rate CLAMP did not bind, i.e.
    /// where the rate itself chose the interval.
    RinsWideInterval = 5,
}

#[cfg(feature = "dcensus")]
pub(crate) const N_SITES: usize = 6;

#[cfg(feature = "dcensus")]
const NAMES: [&str; N_SITES] = [
    "node_cut_repay",
    "endgame_on_pace",
    "rins_rescue",
    "slow_tree",
    "rins_on_pace",
    "rins_wide_interval",
];

#[cfg(feature = "dcensus")]
mod counters {
    use super::N_SITES;
    use std::sync::atomic::AtomicU64;

    pub(super) static EVALS: [AtomicU64; N_SITES] = [const { AtomicU64::new(0) }; N_SITES];
    pub(super) static FIRES: [AtomicU64; N_SITES] = [const { AtomicU64::new(0) }; N_SITES];
    pub(super) static STEER: [AtomicU64; N_SITES] = [const { AtomicU64::new(0) }; N_SITES];
}

/// Record one evaluation of a boolean-verdict site.
#[cfg(feature = "dcensus")]
#[inline]
pub(crate) fn eval(site: Site, fired: bool) {
    use std::sync::atomic::Ordering::Relaxed;
    let i = site as usize;
    counters::EVALS[i].fetch_add(1, Relaxed);
    if fired {
        counters::FIRES[i].fetch_add(1, Relaxed);
    }
}

/// Record one evaluation of a VALUE-carrying site: `value` is the number the rate produced,
/// and `steered` says whether that number actually displaced what the schedule would
/// otherwise have used.
#[cfg(feature = "dcensus")]
#[inline]
pub(crate) fn value(site: Site, value: u64, steered: bool) {
    use std::sync::atomic::Ordering::Relaxed;
    let i = site as usize;
    counters::EVALS[i].fetch_add(1, Relaxed);
    counters::STEER[i].fetch_add(value, Relaxed);
    if steered {
        counters::FIRES[i].fetch_add(1, Relaxed);
    }
}

/// FEATURE OFF: erased. Not a runtime branch — no instruction survives in the node loop.
#[cfg(not(feature = "dcensus"))]
#[inline(always)]
pub(crate) const fn eval(_site: Site, _fired: bool) {}

/// FEATURE OFF: erased. See [`eval`].
#[cfg(not(feature = "dcensus"))]
#[inline(always)]
pub(crate) const fn value(_site: Site, _value: u64, _steered: bool) {}

/// The census. Empty unless the crate was built with the `dcensus` feature.
#[cfg(not(feature = "dcensus"))]
#[must_use]
pub fn dump() -> String {
    String::new()
}

/// The census: one line per site, ALWAYS all six, so `evals=0` is visible as a fact rather
/// than as an absent row. See the module docs for why that distinction is the whole design.
#[cfg(feature = "dcensus")]
#[must_use]
pub fn dump() -> String {
    use std::sync::atomic::Ordering::Relaxed;
    let mut s = String::new();
    for i in 0..N_SITES {
        s.push_str(&format!(
            // Lower-case prefix, matching `acensus`'s `acensus seg..` lines. An `AY_`-shaped
            // prefix would be picked up by `tests/env_ledger.rs`, which scans the crate source
            // for `AY_*` tokens and requires each to be a registered ENVIRONMENT knob — and
            // this is an output label, not an env name. (It failed exactly that way first.)
            "dcensus site={:<19} evals={:<10} fires={:<10} steer_sum={}\n",
            NAMES[i],
            counters::EVALS[i].load(Relaxed),
            counters::FIRES[i].load(Relaxed),
            counters::STEER[i].load(Relaxed),
        ));
    }
    s
}
