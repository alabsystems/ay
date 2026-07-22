// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Machine-independent (deterministic) inprocessing budgets.
//!
//! AY's inprocessing pass scheduling was historically bounded by **wall-clock
//! deadlines** (`INPROCESSING_ROUND_WALL_LIMIT_MS` and the per-pass backbone /
//! sweep `*_WALL_LIMIT_MS` caps). Because those deadlines are wall-clock,
//! host-load jitter shifts *which* passes fit inside a round / a pass, and on
//! trajectory-sensitive instances the diverged simplification cascades into
//! completely different searches. Measured on `f406e2b8` (base `97ce171d`),
//! four byte-identical `--competition -t 120000` runs produced four different
//! verdicts/trajectories (UNKNOWN@120s / SAT@16.9s / UNKNOWN@120s / SAT@9.1s).
//!
//! This module centralizes the opt-in conversion of those deadlines to
//! deterministic **work-count budgets** — `search_ticks` for the solver-side
//! passes (the same BCP/analysis work metric that already drives all of AY's
//! effort-proportional scheduling) and kitten ticks for the sweep sub-solver.
//! With a work-count budget the "which passes fit" decision is a deterministic
//! function of the search trajectory rather than of host load, so a given
//! (formula, seed) yields byte-identical verdicts and counters on every host.
//!
//! Enabled via `AY_AB_DETERMINISTIC_INPROC` (see
//! [`deterministic_inproc_enabled`]); default [`DEFAULT_ON`]. The outer
//! `-t <ms>` total-solve timeout is deliberately *not* converted — it is the
//! user's stated wall-clock budget, not an internal scheduling decision.
//!
//! Soundness surface is zero: these budgets schedule *work*, never *truth*.
//! Verdicts stay guarded regardless of which passes ran or how far each got —
//! stopping a pass early only leaves optional simplification undone.

use std::sync::OnceLock;

/// Compile-time default for the deterministic inprocessing budgets when
/// `AY_AB_DETERMINISTIC_INPROC` is unset.
///
/// `false` = opt-in: the wall-clock budgets remain the default so the board's
/// default config is byte-identical to `main` (zero regression-floor risk),
/// and determinism is requested explicitly with `AY_AB_DETERMINISTIC_INPROC=1`.
/// Flip to `true` once the tick-budget calibration has been validated to hold
/// the full regression floor with no lost solves.
pub(crate) const DEFAULT_ON: bool = false;

/// Per-inprocessing-round `search_ticks` budget — deterministic replacement for
/// the 2000ms `INPROCESSING_ROUND_WALL_LIMIT_MS` round guard.
///
/// Calibration anchor (wf_6503d3eb, base `97ce171d`): a per-round
/// `AY_XP_INPROC_TICK_DEBUG` trace on `f406e2b8` measured BCP-heavy rounds at
/// 6,558-10,910 search_ticks/ms (median ~7,500), so ~2000ms of round work is
/// ~15M search_ticks. Fixed (not formula-class scaled) to mirror the fixed
/// 2000ms wall budget it replaces. Overridable with `AY_XP_INPROC_TICK_BUDGET`.
pub(crate) const ROUND_TICK_BUDGET: u64 = 15_000_000;

/// Bounded-CDCL backbone per-call `search_ticks` budget — deterministic
/// replacement for its 200ms wall cap. `search_ticks` approximate memory-access
/// cost, so on the large-clause formulas the wall cap was designed to protect
/// (high per-conflict cost) the tick budget fires proportionally sooner — a
/// closer match to the wall's intent than a flat conflict count. ~200ms of
/// backbone work at ~7,500 ticks/ms ≈ 1.5M ticks. The pass keeps its
/// deterministic `backbone_conflict_budget` alongside this cap.
pub(crate) const BACKBONE_TICK_BUDGET: u64 = 1_500_000;

/// Binary-backbone ring-scan per-call `search_ticks` budget — deterministic
/// replacement for its 500ms wall cap (~500ms ≈ 3.75M ticks). The scan already
/// resumes across calls via `backbone_binary_cursor`, so a per-call tick budget
/// reproduces the wall cap's "many cheap bounded calls" coverage pattern.
pub(crate) const BACKBONE_BINARY_TICK_BUDGET: u64 = 3_750_000;

/// Whether the deterministic (work-count) inprocessing budgets are active,
/// resolved once from `AY_AB_DETERMINISTIC_INPROC`:
/// - unset  => [`DEFAULT_ON`] (compile-time default)
/// - `"0"`  => forced OFF (wall-clock budgets; the kill switch)
/// - other  => forced ON (deterministic work-count budgets)
///
/// Cached in a `OnceLock` (mirrors the `AY_AB_*` flag convention) so the hot
/// per-pass gates never pay an env syscall.
#[inline]
pub(crate) fn deterministic_inproc_enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(
        || match std::env::var("AY_AB_DETERMINISTIC_INPROC").ok().as_deref() {
            None => DEFAULT_ON,
            Some("0") => false,
            Some(_) => true,
        },
    )
}

/// Per-round `search_ticks` budget used when [`deterministic_inproc_enabled`]
/// is true. `AY_XP_INPROC_TICK_BUDGET=<positive int>` overrides the calibrated
/// [`ROUND_TICK_BUDGET`] default (for recalibration / experiments).
#[inline]
pub(crate) fn round_tick_budget() -> u64 {
    static BUDGET: OnceLock<u64> = OnceLock::new();
    *BUDGET.get_or_init(|| {
        std::env::var("AY_XP_INPROC_TICK_BUDGET")
            .ok()
            .and_then(|s| s.parse::<u64>().ok())
            .filter(|&b| b > 0)
            .unwrap_or(ROUND_TICK_BUDGET)
    })
}
