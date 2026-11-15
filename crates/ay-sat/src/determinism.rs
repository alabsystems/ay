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
//! Enabled via `--sat-deterministic-inproc` (see
//! [`deterministic_inproc_enabled`]); default [`DEFAULT_ON`]. That switch is
//! each solver's starting value: a solver carries its own
//! (`Solver::set_deterministic_inproc`), so an embedder can make one solve
//! clock-free, as ay-dpll does for every bit-blast solve under an SMT
//! `:rlimit`, without changing the process. The outer
//! `-t <ms>` total-solve timeout is deliberately *not* converted — it is the
//! user's stated wall-clock budget, not an internal scheduling decision.
//!
//! Clock-free since 2026-09-14 (owner decision): under the flag no decision of
//! the SAT solve reads elapsed time, so runs of one build write byte-identical
//! proofs under any CPU load. Besides the round, backbone, sweep and
//! preprocessing walls above, these are counted too:
//! - the per-round inprocessing overhead behind `adaptive_tick_scale` and the
//!   arena-compaction bias ([`overhead_ms_equiv`], `solver/det_work.rs`);
//! - lookahead ([`LOOKAHEAD_TICK_BUDGET`]), gate extraction and
//!   independent-support gate recovery ([`GATE_EXTRACT_DET_WORK_BUDGET`]), the
//!   binary backbone's watch scans, and the bounded-backbone backoff;
//! - the early lucky probes (occurrence visits), the GF(p) probe (elementary
//!   operations), the indep_enum head start and slice (sized from the
//!   configured budget, not the time remaining), and ay-xor's XOR finder
//!   (clauses scanned);
//! - the BVE cascade, the fastelim intra-round check, the BVE/transred
//!   proportional guard and the vivify-converge net are off, their counted
//!   partners in force.
//!
//! An UNSAT reached after the deadline or an interrupt is not published
//! under the flag, and the CLI refuses `--parallel`, `--cube-and-conquer` and
//! `--fallback-solver` with it. Only the `-t` stop still reads the clock.
//!
//! Soundness surface is zero: these budgets schedule *work*, never *truth*.
//! Verdicts stay guarded regardless of which passes ran or how far each got —
//! stopping a pass early only leaves optional simplification undone.

use std::sync::OnceLock;

/// Compile-time default for the deterministic inprocessing budgets when
/// `--sat-deterministic-inproc` is unset.
///
/// `false` = opt-in: the wall-clock budgets remain the default so the board's
/// default config is byte-identical to `main` (zero regression-floor risk),
/// and determinism is requested explicitly with `--sat-deterministic-inproc`.
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

/// Search ticks per millisecond of solver work: the calibration anchor of
/// [`ROUND_TICK_BUDGET`] (15M ticks for the 2000 ms round guard). Every wall
/// budget or wall measurement converted under [`deterministic_inproc_enabled`]
/// is written in milliseconds at this rate, so the constants below read as
/// the walls they replace. It is also the unit of a check's tick budget
/// (the development design notes DR-37), so an embedder that turns one of its own wall
/// windows into ticks (ay-chc's frame stall under an effort, P4a slice 8)
/// converts at this rate.
pub const TICKS_PER_MS: u64 = 7_500;
const _: () = assert!(ROUND_TICK_BUDGET == 2_000 * TICKS_PER_MS);

/// The per-round inprocessing overhead of #8099 (a round's work minus the
/// work of its timed passes) in counted work: `work_te` tick equivalents,
/// expressed as the milliseconds `adaptive_tick_scale` and the arena
/// compaction bias bucket at 1, 3, 8, 10 and 100 ms. A finished round is at
/// least one unit: zero means "no data" to the readers, which would give the
/// cheapest rounds the most conservative scale.
#[inline]
pub(crate) fn overhead_ms_equiv(work_te: u64) -> f64 {
    work_te.max(1) as f64 / TICKS_PER_MS as f64
}

/// Lookahead's 500 ms wall (`LOOKAHEAD_WALL_LIMIT_MS`) in search ticks. The
/// probes are decisions plus search propagation, so their work lands in
/// `search_ticks`, the unit [`TICKS_PER_MS`] was measured in.
pub(crate) const LOOKAHEAD_TICK_BUDGET: u64 = 500 * TICKS_PER_MS;

/// Gate extraction's 2 s wall (`GATE_EXTRACT_TIME_BUDGET_MS`, congruence) as
/// clause visits: 2,000 ms at [`TICKS_PER_MS`], one visit per tick. The
/// per-pivot loop charges each pivot's occurrences plus the clause visits of
/// its ITE base-pair scan. On most formulas the existing 20 x num_clauses
/// effort budget binds first, as it does against the wall. Independent-support
/// gate recovery uses the same budget for its own 2 s wall.
pub(crate) const GATE_EXTRACT_DET_WORK_BUDGET: u64 = 2_000 * TICKS_PER_MS;

/// Whether the deterministic (work-count) inprocessing budgets are active,
/// resolved once from `--sat-deterministic-inproc`:
/// - unset  => [`DEFAULT_ON`] (compile-time default)
/// - `"0"`  => forced OFF (wall-clock budgets; the kill switch)
/// - other  => forced ON (deterministic work-count budgets)
///
/// Cached in a `OnceLock` (mirrors the `AY_AB_*` flag convention) so the hot
/// per-pass gates never pay an env syscall.
#[inline]
pub fn deterministic_inproc_enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| match ay_core::sat_ab_switches().deterministic_inproc {
        None => DEFAULT_ON,
        Some(forced) => forced,
    })
}

/// Per-round `search_ticks` budget used when [`deterministic_inproc_enabled`]
/// is true. `AY_XP_INPROC_TICK_BUDGET=<positive int>` overrides the calibrated
/// [`ROUND_TICK_BUDGET`] default (for recalibration / experiments).
#[inline]
pub(crate) fn round_tick_budget() -> u64 {
    // B25: the recalibration env is retired; the named budget stands.
    ROUND_TICK_BUDGET
}

#[cfg(test)]
#[path = "determinism_tests.rs"]
mod tests;
