// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-theory runtime statistics for the LRA solver (#8841).
//!
//! Consolidates 39 telemetry counters that were previously flat fields on
//! `LraSolver`. Grouping them into a single sub-struct shrinks the god-struct
//! constructor bodies (~39 lines each) and clarifies that these fields are
//! pure telemetry: they are incremented/read internally and reported via
//! `collect_statistics()`, never driving control flow outside of the per-check
//! pivot budget (`check_pivot_count`).
//!
//! All fields start at 0 except where noted. `Default::default()` initializes
//! the struct, letting the solver constructors replace ~39 lines of explicit
//! zero assignments with a single `stats: LraStats::default()`.

/// Per-theory runtime statistics (#4706, consolidated in #8841).
///
/// Every field is either a monotonically-increasing counter or a running
/// maximum. None of these fields are read by callers outside the LRA crate —
/// they are exposed only through `TheorySolver::collect_statistics()` as
/// `(name, u64)` pairs for stat dumps (`--stats` / `--stats-json`).
#[derive(Debug, Default, Clone)]
pub(crate) struct LraStats {
    // ----- Core check/conflict/propagation counters -----
    /// Number of `check()` calls.
    pub(crate) check_count: u64,
    /// Number of theory conflicts detected.
    pub(crate) conflict_count: u64,
    /// Number of theory propagations emitted.
    pub(crate) propagation_count: u64,

    // ----- BCP/check skip telemetry -----
    /// Number of times the propagation-time simplex budget was exhausted (#8003).
    pub(crate) propagation_budget_exhaustions: u64,
    /// Number of BCP-time simplex calls skipped after many conflicts (#8901).
    pub(crate) bcp_simplex_skips: u64,
    /// Number of BCP `check_during_propagate` calls where the post-simplex
    /// propagation was fast-skipped because no simplex ran and nothing
    /// changed (#8255).
    pub(crate) bcp_post_simplex_fast_skips: u64,
    /// Number of `assert_literal` calls that skipped setting `dirty=true`
    /// because the same `(term, value)` was already asserted (#8255).
    pub(crate) assert_dirty_skips: u64,
    /// Number of `propagate_impl` calls that skipped `compute_implied_bounds`
    /// because `check_during_propagate` already ran it (#8468).
    pub(crate) propagate_implied_bounds_fresh_skips: u64,
    /// Number of conflicts found by the full `check_impl()` at complete
    /// assignment (#8008).
    pub(crate) full_check_conflict_count: u64,

    // ----- Reason materialization telemetry -----
    /// Number of propagated reasons that were already materialized when queued.
    pub(crate) eager_reason_count: u64,
    /// Number of propagated reasons materialized from a `DeferredReason` on drain.
    pub(crate) deferred_reason_count: u64,
    /// Number of reasons materialized from `DeferredReason::DirectBound` (#6617 Phase 3).
    pub(crate) deferred_direct_count: u64,
    /// Number of reasons materialized from `DeferredReason::Interval` (#8151 Phase 3).
    pub(crate) deferred_interval_count: u64,
    /// Number of reasons materialized from `DeferredReason::ImpliedBound` via
    /// lazy `explain_propagation()` (#8467 Phase 4).
    pub(crate) deferred_implied_count: u64,
    /// Number of lazy propagations emitted (reason_data set, empty reason Vec).
    pub(crate) lazy_emitted_count: u64,
    /// Number of lazy propagations where `explain_propagation()` returned None.
    pub(crate) lazy_rejected_count: u64,

    // ----- Emission telemetry (#8452) -----
    /// Count of `DirectBound` propagations emitted from the `propagate_impl()` drain.
    pub(crate) emitted_direct_count: u64,
    /// Count of `ImpliedBound` propagations emitted from the drain.
    pub(crate) emitted_implied_count: u64,
    /// Count of `ImpliedRow` propagations emitted from the drain.
    pub(crate) emitted_implied_row_count: u64,

    // ----- Stale-reason guard telemetry -----
    /// Propagations dropped by the stale-reason filter (#9031).
    pub(crate) stale_reason_filtered_count: u64,
    /// Conflicts rejected by the release-mode stale-reason guard (#8764).
    pub(crate) stale_conflict_rejected_count: u64,
    /// Unjustified bounds retracted from infeasible rows after an empty
    /// conflict (#A2 conflict_without_literals livelock fix).
    pub(crate) unjustified_bound_retractions: u64,

    // ----- Simplex/pivot counters -----
    /// Number of `check()` calls where simplex returned SAT.
    pub(crate) simplex_sat_count: u64,
    /// Cumulative pivot count across ALL `dual_simplex` calls.
    pub(crate) total_pivots: u64,
    /// Cumulative pivot count across FULL `dual_simplex` calls (budget input).
    pub(crate) full_check_pivots: u64,
    /// Number of `dual_simplex` calls that returned Unknown because the per-call
    /// budget was exhausted (not counting propagation-budget exhaustions).
    pub(crate) simplex_budget_exhaustions: u64,
    /// Number of `dual_simplex` calls skipped because the global pivot budget
    /// was exceeded.
    pub(crate) global_budget_exhaustions: u64,
    /// Per-check() pivot budget counter (#8003). Reset at the start of each
    /// check. When it exceeds `CHECK_PIVOT_BUDGET`, simplex returns Unknown.
    ///
    /// Unlike the other fields here, this is an operational per-check accumulator,
    /// not a cumulative telemetry counter, but it is reset to 0 alongside the
    /// rest and never leaves the solver.
    pub(crate) check_pivot_count: u32,
    /// Number of `check()` calls where the per-check pivot budget was exhausted.
    pub(crate) check_pivot_budget_exhaustions: u64,

    // ----- Cascade/fixpoint telemetry (#8008) -----
    /// Maximum inner cascade depth reached in `compute_implied_bounds()`.
    pub(crate) max_inner_cascade_depth: u32,
    /// Cumulative inner cascade rounds across all `compute_implied_bounds()` calls.
    pub(crate) total_inner_cascade_rounds: u64,
    /// Maximum outer fixpoint iterations reached in `run_post_simplex_propagation()`.
    pub(crate) max_outer_fixpoint_iters: u32,
    /// Cumulative outer fixpoint iterations.
    pub(crate) total_outer_fixpoint_iters: u64,
    /// Number of `compute_implied_bounds` calls where cascade depth was
    /// throttled to 1 (#8255).
    pub(crate) cascade_depth_throttles: u64,

    // ----- f64 pre-screening telemetry (#8606) -----
    /// Rows skipped by row-level f64 pre-screening in `compute_implied_bounds`.
    pub(crate) f64_rows_skipped: u64,
    /// Individual variable derivations skipped by per-variable f64 pre-screening.
    pub(crate) f64_vars_skipped: u64,

    // ----- Snapshot telemetry (#8255) -----
    /// Number of `save_feasible_snapshot` calls skipped because simplex did
    /// not pivot since the last snapshot.
    pub(crate) snapshot_pivot_skips: u64,

    // ----- JIT telemetry -----
    /// Count of propagations produced via the JIT fast path (#8262).
    pub(crate) jit_propagation_count: u64,
    /// Bounded evidence-only waits attempted for pending external code generation sparse substitutes.
    pub(crate) lra_external_codegen_backend_substitute_evidence_wait_attempts: u64,
    /// Waits that installed the matching sparse-substitute artifact in time.
    pub(crate) lra_external_codegen_backend_substitute_evidence_wait_hits: u64,
    /// Waits that reached the configured bound before installing a match.
    pub(crate) lra_external_codegen_backend_substitute_evidence_wait_timeouts: u64,
    /// Total non-blocking install polls performed by bounded evidence waits.
    pub(crate) lra_external_codegen_backend_substitute_evidence_wait_polls: u64,
    /// Total wall-clock microseconds spent in bounded evidence waits.
    pub(crate) lra_external_codegen_backend_substitute_evidence_wait_us_total: u64,

    // ----- LRA basis-region metadata telemetry (#8387) -----
    /// Safe simplex/theory boundaries that considered a basis-region candidate.
    pub(crate) lra_basis_region_boundary_checks: u64,
    /// Metadata-only basis-region requests accepted into the local queue.
    pub(crate) lra_basis_region_requests_queued: u64,
    /// Candidates skipped because external code generation region compilation was disabled.
    pub(crate) lra_basis_region_disabled_skips: u64,
    /// Candidates rejected by conservative eligibility validation.
    pub(crate) lra_basis_region_ineligible_skips: u64,
    /// Candidates dropped because the bounded metadata queue was full.
    pub(crate) lra_basis_region_queue_full_skips: u64,
    /// Bounded safe-boundary waits attempted after accepted basis-region submits.
    pub(crate) lra_basis_region_evidence_wait_attempts: u64,
    /// Basis-region waits that installed an artifact within the configured bound.
    pub(crate) lra_basis_region_evidence_wait_hits: u64,
    /// Basis-region waits that reached the configured bound before an install.
    pub(crate) lra_basis_region_evidence_wait_timeouts: u64,
    /// Total install polls performed by basis-region evidence waits.
    pub(crate) lra_basis_region_evidence_wait_polls: u64,
    /// Total wall-clock microseconds spent in basis-region evidence waits.
    pub(crate) lra_basis_region_evidence_wait_us_total: u64,

    // ----- Per-row adaptive precision stats (#8185) -----
    /// Rows currently at i64 precision.
    pub(crate) precision_i64_rows: u64,
    /// Rows currently at i128 precision.
    pub(crate) precision_i128_rows: u64,
    /// Rows currently at BigInt precision.
    pub(crate) precision_big_rows: u64,
}
