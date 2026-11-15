// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BCP-time Diophantine scratch analysis: when it is armed, and one run of it.
//!
//! Extracted from `check_during_propagate_inner` (which sits on its
//! function-size ceiling) so the arming policy can carry its own reasoning.
//!
//! ## Why the equality key alone is not the cache key
//! (#lia-bcp-dioph-bound-recheck)
//!
//! `try_diophantine_solve` is two computations behind one call:
//!
//! 1. Gaussian elimination over the asserted EQUALITIES, producing
//!    `dioph_cached_substitutions` / `dioph_cached_modular_gcds`. This half is
//!    a function of the equality set alone — the invariant `pop()` relies on
//!    ("they depend only on the asserted equality SET ... not on the
//!    inequality bounds that branch-and-bound and BMC backtracking churn") —
//!    so caching it on the equality key is exact.
//! 2. `check_substitution_bound_feasibility`: composed-substitution bound
//!    violation plus `check_substitution_joint_case_split`. This half reads
//!    the CURRENT integer bounds through
//!    `get_current_integer_bounds_with_reasons`, and a variable with no bound
//!    evaluates to `ValueSetEval::Unknown`, which the feasibility test must
//!    soundly read as "feasible".
//!
//! The BCP-time caller armed the whole call on
//! `dioph_equality_key != equality_key`, so half 2 inherited half 1's cache
//! gate without inheriting its invariant: it was evaluated exactly once per
//! equality-set change. On a query whose equalities are all top level — every
//! `ring_2exp*` cascade, and anything whose equalities are asserted at level 0
//! — that is exactly ONCE, at the weakest bound state of the entire solve, and
//! the "feasible" answer then stands for the rest of the search even though
//! branch-and-bound goes on to establish the very bounds that decide it.
//!
//! Measured on `benchmarks/smt/QF_LIA/ring_2exp16_5vars_cascade_v2_unsat.smt2`
//! under `(set-option :produce-proofs true)`, where the proof lane's disabled
//! second variable-substitution round leaves the `(mod x 3)` divmod encoding
//! in the theory: the `_divmod_q_*` quotient variables carry no bound when the
//! one analysis runs, the joint case split reports its 16-assignment carry
//! space feasible, and the eager split loop then spends ~300 s in integer
//! branch-and-bound before giving up. With the periodic bound re-check below
//! the same query reaches its conflict in 0.4 s (71 conflicts, 433 decisions);
//! mandatory strict certification then rejects the refutation's unsupported
//! steps and the query degrades to a prompt fail-closed `unknown`, exactly as
//! its `ring_2exp16_5vars_cascade` sibling already did.
//!
//! The re-check is bounded twice over, so what it adds is deterministic and
//! machine-independent: `DIOPH_BCP_BOUND_RECHECK_STRIDE` BCP checks must pass
//! between two of them, and `MAX_BCP_DIOPH_BOUND_RECHECKS` caps how many a
//! single search phase may spend. Exhausting the cap restores exactly the
//! pre-repair behaviour, so the cost of the bound is COMPLETENESS, never
//! soundness: a skipped re-check can only delay a conflict, never invent one.

use super::*;

/// Consecutive unproductive BCP-time Dioph runs before the analysis is
/// deferred to the post-SAT final check for the rest of the search phase.
///
/// Search-phase deferral (#nip benchmark): the from-scratch BCP-time Dioph
/// solve ran on EVERY equality-key change — on boundary-pattern problems that
/// is every decision (~205 ms each, ~100% of solve time). Skipping conflict
/// DETECTION mid-search only delays the conflict; it can never accept a wrong
/// SAT, because `needs_final_check_after_sat() == true` guarantees a non-search
/// full check before any SAT is accepted.
const BCP_DIOPH_UNPRODUCTIVE_LIMIT: u32 = 4;

/// BCP checks that must pass between two bound re-checks of an unchanged
/// equality set. The stride is what keeps the re-check off the per-decision
/// cost path that `BCP_DIOPH_UNPRODUCTIVE_LIMIT` exists to protect, and the
/// added work scales as 1/stride: measured on
/// `lia_incremental_bmc_stress::test_bmc_with_mod_100_steps_mixed` (100
/// push/pop check-sats over `mod` constraints, the heaviest re-check consumer
/// in the suite, then at 51.7 s against a 60 s wall cap, since replaced by a
/// 30 s bound on the solving thread's CPU), a stride of 64 cost +3 to +7 s
/// where 512 costs under a second.
const DIOPH_BCP_BOUND_RECHECK_STRIDE: u32 = 512;

/// Bound re-checks one search phase may spend. Each costs one from-scratch
/// Dioph solve of a system already capped at `DIOPH_SIZE_CAP` cells, so this
/// is the deterministic ceiling on the work the repair adds to a search that
/// never converges. The cascade_v2 refutation above reaches its conflict
/// well inside it.
const MAX_BCP_DIOPH_BOUND_RECHECKS: u32 = 128;

/// Arming state for the BCP-time Diophantine analysis.
#[derive(Debug, Default)]
pub(crate) struct BcpDiophState {
    /// Consecutive UNPRODUCTIVE runs (no conflict found). Past
    /// `BCP_DIOPH_UNPRODUCTIVE_LIMIT` the analysis is deferred to the post-SAT
    /// final check for the rest of the search phase. Reset by
    /// `set_search_phase` and by a bound re-check (a run on NEW input, not a
    /// repeat of the cached one) — NOT by `pop`, which an earlier revision of
    /// the field's comment claimed.
    unproductive_streak: u32,
    /// BCP checks since the analysis last ran, for the stride above.
    ticks_since_run: u32,
    /// Bound re-checks spent by this search phase.
    bound_rechecks: u32,
}

impl BcpDiophState {
    /// Reset at a search-phase boundary (`TheorySolver::set_search_phase`).
    pub(crate) fn reset_for_search_phase(&mut self) {
        *self = Self::default();
    }
}

/// What one armed BCP-time Dioph analysis did.
pub(crate) enum BcpDiophOutcome {
    /// The analysis proved integer infeasibility; these are its reasons.
    Conflict(Vec<TheoryLit>),
    /// The analysis was deferred to the post-SAT final check.
    Deferred,
    /// The analysis ran and found nothing; its scratch caches must be cleared
    /// once this check's remaining Dioph-derived consumers have read them.
    Ran,
}

impl LiaSolver<'_> {
    /// Whether the equality key is empty, and whether the BCP-time Dioph
    /// analysis is armed for this check.
    pub(super) fn bcp_dioph_arm(&mut self) -> (bool, bool) {
        // #C5: served from the incrementally maintained assertion view — no
        // per-BCP O(asserted) re-scan + sort.
        let (equality_key_empty, key_changed) = {
            let equality_key = self.equality_key();
            (
                equality_key.is_empty(),
                !equality_key.is_empty() && self.dioph_equality_key != equality_key,
            )
        };
        if key_changed {
            return (equality_key_empty, true);
        }
        if equality_key_empty {
            self.dioph_bcp.ticks_since_run = 0;
            return (true, false);
        }
        (false, self.dioph_bcp_bound_recheck_due())
    }

    /// Whether an unchanged equality set is due a bound re-check: its
    /// feasibility half reads bounds the search has moved since the last run
    /// (#lia-bcp-dioph-bound-recheck).
    fn dioph_bcp_bound_recheck_due(&mut self) -> bool {
        self.dioph_bcp.ticks_since_run = self.dioph_bcp.ticks_since_run.saturating_add(1);
        if self.dioph_bcp.ticks_since_run < DIOPH_BCP_BOUND_RECHECK_STRIDE
            || self.dioph_bcp.bound_rechecks >= MAX_BCP_DIOPH_BOUND_RECHECKS
        {
            return false;
        }
        self.dioph_bcp.bound_rechecks += 1;
        // A run against a bound state the cached answer never saw, not a
        // repeat of it: the unproductive streak counts repeats, so it must not
        // veto this one.
        self.dioph_bcp.unproductive_streak = 0;
        true
    }

    /// Run one armed BCP-time Dioph analysis.
    pub(super) fn bcp_dioph_run(&mut self, debug: bool) -> BcpDiophOutcome {
        // The cache invalidation MUST run unconditionally: stale Dioph
        // substitutions under an outdated equality key are unsound for any
        // downstream consumer.
        self.dioph_equality_key.clear();
        self.clear_dioph_equality_caches();
        self.dioph_modified_bounds = false;
        self.dioph_bound_term_ids.clear();
        self.dioph_bcp.ticks_since_run = 0;

        if self.in_search_phase
            && self.dioph_bcp.unproductive_streak >= BCP_DIOPH_UNPRODUCTIVE_LIMIT
        {
            // Adaptive deferral: this search's BCP-time Dioph runs have been
            // consistently unproductive — stop paying the from-scratch
            // elimination per decision and let the post-SAT final check
            // (guaranteed by needs_final_check_after_sat) cover completeness.
            // Productive searches (modular-cascade class, #8736) never reach
            // the limit and keep their early Dioph conflicts.
            self.dioph_needs_full_check = true;
            return BcpDiophOutcome::Deferred;
        }

        if let Some(reasons) = self.timed_try_diophantine_solve() {
            if debug {
                safe_eprintln!("[LIA] BCP-time Dioph solve detected UNSAT");
            }
            self.dioph_bcp.unproductive_streak = 0;
            return BcpDiophOutcome::Conflict(reasons);
        }
        self.dioph_bcp.unproductive_streak = self.dioph_bcp.unproductive_streak.saturating_add(1);

        // NOTE: nothing between the key comparison in `bcp_dioph_arm` and this
        // point mutates `asserted`, so the view's equality key is unchanged and
        // this clone equals the compared key (#C5).
        self.dioph_equality_key = self.equality_key().to_vec();
        self.dioph_needs_full_check = true;
        BcpDiophOutcome::Ran
    }
}
