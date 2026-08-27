// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Query-owned cumulative WALL envelope for the quantified model gate.
//!
//! # Why this exists
//!
//! The quantified model gate is a SOUNDNESS gate: after the search engine
//! proposes `Sat`, every quantified conjunct must be confirmed against the
//! emitted model or the verdict fails closed to `Unknown`. Confirming a
//! conjunct whose matrix the ground evaluator cannot fold means re-deciding a
//! skolemized ground obligation on a disposable executor
//! (`quantified_gate_checked_ground_solve`), and that probe costs wall time out
//! of the enclosing query's publication window.
//!
//! Until this envelope existed the gate spent that time through TWO
//! independent, unrelated constants, neither of which bounded the query:
//!
//! * a flat **500 ms** per-probe cap at every
//!   `checked_ground_solve(.., 500)` call site, and
//! * a `Instant::now() + Duration::from_secs(2)` candidate-loop window armed
//!   FRESH on entry to each gate arm.
//!
//! The 500 ms cap was measured to be the binding constraint on
//! `Inc Equality_MachineArith`: on
//! `20170501-Heizmann-UltimateAutomizer/exp_loop_true-unreach-call.c.smt2` the
//! positive-existential FP obligation at
//! [`Executor::check_quantified_conjunct_against_model`]'s existential route
//! DECIDES `sat` — but needs 1.58–2.43 s to do it (73 samples, 73/73 decided,
//! zero undecided even at a 60 s budget). Under 500 ms it returns `None`, the
//! gate reports `Indeterminate("nested solve undecided")`, and a `sat` AY has
//! genuinely computed publishes as `unknown (incomplete)`.
//!
//! # Why not simply raise the constant
//!
//! Because `9e5793ba81` did exactly that on the consequence-replay lane and
//! shipped a regression: a per-attempt budget is a MULTIPLIER whenever nothing
//! caps the attempt count. The gate has the same shape. Raising 500 alone is
//! also inert — the 2 s loop window then binds instead — so a flat raise either
//! does nothing or does it four times over. Measured arm sites, all arming a
//! fresh 2 s window today:
//!
//! * [`Executor::apply_quantified_model_failclosed_gate`], the publication
//!   gate, itself reachable from four non-test callers, and
//! * [`Executor::quantified_model_gate_confirms_current_assertions`], the
//!   SAT-restoration confirmation, which runs BEFORE the publication gate on
//!   the same public `check-sat`.
//!
//! Inside one arm the fan-out is unbounded by anything the arm controls: the
//! candidate loop runs one probe per quantified conjunct, and the forall-exists
//! route probes once per witness TUPLE over a candidate cross-product.
//!
//! # Shape
//!
//! Modelled on [`crate::executor::proof::ConsequenceReplayProbeBudget`] and
//! [`crate::executor::theories::ProofCheckpointBudget`]: replenished ONLY at
//! the external API/command decision boundary
//! (`begin_external_decision_query`), never by `begin_public_solve`, a nested
//! solve, or a cascade retry. An arm claims a slice, pre-deducted; on close it
//! refunds whatever it did not spend, so a gate that confirms in 2 ms (the
//! measured non-FP case) costs the query nothing.
//!
//! One clamp does the work of two: the arm's slice is capped at half the
//! caller's REMAINING deadline, and the whole arm then runs under that slice as
//! its `solve_deadline`. Every probe inside is clamped to `solve_deadline` by
//! `qpf_probe_executor`, so bounding the arm bounds the probes transitively —
//! the gate can no longer eat a short `-T` down to zero and leave nothing for
//! `check_scope.finish`, model emission, or a following `(get-model)`.
//!
//! # Soundness
//!
//! Every direction this module can move is toward DECLINING. A smaller slice
//! makes a probe return `None`, which the gate treats exactly as "the nested
//! solve did not decide": `Indeterminate`, then `downgrade_sat_after_gate`,
//! then `Unknown`. A larger slice only lets an obligation the gate was already
//! going to check finish being checked. No verdict, model, certificate, or
//! proof step depends on how much budget was left, and the gate never accepts
//! an unchecked witness because it ran out of time — it fails closed, exactly
//! as before.

use std::time::Duration;

use ay_core::time::Instant;

/// Total wall time one external decision query may spend inside quantified
/// model-gate arms, across every arm, candidate and probe.
///
/// Sized from the measured need distribution plus the candidate loop's own
/// pre-probe work: with the loop window at 2 s the probes were observed being
/// cut off at 2,006–2,222 ms of gate wall, so ~500 ms above the per-probe cap
/// is what makes that cap reachable rather than dead weight.
pub(in crate::executor) const QUERY_GATE_BUDGET_MS: u64 = 3_000;

/// Per-probe ceiling for one gate ground obligation.
///
/// The measured need band on the target division is 1,579–2,426 ms over 73
/// samples with no tail whatsoever (nothing needed 5 s, let alone 30 s), so
/// 2,500 ms covers 100% of it. This is a CEILING, not a grant: the arm slice
/// and the caller's deadline are `min`'d against it downstream.
pub(in crate::executor) const GATE_PROBE_CAP_MS: u64 = 2_500;

/// Largest fraction of the caller's REMAINING deadline one gate arm may claim,
/// as a divisor. `QUERY_GATE_BUDGET_MS` is absolute; this one is relative, and
/// is what keeps the gate from consuming a short caller timeout down to zero
/// before the confirmation handoff and the model emission have run at all.
const DEADLINE_SHARE_DIVISOR: u64 = 2;

/// Query-owned cumulative envelope.
///
/// Deliberately owned by the `Executor` rather than by any per-arm or
/// per-scope state that is saved and restored: that save/restore is exactly
/// the mechanism that turns a per-call budget into a multiplier.
#[derive(Debug)]
pub(in crate::executor) struct QuantifiedGateProbeBudget {
    remaining_ms: u64,
    /// Wall milliseconds HANDED OUT since the last external query boundary,
    /// net of refunds. This is the quantity the flat constants left unbounded,
    /// so it is the quantity a barrier test can assert on without measuring the
    /// host's clock: grants are decided by this module, elapsed time is not.
    granted_ms: u64,
    /// Gate arms opened since the last external query boundary. Unlike
    /// `granted_ms` this is NOT refunded, so it is the clock-free measurement
    /// of fan-out: it counts arms even when every one of them returns in 0 ms.
    arms_opened: u32,
    /// Last per-probe ceiling handed to `checked_ground_solve` by a gate
    /// obligation. Test-only, and the only way a barrier can observe that the
    /// call site passes the budgeted constant rather than a flat literal.
    #[cfg(test)]
    last_probe_cap_ms: std::cell::Cell<u64>,
}

impl Default for QuantifiedGateProbeBudget {
    fn default() -> Self {
        Self {
            remaining_ms: QUERY_GATE_BUDGET_MS,
            granted_ms: 0,
            arms_opened: 0,
            #[cfg(test)]
            last_probe_cap_ms: std::cell::Cell::new(0),
        }
    }
}

/// A granted arm slice, already deducted.
///
/// Pre-deduction is the fail-closed direction: if an arm panics or a future
/// edit forgets to close it, the query has spent the slice rather than kept it.
#[derive(Clone, Copy, Debug)]
pub(in crate::executor) struct GateArmGrant {
    granted_ms: u64,
    opened: Instant,
}

impl GateArmGrant {
    /// Wall deadline this arm — and therefore every probe nested inside it —
    /// must not run past.
    pub(in crate::executor) fn deadline(self) -> Instant {
        self.opened + Duration::from_millis(self.granted_ms)
    }

    /// Wall milliseconds this arm was granted. Read by the barrier tests.
    #[cfg(test)]
    pub(in crate::executor) fn window_ms(self) -> u64 {
        self.granted_ms
    }

    /// Wall milliseconds actually elapsed since the arm opened.
    pub(in crate::executor) fn spent_ms(self) -> u64 {
        u64::try_from(self.opened.elapsed().as_millis()).unwrap_or(u64::MAX)
    }
}

impl QuantifiedGateProbeBudget {
    /// Re-arm at the outer API/command query boundary. Internal authority
    /// restarts, cascade retries, and nested solves must not call this.
    pub(in crate::executor) fn begin_external_query(&mut self) {
        self.remaining_ms = QUERY_GATE_BUDGET_MS;
        self.granted_ms = 0;
        self.arms_opened = 0;
    }

    /// Deduct and return the wall slice one gate arm may run for.
    ///
    /// Always returns a grant, possibly a zero-length one: an exhausted query
    /// then hands the arm an already-expired deadline, its candidate loop
    /// breaks on the first `solve_deadline.expired()` check, and the gate takes
    /// its existing `"gate budget exhausted"` fail-closed path. There is
    /// deliberately no second way to decline — one exhausted path is easier to
    /// keep sound than two.
    pub(in crate::executor) fn open_arm(&mut self, deadline: Option<Instant>) -> GateArmGrant {
        let mut granted = QUERY_GATE_BUDGET_MS.min(self.remaining_ms);
        if let Some(deadline) = deadline {
            let remaining_deadline_ms = u64::try_from(
                deadline
                    .saturating_duration_since(Instant::now())
                    .as_millis(),
            )
            .unwrap_or(u64::MAX);
            granted = granted.min(remaining_deadline_ms / DEADLINE_SHARE_DIVISOR);
        }
        self.remaining_ms = self.remaining_ms.saturating_sub(granted);
        self.granted_ms = self.granted_ms.saturating_add(granted);
        self.arms_opened = self.arms_opened.saturating_add(1);
        GateArmGrant {
            granted_ms: granted,
            opened: Instant::now(),
        }
    }

    /// Record the per-probe ceiling a gate obligation is about to hand to
    /// `checked_ground_solve`. Test-only observation point; compiles away
    /// entirely in a production build.
    #[cfg_attr(not(test), expect(unused_variables, reason = "test-only recorder"))]
    pub(in crate::executor) fn record_probe_cap(&self, cap_ms: u64) {
        #[cfg(test)]
        self.last_probe_cap_ms.set(cap_ms);
    }

    /// Return the unspent remainder of an arm slice. `spent_ms` is measured
    /// wall time; anything at or above the grant refunds nothing.
    pub(in crate::executor) fn close_arm(&mut self, grant: GateArmGrant, spent_ms: u64) {
        let refund = grant.granted_ms.saturating_sub(spent_ms);
        self.remaining_ms = self
            .remaining_ms
            .saturating_add(refund)
            .min(QUERY_GATE_BUDGET_MS);
        self.granted_ms = self.granted_ms.saturating_sub(refund);
    }

    /// Remaining envelope, for attribution and tests.
    #[cfg(test)]
    pub(in crate::executor) fn remaining_ms(&self) -> u64 {
        self.remaining_ms
    }

    /// Wall milliseconds granted to gate arms since the last external query
    /// boundary, net of refunds.
    ///
    /// Read by the fan-out barrier. It is deliberately an ACCOUNTING read, not
    /// a clock read: how many milliseconds were handed out is decided by
    /// [`QuantifiedGateProbeBudget::open_arm`] and is therefore stable on a
    /// loaded host, where elapsed wall time is not. The invariant it pins is
    /// `granted_ms() <= QUERY_GATE_BUDGET_MS`, for any number of arms.
    #[cfg(test)]
    pub(in crate::executor) fn granted_ms(&self) -> u64 {
        self.granted_ms
    }

    /// Gate arms opened since the last external query boundary.
    #[cfg(test)]
    pub(in crate::executor) fn arms_opened(&self) -> u32 {
        self.arms_opened
    }

    /// The per-probe ceiling most recently handed to `checked_ground_solve`.
    #[cfg(test)]
    pub(in crate::executor) fn last_probe_cap_ms(&self) -> u64 {
        self.last_probe_cap_ms.get()
    }

    #[cfg(test)]
    pub(in crate::executor) fn set_remaining_ms(&mut self, remaining_ms: u64) {
        self.remaining_ms = remaining_ms;
    }
}

impl crate::executor::Executor {
    /// Open a quantified-model-gate arm: claim a slice of this query's
    /// envelope and install it as the arm's `solve_deadline`, never extending
    /// an already-tighter outer deadline. Returns the grant and the caller's
    /// saved deadline, which [`Self::close_quantified_gate_arm`] needs back.
    ///
    /// Both arm sites go through here so neither can drift into re-arming a
    /// fresh per-arm constant, and so the install/restore pair stays one
    /// implementation rather than two copies that must agree.
    pub(in crate::executor) fn open_quantified_gate_arm(
        &mut self,
    ) -> (GateArmGrant, Option<Instant>) {
        let saved = self.solve_deadline.get();
        let arm = self.quantified_gate_probe_budget.open_arm(saved);
        let window = arm.deadline();
        self.set_deadline(match saved {
            Some(deadline) if deadline < window => Some(deadline),
            _ => Some(window),
        });
        (arm, saved)
    }

    /// Close a gate arm: restore the caller's deadline, then refund the part
    /// of the slice this arm did not spend. The measured non-FP case confirms
    /// in 0-2 ms, so outside the FP obligation the envelope is a no-op and the
    /// next arm still sees a full window.
    pub(in crate::executor) fn close_quantified_gate_arm(
        &mut self,
        arm: GateArmGrant,
        saved_deadline: Option<Instant>,
    ) {
        self.set_deadline(saved_deadline);
        self.quantified_gate_probe_budget
            .close_arm(arm, arm.spent_ms());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The conversion this envelope exists to enable: a fresh query hands the
    /// gate arm enough wall to reach the measured 1,579–2,426 ms need band,
    /// where the old flat 500 ms constant could not.
    #[test]
    fn a_fresh_envelope_covers_the_measured_need_band() {
        let mut budget = QuantifiedGateProbeBudget::default();
        let grant = budget.open_arm(None);
        assert!(
            grant.window_ms() >= 2_426,
            "an arm got {}ms, below the measured p100 need of 2426ms",
            grant.window_ms()
        );
        assert!(
            GATE_PROBE_CAP_MS >= 2_426,
            "the per-probe cap {GATE_PROBE_CAP_MS}ms cannot reach the measured p100 need"
        );
        assert!(
            QUERY_GATE_BUDGET_MS > GATE_PROBE_CAP_MS,
            "an envelope at or below the per-probe cap makes the cap dead weight: \
             the candidate loop's own pre-probe work would consume the difference"
        );
    }

    /// The 9e5793ba81 failure mode, in one assertion: N arms that each burn
    /// their whole slice cost the query ONE envelope, not N windows. This is
    /// the barrier against fan-out growth — it holds for any arm count,
    /// including arm sites that do not exist yet.
    #[test]
    fn many_exhausting_arms_cost_one_envelope_not_one_window_each() {
        for arms in [2_u64, 4, 8, 32] {
            let mut budget = QuantifiedGateProbeBudget::default();
            let mut spent = 0;
            for _ in 0..arms {
                let grant = budget.open_arm(None);
                // An arm that burns its whole slice refunds nothing.
                budget.close_arm(grant, grant.window_ms());
                spent += grant.window_ms();
            }
            assert_eq!(
                spent, QUERY_GATE_BUDGET_MS,
                "{arms} gate arms spent {spent}ms; the query envelope is \
                 {QUERY_GATE_BUDGET_MS}ms and must bound every arm cumulatively"
            );
            assert_eq!(budget.granted_ms(), QUERY_GATE_BUDGET_MS);
            assert_eq!(budget.remaining_ms(), 0);
        }
    }

    /// A cheap arm — the measured non-FP case confirms in 0–2 ms — must leave
    /// the envelope intact for the arm that actually needs it.
    #[test]
    fn an_unspent_arm_slice_is_refunded_for_the_next_arm() {
        let mut budget = QuantifiedGateProbeBudget::default();
        let first = budget.open_arm(None);
        budget.close_arm(first, 2);
        assert_eq!(budget.remaining_ms(), QUERY_GATE_BUDGET_MS - 2);
        let second = budget.open_arm(None);
        assert_eq!(second.window_ms(), QUERY_GATE_BUDGET_MS - 2);
        assert!(
            second.window_ms() >= 2_426,
            "a 2ms first arm starved the second down to {}ms",
            second.window_ms()
        );
    }

    /// Exhaustion hands out a zero-length window rather than a negative or
    /// wrapped one; the caller's deadline is then already expired and the gate
    /// fails closed.
    #[test]
    fn an_exhausted_envelope_grants_an_already_expired_window() {
        let mut budget = QuantifiedGateProbeBudget::default();
        budget.set_remaining_ms(0);
        let grant = budget.open_arm(None);
        assert_eq!(grant.window_ms(), 0);
        assert!(
            grant.deadline() <= Instant::now(),
            "a zero-length arm window must be already expired"
        );
        assert_eq!(budget.granted_ms(), 0);
    }

    /// The guard `ConsequenceReplayProbeBudget` has and the gate did not: one
    /// arm may not claim the caller's entire remaining deadline, or a `-T`
    /// with 2.5 s left is consumed whole and publication has nothing.
    #[test]
    fn an_arm_may_not_claim_the_callers_whole_remaining_deadline() {
        let mut budget = QuantifiedGateProbeBudget::default();
        let deadline = Instant::now() + Duration::from_millis(2_500);
        let grant = budget.open_arm(Some(deadline));
        assert!(
            grant.window_ms() <= 1_250,
            "an arm claimed {}ms of a 2500ms remaining deadline",
            grant.window_ms()
        );
        assert!(
            grant.deadline() < deadline,
            "the arm window must end strictly before the caller's deadline"
        );
    }

    /// A generous caller deadline must not be clipped below the envelope —
    /// the share guard is a ceiling, not a target.
    #[test]
    fn a_generous_deadline_still_yields_the_whole_envelope() {
        let mut budget = QuantifiedGateProbeBudget::default();
        let deadline = Instant::now() + Duration::from_secs(300);
        let grant = budget.open_arm(Some(deadline));
        assert_eq!(grant.window_ms(), QUERY_GATE_BUDGET_MS);
    }

    #[test]
    fn an_expired_deadline_grants_nothing() {
        let mut budget = QuantifiedGateProbeBudget::default();
        let grant = budget.open_arm(Some(Instant::now()));
        assert_eq!(grant.window_ms(), 0);
    }

    /// Only the external query boundary replenishes. If any nested lane could
    /// call this, the envelope would be the per-arm constant again.
    #[test]
    fn the_external_query_boundary_replenishes() {
        let mut budget = QuantifiedGateProbeBudget::default();
        let grant = budget.open_arm(None);
        budget.close_arm(grant, grant.window_ms());
        assert_eq!(budget.remaining_ms(), 0);
        budget.begin_external_query();
        assert_eq!(budget.remaining_ms(), QUERY_GATE_BUDGET_MS);
        assert_eq!(budget.granted_ms(), 0);
    }

    /// A close that reports more spend than it was granted must not inflate
    /// the envelope (the refund is saturating in the safe direction).
    #[test]
    fn an_overspent_arm_refunds_nothing() {
        let mut budget = QuantifiedGateProbeBudget::default();
        let grant = budget.open_arm(None);
        budget.close_arm(grant, grant.window_ms() + 10_000);
        assert_eq!(budget.remaining_ms(), 0);
        assert_eq!(budget.granted_ms(), QUERY_GATE_BUDGET_MS);
    }
}
