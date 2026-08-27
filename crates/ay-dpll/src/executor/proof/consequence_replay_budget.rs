// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Query-owned cumulative WALL envelope for consequence-replay ground probes.
//!
//! # Why this exists
//!
//! `authored_consequence_replay` discharges a quantified refutation by
//! re-deciding its ground consequences on a disposable executor
//! (`checked_same_context_unsat_proof`). That probe is bounded by a
//! plan-shaped **wall-clock** deadline: 2 s for a standard plan and 5 s for a
//! positive-Skolem plan. The probe's cost is paid out of the ENCLOSING query's
//! publication envelope: whatever the probe spends, certification and the
//! certificate mint no longer have.
//!
//! Until this envelope existed, the then-single probe budget was a per-probe
//! cap with nothing capping the probe COUNT. `MAX_REPLAY_ATTEMPTS` is per
//! *consequence-replay scope*, and `take_consequence_replay_state` hands each
//! nested scope a fresh pair, so one public `check-sat` pays
//! `scopes x MAX_REPLAY_ATTEMPTS x per-probe cap` in the worst case with the
//! scope count unbounded by anything this lane controls.
//!
//! That is what `9e5793ba81` ("certify finite frame consequence proofs")
//! tripped over. It raised the former single cap from 2 s to 5 s because the
//! u64 frame obligation genuinely needs more than 2 s to discharge — a real
//! capability. On `sum_datatype_forall` that raise multiplied out to
//! 4 x 5 s = 20.0 s of probes that decline 4/4, on a query whose ACTUAL
//! refutation costs 47 ms, and the six demand-lane tests (15 s / 20 s caps)
//! went `unsat -> unknown`. The refutation was still derived and still
//! publishable; the lane had simply eaten the clock it needed to be published
//! in. Restoring publication is therefore a matter of bounding the lane's
//! TOTAL spend, not of lowering the per-probe cap the frame proof needs.
//!
//! # Shape
//!
//! Modelled on [`crate::executor::theories::ProofCheckpointBudget`], the other
//! query-owned cumulative envelope: replenished ONLY at the external
//! API/command decision boundary (`begin_external_decision_query`), never by a
//! nested solve, a cascade retry, or an internal probe. Nested corroboration
//! executors (`reconfirms_unsat_within`) construct their own `Executor` and so
//! start with a full envelope of their own; that is deliberate — starving a
//! corroboration re-solve of the lane it needs to build its proof would turn a
//! publication regression into a certification regression.
//!
//! # Soundness
//!
//! Declining a probe can only make this lane return `None`, which the caller
//! treats exactly like "the probe found no strict proof": no verdict, no
//! certificate, no proof step depends on how much budget was left. The
//! envelope can withhold a completeness attempt; it can never admit one.

use ay_core::time::Instant;

use crate::executor::Executor;

/// Total wall time one external decision query may spend inside
/// consequence-replay ground probes, across every scope and retry.
///
/// Deliberately equal to the largest plan-shaped per-probe budget: one
/// positive-Skolem probe may still take the whole 5 s the u64 frame obligation
/// needs, while standard probes remain capped at 2 s and four scopes can no
/// longer take 20 s cumulatively.
pub(in crate::executor) const QUERY_PROBE_BUDGET_MS: u64 = 5_000;

/// Floor under a granted slice. A probe that gets less than this cannot reach
/// a strict-complete proof on any input this lane has been measured on, so
/// granting it only converts the remaining envelope into latency.
const MIN_PROBE_BUDGET_MS: u64 = 250;

/// Largest fraction of the caller's REMAINING deadline a single probe may
/// claim, as a divisor. The envelope above is absolute; this one is relative,
/// and is what keeps the lane from consuming a short caller timeout down to
/// zero before certification and the mint have run at all.
const DEADLINE_SHARE_DIVISOR: u32 = 2;

/// Query-owned cumulative envelope. It deliberately does not live in the
/// consequence-replay state that `take_consequence_replay_state` swaps: that
/// per-scope save/restore is exactly the mechanism that multiplied the cost.
#[derive(Debug)]
pub(in crate::executor) struct ConsequenceReplayProbeBudget {
    remaining_ms: u64,
    /// Wall milliseconds HANDED OUT since the last external query boundary,
    /// net of refunds. This is the quantity the regression made unbounded, so
    /// it is the quantity a barrier test can assert on without measuring the
    /// host's clock: grants are decided by this module, elapsed time is not.
    granted_ms: u64,
}

impl Default for ConsequenceReplayProbeBudget {
    fn default() -> Self {
        Self {
            remaining_ms: QUERY_PROBE_BUDGET_MS,
            granted_ms: 0,
        }
    }
}

/// A granted slice of the envelope, already deducted.
///
/// Pre-deduction is the fail-closed direction: if a probe panics or a future
/// edit forgets to settle, the query has spent the slice rather than kept it.
#[derive(Clone, Copy, Debug)]
pub(in crate::executor) struct ProbeGrant {
    granted_ms: u64,
}

impl ProbeGrant {
    /// Wall budget to hand the disposable probe executor.
    pub(in crate::executor) fn budget_ms(self) -> u64 {
        self.granted_ms
    }
}

impl ConsequenceReplayProbeBudget {
    /// Re-arm at the outer API/command query boundary. Internal authority
    /// restarts, cascade retries, and nested solves must not call this.
    pub(in crate::executor) fn begin_external_query(&mut self) {
        self.remaining_ms = QUERY_PROBE_BUDGET_MS;
        self.granted_ms = 0;
    }

    /// Deduct and return the slice a probe may run for, or `None` when this
    /// query has no useful wall time left to give it.
    ///
    /// `per_probe_cap_ms` is the lane's own per-probe ceiling; `deadline` is
    /// the caller's live solve deadline, if any.
    pub(in crate::executor) fn claim(
        &mut self,
        per_probe_cap_ms: u64,
        deadline: Option<Instant>,
    ) -> Option<ProbeGrant> {
        let mut granted = per_probe_cap_ms.min(self.remaining_ms);
        if let Some(deadline) = deadline {
            let remaining_deadline_ms = u64::try_from(
                deadline
                    .saturating_duration_since(Instant::now())
                    .as_millis(),
            )
            .unwrap_or(u64::MAX);
            granted = granted.min(remaining_deadline_ms / u64::from(DEADLINE_SHARE_DIVISOR));
        }
        if granted < MIN_PROBE_BUDGET_MS {
            return None;
        }
        self.remaining_ms = self.remaining_ms.saturating_sub(granted);
        self.granted_ms = self.granted_ms.saturating_add(granted);
        Some(ProbeGrant {
            granted_ms: granted,
        })
    }

    /// Return the unspent remainder of a grant. `spent_ms` is measured wall
    /// time; anything at or above the grant refunds nothing.
    pub(in crate::executor) fn settle(&mut self, grant: ProbeGrant, spent_ms: u64) {
        let refund = grant.granted_ms.saturating_sub(spent_ms);
        self.remaining_ms = self
            .remaining_ms
            .saturating_add(refund)
            .min(QUERY_PROBE_BUDGET_MS);
        self.granted_ms = self.granted_ms.saturating_sub(refund);
    }

    /// Remaining envelope, for `--trace-cegqi-attr` attribution and tests.
    pub(in crate::executor) fn remaining_ms(&self) -> u64 {
        self.remaining_ms
    }

    /// Wall milliseconds granted to probes since the last external query
    /// boundary, net of refunds. The invariant a barrier test pins:
    /// `granted_ms() <= QUERY_PROBE_BUDGET_MS`, for any number of scopes.
    pub(in crate::executor) fn granted_ms(&self) -> u64 {
        self.granted_ms
    }

    #[cfg(test)]
    pub(in crate::executor) fn set_remaining_ms(&mut self, remaining_ms: u64) {
        self.remaining_ms = remaining_ms;
    }
}

impl Executor {
    /// Run ONE consequence-replay ground probe under this query's cumulative
    /// wall envelope, or decline without running it.
    ///
    /// The probe's wall clock is spent out of the enclosing query's
    /// PUBLICATION window: every millisecond here is one certification and the
    /// certificate mint no longer have. `consequence_replay_attempts` cannot
    /// bound that spend — it is per consequence-replay SCOPE and
    /// `take_consequence_replay_state` hands each nested scope a fresh pair —
    /// so the ceiling that matters is metered here instead.
    pub(in crate::executor) fn metered_consequence_replay_probe(
        &mut self,
        consequences: &[ay_core::TermId],
        per_probe_cap_ms: u64,
    ) -> Option<ay_core::Proof> {
        use crate::executor::quantifier_loop::result_mapping::SameContextProbeOutcome;

        // First attempt: window-scoped array-axiom surface. This is the
        // #7956 posture — a derived window on the shared store must not let
        // the fixpoint seed hundreds of phantom congruence axioms from the
        // outer solve's dead array-equality terms.
        match self.granted_consequence_replay_probe(consequences, per_probe_cap_ms, true)? {
            SameContextProbeOutcome::Proof(proof) => Some(proof),
            SameContextProbeOutcome::UnsatUnpromotable => {
                // (#frame-probe-unscoped-retry) The scoped probe refuted the
                // consequence set, but its conflicts fused into theory lemmas
                // the strict checker refuses — the shape a window with no
                // array-equality atom of its own produces, because every
                // congruence/extensionality seed was scoped away (measured on
                // the array-frame self-check fixture: scoped ext=0/ac=0 ->
                // fused 23-literal Generic; unscoped ext=2/ac=134 -> the same
                // probe's proof is strict-complete). Retry once with the
                // whole-store surface, under a fresh grant from the SAME
                // unchanged envelope. Verdict authority cannot widen: only
                // the raw-UNSAT-but-unpromotable outcome is retried, and the
                // retried proof still passes the probe's strict checker, the
                // stitcher, and the outer strict re-check before publication.
                match self.granted_consequence_replay_probe(
                    consequences,
                    per_probe_cap_ms,
                    false,
                )? {
                    SameContextProbeOutcome::Proof(proof) => Some(proof),
                    SameContextProbeOutcome::UnsatUnpromotable | SameContextProbeOutcome::Other => {
                        None
                    }
                }
            }
            SameContextProbeOutcome::Other => None,
        }
    }

    /// Claim one grant from the query envelope, run one same-context probe
    /// under it, settle the unspent remainder, and report the attribution.
    /// `None` means the envelope itself declined (no grant, no probe run).
    fn granted_consequence_replay_probe(
        &mut self,
        consequences: &[ay_core::TermId],
        per_probe_cap_ms: u64,
        scope_to_window: bool,
    ) -> Option<crate::executor::quantifier_loop::result_mapping::SameContextProbeOutcome> {
        use crate::executor::quantifier_loop::result_mapping::SameContextProbeOutcome;

        let deadline = self.solve_deadline.get();
        let Some(grant) = self
            .consequence_replay_probe_budget
            .claim(per_probe_cap_ms, deadline)
        else {
            super::authored_consequence_replay::replay_note(|| {
                "decline: query probe envelope exhausted; a refutation this lane \
                 would have stitched must now publish through another lane"
                    .to_string()
            });
            return None;
        };
        let started = Instant::now();
        let outcome =
            self.checked_same_context_unsat_proof(consequences, grant.budget_ms(), scope_to_window);
        let spent_ms = u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX);
        self.consequence_replay_probe_budget.settle(grant, spent_ms);
        super::authored_consequence_replay::replay_note(|| {
            format!(
                "probe(scoped={scope_to_window}): {}, {spent_ms}ms of a {}ms grant \
                 ({}ms granted, {}ms left in the query envelope)",
                match &outcome {
                    SameContextProbeOutcome::Proof(_) => "proof",
                    SameContextProbeOutcome::UnsatUnpromotable => "unsat but no strict proof",
                    SameContextProbeOutcome::Other => "no proof",
                },
                grant.budget_ms(),
                self.consequence_replay_probe_budget.granted_ms(),
                self.consequence_replay_probe_budget.remaining_ms(),
            )
        });
        Some(outcome)
    }
}

#[cfg(test)]
impl Executor {
    /// Wall milliseconds this query's consequence-replay lane has been granted
    /// for ground probes, net of refunds.
    ///
    /// Read by the envelope barrier test. It is deliberately an accounting
    /// read, not a clock read: the number of milliseconds HANDED OUT is decided
    /// by [`ConsequenceReplayProbeBudget::claim`] and is therefore stable on a
    /// loaded host, where elapsed wall time is not.
    pub(crate) fn consequence_replay_probe_ms_granted(&self) -> u64 {
        self.consequence_replay_probe_budget.granted_ms()
    }

    /// The per-query envelope, for the barrier test's upper bound.
    pub(crate) fn consequence_replay_probe_envelope_ms() -> u64 {
        QUERY_PROBE_BUDGET_MS
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn a_fresh_envelope_grants_the_whole_per_probe_cap() {
        let mut budget = ConsequenceReplayProbeBudget::default();
        let grant = budget.claim(5_000, None).expect("fresh envelope grants");
        assert_eq!(grant.budget_ms(), 5_000);
        assert_eq!(budget.remaining_ms(), 0);
    }

    /// The regression in one assertion: four probes that each burn their whole
    /// slice cost the query ONE envelope, not four per-probe caps.
    #[test]
    fn four_exhausting_probes_cost_one_envelope_not_four_caps() {
        let mut budget = ConsequenceReplayProbeBudget::default();
        let mut spent = 0;
        for _ in 0..4 {
            let Some(grant) = budget.claim(5_000, None) else {
                continue;
            };
            // A probe that exhausts its slice refunds nothing.
            budget.settle(grant, grant.budget_ms());
            spent += grant.budget_ms();
        }
        assert_eq!(
            spent, QUERY_PROBE_BUDGET_MS,
            "the lane's total wall spend per query must be the envelope, not 4 x the per-probe cap"
        );
    }

    #[test]
    fn an_unspent_grant_is_refunded_for_the_next_probe() {
        let mut budget = ConsequenceReplayProbeBudget::default();
        let first = budget.claim(5_000, None).expect("fresh envelope grants");
        budget.settle(first, 40);
        assert_eq!(budget.remaining_ms(), QUERY_PROBE_BUDGET_MS - 40);
        let second = budget.claim(5_000, None).expect("refunded envelope grants");
        assert_eq!(second.budget_ms(), QUERY_PROBE_BUDGET_MS - 40);
    }

    #[test]
    fn a_slice_below_the_floor_is_declined_rather_than_granted() {
        let mut budget = ConsequenceReplayProbeBudget::default();
        budget.set_remaining_ms(MIN_PROBE_BUDGET_MS - 1);
        assert!(budget.claim(5_000, None).is_none());
        assert_eq!(
            budget.remaining_ms(),
            MIN_PROBE_BUDGET_MS - 1,
            "a declined claim must not deduct"
        );
    }

    #[test]
    fn a_probe_may_not_claim_the_callers_whole_remaining_deadline() {
        let mut budget = ConsequenceReplayProbeBudget::default();
        let deadline = Instant::now() + Duration::from_secs(3);
        let grant = budget.claim(5_000, Some(deadline)).expect("grants a share");
        assert!(
            grant.budget_ms() <= 1_500,
            "a probe claimed {}ms of a 3000ms remaining deadline",
            grant.budget_ms()
        );
    }

    #[test]
    fn an_expired_deadline_declines_instead_of_granting() {
        let mut budget = ConsequenceReplayProbeBudget::default();
        let deadline = Instant::now();
        assert!(budget.claim(5_000, Some(deadline)).is_none());
    }

    #[test]
    fn the_external_query_boundary_replenishes() {
        let mut budget = ConsequenceReplayProbeBudget::default();
        let grant = budget.claim(5_000, None).expect("fresh envelope grants");
        budget.settle(grant, grant.budget_ms());
        assert_eq!(budget.remaining_ms(), 0);
        budget.begin_external_query();
        assert_eq!(budget.remaining_ms(), QUERY_PROBE_BUDGET_MS);
    }
}
