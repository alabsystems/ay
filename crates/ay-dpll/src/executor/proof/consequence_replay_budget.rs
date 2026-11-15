// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Query-owned cumulative envelope for consequence-replay ground probes,
//! counted in split-loop round trips and backstopped by wall time.
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
//! # Counted, not timed (#deterministic-probe-metering)
//!
//! A probe used to stop at its wall grant. A same-context probe runs on the
//! ENCLOSING query's term store, so where it stops decides which terms it
//! mints, and every later solve of the query sees them: the deductive-checks set-fold
//! obligation (`deductive_checks_set_fold_posture`) cut its anchored probe at 123
//! split rounds on an X925 core and at 69 on an A725 core, after which the
//! whole-set probe, the corroboration solve and the verdict's timing all
//! differed run to run. A grant is now counted in split-loop round trips
//! (`ay_core::resource::enter_work_grant`), which stop a probe at the same
//! round on every host. The wall grant stays, unchanged, as the BACKSTOP: a
//! probe never runs longer than it did before, and only a probe whose rounds
//! are slower than the calibration at [`ProbeCap`] still stops at the wall.
//!
//! Both currencies are deducted at claim and refunded at settle. The counted
//! one is the one a probe normally runs out of; the wall one keeps the lane's
//! total wall spend inside [`QUERY_PROBE_BUDGET_MS`] whatever the rounds cost.
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

/// One probe's ceiling in both currencies: the counted grant it normally
/// stops at, and the wall backstop it never outlives.
///
/// CALIBRATION (541fd07bb, release, `-C target-cpu=native`), per plan shape.
///
/// Capability, the floor under each count: across the 770 metered probes of
/// `group_quantifiers`, `group_proofs`, `group_auflia`, `group_regression`
/// and `deductive_checks_*`, the probes that RETURNED A PROOF used at most 7 split-loop
/// round trips under a standard plan, 4 in a standard anchored attempt, 1
/// under a positive-Skolem plan and 50 in a positive-Skolem anchored attempt
/// (a quarter of the plan's grant here: 60). A scoped whole-set probe whose
/// raw UNSAT has no strict proof (`UnsatUnpromotable`) arms the unscoped
/// retry, so its count matters too: the most such a probe used is 59
/// (`deductive_checks` quantified frame), five under the standard grant. On base's
/// X925 trajectory of the set-fold obligation one reached raw UNSAT only
/// after 82; a 64-round grant cuts it (its retry proved nothing there).
///
/// Wall, the ceiling over each count: the costliest probe rounds measured,
/// the deductive-checks set-fold obligation's whole-set probes (standard plan), take
/// up to 14.1 ms each on a slow (A725) core at the host's usual load of 9-14
/// (7.5-8.9 ms on an X925 core), so 64 of them take 0.9 s of the 2 s cap and
/// 240 would take 3.4 s of 5 s; two solves sharing one A725 core still stop
/// that probe at its count, after 1.6 s. A probe whose rounds cost more than
/// `wall_ms / round_trips` on its host stops at its unchanged wall grant
/// first, as before.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) struct ProbeCap {
    pub(in crate::executor) wall_ms: u64,
    pub(in crate::executor) round_trips: u64,
}

impl ProbeCap {
    /// Forall, dual-source and negative-Skolem plans.
    pub(in crate::executor) const STANDARD: Self = Self {
        wall_ms: 2_000,
        round_trips: 64,
    };

    /// The positive-Skolem plan of finite-frame replay.
    pub(in crate::executor) const POSITIVE_SKOLEM: Self = Self {
        wall_ms: 5_000,
        round_trips: 240,
    };

    /// `1 / divisor` of this cap, in both currencies.
    pub(in crate::executor) const fn share(self, divisor: u64) -> Self {
        Self {
            wall_ms: self.wall_ms / divisor,
            round_trips: self.round_trips / divisor,
        }
    }
}

/// The counted envelope, sized like [`QUERY_PROBE_BUDGET_MS`]: one whole
/// positive-Skolem probe.
pub(in crate::executor) const QUERY_PROBE_ROUND_TRIPS: u64 = ProbeCap::POSITIVE_SKOLEM.round_trips;

/// The counted floor: [`MIN_PROBE_BUDGET_MS`] of a standard plan's rounds.
const MIN_PROBE_ROUND_TRIPS: u64 = 8;

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
    /// Grants handed out since the last external query boundary. A count,
    /// not a clock: it tells one probe from a probe plus its unscoped retry
    /// identically on an idle and on a loaded host.
    claims: u32,
    /// The counted envelope left, in split-loop round trips.
    remaining_round_trips: u64,
    /// Round trips HANDED OUT since the last external query boundary, net of
    /// refunds: `granted_round_trips() <= QUERY_PROBE_ROUND_TRIPS`.
    granted_round_trips: u64,
}

impl Default for ConsequenceReplayProbeBudget {
    fn default() -> Self {
        Self {
            remaining_ms: QUERY_PROBE_BUDGET_MS,
            granted_ms: 0,
            claims: 0,
            remaining_round_trips: QUERY_PROBE_ROUND_TRIPS,
            granted_round_trips: 0,
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
    round_trips: u64,
}

impl ProbeGrant {
    /// Wall backstop to hand the disposable probe executor.
    pub(in crate::executor) fn budget_ms(self) -> u64 {
        self.granted_ms
    }

    /// Split-loop round trips the probe may run: the grant it normally stops
    /// at, at the same round on every host.
    pub(in crate::executor) fn round_trips(self) -> u64 {
        self.round_trips
    }
}

impl ConsequenceReplayProbeBudget {
    /// Re-arm at the outer API/command query boundary. Internal authority
    /// restarts, cascade retries, and nested solves must not call this.
    pub(in crate::executor) fn begin_external_query(&mut self) {
        *self = Self::default();
    }

    /// Deduct and return the slice a probe may run for, or `None` when this
    /// query has no useful work or wall time left to give it.
    ///
    /// `cap` is the lane's own per-probe ceiling. `deadline` is the caller's
    /// live solve deadline, if any: it is the outer wall, and only the wall
    /// backstop is shared out of it.
    pub(in crate::executor) fn claim(
        &mut self,
        cap: ProbeCap,
        deadline: Option<Instant>,
    ) -> Option<ProbeGrant> {
        let round_trips = cap.round_trips.min(self.remaining_round_trips);
        let mut granted = cap.wall_ms.min(self.remaining_ms);
        if let Some(deadline) = deadline {
            let remaining_deadline_ms = u64::try_from(
                deadline
                    .saturating_duration_since(Instant::now())
                    .as_millis(),
            )
            .unwrap_or(u64::MAX);
            granted = granted.min(remaining_deadline_ms / u64::from(DEADLINE_SHARE_DIVISOR));
        }
        if granted < MIN_PROBE_BUDGET_MS || round_trips < MIN_PROBE_ROUND_TRIPS {
            return None;
        }
        self.remaining_ms = self.remaining_ms.saturating_sub(granted);
        self.granted_ms = self.granted_ms.saturating_add(granted);
        self.remaining_round_trips = self.remaining_round_trips.saturating_sub(round_trips);
        self.granted_round_trips = self.granted_round_trips.saturating_add(round_trips);
        self.claims = self.claims.saturating_add(1);
        Some(ProbeGrant {
            granted_ms: granted,
            round_trips,
        })
    }

    /// Return the unspent remainder of a grant in both currencies. `spent_ms`
    /// is measured wall time and `spent_round_trips` the round trips the probe
    /// started; anything at or above the grant refunds nothing.
    pub(in crate::executor) fn settle(
        &mut self,
        grant: ProbeGrant,
        spent_ms: u64,
        spent_round_trips: u64,
    ) {
        let refund = grant.granted_ms.saturating_sub(spent_ms);
        self.remaining_ms = self
            .remaining_ms
            .saturating_add(refund)
            .min(QUERY_PROBE_BUDGET_MS);
        self.granted_ms = self.granted_ms.saturating_sub(refund);
        let refund = grant.round_trips.saturating_sub(spent_round_trips);
        self.remaining_round_trips = self
            .remaining_round_trips
            .saturating_add(refund)
            .min(QUERY_PROBE_ROUND_TRIPS);
        self.granted_round_trips = self.granted_round_trips.saturating_sub(refund);
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

    /// Grants handed out since the last external query boundary.
    pub(in crate::executor) fn claims(&self) -> u32 {
        self.claims
    }

    /// Counted envelope left, in round trips.
    pub(in crate::executor) fn remaining_round_trips(&self) -> u64 {
        self.remaining_round_trips
    }

    /// Round trips granted to probes since the last external query boundary,
    /// net of refunds.
    #[cfg(test)]
    pub(in crate::executor) fn granted_round_trips(&self) -> u64 {
        self.granted_round_trips
    }

    #[cfg(test)]
    pub(in crate::executor) fn set_remaining_ms(&mut self, remaining_ms: u64) {
        self.remaining_ms = remaining_ms;
    }

    #[cfg(test)]
    pub(in crate::executor) fn set_remaining_round_trips(&mut self, remaining: u64) {
        self.remaining_round_trips = remaining;
    }
}

impl Executor {
    /// Run ONE consequence-replay ground probe under this query's cumulative
    /// envelope, counted and wall-backstopped, or decline without running it.
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
        cap: ProbeCap,
    ) -> Option<ay_core::Proof> {
        use crate::executor::quantifier_loop::result_mapping::SameContextProbeOutcome;

        // First attempt: window-scoped array-axiom surface. This is the
        // #7956 posture — a derived window on the shared store must not let
        // the fixpoint seed hundreds of phantom congruence axioms from the
        // outer solve's dead array-equality terms.
        match self.granted_consequence_replay_probe(consequences, cap, true)? {
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
                match self.granted_consequence_replay_probe(consequences, cap, false)? {
                    SameContextProbeOutcome::Proof(proof) => Some(proof),
                    SameContextProbeOutcome::UnsatUnpromotable | SameContextProbeOutcome::Other => {
                        None
                    }
                }
            }
            SameContextProbeOutcome::Other => None,
        }
    }

    /// ONE window-scoped claim and no unscoped retry: the anchored-first
    /// consequence-replay attempt's probe. Its spend can then never exceed the
    /// one grant it was sized for, so the whole-set probe that follows a
    /// failed attempt keeps the rest of the envelope.
    pub(in crate::executor) fn metered_scoped_consequence_replay_probe(
        &mut self,
        consequences: &[ay_core::TermId],
        cap: ProbeCap,
    ) -> Option<ay_core::Proof> {
        use crate::executor::quantifier_loop::result_mapping::SameContextProbeOutcome;

        match self.granted_consequence_replay_probe(consequences, cap, true)? {
            SameContextProbeOutcome::Proof(proof) => Some(proof),
            SameContextProbeOutcome::UnsatUnpromotable | SameContextProbeOutcome::Other => None,
        }
    }

    /// Claim one grant from the query envelope, run one same-context probe
    /// under it, settle the unspent remainder, and report the attribution.
    /// `None` means the envelope itself declined (no grant, no probe run).
    fn granted_consequence_replay_probe(
        &mut self,
        consequences: &[ay_core::TermId],
        cap: ProbeCap,
        scope_to_window: bool,
    ) -> Option<crate::executor::quantifier_loop::result_mapping::SameContextProbeOutcome> {
        use crate::executor::quantifier_loop::result_mapping::SameContextProbeOutcome;

        let deadline = self.solve_deadline.get();
        let Some(grant) = self.consequence_replay_probe_budget.claim(cap, deadline) else {
            super::authored_consequence_replay::replay_note(|| {
                "decline: query probe envelope exhausted; a refutation this lane \
                 would have stitched must now publish through another lane"
                    .to_string()
            });
            return None;
        };
        let started = Instant::now();
        let round_trips_before = ay_core::resource::thread_round_trips();
        let outcome = self.checked_same_context_unsat_proof(
            consequences,
            crate::executor::quantifier_loop::result_mapping::SameContextWindow::Ground,
            Some(grant.budget_ms()),
            Some(grant.round_trips()),
            scope_to_window,
        );
        let spent_round_trips =
            ay_core::resource::thread_round_trips().saturating_sub(round_trips_before);
        let spent_ms = u64::try_from(started.elapsed().as_millis()).unwrap_or(u64::MAX);
        self.consequence_replay_probe_budget
            .settle(grant, spent_ms, spent_round_trips);
        super::authored_consequence_replay::replay_note(|| {
            format!(
                "probe(scoped={scope_to_window}, claim {}): {}, {spent_round_trips} of {} round \
                 trips and {spent_ms}ms of a {}ms wall backstop ({} round trips and {}ms \
                 left in the query envelope)",
                self.consequence_replay_probe_budget.claims(),
                match &outcome {
                    SameContextProbeOutcome::Proof(_) => "proof",
                    SameContextProbeOutcome::UnsatUnpromotable => "unsat but no strict proof",
                    SameContextProbeOutcome::Other => "no proof",
                },
                grant.round_trips(),
                grant.budget_ms(),
                self.consequence_replay_probe_budget.remaining_round_trips(),
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

    /// Probe grants this query's consequence-replay lane has claimed. An
    /// accounting read like the one above, but free of wall time entirely.
    pub(crate) fn consequence_replay_probe_claims(&self) -> u32 {
        self.consequence_replay_probe_budget.claims()
    }

    /// Split-loop round trips this query's lane has been granted, net of
    /// refunds, and the counted envelope that bounds them.
    pub(crate) fn consequence_replay_probe_round_trips_granted(&self) -> (u64, u64) {
        (
            self.consequence_replay_probe_budget.granted_round_trips(),
            QUERY_PROBE_ROUND_TRIPS,
        )
    }
}

#[cfg(test)]
#[path = "consequence_replay_budget_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "consequence_replay_work_grant_tests.rs"]
mod work_grant_tests;
