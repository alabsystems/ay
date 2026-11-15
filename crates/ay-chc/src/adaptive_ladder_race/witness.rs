// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A ladder race's witness-free Unsafe where the caller requires a ground
//! UNSAFE trace ([`AdaptiveConfig::require_ground_unsafe_trace`]: the CLI's
//! strict request, whose STEP D ground-checks the published counterexample).
//!
//! The serial ladder ran the front BMC probe first, so a shallow Unsafe was
//! published with BMC's concrete trace. In the race the first definitive
//! outcome decides, and a stage that proves Unsafe WITHOUT a concrete trace
//! can beat the BMC member. Measured at e2e3bd3a8 on a 7-step counter loop
//! (`ay --strict-proofs`): the portfolio foreground's CEGAR engine returned a
//! value-free trace at 0.07 s ("witness-less Unsafe validated eagerly"); the
//! final boundary accepts such a trace through the transition-system
//! reachability check, which confirms it without making it checkable, and
//! STEP D demoted the correct `unsat` to `unknown` ("missing concrete trace
//! assignment for step 0, state arg 0").
//!
//! Under that requirement such an outcome does not decide the race as it is.
//! Its participant first re-derives the counterexample by a bounded BMC replay
//! on the ORIGINAL clauses from the trace's depth — the discipline of the
//! collapse-first replay and of the verifier's witness-free arm (ba09f0476):
//! the replay's own verified trace is what gets offered. A replay that does
//! not confirm (nonlinear clauses, no budget, no witness within its depth
//! bound, a decided race) leaves the race OPEN: the outcome is held and
//! published only if the race ends undecided, so a witness-bearing verdict
//! (the front BMC member, PDR) that arrives later still decides. Measured on
//! the `x > 45` counter at 50 s when an unconfirmed trace decided: the
//! replay's 10 s reached depth 27, and the front BMC member, cancelled at
//! depth 41 of the 46 it needed, lost to a trace STEP D then demoted. A
//! verdict is never dropped here and never gains trust: the final boundary
//! and the strict gate judge whatever is published exactly as before,
//! fail-closed.
//!
//! Without the requirement (the default) nothing changes: a witness-free
//! Unsafe decides at once, so the race keeps its latency where no ground
//! trace is required (a replay before every such offer took the `x > 35`
//! counter from ~5.5 s to ~15 s).
//!
//! [`AdaptiveConfig::require_ground_unsafe_trace`]: crate::AdaptiveConfig::require_ground_unsafe_trace

use std::panic::AssertUnwindSafe;
use std::sync::Mutex;
use std::time::Duration;

use super::{lock, refused_outcome, CancellationToken, LadderOutcome, RaceState};
use crate::adaptive::AdaptivePortfolio;
use crate::pdr::Counterexample;
use crate::portfolio::PortfolioResult;
use crate::ChcProblem;

/// Upper bound of one witness replay: the collapse-first replay's cap and the
/// verifier's witness-free replay budget.
const WITNESS_REPLAY_CAP: Duration = Duration::from_secs(10);

/// Below this the replay declines to start
/// (`BmcSolver::replay_confirm_unsafe_on_problem`).
const WITNESS_REPLAY_FLOOR: Duration = Duration::from_millis(250);

/// The replay's budget from the solve's remaining time: at most half of it
/// (the final boundary still has to validate whichever trace is published)
/// and at most [`WITNESS_REPLAY_CAP`]. `None` (an unbounded solve) gets the
/// cap.
fn witness_replay_budget(remaining: Option<Duration>) -> Duration {
    remaining.map_or(WITNESS_REPLAY_CAP, |remaining| {
        (remaining / 2).min(WITNESS_REPLAY_CAP)
    })
}

/// True when `cex` carries neither a derivation witness nor a ground
/// derivation, and its steps do not ground-evaluate on `problem` — the trace
/// the strict gate (`Counterexample::ground_checks_unsafe`) cannot confirm.
/// A trace that does carry a witness is left to the final boundary: its
/// producer (BMC, PDR) already derived it, and a replay would only repeat
/// that work.
pub(super) fn lacks_ground_witness(problem: &ChcProblem, cex: &Counterexample) -> bool {
    let has_witness = cex
        .witness
        .as_ref()
        .is_some_and(|witness| !witness.entries.is_empty());
    if has_witness || cex.ground_derivation.is_some() {
        return false;
    }
    !matches!(
        std::panic::catch_unwind(AssertUnwindSafe(|| cex.ground_checks_unsafe(problem))),
        Ok(Ok(true))
    )
}

/// What a participant's outcome does to the race.
pub(super) enum Offer {
    /// Offered as the race's decision ([`RaceState::offer`]).
    Decide(LadderOutcome),
    /// A witness-free Unsafe no replay re-derived while a ground trace is
    /// required: it does not decide, and is published only by an undecided
    /// race.
    Hold(LadderOutcome),
}

impl Offer {
    /// The participant's result for the race's decision log.
    pub(super) fn label(&self) -> &'static str {
        match self {
            Self::Decide((result, _)) => AdaptivePortfolio::result_to_str(result),
            Self::Hold(_) => "unsafe(held)",
        }
    }
}

/// The first witness-free Unsafe a race held.
#[derive(Default)]
pub(super) struct HeldUnsafe(Mutex<Option<(&'static str, LadderOutcome)>>);

impl HeldUnsafe {
    /// The held outcome, for a race that ended undecided.
    pub(super) fn publish(&self, race: &'static str) -> Option<LadderOutcome> {
        let (name, outcome) = lock(&self.0).take()?;
        tracing::info!(
            "Adaptive: {race} ladder race undecided; publishing {name}'s held witness-free \
             Unsafe (no ground witness was derived)"
        );
        Some(outcome)
    }
}

impl RaceState {
    /// Submit a participant's outcome: a decision is offered and handed back
    /// when refused; a held Unsafe waits for an undecided race.
    pub(super) fn submit(
        &self,
        name: &'static str,
        token: &CancellationToken,
        offer: Offer,
    ) -> Option<LadderOutcome> {
        // Holding a witness-free outcome cannot bypass the same original
        // participant boundary that governs an offered definitive verdict.
        if !self.caller.participant_open(token) {
            return Some(refused_outcome());
        }
        match offer {
            Offer::Decide(outcome) => self.offer(name, token, outcome).err(),
            Offer::Hold(outcome) => {
                let mut held = lock(&self.held.0);
                if !self.caller.participant_open(token) {
                    return Some(refused_outcome());
                }
                if held.is_none() {
                    *held = Some((name, outcome));
                }
                None
            }
        }
    }
}

impl AdaptivePortfolio {
    /// `outcome` as the race participant `name` submits it. Only a
    /// witness-free Unsafe under [`crate::AdaptiveConfig::require_ground_unsafe_trace`]
    /// changes: replaced by the bounded BMC replay's verified counterexample
    /// when the replay confirms one, held otherwise. Runs on the participant's
    /// thread under its lane, so a decided race cancels the replay.
    pub(super) fn witnessed_ladder_outcome(
        &self,
        name: &'static str,
        outcome: LadderOutcome,
    ) -> Offer {
        if !self.config.require_ground_unsafe_trace {
            return Offer::Decide(outcome);
        }
        let (PortfolioResult::Unsafe(cex), evidence) = outcome else {
            return Offer::Decide(outcome);
        };
        if !lacks_ground_witness(&self.problem, &cex) {
            return Offer::Decide((PortfolioResult::Unsafe(cex), evidence));
        }
        let depth_hint = cex.steps.len().saturating_add(2);
        match self.replay_ground_witness(depth_hint) {
            Some(witnessed) => {
                tracing::info!(
                    "Adaptive: ladder participant {name}'s witness-free Unsafe re-derived with a \
                     ground witness by a bounded BMC replay (depth hint {depth_hint})"
                );
                Offer::Decide((PortfolioResult::Unsafe(witnessed), evidence))
            }
            None => {
                tracing::info!(
                    "Adaptive: ladder participant {name}'s witness-free Unsafe not re-derived \
                     (depth hint {depth_hint}); held while the race stays open"
                );
                Offer::Hold((PortfolioResult::Unsafe(cex), evidence))
            }
        }
    }

    /// The bounded BMC replay on the original clauses: `Some` only for a
    /// counterexample it found AND re-verified. Budget zero once the race is
    /// decided (a cancelled lane has none): a losing participant does not
    /// replay.
    fn replay_ground_witness(&self, depth_hint: usize) -> Option<Counterexample> {
        let budget =
            witness_replay_budget(self.remaining_budget(self.enclosing_subsolve_deadline()));
        if budget < WITNESS_REPLAY_FLOOR {
            return None;
        }
        std::panic::catch_unwind(AssertUnwindSafe(|| {
            crate::bmc::BmcSolver::replay_confirm_unsafe_on_problem(
                &self.problem,
                depth_hint,
                budget,
                Some(self.lane_token()),
                self.config.verbose,
            )
        }))
        .ok()
        .flatten()
    }
}

#[cfg(test)]
mod tests;
