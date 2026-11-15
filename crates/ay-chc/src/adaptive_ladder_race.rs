// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Concurrent pre-stage ladder (item #2 of
//! the development design notes).
//!
//! [`AdaptivePortfolio::race_ladder`] runs the stages as concurrent members
//! from t=0 next to the arm's foreground (the portfolio / BV dual lane / the
//! rest of the dispatch). The first admitted DEFINITIVE outcome (Safe/Unsafe)
//! is held as the candidate; every other participant is cancelled and joined.
//! Original caller boundaries are checked again before returning the outcome.
//!
//! Each member thread gets what a portfolio engine thread gets:
//! * the caller's thread-local boundaries (solve deadline, SMT deadline,
//!   term-memory budget), which worker threads never inherit;
//! * its own memory share (`EngineMemoryLane`, WP-F): crossing it cancels
//!   that member alone;
//! * a lane cancellation (`ScopedLaneCancellation`): once the race is decided
//!   every SMT check on the member's thread answers `Unknown` at once, its
//!   executors are interrupted mid-check, and `AdaptivePortfolio::lane_token`
//!   links the member's token into every route token created on the thread.
//!
//! The foreground runs on the calling thread under the same kind of lane
//! cancellation, so a member's win stops the portfolio promptly.
//!
//! SOUNDNESS: unchanged by construction. Every member is an existing stage
//! with its own validation gating; the race only changes WHEN it runs, and a
//! cancelled participant can only degrade to `Unknown`. The winner still
//! passes the caller's `finalize_verified_result` boundary like any serial
//! stage's result. `Some(Unknown)` from a member (a stage giving up) is not a
//! decision: the others keep running. Where a ground UNSAFE trace is required,
//! a witness-free Unsafe is re-derived before it decides, or held ([`witness`]).

use std::panic::AssertUnwindSafe;
use std::sync::{Arc, Mutex, MutexGuard, PoisonError};

use ay_core::time::Instant;

use crate::adaptive::{AdaptiveExecutionMode, AdaptivePortfolio, ADAPTIVE_SOLVER_STACK_SIZE};
use crate::adaptive_decision_log::DecisionEntry;
use crate::cancellation::CancellationToken;
use crate::classifier::ProblemFeatures;
use crate::engine_result::ValidationEvidence;
use crate::portfolio::engine_memory::{EngineMemoryLane, LaneMemoryLimits};
use crate::portfolio::PortfolioResult;

mod admission;
mod settlement;
mod witness;
use admission::{refused_outcome, CallerAdmission, InheritedBoundaries};
pub(crate) use settlement::race_settled;
use settlement::{ScopedSettlement, Settlement};
use witness::{HeldUnsafe, Offer};

/// What a ladder stage (or the foreground) concluded.
pub(crate) type LadderOutcome = (PortfolioResult, ValidationEvidence);

/// The front BMC probe member: the SimpleLoop portfolio drops its own BMC
/// engine exactly when a member of this name races.
pub(crate) const FRONT_BMC_MEMBER: &str = "front_bmc";

/// One concurrent pre-stage of a ladder race.
pub(crate) struct LadderMember<'a> {
    pub(crate) name: &'static str,
    run: Box<dyn FnOnce() -> Option<LadderOutcome> + Send + 'a>,
}

impl<'a> LadderMember<'a> {
    pub(crate) fn new(
        name: &'static str,
        run: impl FnOnce() -> Option<LadderOutcome> + Send + 'a,
    ) -> Self {
        Self {
            name,
            run: Box::new(run),
        }
    }
}

fn definitive(result: &PortfolioResult) -> bool {
    matches!(
        result,
        PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_)
    )
}

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

struct Finish {
    name: &'static str,
    elapsed_secs: f64,
    result: &'static str,
    memory_tripped: bool,
}

struct RaceState {
    /// Cancelled (own flag, so executor interrupts fire) once decided: one per
    /// member, then the foreground's.
    tokens: Vec<CancellationToken>,
    winner: Mutex<Option<(&'static str, LadderOutcome)>>,
    /// A witness-free Unsafe that must not decide ([`witness`]).
    held: HeldUnsafe,
    finishes: Mutex<Vec<Finish>>,
    boundaries: InheritedBoundaries,
    caller: CallerAdmission,
    memory_limits: Option<LaneMemoryLimits>,
    /// Set (before the tokens are cancelled) once a candidate is held; bound to
    /// every participant's thread ([`race_settled`]).
    settlement: Arc<Settlement>,
}

impl RaceState {
    /// One token per member plus the foreground's: children of the solve's
    /// handle that also observe the lane owning the calling thread (a race
    /// nested in another race's participant stops with it).
    fn new(solve: &CancellationToken, members: usize, enclosing_deadline: Option<Instant>) -> Self {
        let caller = CallerAdmission::capture(solve, enclosing_deadline);
        let tokens = (0..=members).map(|_| caller.participant_token()).collect();
        Self {
            tokens,
            winner: Mutex::new(None),
            held: HeldUnsafe::default(),
            finishes: Mutex::new(Vec::new()),
            boundaries: caller.boundaries,
            caller,
            memory_limits: LaneMemoryLimits::from_process_limit(),
            settlement: Arc::new(Settlement::nested()),
        }
    }

    fn foreground_token(&self) -> &CancellationToken {
        &self.tokens[self.tokens.len() - 1]
    }

    fn decided(&self) -> bool {
        lock(&self.winner).is_some()
    }

    /// Accept `outcome` as the race's decision when it is definitive and the
    /// race is still open; otherwise hand it back.
    fn offer(
        &self,
        name: &'static str,
        token: &CancellationToken,
        outcome: LadderOutcome,
    ) -> Result<(), LadderOutcome> {
        if !definitive(&outcome.0) {
            return Err(outcome);
        }
        {
            let mut winner = lock(&self.winner);
            if winner.is_some() {
                return Err(outcome);
            }
            // Sample the participant's original boundaries at publication,
            // after its lane scope and cleanup, not only before running it.
            if !self.caller.participant_open(token) {
                return Err(refused_outcome());
            }
            *winner = Some((name, outcome));
        }
        // Settled first: a participant that observes its cancelled token must
        // already see that a held candidate (not a timeout) cancelled it.
        self.settlement.settle();
        for token in &self.tokens {
            token.cancel();
        }
        Ok(())
    }

    fn cancel_all(&self) {
        for token in &self.tokens {
            token.cancel();
        }
    }

    fn record(&self, finish: Finish) {
        lock(&self.finishes).push(finish);
    }
}

impl AdaptivePortfolio {
    /// Run `members` concurrently with `foreground` and return the first
    /// definitive outcome; with none, the foreground's own outcome.
    ///
    /// Deterministic-sequential mode keeps the historical serial order:
    /// members in order, then the foreground.
    pub(crate) fn race_ladder<'a>(
        &'a self,
        race: &'static str,
        members: Vec<LadderMember<'a>>,
        foreground: impl FnOnce() -> LadderOutcome,
    ) -> LadderOutcome {
        let started = Instant::now();
        let state = RaceState::new(
            &self.cancellation_token,
            members.len(),
            self.enclosing_subsolve_deadline(),
        );
        if !state.caller.open() {
            return refused_outcome();
        }
        if members.is_empty()
            || self.config.execution_mode == AdaptiveExecutionMode::DeterministicSequential
        {
            return admission::run_serial(&state, members, foreground);
        }
        let names: Vec<&'static str> = members.iter().map(|member| member.name).collect();
        tracing::info!(
            "Adaptive: {race} ladder race: {} concurrent member(s) [{}] + foreground",
            names.len(),
            names.join(", ")
        );
        let slots: Vec<Mutex<Option<LadderMember<'a>>>> = members
            .into_iter()
            .map(|member| Mutex::new(Some(member)))
            .collect();
        let foreground_outcome = std::thread::scope(|scope| {
            let mut unspawned = Vec::new();
            for (index, slot) in slots.iter().enumerate() {
                let state = &state;
                let spawned = std::thread::Builder::new()
                    .name(format!("ay-ladder-{}", names[index]))
                    .stack_size(ADAPTIVE_SOLVER_STACK_SIZE)
                    .spawn_scoped(scope, move || {
                        let _solve_deadline =
                            crate::smt::ScopedSolveDeadline::new(state.boundaries.solve_deadline);
                        let _smt_deadline = state
                            .boundaries
                            .smt_deadline
                            .map(crate::smt::ScopedSmtDeadline::install_until);
                        let _term_budget = crate::smt::SmtContext::scoped_thread_term_memory_budget(
                            state.boundaries.term_memory_budget,
                        );
                        self.run_ladder_member(state, slot, &state.tokens[index]);
                    });
                if spawned.is_err() {
                    unspawned.push(index);
                }
            }
            let outcome = self.run_ladder_foreground(&state, foreground);
            // Unspawned members run inline after the foreground.
            for index in unspawned {
                if state.decided() {
                    break;
                }
                self.run_ladder_member(&state, &slots[index], &state.tokens[index]);
            }
            outcome
        });
        self.conclude_ladder_race(race, started, &state, foreground_outcome)
    }

    /// Run the foreground under its lane; only an on-time, uncancelled
    /// admitted outcome decides. A held Unsafe waits without cancelling
    /// other participants; a refused candidate becomes Unknown.
    fn run_ladder_foreground(
        &self,
        state: &RaceState,
        foreground: impl FnOnce() -> LadderOutcome,
    ) -> Option<LadderOutcome> {
        let token = state.foreground_token();
        let started = Instant::now();
        let outcome = {
            let _lane = crate::smt::ScopedLaneCancellation::install(
                token.clone(),
                Some(token.interrupt_flag()),
            );
            let _settlement = ScopedSettlement::install(Arc::clone(&state.settlement));
            std::panic::catch_unwind(AssertUnwindSafe(|| {
                let outcome = if state.caller.participant_open(token) {
                    foreground()
                } else {
                    refused_outcome()
                };
                self.witnessed_ladder_outcome("foreground", outcome)
            }))
        };
        let outcome = match outcome {
            Ok(outcome) => outcome,
            Err(payload) => {
                // Stop the members before the scope joins them, then re-raise
                // the foreground's panic to the caller.
                state.cancel_all();
                std::panic::resume_unwind(payload);
            }
        };
        state.record(Finish {
            name: "foreground",
            elapsed_secs: started.elapsed().as_secs_f64(),
            result: outcome.label(),
            memory_tripped: false,
        });
        state.submit("foreground", token, outcome)
    }

    fn conclude_ladder_race(
        &self,
        race: &'static str,
        started: Instant,
        state: &RaceState,
        foreground_outcome: Option<LadderOutcome>,
    ) -> LadderOutcome {
        let winner = lock(&state.winner).take();
        self.log_ladder_race(race, started, state, winner.as_ref().map(|(name, _)| *name));
        let outcome = match winner {
            Some((name, outcome)) => {
                tracing::info!(
                    "Adaptive: {race} ladder race holds candidate from {name} ({}) after {:.2}s",
                    Self::result_to_str(&outcome.0),
                    started.elapsed().as_secs_f64()
                );
                outcome
            }
            None => state.held.publish(race).or(foreground_outcome).unwrap_or((
                PortfolioResult::Unknown,
                ValidationEvidence::FullVerification,
            )),
        };
        // Joins and logging consume the same caller clock. Winning cancels
        // only participant flags; this independent owner still sees external
        // cancellation, original deadlines and sticky inherited memory.
        state.caller.limit(outcome)
    }

    fn run_ladder_member(
        &self,
        state: &RaceState,
        slot: &Mutex<Option<LadderMember<'_>>>,
        token: &CancellationToken,
    ) {
        let Some(member) = lock(slot).take() else {
            return;
        };
        if !state.caller.participant_open(token) {
            return;
        }
        let name = member.name;
        let started = Instant::now();
        let memory = EngineMemoryLane::enter(name, state.memory_limits, token);
        let outcome = {
            let _lane = crate::smt::ScopedLaneCancellation::install(
                token.clone(),
                Some(token.interrupt_flag()),
            );
            let _settlement = ScopedSettlement::install(Arc::clone(&state.settlement));
            if !state.caller.participant_open(token) {
                None
            } else {
                match std::panic::catch_unwind(AssertUnwindSafe(|| {
                    (member.run)().map(|outcome| self.witnessed_ladder_outcome(name, outcome))
                })) {
                    Ok(outcome) => outcome,
                    Err(_) => {
                        tracing::warn!(
                            "Adaptive: ladder member {name} panicked; treated as no verdict"
                        );
                        None
                    }
                }
            }
        };
        let memory_tripped = memory.as_ref().is_some_and(EngineMemoryLane::tripped);
        drop(memory);
        // The sticky memory observation remains authoritative even if an
        // unexpected flag change makes the token appear open again.
        let outcome = if memory_tripped { None } else { outcome };
        state.record(Finish {
            name,
            elapsed_secs: started.elapsed().as_secs_f64(),
            result: outcome.as_ref().map_or("unknown", Offer::label),
            memory_tripped,
        });
        if memory_tripped {
            tracing::info!(
                "Adaptive: ladder member {name} exceeded its memory share; cancelled alone"
            );
        }
        if let Some(outcome) = outcome {
            // Losing, refused and non-definitive member outcomes are dropped.
            let _ = state.submit(name, token, outcome);
        }
    }

    fn log_ladder_race(
        &self,
        race: &'static str,
        started: Instant,
        state: &RaceState,
        winner: Option<&'static str>,
    ) {
        let finishes = lock(&state.finishes);
        let summary = finishes
            .iter()
            .map(|finish| {
                format!(
                    "{}={}@{:.2}s{}",
                    finish.name,
                    finish.result,
                    finish.elapsed_secs,
                    if finish.memory_tripped {
                        "(memory)"
                    } else {
                        ""
                    }
                )
            })
            .collect::<Vec<_>>()
            .join(" ");
        tracing::info!(
            "Adaptive: {race} ladder race after {:.2}s: held_candidate={}; {summary}",
            started.elapsed().as_secs_f64(),
            winner.unwrap_or("none")
        );
        self.decision_log.log_decision(DecisionEntry {
            stage: "ladder_race",
            gate_result: winner.is_some(),
            gate_reason: format!(
                "{race}: held_candidate={}; {summary}",
                winner.unwrap_or("none")
            ),
            budget_secs: 0.0,
            elapsed_secs: started.elapsed().as_secs_f64(),
            result: if winner.is_some() {
                "candidate"
            } else {
                "unknown"
            },
            lemmas_learned: 0,
            max_frame: 0,
        });
    }
}

impl AdaptivePortfolio {
    /// The SimpleLoop ladder's concurrent members. Each stage keeps its own
    /// gate (it returns `None` at once off-shape), budget and validation.
    pub(crate) fn simple_loop_ladder_members<'a>(
        &'a self,
        features: &'a ProblemFeatures,
        deadline: Option<Instant>,
        query_flag_race_started: bool,
    ) -> Vec<LadderMember<'a>> {
        let mut members = Vec::new();
        members.push(if query_flag_race_started {
            LadderMember::new("query_flag_race", move || self.query_flag_race_member())
        } else {
            // Synchronous guess-and-check of the same candidate, for the
            // modes where the background validation does not run.
            LadderMember::new("query_flag_prepass", move || {
                self.try_query_flag_invariant_prepass(features, deadline)
            })
        });
        // Shallow counterexamples: the whole-budget front BMC probe replaces
        // the portfolio's own BMC (the foreground drops it) when the solve
        // has a budget to share with it.
        if self.front_bmc_probe_member_runs(features, deadline) {
            members.push(LadderMember::new(FRONT_BMC_MEMBER, move || {
                self.front_bmc_probe_member(features, deadline)
            }));
        }
        // Conjunctive Houdini (#11 QUAL-MINE for BV: scalar BV only).
        if !self.problem.has_bv_sorts() || (!features.uses_arrays && !features.uses_datatypes) {
            members.push(LadderMember::new("houdini", move || {
                self.try_houdini_conjunctive_prepass(features, deadline)
            }));
        }
        members.push(LadderMember::new("lia_farkas_pdr", move || {
            self.try_lia_farkas_pdr_route(features, deadline)
        }));
        members.push(LadderMember::new("direct_kind", move || {
            self.try_simple_loop_direct_kind(features, deadline)
        }));
        members.push(LadderMember::new("solo_pdr", move || {
            self.try_simple_loop_solo_pdr_probe(features, deadline)
        }));
        members
    }
}

#[cfg(test)]
mod tests;
