// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Background validation of the query-flag candidate invariant (T1/T9 of
//! the development design notes at `9598c4206`).
//!
//! 47 % of the safe lustre instances in LIA-Lin are 1-INDUCTIVE: the property
//! flag the query names is itself the inductive invariant, and the proof is
//! one init obligation plus one consecution obligation. The synchronous
//! `try_query_flag_invariant_prepass` guesses exactly that candidate, but it
//! ran BEHIND the ~14 s front BMC probe with a 6 s per-clause cap (≈4.5 s
//! after the dv-off reserve), and a candidate that timed out there was
//! discarded although ~45 s of budget remained. Measured on the taxonomy's
//! 16-instance 1-inductive sample (T8 binary): 14 proofs land in 0.00–3.6 s,
//! two need more than the cap, and every solved instance still paid the probe
//! first (14–19 s wall for a 0.01 s proof).
//!
//! The race fixes both without changing what is proved or accepted. The
//! SimpleLoop round starts the validation FIRST, on a background thread whose
//! budget is the whole remaining run; a ladder-race member
//! ([`AdaptivePortfolio::query_flag_race_member`], `adaptive_ladder_race`)
//! publishes a proof the moment it lands, which ends every concurrent stage
//! and the portfolio. Route tokens additionally observe the race's proof
//! signal ([`AdaptivePortfolio::lane_token`]).
//! Each obligation gets a first attempt at the synchronous prepass's 6 s cap
//! (keeping its dv-off rescue timing) and, if still undecided, a second
//! attempt with the remaining budget. A SAT obligation refutes the candidate
//! for good; nothing is retried after a refutation.
//!
//! Soundness is the prepass's: every original clause's violation query must
//! be proven UNSAT by AY's own executor-backed SMT (fail-closed on Sat /
//! Unknown / panic / interrupt), the verdict carries the same
//! `ValidationEvidence::FullVerification`, and it passes through the same
//! bounded finalization boundary as every other Safe. The
//! deterministic-sequential mode never starts a race (it keeps the
//! synchronous prepass), and neither does a problem outside the prepass's
//! gate (arrays, datatypes, BV, multi-predicate, non-flag query).

use std::panic::AssertUnwindSafe;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{self, Receiver, RecvTimeoutError, Sender, TryRecvError};
use std::sync::{Arc, Mutex, MutexGuard};
use std::thread::JoinHandle;
use std::time::Duration;

use ay_core::time::Instant;

use crate::adaptive::{AdaptiveExecutionMode, AdaptivePortfolio, ADAPTIVE_SOLVER_STACK_SIZE};
use crate::adaptive_decision_log::DecisionEntry;
use crate::cancellation::CancellationToken;
use crate::classifier::ProblemFeatures;
use crate::engine_result::ValidationEvidence;
use crate::pdr::InvariantModel;
use crate::portfolio::PortfolioResult;
use crate::smt::executor_adapter::{InterruptObserver, ReplayCancellation};
use crate::smt::{PdrExecutorBackend, ScopedSmtDeadline, ScopedSolveDeadline, SmtResult};
use crate::ChcExpr;

/// First attempt per obligation: the synchronous prepass's per-clause floor,
/// so the inc-18/inc-21 dv-off retry still fires at the same point for the
/// queries that mode rescues.
const QUERY_FLAG_RACE_FIRST_ATTEMPT_CAP: Duration = Duration::from_secs(6);
/// Kept off the global deadline so the worker can never publish past it.
const QUERY_FLAG_RACE_DEADLINE_MARGIN: Duration = Duration::from_millis(250);
/// Below this remaining budget the race is not worth a thread.
const QUERY_FLAG_RACE_MIN_BUDGET: Duration = Duration::from_millis(100);
/// Below this remaining budget an attempt is not issued.
const QUERY_FLAG_RACE_MIN_ATTEMPT: Duration = Duration::from_millis(25);
/// Decision-log stage name shared by every entry the race writes.
const STAGE: &str = "query_flag_candidate_race";

/// What the worker thread concluded about the candidate.
enum QueryFlagRaceOutcome {
    /// Every original clause's violation query is UNSAT: the candidate is an
    /// inductive invariant of the original problem.
    Proven(InvariantModel),
    /// Some clause's violation query is SAT: the candidate is not inductive.
    Refuted { clause: usize },
    /// The budget (or the interrupt) ran out with a clause still undecided.
    Exhausted { clause: usize },
}

/// The foreground's memo of an outcome it has already observed.
enum Resolution {
    /// Proven; the model is handed out exactly once.
    Proven { model: Option<InvariantModel> },
    /// Refuted, exhausted, or the worker ended without a verdict.
    Settled,
}

/// Snapshot caller-owned controls before crossing the thread boundary. The
/// shared interrupt is sticky for this attempt, including publication after
/// a caller reset. Term limits are not an aggregate/RSS allocation guarantee.
#[derive(Clone)]
struct RaceControl {
    deadline: Instant,
    term_memory_limit: Option<usize>,
    cancellation: ReplayCancellation,
    interrupt: Arc<AtomicBool>,
}

impl RaceControl {
    fn capture(
        deadline: Instant,
        term_memory_limit: Option<usize>,
        parent: &CancellationToken,
    ) -> Self {
        Self {
            deadline: [
                Some(deadline),
                crate::smt::current_thread_solve_deadline(),
                crate::smt::deadline::current_smt_deadline(),
            ]
            .into_iter()
            .flatten()
            .min()
            .unwrap_or(deadline),
            term_memory_limit: term_memory_limit
                .into_iter()
                .chain(crate::smt::SmtContext::current_thread_term_memory_budget())
                .min(),
            cancellation: ReplayCancellation::new(&parent.sticky_child()),
            interrupt: Arc::new(AtomicBool::new(false)),
        }
    }

    fn open(&self) -> bool {
        self.open_at(Instant::now())
    }

    fn open_at(&self, now: Instant) -> bool {
        if self.interrupt.load(Ordering::Relaxed)
            || self.cancellation.is_cancelled()
            || now >= self.deadline
            || self.term_memory_limit == Some(0)
            || ay_core::TermStore::global_memory_exceeded()
        {
            self.stop();
            false
        } else {
            true
        }
    }

    fn stop(&self) {
        self.interrupt.store(true, Ordering::Relaxed);
    }

    fn wait_budget_at(&self, requested: Duration, now: Instant) -> Duration {
        requested.min(self.deadline.saturating_duration_since(now))
    }
}

/// One in-flight (or already resolved) background validation.
pub(crate) struct QueryFlagRace {
    started: Instant,
    budget: Duration,
    /// Cancelled by the worker when the candidate is PROVEN; stages that can
    /// stop early observe it through
    /// [`AdaptivePortfolio::lane_token`].
    signal: CancellationToken,
    /// Cooperative stop for the worker's executor, set when the race is
    /// dropped (the ladder has answered).
    control: RaceControl,
    observer: Option<InterruptObserver>,
    worker: Option<JoinHandle<()>>,
    receiver: Receiver<QueryFlagRaceOutcome>,
    resolution: Option<Resolution>,
}

impl Drop for QueryFlagRace {
    fn drop(&mut self) {
        self.control.stop();
        // The existing observer wakes and joins its atomic-only monitor.
        // Never wait for an unfinished solver: construction, serialization,
        // normalization and solver cleanup can be opaque intervals. Its
        // shared interrupt/deadline remain installed after this owner drops.
        drop(self.observer.take());
        if let Some(worker) = self.worker.take().filter(JoinHandle::is_finished) {
            if let Err(payload) = worker.join() {
                if let Err(secondary) = std::panic::catch_unwind(AssertUnwindSafe(|| drop(payload)))
                {
                    std::mem::forget(secondary);
                }
            }
        }
    }
}

struct QueryFlagRaceWorker {
    /// `(clause index, violation query)` for every clause whose violation did
    /// not simplify away; the candidate is proven when all are UNSAT.
    obligations: Vec<(usize, ChcExpr)>,
    model: InvariantModel,
    control: RaceControl,
    signal: CancellationToken,
    sender: Sender<QueryFlagRaceOutcome>,
}

enum Discharge {
    Unsat,
    Sat,
    Undecided,
}

impl QueryFlagRaceWorker {
    fn run(self) {
        let Self {
            obligations,
            model,
            control,
            signal,
            sender,
        } = self;
        // The same thread-local boundaries every SMT context honours: the
        // executor's own timeout and the dv-off retry are clamped to them.
        let _solve_deadline = ScopedSolveDeadline::new(Some(control.deadline));
        let _smt_deadline = ScopedSmtDeadline::install_until(control.deadline);
        let _memory =
            crate::smt::SmtContext::scoped_thread_term_memory_budget(control.term_memory_limit);
        if !control.open() {
            return;
        }
        let mut backend = PdrExecutorBackend::new();
        backend.set_interrupt(Arc::clone(&control.interrupt));
        if !backend.set_resource_limits(control.deadline, control.term_memory_limit) {
            control.stop();
            return;
        }

        let mut outcome = None;
        for (clause, violation) in &obligations {
            match Self::discharge(&mut backend, violation, &control) {
                Discharge::Unsat => {}
                Discharge::Sat => {
                    outcome = Some(QueryFlagRaceOutcome::Refuted { clause: *clause });
                    break;
                }
                Discharge::Undecided => {
                    outcome = Some(QueryFlagRaceOutcome::Exhausted { clause: *clause });
                    break;
                }
            }
        }
        let outcome = outcome.unwrap_or(QueryFlagRaceOutcome::Proven(model));
        let proven = matches!(outcome, QueryFlagRaceOutcome::Proven(_));
        if !control.open() || !backend.resources_open() {
            control.stop();
            return;
        }
        // Publish BEFORE signalling: a stage woken by the signal polls the
        // channel next and must find the proof there.
        let _ = sender.send(outcome);
        if proven {
            signal.cancel();
        }
    }

    /// Two attempts on the same hermetic backend: the prepass's 6 s cap
    /// first, then everything that is left. The T1 tail (3.5–18 s isolated
    /// consecution proofs) is exactly what the single capped attempt lost.
    fn discharge(
        backend: &mut PdrExecutorBackend,
        violation: &ChcExpr,
        control: &RaceControl,
    ) -> Discharge {
        if !control.open() {
            return Discharge::Undecided;
        }
        let remaining = || control.deadline.saturating_duration_since(Instant::now());
        let first = remaining().min(QUERY_FLAG_RACE_FIRST_ATTEMPT_CAP);
        if first < QUERY_FLAG_RACE_MIN_ATTEMPT {
            return Discharge::Undecided;
        }
        let first = backend.check_sat_with_dv_hint(violation, first, false);
        if !control.open() || !backend.resources_open() {
            control.stop();
            return Discharge::Undecided;
        }
        match Self::classify(first) {
            Discharge::Undecided => {}
            decided => return decided,
        }
        let rest = remaining();
        if rest < QUERY_FLAG_RACE_MIN_ATTEMPT {
            return Discharge::Undecided;
        }
        let result = backend.check_sat_with_dv_hint(violation, rest, false);
        if !control.open() || !backend.resources_open() {
            control.stop();
            Discharge::Undecided
        } else {
            Self::classify(result)
        }
    }

    fn classify(result: SmtResult) -> Discharge {
        if result.is_unsat() {
            Discharge::Unsat
        } else if result.is_sat() {
            Discharge::Sat
        } else {
            Discharge::Undecided
        }
    }
}

fn lock_race(slot: &Mutex<Option<QueryFlagRace>>) -> MutexGuard<'_, Option<QueryFlagRace>> {
    slot.lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

impl AdaptivePortfolio {
    /// Start validating the query-flag candidate in the background for the
    /// current SimpleLoop round. Returns `false` when no race runs — no
    /// candidate (gate), deterministic-sequential mode, no budget, a clause
    /// the candidate cannot be instantiated on, a statically refuted
    /// candidate, or a thread that could not be spawned — in which case the
    /// ladder keeps its synchronous `try_query_flag_invariant_prepass`.
    pub(crate) fn start_query_flag_candidate_race(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> bool {
        if self.config.execution_mode == AdaptiveExecutionMode::DeterministicSequential {
            return false;
        }
        let Some(model) = self.query_flag_candidate_model(features) else {
            return false;
        };
        let started = Instant::now();
        let budget = self
            .remaining_budget(deadline)
            .unwrap_or(self.config.time_budget)
            .saturating_sub(QUERY_FLAG_RACE_DEADLINE_MARGIN);
        if budget < QUERY_FLAG_RACE_MIN_BUDGET {
            return false;
        }
        let deadline = self
            .enclosing_subsolve_deadline()
            .map_or(started + budget, |outer| outer.min(started + budget));
        let mut control = RaceControl::capture(
            deadline,
            self.config.memory_budget,
            &self.cancellation_token,
        );
        if !control.open() {
            return false;
        }

        // Instantiate every clause's violation query up front (a
        // substitution plus constant folding) so the worker owns plain
        // expressions and never touches the portfolio.
        let mut obligations = Vec::new();
        for (clause, horn) in self.problem.clauses().iter().enumerate() {
            if !control.open() {
                return false;
            }
            let Some(violation) = self.cruise_phase_clause_violation_query(&model, horn) else {
                self.log_query_flag_race(
                    false,
                    format!("could not instantiate clause {clause} under the candidate"),
                    budget,
                    started,
                    "skipped",
                );
                return false;
            };
            match violation.simplify_constants() {
                ChcExpr::Bool(false) => {}
                ChcExpr::Bool(true) => {
                    self.log_query_flag_race(
                        false,
                        format!("clause {clause} violation simplified to true: candidate refuted"),
                        budget,
                        started,
                        "skipped",
                    );
                    return false;
                }
                violation => obligations.push((clause, violation)),
            }
        }

        if !control.open() {
            return false;
        }
        let observer = match InterruptObserver::new(&control.cancellation) {
            Ok(observer) => observer,
            Err(_) => return false,
        };
        control.interrupt = observer.interrupt();
        if !control.open() {
            return false;
        }

        let (sender, receiver) = mpsc::channel();
        let signal = CancellationToken::new();
        let count = obligations.len();
        let worker = QueryFlagRaceWorker {
            obligations,
            model,
            control: control.clone(),
            signal: signal.clone(),
            sender,
        };
        let spawned = std::thread::Builder::new()
            .name("ay-query-flag-race".to_string())
            .stack_size(ADAPTIVE_SOLVER_STACK_SIZE)
            .spawn(move || {
                // A panicking worker drops its sender; the foreground sees
                // `Disconnected` and settles the race without a verdict.
                let _ = std::panic::catch_unwind(AssertUnwindSafe(move || worker.run()));
            });
        let worker = match spawned {
            Ok(worker) => worker,
            Err(_) => {
                self.log_query_flag_race(
                    false,
                    "worker thread could not be spawned; synchronous prepass keeps its slot"
                        .to_string(),
                    budget,
                    started,
                    "skipped",
                );
                return false;
            }
        };

        *lock_race(&self.query_flag_race) = Some(QueryFlagRace {
            started,
            budget,
            signal,
            control,
            observer: Some(observer),
            worker: Some(worker),
            receiver,
            resolution: None,
        });
        self.log_query_flag_race(
            true,
            format!(
                "started: {count} clause obligations, budget {:.1}s",
                budget.as_secs_f64()
            ),
            budget,
            started,
            "started",
        );
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: query-flag candidate validation started in the background ({count} obligations, budget {:.1}s)",
                budget.as_secs_f64()
            );
        }
        true
    }

    /// Wait up to `wait` for the race and publish a proven candidate as
    /// `Safe`. Any other outcome (still running, refuted, exhausted, worker
    /// lost) is `None`; a proof is handed out exactly once.
    pub(crate) fn query_flag_race_wait(
        &self,
        wait: Duration,
        at: &str,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        let mut slot = lock_race(&self.query_flag_race);
        let race = slot.as_mut()?;
        if !race.control.open() {
            race.resolution = Some(Resolution::Settled);
            return None;
        }
        if race.resolution.is_none() {
            // The observer interrupts solver work, not this channel wait.
            // Cancellation is sampled again after receipt; an opaque worker
            // cannot extend this wait beyond the captured deadline.
            let wait = race.control.wait_budget_at(wait, Instant::now());
            let received = if wait.is_zero() {
                race.receiver.try_recv().map_err(|error| match error {
                    TryRecvError::Empty => RecvTimeoutError::Timeout,
                    TryRecvError::Disconnected => RecvTimeoutError::Disconnected,
                })
            } else {
                race.receiver.recv_timeout(wait)
            };
            if !race.control.open() {
                race.resolution = Some(Resolution::Settled);
                return None;
            }
            let elapsed = race.started.elapsed().as_secs_f64();
            let (resolution, gate_result, reason, result) = match received {
                Err(RecvTimeoutError::Timeout) => return None,
                Err(RecvTimeoutError::Disconnected) => (
                    Resolution::Settled,
                    false,
                    format!("worker ended without a verdict after {elapsed:.2}s"),
                    "unknown",
                ),
                Ok(QueryFlagRaceOutcome::Proven(model)) => (
                    Resolution::Proven { model: Some(model) },
                    true,
                    format!("proven in the background after {elapsed:.2}s; picked up {at}"),
                    "safe",
                ),
                Ok(QueryFlagRaceOutcome::Refuted { clause }) => (
                    Resolution::Settled,
                    false,
                    format!(
                        "clause {clause} violation satisfiable after {elapsed:.2}s: candidate is not inductive"
                    ),
                    "unknown",
                ),
                Ok(QueryFlagRaceOutcome::Exhausted { clause }) => (
                    Resolution::Settled,
                    false,
                    format!(
                        "clause {clause} violation undecided when the budget ran out after {elapsed:.2}s"
                    ),
                    "unknown",
                ),
            };
            let (budget, started) = (race.budget, race.started);
            race.resolution = Some(resolution);
            if self.config.verbose {
                safe_eprintln!("Adaptive: query-flag candidate race: {reason}");
            }
            self.log_query_flag_race(gate_result, reason, budget, started, result);
        }
        match race.resolution.as_mut() {
            Some(Resolution::Proven { model }) => model.take().map(|model| {
                (
                    PortfolioResult::Safe(model),
                    ValidationEvidence::FullVerification,
                )
            }),
            _ => None,
        }
    }

    /// Non-blocking [`Self::query_flag_race_wait`].
    pub(crate) fn query_flag_race_poll(
        &self,
        at: &str,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        self.query_flag_race_wait(Duration::ZERO, at)
    }

    /// The proof signal of a race the foreground has not yet resolved.
    fn query_flag_race_signal(&self) -> Option<CancellationToken> {
        lock_race(&self.query_flag_race)
            .as_ref()
            .filter(|race| race.resolution.is_none())
            .map(|race| race.signal.clone())
    }

    /// A route token: a child of the portfolio handle (external cancellation
    /// propagates in) that ALSO observes the query-flag race's proof signal
    /// and the lane owning the calling thread (a ladder-race member or the
    /// race foreground, `adaptive_ladder_race`), so work handed to another
    /// thread stops when the lane is cancelled. Link before handing the token
    /// to a solver.
    pub(crate) fn lane_token(&self) -> CancellationToken {
        let mut token = self.cancellation_token.child();
        if let Some(signal) = self.query_flag_race_signal() {
            token.link_upstream(&signal);
        }
        if let Some(lane) = crate::smt::deadline::current_lane_token() {
            token.link_upstream(&lane);
        }
        token
    }

    /// Ladder-race member that publishes the background query-flag proof the
    /// moment it lands, which decides the race and interrupts every other
    /// participant. Polls without holding the race lock across the wait.
    pub(crate) fn query_flag_race_member(&self) -> Option<(PortfolioResult, ValidationEvidence)> {
        const POLL: Duration = Duration::from_millis(20);
        loop {
            if let Some(result) = self.query_flag_race_poll("as a ladder-race member") {
                return Some(result);
            }
            if self.query_flag_race_signal().is_none()
                || crate::smt::deadline::lane_cancelled()
                || self.cancellation_token.is_cancelled()
            {
                return None;
            }
            std::thread::sleep(POLL);
        }
    }

    /// End of the SimpleLoop ladder: a non-definitive outcome gets one last
    /// poll, then the race is dropped (which interrupts a still-running
    /// worker).
    pub(crate) fn conclude_query_flag_candidate_race(
        &self,
        outcome: (PortfolioResult, ValidationEvidence),
    ) -> (PortfolioResult, ValidationEvidence) {
        let definitive = matches!(
            outcome.0,
            PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_)
        );
        let outcome = if definitive {
            outcome
        } else {
            self.query_flag_race_poll("at the end of the ladder")
                .unwrap_or(outcome)
        };
        let race = lock_race(&self.query_flag_race).take();
        if let Some(race) = race {
            if race.resolution.is_none() {
                self.log_query_flag_race(
                    false,
                    format!(
                        "unresolved when the ladder ended after {:.2}s",
                        race.started.elapsed().as_secs_f64()
                    ),
                    race.budget,
                    race.started,
                    "unknown",
                );
            }
            drop(race);
        }
        outcome
    }

    fn log_query_flag_race(
        &self,
        gate_result: bool,
        gate_reason: String,
        budget: Duration,
        started: Instant,
        result: &'static str,
    ) {
        self.decision_log.log_decision(DecisionEntry {
            stage: STAGE,
            gate_result,
            gate_reason,
            budget_secs: budget.as_secs_f64(),
            elapsed_secs: started.elapsed().as_secs_f64(),
            result,
            lemmas_learned: 0,
            max_frame: 0,
        });
    }
}

#[cfg(test)]
mod control_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::adaptive::AdaptiveConfig;
    use crate::classifier::ProblemClassifier;
    use crate::ChcParser;

    /// lustre shape, and the flag IS 1-inductive (the transition preserves it).
    const ONE_INDUCTIVE: &str = "(set-logic HORN)
(declare-fun state (Int Bool) Bool)
(assert (forall ((x Int) (ok Bool)) (=> (and (= x 0) ok) (state x ok))))
(assert (forall ((x Int) (ok Bool) (x1 Int) (ok1 Bool))
  (=> (and (state x ok) (= x1 (+ x 1)) (= ok1 ok)) (state x1 ok1))))
(assert (forall ((x Int) (ok Bool)) (=> (and (state x ok) (not ok)) false)))";

    /// Same shape; the flag alone is NOT inductive (`x1 < 10` is needed too).
    const NOT_INDUCTIVE: &str = "(set-logic HORN)
(declare-fun state (Int Bool) Bool)
(assert (forall ((x Int) (ok Bool)) (=> (and (= x 0) ok) (state x ok))))
(assert (forall ((x Int) (ok Bool) (x1 Int) (ok1 Bool))
  (=> (and (state x ok) (= x1 (+ x 1)) (= ok1 (and ok (< x1 10)))) (state x1 ok1))))
(assert (forall ((x Int) (ok Bool)) (=> (and (state x ok) (not ok)) false)))";

    fn portfolio(source: &str, config: AdaptiveConfig) -> AdaptivePortfolio {
        let problem = ChcParser::parse(source).expect("fixture parses");
        AdaptivePortfolio::new(problem, config)
    }

    fn budgeted() -> AdaptiveConfig {
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(20))
    }

    #[test]
    fn one_inductive_flag_is_proven_in_the_background_and_handed_out_once() {
        let portfolio = portfolio(ONE_INDUCTIVE, budgeted());
        let features = ProblemClassifier::classify(&portfolio.problem);
        assert!(portfolio.start_query_flag_candidate_race(&features, None));
        let result = portfolio.query_flag_race_wait(Duration::from_secs(15), "test");
        assert!(
            matches!(
                result,
                Some((
                    PortfolioResult::Safe(_),
                    ValidationEvidence::FullVerification
                ))
            ),
            "the 1-inductive flag must be proven"
        );
        assert!(
            portfolio.query_flag_race_poll("test").is_none(),
            "a proof is published exactly once"
        );
    }

    #[test]
    fn refuted_flag_is_never_published() {
        let portfolio = portfolio(NOT_INDUCTIVE, budgeted());
        let features = ProblemClassifier::classify(&portfolio.problem);
        assert!(portfolio.start_query_flag_candidate_race(&features, None));
        assert!(portfolio
            .query_flag_race_wait(Duration::from_secs(15), "test")
            .is_none());
        let (result, _) = portfolio.conclude_query_flag_candidate_race((
            PortfolioResult::Unknown,
            ValidationEvidence::FullVerification,
        ));
        assert!(matches!(result, PortfolioResult::Unknown));
        assert!(
            !portfolio.lane_token().is_cancelled(),
            "no race left: the lane token is a plain child"
        );
    }

    #[test]
    fn proof_signal_cancels_linked_lanes_but_not_the_portfolio_handle() {
        let portfolio = portfolio(ONE_INDUCTIVE, budgeted());
        let features = ProblemClassifier::classify(&portfolio.problem);
        assert!(portfolio.start_query_flag_candidate_race(&features, None));
        let lane = portfolio.lane_token();
        let waited = Instant::now();
        while !lane.is_cancelled() && waited.elapsed() < Duration::from_secs(15) {
            std::thread::sleep(Duration::from_millis(10));
        }
        assert!(lane.is_cancelled(), "the proof signal must reach the lane");
        assert!(
            !portfolio.cancellation_token.is_cancelled(),
            "the shared portfolio handle is never cancelled by the race"
        );
        assert!(matches!(
            portfolio.query_flag_race_poll("test"),
            Some((PortfolioResult::Safe(_), _))
        ));
    }

    #[test]
    fn deterministic_mode_never_starts_a_race() {
        let mut config = budgeted();
        config.execution_mode = AdaptiveExecutionMode::DeterministicSequential;
        let portfolio = portfolio(ONE_INDUCTIVE, config);
        let features = ProblemClassifier::classify(&portfolio.problem);
        assert!(!portfolio.start_query_flag_candidate_race(&features, None));
        assert!(portfolio.query_flag_race_poll("test").is_none());
    }
}
