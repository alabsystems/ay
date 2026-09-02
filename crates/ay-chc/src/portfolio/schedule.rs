// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Engine scheduling for the CHC portfolio.
//!
//! Handles spawning solver threads, parallel execution with cancellation,
//! and sequential execution with per-engine timeouts.

use super::accept::AcceptDecision;
use super::engines::run_engine;
use super::{PortfolioResult, PortfolioSolver};
use crate::blackboard::{BlackboardHintProvider, SharedBlackboard};
#[cfg(test)]
use std::cell::Cell;
use std::sync::{mpsc, Arc};
use std::thread;
use std::time::Duration;

/// Stack size for portfolio solver threads (8 MB).
///
/// With `impl Drop for ChcExpr` (iterative, O(1) stack) and stacker
/// guards on all recursive traversal paths, 8 MB is sufficient. Deep
/// recursion is handled by stacker::maybe_grow (heap-backed segments)
/// and Drop no longer recurses into children.
///
/// Reduced from 128 MB → 32 MB → 8 MB:
/// - 128 → 32 MB: added stacker guards to P0 recursion sites.
/// - 32 → 8 MB: implemented iterative Drop for ChcExpr, eliminating
///   the last source of implicit deep recursion.
///   12 engines × 8 MB = 96 MB total (vs the original 1.5 GB).
const SOLVER_THREAD_STACK_SIZE: usize = 8 * 1024 * 1024;

/// Grace period after the parallel timeout fires (#7899).
///
/// When the portfolio timeout expires, engines are cooperatively cancelled.
/// However, an engine may be in the final stage of its proof (e.g., the last
/// SMT check before returning Safe) when the timeout fires. Without a grace
/// period, the portfolio returns Unknown even though a definitive result is
/// milliseconds away. This is the primary source of verdict non-determinism:
/// identical harnesses return PROOF on one run and UNKNOWN on the next,
/// depending on whether the winning engine finishes just before or just after
/// the timeout.
///
/// The grace period drains the result channel for this duration after
/// cancellation, accepting only definitive results timestamped before the
/// timeout. This recovers delayed channel publication without extending the
/// solver's semantic deadline.
///
/// Why 2000ms (#7899): The previous 500ms grace was insufficient for model-checker-consumer
/// harnesses where PDR's final SMT check (inductive invariant verification)
/// takes 500-1500ms depending on OS scheduling and memory pressure. 2000ms
/// captures >99% of "just barely missed the timeout" cases based on
/// empirical measurement of model-checker-consumer probe_pop_each_field harnesses. The cost
/// is at most 2s added to the total solve time, which is acceptable for a
/// 27-30s budget (the portfolio already timed out, so the extra 2s is within
/// the 3s margin between the 27s solve budget and 30s wall-clock limit).
const PARALLEL_TIMEOUT_GRACE_PERIOD: Duration = Duration::from_secs(2);

/// Grace period for sequential engine timeouts (#7899).
///
/// When a sequential engine's budget expires, the engine is cooperatively
/// cancelled. This grace period allows it to finish if it was already in
/// its final computation. Shorter than the parallel grace because sequential
/// mode retries with the next engine, so over-waiting here steals budget
/// from subsequent engines. 500ms is enough to capture final SMT checks
/// without significantly impacting the remaining budget.
const SEQUENTIAL_ENGINE_GRACE_PERIOD: Duration = Duration::from_millis(500);

type ParallelWorkerMessage = (
    usize,
    super::types::EngineResult,
    Duration,
    ay_core::time::Instant,
);

#[derive(Clone, Copy)]
struct ParallelLaunchInputs<'a> {
    problem: &'a crate::ChcProblem,
    blackboard: &'a Arc<SharedBlackboard>,
    cancellation: &'a crate::cancellation::CancellationToken,
    sender: &'a mpsc::Sender<ParallelWorkerMessage>,
    term_memory_budget: Option<usize>,
}

struct ParallelQueueState {
    next_engine: usize,
    worker_limit: usize,
    launched: Vec<bool>,
    spawn_failed: Vec<bool>,
    admission_timed_out: Vec<bool>,
    launch_budgets: Vec<Duration>,
    launched_at: Vec<Option<ay_core::time::Instant>>,
    deadlines: Vec<Option<ay_core::time::Instant>>,
    planned_budgets: Vec<Duration>,
}

impl ParallelQueueState {
    fn new(worker_limit: usize, planned_budgets: Vec<Duration>) -> Self {
        let engine_count = planned_budgets.len();
        Self {
            next_engine: 0,
            worker_limit,
            launched: vec![false; engine_count],
            spawn_failed: vec![false; engine_count],
            admission_timed_out: vec![false; engine_count],
            launch_budgets: vec![Duration::ZERO; engine_count],
            launched_at: vec![None; engine_count],
            deadlines: vec![None; engine_count],
            planned_budgets,
        }
    }

    fn budget_for(&self, idx: usize, fallback: Duration) -> Duration {
        if self.was_launched(idx) || self.spawn_failed(idx) || self.admission_timed_out(idx) {
            self.launch_budgets.get(idx).copied().unwrap_or(fallback)
        } else {
            Duration::ZERO
        }
    }

    fn was_launched(&self, idx: usize) -> bool {
        self.launched.get(idx).copied().unwrap_or(false)
    }

    fn spawn_failed(&self, idx: usize) -> bool {
        self.spawn_failed.get(idx).copied().unwrap_or(false)
    }

    fn admission_timed_out(&self, idx: usize) -> bool {
        self.admission_timed_out.get(idx).copied().unwrap_or(false)
    }

    fn elapsed_since_launch(&self, idx: usize, now: ay_core::time::Instant) -> Duration {
        self.launched_at
            .get(idx)
            .copied()
            .flatten()
            .map_or(Duration::ZERO, |launched_at| {
                now.saturating_duration_since(launched_at)
            })
    }

    fn deadline_for(&self, idx: usize) -> Option<ay_core::time::Instant> {
        self.deadlines.get(idx).copied().flatten()
    }

    fn missing_stop_reason(
        &self,
        idx: usize,
        launched_reason: super::types::EngineStopReason,
    ) -> super::types::EngineStopReason {
        if self.spawn_failed(idx) {
            super::types::EngineStopReason::LaunchFailed
        } else if self.admission_timed_out(idx) {
            super::types::EngineStopReason::Timeout
        } else if self.was_launched(idx) {
            launched_reason
        } else {
            super::types::EngineStopReason::NotStarted
        }
    }
}

enum ParallelSpawnOutcome {
    Spawned(thread::JoinHandle<()>),
    Blocked,
    Failed,
}

/// Panic-safe ownership of every worker spawned by one parallel invocation.
///
/// Explicit scheduler exits call [`Self::reap`]. If validation or reporting
/// unwinds first, Drop still cancels and joins every worker, preserving the
/// no-hidden-overlap contract for embedding callers that catch AY panics.
struct ParallelWorkerGroup {
    handles: Option<Vec<(usize, thread::JoinHandle<()>)>>,
    cancellation: crate::cancellation::CancellationToken,
    verbose: bool,
}

impl ParallelWorkerGroup {
    fn new(cancellation: crate::cancellation::CancellationToken, verbose: bool) -> Self {
        Self {
            handles: Some(Vec::new()),
            cancellation,
            verbose,
        }
    }

    fn active_count(&self) -> usize {
        self.handles.as_ref().map_or(0, Vec::len)
    }

    fn attach(&mut self, idx: usize, handle: thread::JoinHandle<()>) {
        if let Some(handles) = self.handles.as_mut() {
            handles.push((idx, handle));
        }
    }

    /// Join a worker that has published its result, freeing one scheduler slot.
    fn reap_finished(&mut self, idx: usize) {
        let Some(handles) = self.handles.as_mut() else {
            return;
        };
        let Some(position) = handles
            .iter()
            .position(|(worker_idx, _)| *worker_idx == idx)
        else {
            return;
        };
        let (_, handle) = handles.swap_remove(position);
        if let Err(payload) = handle.join() {
            safe_eprintln!(
                "Portfolio: Engine {} panicked after publishing: {}",
                idx,
                panic_message(&*payload)
            );
        }
    }

    fn reap(&mut self, reason: &'static str) {
        if let Some(handles) = self.handles.take() {
            PortfolioSolver::reap_parallel_workers(handles, self.verbose, reason);
        }
    }
}

impl Drop for ParallelWorkerGroup {
    fn drop(&mut self) {
        self.cancellation.cancel();
        self.reap("scheduler unwind");
    }
}

#[cfg(test)]
std::thread_local! {
    pub(super) static FORCE_SOLVER_THREAD_SPAWN_FAILURE: Cell<bool> = const { Cell::new(false) };
    pub(super) static PARALLEL_TEST_PREPARE_DELAY: Cell<Option<(usize, Duration)>> = const { Cell::new(None) };
    pub(super) static PARALLEL_TEST_DISABLE_LANE_TIMER: Cell<Option<usize>> = const { Cell::new(None) };
}

/// Extract a human-readable message from a panic payload.
pub(super) fn panic_message(payload: &(dyn std::any::Any + Send)) -> String {
    if let Some(s) = payload.downcast_ref::<&str>() {
        (*s).to_string()
    } else if let Some(s) = payload.downcast_ref::<String>() {
        s.clone()
    } else {
        "unknown panic".to_string()
    }
}

impl PortfolioSolver {
    pub(super) fn spawn_solver_thread<F, T>(task: F) -> std::io::Result<thread::JoinHandle<T>>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        #[cfg(test)]
        if FORCE_SOLVER_THREAD_SPAWN_FAILURE.with(Cell::get) {
            return Err(std::io::Error::other(
                "forced solver thread spawn failure for test",
            ));
        }

        thread::Builder::new()
            .stack_size(SOLVER_THREAD_STACK_SIZE)
            .spawn(task)
    }

    /// Reclaim a worker rejected at a deterministic timeout boundary.
    ///
    /// Rust threads cannot be killed and `JoinHandle::join` has no bounded
    /// form. Deterministic execution therefore fails closed: after requesting
    /// cancellation it waits here until the worker exits. This may block
    /// indefinitely if an engine does not honor cancellation, but it provides
    /// the stronger invariant required by obligation batches: this solve never
    /// returns while its worker can still mutate process-global solver state.
    fn reap_deterministic_timeout_worker(
        handle: thread::JoinHandle<()>,
        idx: usize,
        verbose: bool,
    ) {
        if let Err(payload) = handle.join() {
            safe_eprintln!(
                "Portfolio: Engine {} panicked after deterministic timeout: {}",
                idx,
                panic_message(&*payload)
            );
        } else if verbose {
            safe_eprintln!(
                "Portfolio: Engine {} reaped after deterministic timeout",
                idx
            );
        }
    }

    /// Cancelled parallel workers must be gone before a portfolio returns.
    ///
    /// This is intentionally a synchronous fail-closed barrier. A worker that
    /// ignores cooperative cancellation is an engine bug; detaching it would
    /// let its solver state and process-global accounting overlap a successor
    /// query, multiplying the embedding caller's resource envelope.
    fn reap_parallel_workers(
        handles: Vec<(usize, thread::JoinHandle<()>)>,
        verbose: bool,
        reason: &'static str,
    ) {
        for (idx, handle) in handles {
            if let Err(payload) = handle.join() {
                safe_eprintln!(
                    "Portfolio: Engine {} panicked while reaping after {}: {}",
                    idx,
                    reason,
                    panic_message(&*payload)
                );
            } else if verbose {
                safe_eprintln!("Portfolio: Engine {} reaped after {}", idx, reason);
            }
        }
    }

    /// Whether a deterministic result completed inside its allocated share.
    ///
    /// The interval is deliberately half-open: at the exact deadline the
    /// engine has consumed its entire allocation, so the result is late.
    pub(super) fn deterministic_completion_within_budget(
        completed_at: ay_core::time::Instant,
        deadline: ay_core::time::Instant,
    ) -> bool {
        completed_at < deadline
    }

    /// Prepare an engine config with cross-engine sharing infrastructure.
    ///
    /// Injects blackboard, lemma cache, and hint providers into the engine
    /// config. This is the single preparation path used by both parallel
    /// and sequential schedulers (#7946).
    fn prepare_engine(
        engine_config: &mut super::types::EngineConfig,
        blackboard: &Arc<SharedBlackboard>,
        lemma_cache: Option<&crate::lemma_cache::LemmaCache>,
        idx: usize,
        strict_proofs: bool,
    ) {
        engine_config.inject_blackboard(blackboard.clone(), idx);
        engine_config.inject_strict_proofs(strict_proofs);
        if let Some(cache) = lemma_cache {
            engine_config.inject_lemma_cache(cache);
            engine_config.seed_from_lemma_cache(cache);
        }
        if let super::types::EngineConfig::Pdr(ref mut pdr) = engine_config {
            let provider = BlackboardHintProvider::new(blackboard.clone(), idx);
            pdr.user_hint_providers.0.push(Arc::new(provider));
        }
    }

    /// Run an engine with panic recovery (#2723, #7946).
    ///
    /// Wraps `run_engine` in `catch_unwind` with backtrace capture.
    /// On panic, returns the engine's `unknown_result()` variant so
    /// the portfolio can continue with remaining engines.
    fn run_engine_guarded(
        engine_config: super::types::EngineConfig,
        problem: crate::ChcProblem,
        idx: usize,
        verbose: bool,
        term_memory_budget: Option<usize>,
    ) -> super::types::EngineResult {
        let _term_budget_guard =
            crate::smt::SmtContext::scoped_thread_term_memory_budget(term_memory_budget);
        let engine_name = engine_config.name();
        let panic_result = engine_config.unknown_result();

        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            run_engine(engine_config, problem, idx, verbose)
        }));

        match result {
            Ok(engine_result) => engine_result,
            Err(payload) => {
                let bt = std::backtrace::Backtrace::force_capture();
                safe_eprintln!(
                    "Portfolio: Engine {} ({}) panicked: {}\nBacktrace:\n{}",
                    idx,
                    engine_name,
                    panic_message(&*payload),
                    bt
                );
                panic_result
            }
        }
    }

    /// Maximum workers that a bounded parallel portfolio may run at once.
    ///
    /// The host-reported value respects CPU affinity and common container
    /// limits. Untimed portfolios retain the historical all-engine launch:
    /// without an absolute boundary, a non-cooperative engine in the first
    /// wave could otherwise prevent a queued complete engine from ever running.
    fn parallel_worker_limit(&self) -> usize {
        let engine_count = self.config.engines.len().max(1);
        if self.config.parallel_timeout.is_none() && self.construction_deadline.is_none() {
            return engine_count;
        }

        #[cfg(test)]
        if let Some(limit) = self.parallel_worker_limit_override {
            return limit.clamp(1, engine_count);
        }

        std::thread::available_parallelism()
            .map(std::num::NonZeroUsize::get)
            .unwrap_or(1)
            .clamp(1, engine_count)
    }

    /// Spawn one parallel engine in canonical portfolio order.
    fn spawn_parallel_engine(
        &self,
        idx: usize,
        engine_config: &super::types::EngineConfig,
        inputs: ParallelLaunchInputs<'_>,
        engine_deadline: Option<ay_core::time::Instant>,
    ) -> ParallelSpawnOutcome {
        let tx = inputs.sender.clone();
        let problem = inputs.problem.clone();
        let mut engine_config = engine_config.clone();
        Self::prepare_engine(
            &mut engine_config,
            inputs.blackboard,
            None,
            idx,
            self.config.strict_proofs,
        );
        #[cfg(test)]
        PARALLEL_TEST_PREPARE_DELAY.with(|delay| {
            if let Some((delayed_idx, duration)) = delay.get() {
                if delayed_idx == idx {
                    thread::sleep(duration);
                }
            }
        });

        let verbose = self.config.verbose;
        // Per-engine cancellation stays lane-local while observing the shared
        // winner/deadline/external parent. Its timer can release this slot
        // without cancelling sibling engines.
        let token = inputs.cancellation.child();
        let engine_name = engine_config.name();
        let term_memory_budget = inputs.term_memory_budget;
        #[cfg(test)]
        let parallel_test_engine = self.sequential_test_engine.clone();
        #[cfg(test)]
        let parallel_test_publish_delay = self.sequential_test_publish_delay;
        #[cfg(test)]
        let engine_timeout_deadline = PARALLEL_TEST_DISABLE_LANE_TIMER.with(|disabled| {
            if disabled.get() == Some(idx) {
                None
            } else {
                engine_deadline
            }
        });
        #[cfg(not(test))]
        let engine_timeout_deadline = engine_deadline;

        // Preparation can consume the final fraction of this lane's share.
        // Re-check immediately before creating the worker.
        if inputs.cancellation.is_cancelled()
            || ay_core::TermStore::global_memory_exceeded()
            || engine_deadline.is_some_and(|deadline| ay_core::time::Instant::now() >= deadline)
        {
            return ParallelSpawnOutcome::Blocked;
        }

        match Self::spawn_solver_thread(move || {
            let engine_start = ay_core::time::Instant::now();
            let mut config = engine_config;
            let _engine_deadline = crate::smt::ScopedSolveDeadline::new(engine_deadline);
            let _engine_timeout = engine_timeout_deadline.map(|deadline| {
                token
                    .cancel_after(deadline.saturating_duration_since(ay_core::time::Instant::now()))
            });

            // Close the admission race between the coordinator's final check
            // and this OS thread beginning execution.
            let result = if token.is_cancelled()
                || ay_core::TermStore::global_memory_exceeded()
                || engine_deadline.is_some_and(|deadline| ay_core::time::Instant::now() >= deadline)
            {
                config.unknown_result()
            } else {
                let panic_result = config.unknown_result();
                let guarded = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    #[cfg(test)]
                    let test_cancellation = token.clone();
                    config.inject_cancellation_token(token);
                    #[cfg(test)]
                    if let Some(run) = parallel_test_engine {
                        return run(idx, test_cancellation);
                    }
                    Self::run_engine_guarded(config, problem, idx, verbose, term_memory_budget)
                }));
                match guarded {
                    Ok(result) => result,
                    Err(payload) => {
                        safe_eprintln!(
                            "Portfolio: Engine {} ({}) worker wrapper panicked: {}",
                            idx,
                            engine_name,
                            panic_message(&*payload)
                        );
                        panic_result
                    }
                }
            };
            let engine_elapsed = engine_start.elapsed();
            // Completion, not channel delivery, owns the timeout boundary.
            let completed_at = ay_core::time::Instant::now();
            #[cfg(test)]
            if let Some(delay) = parallel_test_publish_delay {
                thread::sleep(delay);
            }
            let _ = tx.send((idx, result, engine_elapsed, completed_at));
        }) {
            Ok(handle) => ParallelSpawnOutcome::Spawned(handle),
            Err(err) => {
                safe_eprintln!(
                    "Portfolio: Failed to spawn engine {} ({}): {}, treating as Unknown",
                    idx,
                    engine_name,
                    err
                );
                ParallelSpawnOutcome::Failed
            }
        }
    }

    /// Fill every free worker slot from the priority-ordered engine queue.
    ///
    /// A failed spawn consumes that queue entry as `LaunchFailed` and
    /// immediately tries the next engine. No call launches after cancellation
    /// or the one absolute parallel deadline.
    fn fill_parallel_worker_slots(
        &self,
        workers: &mut ParallelWorkerGroup,
        queue: &mut ParallelQueueState,
        inputs: ParallelLaunchInputs<'_>,
        parallel_deadline: Option<ay_core::time::Instant>,
    ) {
        while workers.active_count() < queue.worker_limit
            && queue.next_engine < self.config.engines.len()
            && !inputs.cancellation.is_cancelled()
            && !ay_core::TermStore::global_memory_exceeded()
            && parallel_deadline.is_none_or(|deadline| ay_core::time::Instant::now() < deadline)
        {
            let idx = queue.next_engine;
            queue.next_engine += 1;
            let now = ay_core::time::Instant::now();
            let engine_budget = parallel_deadline
                .map_or(Duration::from_secs(u64::MAX), |deadline| {
                    queue.planned_budgets[idx].min(deadline.saturating_duration_since(now))
                });
            if engine_budget.is_zero() {
                continue;
            }
            let engine_deadline = parallel_deadline.map(|_| now + engine_budget);
            queue.launch_budgets[idx] = engine_budget;
            queue.deadlines[idx] = engine_deadline;
            match self.spawn_parallel_engine(
                idx,
                &self.config.engines[idx],
                inputs,
                engine_deadline,
            ) {
                ParallelSpawnOutcome::Spawned(handle) => {
                    queue.launched[idx] = true;
                    queue.launched_at[idx] = Some(ay_core::time::Instant::now());
                    workers.attach(idx, handle);
                }
                ParallelSpawnOutcome::Blocked => {
                    // Preparation may consume only this lane's planned share.
                    // Preserve the canonical queue and immediately try its
                    // successor while the shared portfolio boundary is open.
                    // Shared cancellation, OOM, or the absolute deadline
                    // closes admission for every remaining engine.
                    if inputs.cancellation.is_cancelled()
                        || ay_core::TermStore::global_memory_exceeded()
                        || parallel_deadline
                            .is_some_and(|deadline| ay_core::time::Instant::now() >= deadline)
                    {
                        break;
                    }
                    queue.admission_timed_out[idx] = true;
                }
                ParallelSpawnOutcome::Failed => queue.spawn_failed[idx] = true,
            }
        }
    }

    /// Run engines in parallel, return first definitive result.
    ///
    /// Thin wrapper over [`Self::solve_parallel_impl`] without a budget report.
    pub(super) fn solve_parallel(&self) -> PortfolioResult {
        self.solve_parallel_impl(None)
    }

    /// Run engines in parallel with budget reporting.
    ///
    /// Thin wrapper over [`Self::solve_parallel_impl`] that populates `report`
    /// with per-engine timing data (#8418).
    pub(super) fn solve_parallel_with_report(
        &self,
        report: &mut super::types::BudgetReport,
    ) -> PortfolioResult {
        self.solve_parallel_impl(Some(report))
    }

    /// Unified parallel-solve implementation (#8844).
    ///
    /// Deduplicates the core scheduling loop shared by [`Self::solve_parallel`]
    /// and [`Self::solve_parallel_with_report`]. When `report` is `Some`, the
    /// function records per-engine timing/stop-reason entries as engines finish
    /// or are cancelled; when `None`, the report bookkeeping is elided.
    fn solve_parallel_impl(
        &self,
        mut report: Option<&mut super::types::BudgetReport>,
    ) -> PortfolioResult {
        // Reset global term memory counter for this solve invocation (#2769).
        // Each engine creates its own TermStore; the global counter tracks aggregate
        // allocation so engines can detect OOM conditions cooperatively.
        ay_core::TermStore::reset_global_term_bytes();
        let start_time = ay_core::time::Instant::now();
        // The constructor boundary starts before preprocessing. Never reopen a
        // fresh full parallel timeout after that earlier work consumed time.
        let configured_deadline = self
            .config
            .parallel_timeout
            .map(|timeout| start_time + timeout);
        let parallel_deadline = match (configured_deadline, self.construction_deadline) {
            (Some(configured), Some(construction)) => Some(configured.min(construction)),
            (Some(configured), None) => Some(configured),
            (None, construction) => construction,
        };
        let parallel_budget = parallel_deadline.map_or(Duration::from_secs(u64::MAX), |deadline| {
            deadline.saturating_duration_since(start_time)
        });
        let worker_limit = self.parallel_worker_limit();
        // Only concurrently live engines divide the portfolio term budget.
        ay_core::TermStore::set_engine_count(worker_limit);
        let term_memory_budget = self.config.per_engine_term_budget(worker_limit);

        let engine_problem = self.engine_problem().clone();
        let (tx, rx) = mpsc::channel();

        // Use a child token for cooperative worker stopping. Internal
        // winner/timeout/OOM cancellation must stop engine workers without
        // poisoning `self.cancellation_token`, which is the external-parent
        // token checked by the acceptance validators. Otherwise every grace or
        // queued-result validation is rejected solely because the scheduler
        // cancelled its losers before calling `accept_or_reject`. External
        // cancellation still propagates from the portfolio token into this
        // child and continues to fail closed at the validation boundary.
        let cancellation_token = self.cancellation_token.child();
        // Cancel workers at the absolute boundary even while the coordinator
        // is validating a candidate instead of polling the result channel.
        let _parallel_deadline_guard = parallel_deadline.map(|deadline| {
            cancellation_token
                .cancel_after(deadline.saturating_duration_since(ay_core::time::Instant::now()))
        });

        if self.config.verbose {
            safe_eprintln!(
                "Portfolio: Scheduling {} engines with at most {} concurrent workers",
                self.config.engines.len(),
                worker_limit
            );
            if self.should_run_engines_on_original_problem() {
                safe_eprintln!(
                    "Portfolio: Preprocessing erased all predicates but original problem still has them — running engines on original problem"
                );
            }
        }

        // Create cooperative blackboard for cross-engine lemma sharing (#7910).
        // All PDR engines get a BlackboardHintProvider so they can consume lemmas
        // published by other engines during hint application.
        let blackboard = SharedBlackboard::new();

        // Budget/engine-type metadata needed only for reporting paths.
        let engine_types: Vec<super::types::EngineType> = self
            .config
            .engines
            .iter()
            .map(|e| e.engine_type())
            .collect();

        let planned_budgets = if parallel_deadline.is_some() {
            Self::parallel_engine_budgets(parallel_budget, &self.config, worker_limit)
        } else {
            vec![Duration::from_secs(u64::MAX); self.config.engines.len()]
        };
        let mut workers = ParallelWorkerGroup::new(cancellation_token.clone(), self.config.verbose);
        let mut queue = ParallelQueueState::new(worker_limit, planned_budgets);
        let launch_inputs = ParallelLaunchInputs {
            problem: &engine_problem,
            blackboard: &blackboard,
            cancellation: &cancellation_token,
            sender: &tx,
            term_memory_budget,
        };
        self.fill_parallel_worker_slots(&mut workers, &mut queue, launch_inputs, parallel_deadline);

        // Wait for results with optional timeout
        let best_result = PortfolioResult::Unknown;
        let mut timed_out = false;
        let mut memory_exceeded = false;
        let mut externally_cancelled = false;

        // Witness-LESS Unsafe cexs are stashed here instead of being validated
        // inline in the receive loop below. Their validation runs an array-SAT
        // cross-check / BMC replay that can burn up to REPLAY_BUDGET (~10s)
        // each; doing that inline on this single accept-loop thread lets a
        // couple of slow witness-less cross-checks monopolize the loop and
        // starve a cheap (~12ms), already-validated WITNESSED Unsafe buffered
        // behind them (the portfolio then times out and discards the genuine
        // Unsafe as Unknown). They are drained through the SAME accept pipeline
        // — validation reordered, never skipped — only when no cheaper
        // witnessed/Safe result was accepted inline.
        let mut deferred_witnessless: Vec<(usize, PortfolioResult, bool, &'static str, Duration)> =
            Vec::new();
        let mut accepted_deferred: Option<PortfolioResult> = None;

        loop {
            if self.cancellation_token.is_cancelled() {
                cancellation_token.cancel();
                externally_cancelled = true;
                break;
            }
            if ay_core::TermStore::global_memory_exceeded() {
                cancellation_token.cancel();
                accepted_deferred = self.accept_first_deferred_witnessless(
                    std::mem::take(&mut deferred_witnessless),
                    report.as_deref_mut(),
                );
                memory_exceeded = true;
                break;
            }

            // A completed/rejected/Unknown worker frees one real slot. Refill
            // it from the canonical queue before waiting again; a hung sibling
            // therefore cannot block other slots from advancing.
            self.fill_parallel_worker_slots(
                &mut workers,
                &mut queue,
                launch_inputs,
                parallel_deadline,
            );
            if workers.active_count() == 0 {
                if parallel_deadline
                    .is_some_and(|deadline| ay_core::time::Instant::now() >= deadline)
                {
                    cancellation_token.cancel();
                    timed_out = true;
                } else if self.cancellation_token.is_cancelled() {
                    cancellation_token.cancel();
                    externally_cancelled = true;
                } else if ay_core::TermStore::global_memory_exceeded() {
                    cancellation_token.cancel();
                    memory_exceeded = true;
                }
                accepted_deferred = self.accept_first_deferred_witnessless(
                    std::mem::take(&mut deferred_witnessless),
                    report.as_deref_mut(),
                );
                break;
            }

            // Calculate remaining time against the single absolute boundary.
            let recv_result = if let Some(deadline) = parallel_deadline {
                let now = ay_core::time::Instant::now();
                if now >= deadline {
                    // Stop workers at the boundary before spending time on
                    // deferred validation. The worker token is a child, so this
                    // does not poison the external-parent token observed by
                    // `accept_or_reject`.
                    cancellation_token.cancel();
                    accepted_deferred = self.accept_first_deferred_witnessless(
                        std::mem::take(&mut deferred_witnessless),
                        report.as_deref_mut(),
                    );
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Timeout ({:?}) expired, cancelling all engines",
                            parallel_budget
                        );
                    }
                    timed_out = true;
                    break;
                }
                let remaining = deadline.saturating_duration_since(now);
                if remaining.is_zero() {
                    cancellation_token.cancel();
                    accepted_deferred = self.accept_first_deferred_witnessless(
                        std::mem::take(&mut deferred_witnessless),
                        report.as_deref_mut(),
                    );
                    timed_out = true;
                    break;
                }
                rx.recv_timeout(remaining)
            } else {
                // No timeout - blocking recv
                rx.recv().map_err(|_| mpsc::RecvTimeoutError::Disconnected)
            };

            match recv_result {
                Ok((idx, result, engine_elapsed, completed_at)) => {
                    // The publication proves this worker finished. Join it
                    // before a successor is admitted, so the concurrency cap
                    // applies to live OS threads, not merely solver calls.
                    workers.reap_finished(idx);
                    let (portfolio_result, needs_validation, engine_name) =
                        self.convert_engine_result(result);
                    let completion_deadline = queue.deadline_for(idx).or(parallel_deadline);
                    let completed_within_budget =
                        completion_deadline.is_none_or(|deadline| completed_at < deadline);

                    // Reporting: record this engine's entry before routing.
                    if let Some(r) = report.as_deref_mut() {
                        let stop_reason = if !completed_within_budget {
                            super::types::EngineStopReason::Timeout
                        } else {
                            match &portfolio_result {
                                PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_) => {
                                    super::types::EngineStopReason::Completed
                                }
                                PortfolioResult::Unknown => super::types::EngineStopReason::Unknown,
                                PortfolioResult::NotApplicable => {
                                    super::types::EngineStopReason::NotApplicable
                                }
                            }
                        };
                        r.entries.push(super::types::EngineBudgetEntry {
                            engine: engine_types
                                .get(idx)
                                .copied()
                                .unwrap_or(super::types::EngineType::Pdr),
                            index: idx,
                            budget_allocated: queue.budget_for(idx, parallel_budget),
                            elapsed: engine_elapsed,
                            stop_reason,
                        });
                    }

                    // Every lane allocation is half-open. A result computed at
                    // or after its lane deadline cannot win a channel race;
                    // release that slot so the next configured engine runs.
                    if !completed_within_budget {
                        if parallel_deadline
                            .is_some_and(|deadline| ay_core::time::Instant::now() >= deadline)
                        {
                            cancellation_token.cancel();
                            accepted_deferred = self.accept_first_deferred_witnessless(
                                std::mem::take(&mut deferred_witnessless),
                                report.as_deref_mut(),
                            );
                            timed_out = true;
                            break;
                        }
                        continue;
                    }

                    // Defer WITNESS-LESS Unsafe cexs: stash them and keep
                    // receiving so a cheap WITNESSED Unsafe (or a Safe result)
                    // buffered behind them validates and wins inline first,
                    // instead of a ~10s witness-less array cross-check
                    // monopolizing this loop and starving the genuine Unsafe.
                    // The stash is drained through accept_or_reject at the
                    // loop's natural/timeout exit (validation reordered, never
                    // skipped) if nothing cheaper was accepted.
                    if matches!(
                        &portfolio_result,
                        PortfolioResult::Unsafe(cex) if cex.witness.is_none()
                    ) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "Portfolio: Engine {} ({}) witness-less Unsafe deferred to avoid starving a witnessed result",
                                idx, engine_name
                            );
                        }
                        deferred_witnessless.push((
                            idx,
                            portfolio_result,
                            needs_validation,
                            engine_name,
                            engine_elapsed,
                        ));
                        continue;
                    }

                    if matches!(
                        &portfolio_result,
                        PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_)
                    ) {
                        match self.accept_or_reject(
                            portfolio_result,
                            needs_validation,
                            engine_name,
                            idx,
                        ) {
                            AcceptDecision::Accept(accepted) => {
                                cancellation_token.cancel();
                                if self.config.verbose {
                                    safe_eprintln!("Portfolio: Engine {} returned definitive result, cancelling others", idx);
                                }

                                // No losing worker may outlive the invocation.
                                workers.reap("definitive winner");

                                // Reporting: drain results published before each
                                // synchronously-reaped worker exited, then mark
                                // any unreported engine as superseded.
                                if let Some(r) = report.as_deref_mut() {
                                    while let Ok((other_idx, _, other_elapsed, completed_at)) =
                                        rx.try_recv()
                                    {
                                        let et = engine_types
                                            .get(other_idx)
                                            .copied()
                                            .unwrap_or(super::types::EngineType::Pdr);
                                        let stop_reason = if queue
                                            .deadline_for(other_idx)
                                            .is_some_and(|deadline| completed_at >= deadline)
                                        {
                                            super::types::EngineStopReason::Timeout
                                        } else {
                                            super::types::EngineStopReason::Superseded
                                        };
                                        r.entries.push(super::types::EngineBudgetEntry {
                                            engine: et,
                                            index: other_idx,
                                            budget_allocated: queue
                                                .budget_for(other_idx, parallel_budget),
                                            elapsed: other_elapsed,
                                            stop_reason,
                                        });
                                    }
                                    for (i, engine_type) in engine_types.iter().enumerate() {
                                        if !r.entries.iter().any(|e| e.index == i) {
                                            r.entries.push(super::types::EngineBudgetEntry {
                                                engine: *engine_type,
                                                index: i,
                                                budget_allocated: queue
                                                    .budget_for(i, parallel_budget),
                                                elapsed: queue.elapsed_since_launch(
                                                    i,
                                                    ay_core::time::Instant::now(),
                                                ),
                                                stop_reason: queue.missing_stop_reason(
                                                    i,
                                                    super::types::EngineStopReason::Superseded,
                                                ),
                                            });
                                        }
                                    }
                                    r.entries.sort_by_key(|e| e.index);
                                }

                                return accepted;
                            }
                            AcceptDecision::Reject => {
                                // Match sequential-report semantics: a raw
                                // definitive candidate that fails the mandatory
                                // acceptance pipeline did not complete the
                                // portfolio obligation.
                                if let Some(r) = report.as_deref_mut() {
                                    if let Some(entry) =
                                        r.entries.iter_mut().rev().find(|entry| entry.index == idx)
                                    {
                                        entry.stop_reason = super::types::EngineStopReason::Unknown;
                                    }
                                }
                                continue;
                            }
                        }
                    } else {
                        // Unknown/NotApplicable: if global memory is exceeded,
                        // cancel all remaining engines rather than waiting for
                        // each to discover it independently (#2771).
                        if ay_core::TermStore::global_memory_exceeded() {
                            cancellation_token.cancel();
                            if self.config.verbose {
                                safe_eprintln!(
                                    "Portfolio: Global memory exceeded after engine {} returned Unknown, cancelling remaining",
                                    idx
                                );
                            }
                            memory_exceeded = true;
                            break;
                        }
                    }
                }
                Err(mpsc::RecvTimeoutError::Timeout) => {
                    // Cancel worker children first; validation observes the
                    // separate external-parent token and remains available for
                    // candidates received before the timeout boundary.
                    cancellation_token.cancel();
                    accepted_deferred = self.accept_first_deferred_witnessless(
                        std::mem::take(&mut deferred_witnessless),
                        report.as_deref_mut(),
                    );
                    if self.config.verbose {
                        safe_eprintln!("Portfolio: Timeout expired, cancelling all engines");
                    }
                    timed_out = true;
                    break;
                }
                Err(mpsc::RecvTimeoutError::Disconnected) => {
                    // All engines finished without an inline-accepted result.
                    // Validate any deferred witness-less Unsafe cexs now (no
                    // witnessed/Safe result won inline) before giving up. No
                    // cancel is needed — every engine already disconnected.
                    accepted_deferred = self.accept_first_deferred_witnessless(
                        std::mem::take(&mut deferred_witnessless),
                        report.as_deref_mut(),
                    );
                    break;
                }
            }
        }

        // No more engines may be admitted after the receive loop. Dropping the
        // coordinator sender lets grace terminate as soon as all live workers
        // publish, rather than forcing the full grace interval.
        drop(tx);

        // Grace period drain (#7899): after the main loop exits early (timeout
        // or memory exceeded), drain the channel briefly to capture definitive
        // results from engines that already completed. This eliminates verdict
        // non-determinism caused by:
        // 1. Timeout: an engine completing before the deadline but publishing
        //    milliseconds after it.
        // 2. Memory exceeded: a definitive result already queued in the channel
        //    from an engine that finished before the OOM-triggering Unknown was
        //    received. Without this drain, the arrival order of mpsc messages
        //    determines whether the portfolio returns Safe or Unknown (#7899).
        if (timed_out || memory_exceeded) && accepted_deferred.is_none() {
            let grace = if memory_exceeded {
                // Memory exceeded: results are already in the channel buffer
                // (no engine is still computing a final answer after OOM), so
                // a non-blocking sweep via Duration::ZERO suffices.
                Duration::ZERO
            } else {
                // Timeout: engines may still be finishing their final SMT check.
                PARALLEL_TIMEOUT_GRACE_PERIOD
            };
            let grace_result = self.drain_channel_for_grace_period_impl(
                &rx,
                grace,
                report.as_deref_mut(),
                &engine_types,
                parallel_budget,
                &queue.launch_budgets,
                &queue.deadlines,
            );
            if let Some(accepted) = grace_result {
                if self.config.verbose {
                    let reason = if memory_exceeded {
                        "memory-exceeded drain"
                    } else {
                        "grace period"
                    };
                    safe_eprintln!("Portfolio: Accepted definitive result during {}", reason);
                }

                workers.reap("timeout grace result");

                // Reporting: after every worker is gone, retain its actual
                // completion duration when it published one. These losing
                // results are still superseded by the accepted grace result.
                if let Some(r) = report.as_deref_mut() {
                    while let Ok((other_idx, _, other_elapsed, completed_at)) = rx.try_recv() {
                        if r.entries.iter().any(|entry| entry.index == other_idx) {
                            continue;
                        }
                        let engine = engine_types
                            .get(other_idx)
                            .copied()
                            .unwrap_or(super::types::EngineType::Pdr);
                        let stop_reason = if queue
                            .deadline_for(other_idx)
                            .is_some_and(|deadline| completed_at >= deadline)
                        {
                            super::types::EngineStopReason::Timeout
                        } else {
                            super::types::EngineStopReason::Superseded
                        };
                        r.entries.push(super::types::EngineBudgetEntry {
                            engine,
                            index: other_idx,
                            budget_allocated: queue.budget_for(other_idx, parallel_budget),
                            elapsed: other_elapsed,
                            stop_reason,
                        });
                    }
                    let missing_reason = if timed_out {
                        super::types::EngineStopReason::Timeout
                    } else {
                        super::types::EngineStopReason::Unknown
                    };
                    for (i, engine_type) in engine_types.iter().enumerate() {
                        if !r.entries.iter().any(|e| e.index == i) {
                            r.entries.push(super::types::EngineBudgetEntry {
                                engine: *engine_type,
                                index: i,
                                budget_allocated: queue.budget_for(i, parallel_budget),
                                elapsed: queue
                                    .elapsed_since_launch(i, ay_core::time::Instant::now()),
                                stop_reason: queue.missing_stop_reason(i, missing_reason),
                            });
                        }
                    }
                    r.entries.sort_by_key(|e| e.index);
                }

                return accepted;
            }
        }

        // Always cross a synchronous reaping barrier, including timeout/OOM.
        // The portfolio may overrun its cooperative wall boundary if an engine
        // is slow to cancel, but it fails closed and never hides overlap from a
        // following model-checking obligation.
        let reap_reason = if timed_out {
            "timeout"
        } else if memory_exceeded {
            "memory exhaustion"
        } else if externally_cancelled {
            "external cancellation"
        } else {
            "normal completion"
        };
        workers.reap(reap_reason);

        // Only report final worker durations after the lifecycle barrier. Drain
        // every publication made while joining; a result that completed after
        // timeout remains Timeout rather than being promoted after the boundary.
        if let Some(r) = report {
            let unreported_reason = if timed_out {
                super::types::EngineStopReason::Timeout
            } else {
                super::types::EngineStopReason::Unknown
            };
            while let Ok((idx, _, engine_elapsed, completed_at)) = rx.try_recv() {
                if r.entries.iter().any(|entry| entry.index == idx) {
                    continue;
                }
                let engine = engine_types
                    .get(idx)
                    .copied()
                    .unwrap_or(super::types::EngineType::Pdr);
                let stop_reason = if queue
                    .deadline_for(idx)
                    .is_some_and(|deadline| completed_at >= deadline)
                {
                    super::types::EngineStopReason::Timeout
                } else {
                    unreported_reason
                };
                r.entries.push(super::types::EngineBudgetEntry {
                    engine,
                    index: idx,
                    budget_allocated: queue.budget_for(idx, parallel_budget),
                    elapsed: engine_elapsed,
                    stop_reason,
                });
            }
            let report_time = ay_core::time::Instant::now();
            for (i, engine_type) in engine_types.iter().enumerate() {
                if !r.entries.iter().any(|entry| entry.index == i) {
                    r.entries.push(super::types::EngineBudgetEntry {
                        engine: *engine_type,
                        index: i,
                        budget_allocated: queue.budget_for(i, parallel_budget),
                        elapsed: queue.elapsed_since_launch(i, report_time),
                        stop_reason: queue.missing_stop_reason(i, unreported_reason),
                    });
                }
            }
            r.entries.sort_by_key(|entry| entry.index);
        }

        // A validated deferred witness-less Unsafe (accepted at a loop exit)
        // takes precedence over the Unknown fallback.
        accepted_deferred.unwrap_or(best_result)
    }

    /// Validate and try to accept the deferred witness-LESS Unsafe cexs.
    ///
    /// Witness-less Unsafe cexs are stashed during the parallel receive loop
    /// instead of being validated inline, so their expensive validation (an
    /// array-SAT cross-check / BMC replay, up to REPLAY_BUDGET each) cannot
    /// monopolize the single accept-loop thread and starve a cheap, validated
    /// WITNESSED Unsafe (or Safe) result buffered behind them. This drains the
    /// stash through the SAME `accept_or_reject` soundness pipeline —
    /// validation is reordered, never skipped — accepting the first cex that
    /// validates.
    ///
    /// Worker cancellation uses a child token, so this may safely run after the
    /// timeout/OOM boundary has stopped workers. `accept_or_reject` observes the
    /// distinct portfolio token and still fails closed on external cancellation.
    fn accept_first_deferred_witnessless(
        &self,
        deferred: Vec<(usize, PortfolioResult, bool, &'static str, Duration)>,
        mut report: Option<&mut super::types::BudgetReport>,
    ) -> Option<PortfolioResult> {
        for (idx, result, needs_validation, engine_name, _elapsed) in deferred {
            match self.accept_or_reject(result, needs_validation, engine_name, idx) {
                AcceptDecision::Accept(accepted) => return Some(accepted),
                AcceptDecision::Reject => {
                    if let Some(r) = report.as_deref_mut() {
                        if let Some(entry) =
                            r.entries.iter_mut().rev().find(|entry| entry.index == idx)
                        {
                            entry.stop_reason = super::types::EngineStopReason::Unknown;
                        }
                    }
                }
            }
        }
        None
    }

    /// Drain the result channel after the main loop exits early (#7899).
    ///
    /// Unified implementation shared by both reporting and non-reporting
    /// parallel solves (#8844). Accepts the first definitive (Safe/Unsafe)
    /// result already buffered in the channel or arriving within `grace`, but
    /// only when its completion timestamp precedes that engine's recorded
    /// completion deadline.
    ///
    /// Two calling modes:
    /// - **Timeout** (`grace > 0`): wait up to `grace` for a pre-deadline
    ///   completion whose channel publication was delayed.
    /// - **Memory exceeded** (`grace == 0`): engines have already sent their
    ///   results. Do a non-blocking sweep of all buffered messages via
    ///   `try_recv` to catch definitive results that lost the mpsc delivery
    ///   race against the Unknown that triggered the OOM break.
    ///
    /// When `report` is `Some`, each drained engine produces a report entry.
    fn drain_channel_for_grace_period_impl(
        &self,
        rx: &mpsc::Receiver<(
            usize,
            super::types::EngineResult,
            Duration,
            ay_core::time::Instant,
        )>,
        grace: Duration,
        mut report: Option<&mut super::types::BudgetReport>,
        engine_types: &[super::types::EngineType],
        parallel_budget: Duration,
        engine_launch_budgets: &[Duration],
        completion_deadlines: &[Option<ay_core::time::Instant>],
    ) -> Option<PortfolioResult> {
        // Record a drained engine in the report (if enabled).
        let record = |report: &mut Option<&mut super::types::BudgetReport>,
                      idx: usize,
                      engine_elapsed: Duration,
                      portfolio_result: &PortfolioResult,
                      completed_within_budget: bool| {
            if let Some(r) = report.as_deref_mut() {
                let stop_reason = if !completed_within_budget {
                    super::types::EngineStopReason::Timeout
                } else {
                    match portfolio_result {
                        PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_) => {
                            super::types::EngineStopReason::Completed
                        }
                        PortfolioResult::NotApplicable => {
                            super::types::EngineStopReason::NotApplicable
                        }
                        PortfolioResult::Unknown => super::types::EngineStopReason::Unknown,
                    }
                };
                r.entries.push(super::types::EngineBudgetEntry {
                    engine: engine_types
                        .get(idx)
                        .copied()
                        .unwrap_or(super::types::EngineType::Pdr),
                    index: idx,
                    budget_allocated: engine_launch_budgets
                        .get(idx)
                        .copied()
                        .unwrap_or(parallel_budget),
                    elapsed: engine_elapsed,
                    stop_reason,
                });
            }
        };

        if grace.is_zero() {
            // Non-blocking sweep: drain all already-buffered messages.
            // This is the memory-exceeded path where results are already
            // in the channel; we just need to check them without waiting.
            loop {
                match rx.try_recv() {
                    Ok((idx, result, engine_elapsed, completed_at)) => {
                        let (portfolio_result, needs_validation, engine_name) =
                            self.convert_engine_result(result);
                        let completed_within_budget = completion_deadlines
                            .get(idx)
                            .copied()
                            .flatten()
                            .is_none_or(|deadline| completed_at < deadline);
                        record(
                            &mut report,
                            idx,
                            engine_elapsed,
                            &portfolio_result,
                            completed_within_budget,
                        );
                        if !completed_within_budget {
                            continue;
                        }
                        if matches!(
                            &portfolio_result,
                            PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_)
                        ) {
                            match self.accept_or_reject(
                                portfolio_result,
                                needs_validation,
                                engine_name,
                                idx,
                            ) {
                                AcceptDecision::Accept(accepted) => {
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "Portfolio: Engine {} returned definitive result during channel drain",
                                            idx
                                        );
                                    }
                                    return Some(accepted);
                                }
                                AcceptDecision::Reject => {
                                    if let Some(r) = report.as_deref_mut() {
                                        if let Some(entry) = r
                                            .entries
                                            .iter_mut()
                                            .rev()
                                            .find(|entry| entry.index == idx)
                                        {
                                            entry.stop_reason =
                                                super::types::EngineStopReason::Unknown;
                                        }
                                    }
                                    continue;
                                }
                            }
                        }
                        // Unknown/NotApplicable: skip, keep draining.
                    }
                    Err(_) => return None, // Empty or disconnected
                }
            }
        }

        // Timed drain: wait up to `grace` for results to arrive.
        let grace_start = ay_core::time::Instant::now();
        loop {
            let remaining = grace.saturating_sub(grace_start.elapsed());
            if remaining.is_zero() {
                return None;
            }
            match rx.recv_timeout(remaining) {
                Ok((idx, result, engine_elapsed, completed_at)) => {
                    let (portfolio_result, needs_validation, engine_name) =
                        self.convert_engine_result(result);
                    let completed_within_budget = completion_deadlines
                        .get(idx)
                        .copied()
                        .flatten()
                        .is_none_or(|deadline| completed_at < deadline);
                    record(
                        &mut report,
                        idx,
                        engine_elapsed,
                        &portfolio_result,
                        completed_within_budget,
                    );
                    if !completed_within_budget {
                        continue;
                    }
                    if matches!(
                        &portfolio_result,
                        PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_)
                    ) {
                        match self.accept_or_reject(
                            portfolio_result,
                            needs_validation,
                            engine_name,
                            idx,
                        ) {
                            AcceptDecision::Accept(accepted) => {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "Portfolio: Engine {} returned definitive result during grace period ({:.0}ms after timeout)",
                                        idx,
                                        grace_start.elapsed().as_secs_f64() * 1000.0
                                    );
                                }
                                return Some(accepted);
                            }
                            AcceptDecision::Reject => {
                                if let Some(r) = report.as_deref_mut() {
                                    if let Some(entry) =
                                        r.entries.iter_mut().rev().find(|entry| entry.index == idx)
                                    {
                                        entry.stop_reason = super::types::EngineStopReason::Unknown;
                                    }
                                }
                                continue;
                            }
                        }
                    }
                    // Unknown/NotApplicable results are ignored during grace period.
                }
                Err(mpsc::RecvTimeoutError::Timeout) => return None,
                Err(mpsc::RecvTimeoutError::Disconnected) => return None,
            }
        }
    }

    /// Compute the per-engine timeout for sequential budget splitting (#7932).
    ///
    /// Splits the remaining wall-clock budget equally across engines still to
    /// run. Each engine receives `remaining / engines_remaining`, capped by
    /// the configured per-engine timeout. If an engine finishes early, its
    /// unused time is automatically available to subsequent engines because
    /// the function re-measures remaining time on each call.
    ///
    /// Previous approach (50% halving) caused exponential budget decay:
    /// with 11 engines, engine 8+ received <0.2% of the total budget,
    /// causing timeout starvation and ERROR harness results (#7932).
    ///
    /// Equal-share allocation guarantees every engine gets at least
    /// `total_budget / N` seconds, while engines that finish early
    /// donate their surplus to the remaining pool.
    ///
    /// Returns the per-engine timeout for the current engine given:
    /// - `total_timeout`: the configured per-engine timeout (portfolio-level)
    /// - `deadline`: absolute wall-clock deadline for the entire sequential solve
    /// - `engines_remaining`: number of engines left to run (including current)
    pub(super) fn budget_for_engine(
        total_timeout: Duration,
        deadline: ay_core::time::Instant,
        engines_remaining: usize,
    ) -> Duration {
        let now = ay_core::time::Instant::now();
        let remaining = deadline.saturating_duration_since(now);
        if remaining.is_zero() {
            return Duration::ZERO;
        }

        if engines_remaining <= 1 {
            // Last engine gets all remaining budget.
            return remaining.min(total_timeout);
        }

        // Equal share: divide remaining budget evenly across remaining engines.
        // This ensures every engine gets a fair share. If earlier engines finish
        // early, their unused time redistributes automatically because we
        // re-measure `remaining` on each call (#7932).
        //
        // Route through `ay_dispatch::FixedOrderSchedule::equal_share` so the
        // shared dispatch crate is the single source of truth for equal-share
        // allocation (#8775). The slot identity is irrelevant here — we only
        // need the per-engine duration — so any uniform `EngineId` value works.
        // Using the first active engine type keeps the call typed and avoids
        // introducing a synthetic placeholder.
        let slots = vec![super::types::EngineType::Pdr; engines_remaining];
        let schedule = ay_dispatch::FixedOrderSchedule::equal_share(slots, remaining);
        let equal_share = schedule
            .entries()
            .first()
            .map(|(_, d)| *d)
            .unwrap_or(Duration::ZERO);

        // Cap at the configured per-engine timeout (don't exceed what the
        // caller requested even if there's plenty of wall-clock budget left).
        equal_share.min(total_timeout)
    }

    /// Compute per-engine budget with policy-aware allocation (#8418).
    ///
    /// Like `budget_for_engine` but also considers [`BudgetPolicy`] settings
    /// from the portfolio config. Percentage/default policy minima are applied
    /// as floors on top of the equal-share computation. `Fixed` replaces the
    /// equal share exactly.
    ///
    /// Returns the per-engine timeout adjusted for the engine's policy.
    pub(super) fn budget_for_engine_with_policy(
        total_timeout: Duration,
        deadline: ay_core::time::Instant,
        engines_remaining: usize,
        engine_config: &super::types::EngineConfig,
        portfolio_config: &super::types::PortfolioConfig,
    ) -> Duration {
        let base_budget = Self::budget_for_engine(total_timeout, deadline, engines_remaining);

        if portfolio_config.engine_budgets.is_empty() {
            return base_budget;
        }

        let engine_type = engine_config.engine_type();
        let num_active = portfolio_config.engines.len();
        if let Some(policy_budget) =
            portfolio_config.compute_engine_budget(engine_type, total_timeout, num_active)
        {
            let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
            let requested = match portfolio_config.budget_policy(engine_type) {
                // Fixed is an exact allocation, not a minimum.
                super::types::BudgetPolicy::Fixed(_) => policy_budget,
                // MinPercent and Default remain floors on the equal share.
                _ => base_budget.max(policy_budget),
            };
            requested.min(remaining)
        } else {
            // Engine is disabled (should not happen if apply_budget_policies ran).
            Duration::ZERO
        }
    }

    /// Precompute a deterministic, policy-aware sequential budget schedule.
    ///
    /// Every active engine starts with the equal share. `MinPercent` may raise
    /// that floor, while `Fixed` replaces it exactly. Allocations are capped by
    /// the unallocated total in configured order because conflicting floors can
    /// exceed 100%; earlier engines win
    /// deterministically. Unused time is not donated after completion, so the
    /// returned vector is independent of runtime.
    pub(super) fn deterministic_engine_budgets(
        total_timeout: Duration,
        portfolio_config: &super::types::PortfolioConfig,
    ) -> Vec<Duration> {
        let num_active = portfolio_config.engines.len();
        if num_active == 0 || total_timeout.is_zero() {
            return vec![Duration::ZERO; num_active];
        }

        let divisor = match u32::try_from(num_active) {
            Ok(divisor) => divisor,
            Err(_) => u32::MAX,
        };
        let equal_share = total_timeout / divisor;
        let mut unallocated = total_timeout;

        portfolio_config
            .engines
            .iter()
            .map(|engine| {
                let policy_budget = portfolio_config
                    .compute_engine_budget(engine.engine_type(), total_timeout, num_active)
                    .unwrap_or(Duration::ZERO);
                let requested = match portfolio_config.budget_policy(engine.engine_type()) {
                    super::types::BudgetPolicy::Fixed(_) => policy_budget,
                    _ => equal_share.max(policy_budget),
                };
                let allocated = requested.min(unallocated);
                unallocated = unallocated.saturating_sub(allocated);
                allocated
            })
            .collect()
    }

    /// Precompute policy-aware budgets for a bounded parallel schedule.
    ///
    /// Concurrent allocations overlap, so their sum must not be capped to one
    /// wall-clock budget as in the sequential planner. The default share is one
    /// equal slice per capacity-sized wave: a roster that fits in one wave keeps
    /// the full timeout, while `N` engines at capacity `C` reserve time for
    /// `ceil(N / C)` waves. `Fixed` replaces that share; `MinPercent` and the
    /// default 5% floor may raise it. The absolute portfolio deadline remains
    /// authoritative, so a roster whose requested allocations exceed total
    /// worker capacity can leave tail engines queued at the boundary.
    pub(super) fn parallel_engine_budgets(
        total_timeout: Duration,
        portfolio_config: &super::types::PortfolioConfig,
        worker_limit: usize,
    ) -> Vec<Duration> {
        let engine_count = portfolio_config.engines.len();
        if engine_count == 0 || total_timeout.is_zero() {
            return vec![Duration::ZERO; engine_count];
        }

        let wave_count = engine_count.div_ceil(worker_limit.max(1));
        let divisor = u32::try_from(wave_count).unwrap_or(u32::MAX);
        let wave_share = total_timeout / divisor;

        portfolio_config
            .engines
            .iter()
            .map(|engine| {
                let engine_type = engine.engine_type();
                let policy_budget = portfolio_config
                    .compute_engine_budget(engine_type, total_timeout, engine_count)
                    .unwrap_or(Duration::ZERO);
                match portfolio_config.budget_policy(engine_type) {
                    super::types::BudgetPolicy::Disabled => Duration::ZERO,
                    super::types::BudgetPolicy::Fixed(_) => policy_budget,
                    super::types::BudgetPolicy::MinPercent(_) => wave_share.max(policy_budget),
                    super::types::BudgetPolicy::Default => wave_share.max(policy_budget),
                }
            })
            .collect()
    }

    /// Run engines sequentially, stopping on first definitive result.
    ///
    /// Thin wrapper over [`Self::solve_sequential_impl`] without a budget report.
    pub(super) fn solve_sequential(&self) -> PortfolioResult {
        self.solve_sequential_impl(None)
    }

    /// Run engines sequentially with budget reporting (#8418).
    ///
    /// Thin wrapper over [`Self::solve_sequential_impl`] that populates
    /// `report` with per-engine timing data.
    pub(super) fn solve_sequential_with_report(
        &self,
        report: &mut super::types::BudgetReport,
    ) -> PortfolioResult {
        self.solve_sequential_impl(Some(report))
    }

    /// Unified sequential-solve implementation (#8844).
    ///
    /// Deduplicates the core per-engine loop shared by
    /// [`Self::solve_sequential`] and [`Self::solve_sequential_with_report`].
    /// When `report` is `Some`, the function records per-engine timing and
    /// stop-reason entries as engines complete, time out, fail to spawn, or
    /// are skipped due to exhausted budget.
    fn solve_sequential_impl(
        &self,
        mut report: Option<&mut super::types::BudgetReport>,
    ) -> PortfolioResult {
        // Reset global term memory counter for this solve invocation (#2769).
        ay_core::TermStore::reset_global_term_bytes();
        // Set engine count for per-engine memory budgeting (#8600).
        ay_core::TermStore::set_engine_count(1);
        let term_memory_budget = self.config.per_engine_term_budget(1);

        let engine_problem = self.engine_problem().clone();

        if self.config.verbose {
            safe_eprintln!(
                "Portfolio: Running {} engines sequentially",
                self.config.engines.len()
            );
            if self.should_run_engines_on_original_problem() {
                safe_eprintln!(
                    "Portfolio: Preprocessing erased all predicates but original problem still has them — running engines on original problem"
                );
            }
        }

        // Cross-engine lemma transfer cache (#7919).
        // PDR engines that return Unknown export their learned lemmas here.
        // Subsequent PDR engines receive accumulated lemmas at startup via
        // `PdrConfig::lemma_hints`, seeding their search with prior knowledge.
        let lemma_cache = crate::lemma_cache::LemmaCache::new();

        // Create blackboard for cross-engine information sharing (#7910).
        // In sequential mode, BMC publishes its discovered bounds (safe depths,
        // counterexample depths) and PDR reads them to skip redundant work.
        let blackboard = SharedBlackboard::new();

        // Compute a wall-clock deadline for the entire sequential solve (#7932).
        // When `self.config.timeout` is set, the total budget is used to split
        // time across engines so fallbacks get a fair share. Without a timeout,
        // `deadline` is None and engines run without wall-clock limits.
        let schedule_start = ay_core::time::Instant::now();
        let deadline = if self.deterministic_sequential_schedule {
            self.deterministic_global_deadline
                .or_else(|| self.config.timeout.map(|timeout| schedule_start + timeout))
        } else {
            self.config.timeout.map(|timeout| schedule_start + timeout)
        };
        let num_engines = self.config.engines.len();
        let deterministic_budgets = if self.deterministic_sequential_schedule {
            deadline.map(|global_deadline| {
                Self::deterministic_engine_budgets(
                    global_deadline.saturating_duration_since(schedule_start),
                    &self.config,
                )
            })
        } else {
            None
        };

        for (idx, engine_config) in self.config.engines.iter().enumerate() {
            // External cancellation (item 5): the portfolio-level token is only
            // cancelled from outside in sequential mode (e.g. an embedding
            // driver's AdaptivePortfolio::cancellation_handle), so observing it
            // here stops the rotation promptly instead of launching further
            // engines. Degrade-only: returns Unknown, never flips a verdict.
            if self.cancellation_token.is_cancelled() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Portfolio: Externally cancelled before engine {}, returning Unknown",
                        idx
                    );
                }
                break;
            }

            // Check global memory budget before launching next engine (#2771).
            // Previous engine may have exhausted memory and returned Unknown;
            // starting another engine with memory already over budget wastes time.
            if ay_core::TermStore::global_memory_exceeded() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Portfolio: Global memory budget exceeded before engine {}, returning Unknown",
                        idx
                    );
                }
                break;
            }

            let engine_start = ay_core::time::Instant::now();
            let engine_type = engine_config.engine_type();
            let engine_budget_allocated;

            // Track which engine type for validation
            let (result, needs_validation, engine_name) = if let Some(timeout) = self.config.timeout
            {
                // Compute this engine's budget share (#7932, #8418).
                // `budget_for_engine_with_policy` splits remaining wall-clock
                // budget across remaining engines, respecting per-engine
                // budget policies from #8418. Falls back to equal-share
                // allocation when no policies are set.
                let engines_remaining = num_engines - idx;
                let engine_budget = if self.deterministic_sequential_schedule {
                    // The policy-aware share was fixed before any engine ran.
                    // Clamp only to the whole-run wall budget: scheduler and
                    // validation overhead must not reopen time past the global
                    // deadline.
                    deterministic_budgets
                        .as_ref()
                        .and_then(|budgets| budgets.get(idx))
                        .copied()
                        .unwrap_or(Duration::ZERO)
                        .min(
                            deadline
                                .unwrap()
                                .saturating_duration_since(ay_core::time::Instant::now()),
                        )
                } else {
                    Self::budget_for_engine_with_policy(
                        timeout,
                        deadline.unwrap(),
                        engines_remaining,
                        engine_config,
                        &self.config,
                    )
                };
                engine_budget_allocated = engine_budget;
                let engine_deadline = engine_start + engine_budget;

                if engine_budget.is_zero() {
                    let explicit_zero = matches!(
                        self.config.budget_policy(engine_type),
                        super::types::BudgetPolicy::Fixed(fixed) if fixed.is_zero()
                    );
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: No budget remaining for engine {} ({}), skipping",
                            idx,
                            engine_config.name()
                        );
                    }
                    if let Some(r) = report.as_deref_mut() {
                        r.entries.push(super::types::EngineBudgetEntry {
                            engine: engine_type,
                            index: idx,
                            budget_allocated: Duration::ZERO,
                            elapsed: Duration::ZERO,
                            stop_reason: if explicit_zero {
                                super::types::EngineStopReason::NotStarted
                            } else {
                                super::types::EngineStopReason::Timeout
                            },
                        });
                    }
                    if explicit_zero {
                        continue;
                    }
                    break;
                }

                if self.config.verbose {
                    safe_eprintln!(
                        "Portfolio: Engine {} ({}) budget: {:.1}s of {:.1}s remaining",
                        idx,
                        engine_config.name(),
                        engine_budget.as_secs_f64(),
                        deadline
                            .unwrap()
                            .saturating_duration_since(ay_core::time::Instant::now())
                            .as_secs_f64()
                    );
                }

                // Run each engine in a thread so we can enforce a wall-clock timeout without
                // risking a hang (e.g., stuck SMT queries).
                let (tx, rx) = mpsc::channel();

                let mut engine_config = engine_config.clone();

                // Prepare engine with cross-engine sharing (#7946).
                Self::prepare_engine(
                    &mut engine_config,
                    &blackboard,
                    Some(&lemma_cache),
                    idx,
                    self.config.strict_proofs,
                );

                // Item 5a: a successor engine is waiting for this engine's
                // budget share, so let PDR self-report hopeless stagnation
                // (ConvergenceHealth::Stuck) and release the remainder instead
                // of burning it. Only set when another lane exists to try.
                if idx + 1 < num_engines {
                    engine_config.enable_give_up_on_stuck();
                }

                // Per-engine token as a CHILD of the portfolio token (item 5):
                // the budget-expiry cancel below stays engine-local, while an
                // external cancel on the portfolio handle reaches the running
                // engine through the same token. With no external handle this
                // behaves identically to the previous fresh token.
                let cancellation_token = self.cancellation_token.child();
                engine_config.inject_cancellation_token(cancellation_token.clone());
                #[cfg(test)]
                let test_cancellation_token = cancellation_token.clone();

                let problem = engine_problem.clone();
                let verbose = self.config.verbose;
                let engine_name = engine_config.name();
                #[cfg(test)]
                let sequential_test_engine = self.sequential_test_engine.clone();
                #[cfg(test)]
                let sequential_test_publish_delay = self.sequential_test_publish_delay;

                if verbose && !lemma_cache.is_empty() {
                    safe_eprintln!(
                        "Portfolio: Engine {} ({}) seeded with {} cached lemmas (#7907)",
                        idx,
                        engine_name,
                        lemma_cache.len()
                    );
                }

                let handle = match Self::spawn_solver_thread(move || {
                    #[cfg(test)]
                    let result = if let Some(run) = sequential_test_engine {
                        run(idx, test_cancellation_token)
                    } else {
                        Self::run_engine_guarded(
                            engine_config,
                            problem,
                            idx,
                            verbose,
                            term_memory_budget,
                        )
                    };
                    #[cfg(not(test))]
                    let result = Self::run_engine_guarded(
                        engine_config,
                        problem,
                        idx,
                        verbose,
                        term_memory_budget,
                    );
                    // Timestamp completion before publishing the result. The
                    // deterministic receiver uses this timestamp, rather than
                    // its own wake-up time, to decide the exact budget edge.
                    let completed_at = ay_core::time::Instant::now();
                    #[cfg(test)]
                    if let Some(delay) = sequential_test_publish_delay {
                        thread::sleep(delay);
                    }
                    // Ignore send errors: receiver might stop waiting due to timeout.
                    let _ = tx.send((completed_at, result));
                }) {
                    Ok(h) => h,
                    Err(err) => {
                        safe_eprintln!(
                            "Portfolio: Failed to spawn engine {} ({}): {}, treating as Unknown",
                            idx,
                            engine_name,
                            err
                        );
                        if let Some(r) = report.as_deref_mut() {
                            r.entries.push(super::types::EngineBudgetEntry {
                                engine: engine_type,
                                index: idx,
                                budget_allocated: engine_budget,
                                elapsed: engine_start.elapsed(),
                                stop_reason: super::types::EngineStopReason::Unknown,
                            });
                        }
                        continue;
                    }
                };

                let mut handle = Some(handle);
                let receive_budget = if self.deterministic_sequential_schedule {
                    engine_deadline.saturating_duration_since(ay_core::time::Instant::now())
                } else {
                    engine_budget
                };
                let mut received = rx.recv_timeout(receive_budget);

                // `recv_timeout` can reach the deadline even though the worker
                // timestamped a genuine pre-deadline completion: the worker may
                // be descheduled between taking the timestamp and publishing to
                // the channel. Reap first, then drain the now-closed channel so
                // deterministic admission depends only on the worker timestamp,
                // never on receiver wake-up or publication scheduling.
                if self.deterministic_sequential_schedule
                    && matches!(&received, Err(mpsc::RecvTimeoutError::Timeout))
                {
                    cancellation_token.cancel();
                    if let Some(worker) = handle.take() {
                        Self::reap_deterministic_timeout_worker(worker, idx, self.config.verbose);
                    }
                    if let Ok(completed) = rx.try_recv() {
                        received = Ok(completed);
                    }
                }
                let deterministic_boundary_missed = self.deterministic_sequential_schedule
                    && match &received {
                        // The allowed interval is half-open: completion exactly
                        // at the deadline has exhausted the allocated share.
                        Ok((completed_at, _)) => !Self::deterministic_completion_within_budget(
                            *completed_at,
                            engine_deadline,
                        ),
                        Err(mpsc::RecvTimeoutError::Timeout) => true,
                        Err(mpsc::RecvTimeoutError::Disconnected) => false,
                    };
                if deterministic_boundary_missed {
                    cancellation_token.cancel();
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Engine {} crossed fixed {:.1}s budget; rejecting late result",
                            idx,
                            engine_budget.as_secs_f64()
                        );
                    }
                    // Discard an `Ok` value too: recv_timeout may observe a
                    // result after its wall deadline when the receiver wakes
                    // late. Deterministic mode never accepts that race.
                    drop(received);
                    if let Some(worker) = handle.take() {
                        Self::reap_deterministic_timeout_worker(worker, idx, self.config.verbose);
                    }
                    if let Some(r) = report.as_deref_mut() {
                        r.entries.push(super::types::EngineBudgetEntry {
                            engine: engine_type,
                            index: idx,
                            budget_allocated: engine_budget,
                            // Include any cancellation overrun spent inside
                            // the fail-closed reap barrier.
                            elapsed: engine_start.elapsed(),
                            stop_reason: super::types::EngineStopReason::Timeout,
                        });
                    }
                    if deadline
                        .unwrap()
                        .saturating_duration_since(ay_core::time::Instant::now())
                        .is_zero()
                    {
                        return PortfolioResult::Unknown;
                    }
                    // The worker has been synchronously reaped, so continuing
                    // cannot overlap it. The successor receives its own fixed
                    // share, clipped to the remaining whole-run deadline.
                    continue;
                }

                let engine_result = match received {
                    Ok((_completed_at, result)) => {
                        // Engine finished within budget — join to reclaim resources.
                        if let Some(worker) = handle.take() {
                            let _ = worker.join();
                        }
                        result
                    }
                    Err(mpsc::RecvTimeoutError::Timeout) => {
                        // Sequential grace period (#7899): the engine may be in
                        // its final SMT check when the budget expires. Cancel
                        // cooperatively, then wait briefly for the result.
                        // This eliminates the same non-determinism pattern as
                        // the parallel grace period: an engine that finishes
                        // 50ms after its budget would return Unknown without
                        // the grace window, but Safe/Unsafe with it.
                        cancellation_token.cancel();
                        match rx.recv_timeout(SEQUENTIAL_ENGINE_GRACE_PERIOD) {
                            Ok((_completed_at, result)) => {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "Portfolio: Engine {} completed during grace period after {:.1}s budget",
                                        idx,
                                        engine_budget.as_secs_f64()
                                    );
                                }
                                // Join now that engine has sent its result.
                                if let Some(worker) = handle.take() {
                                    let _ = worker.join();
                                }
                                result
                            }
                            Err(_) => {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "Portfolio: Engine {} timed out after {:.1}s budget + grace, trying next",
                                        idx,
                                        engine_budget.as_secs_f64()
                                    );
                                }
                                // Engine still running after grace. Reap it
                                // synchronously before launching a successor so
                                // no portfolio invocation can overlap hidden
                                // solver state with the next engine/query.
                                if let Some(worker) = handle.take() {
                                    let _ = worker.join();
                                }
                                if let Some(r) = report.as_deref_mut() {
                                    r.entries.push(super::types::EngineBudgetEntry {
                                        engine: engine_type,
                                        index: idx,
                                        budget_allocated: engine_budget,
                                        elapsed: engine_start.elapsed(),
                                        stop_reason: super::types::EngineStopReason::Timeout,
                                    });
                                }
                                continue;
                            }
                        }
                    }
                    Err(mpsc::RecvTimeoutError::Disconnected) => {
                        // Channel disconnected = sender thread exited without sending.
                        // This typically means a double panic (panic inside catch_unwind's
                        // error handler) or FFI unwind. Always log — this is a bug (#5565).
                        safe_eprintln!(
                            "Portfolio: Engine {} channel disconnected without result (possible double panic), trying next",
                            idx
                        );
                        // Join handle now that the thread has exited.
                        if let Some(worker) = handle.take() {
                            let _ = worker.join();
                        }
                        if let Some(r) = report.as_deref_mut() {
                            r.entries.push(super::types::EngineBudgetEntry {
                                engine: engine_type,
                                index: idx,
                                budget_allocated: engine_budget,
                                elapsed: engine_start.elapsed(),
                                stop_reason: super::types::EngineStopReason::Unknown,
                            });
                        }
                        continue;
                    }
                };

                self.convert_engine_result(engine_result)
            } else {
                engine_budget_allocated = Duration::from_secs(u64::MAX);
                let engine_name = engine_config.name();

                // Prepare engine with cross-engine sharing (#7946).
                let mut engine_config = engine_config.clone();
                Self::prepare_engine(
                    &mut engine_config,
                    &blackboard,
                    Some(&lemma_cache),
                    idx,
                    self.config.strict_proofs,
                );

                // An unbounded engine still needs to observe a caller-owned
                // cooperative-cancellation parent. Avoid injecting a standalone
                // token into direct portfolios that did not request external
                // cancellation: for PDR, the mere presence of a token enables
                // budget-aware stagnation gates and would otherwise change the
                // historical unbounded solve semantics.
                let cancellation_token = self.cancellation_token.child();
                if self.config.external_cancellation.is_some() {
                    engine_config.inject_cancellation_token(cancellation_token.clone());
                }

                if self.config.verbose && !lemma_cache.is_empty() {
                    safe_eprintln!(
                        "Portfolio: Engine {} ({}) seeded with {} cached lemmas (#7919)",
                        idx,
                        engine_name,
                        lemma_cache.len()
                    );
                }

                #[cfg(test)]
                let result = if let Some(run) = self.sequential_test_engine.clone() {
                    run(idx, cancellation_token)
                } else {
                    Self::run_engine_guarded(
                        engine_config,
                        engine_problem.clone(),
                        idx,
                        self.config.verbose,
                        term_memory_budget,
                    )
                };
                #[cfg(not(test))]
                let result = Self::run_engine_guarded(
                    engine_config,
                    engine_problem.clone(),
                    idx,
                    self.config.verbose,
                    term_memory_budget,
                );
                self.convert_engine_result(result)
            };

            let engine_elapsed = engine_start.elapsed();

            if matches!(
                &result,
                PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_)
            ) {
                match self.accept_or_reject(result, needs_validation, engine_name, idx) {
                    AcceptDecision::Accept(accepted) => {
                        if self.config.verbose {
                            safe_eprintln!("Portfolio: Engine {} returned definitive result", idx);
                        }
                        if let Some(r) = report.as_deref_mut() {
                            r.entries.push(super::types::EngineBudgetEntry {
                                engine: engine_type,
                                index: idx,
                                budget_allocated: engine_budget_allocated,
                                elapsed: engine_elapsed,
                                stop_reason: super::types::EngineStopReason::Completed,
                            });
                        }
                        return accepted;
                    }
                    AcceptDecision::Reject => {
                        if let Some(r) = report.as_deref_mut() {
                            r.entries.push(super::types::EngineBudgetEntry {
                                engine: engine_type,
                                index: idx,
                                budget_allocated: engine_budget_allocated,
                                elapsed: engine_elapsed,
                                stop_reason: super::types::EngineStopReason::Unknown,
                            });
                        }
                        continue;
                    }
                }
            } else {
                if self.config.verbose {
                    safe_eprintln!(
                        "Portfolio: Engine {} returned Unknown, trying next (lemma cache: {} lemmas)",
                        idx,
                        lemma_cache.len()
                    );
                }
                if let Some(r) = report.as_deref_mut() {
                    let stop_reason = match &result {
                        PortfolioResult::NotApplicable => {
                            super::types::EngineStopReason::NotApplicable
                        }
                        // Item 5a: PDR self-reported hopeless stagnation and
                        // released its remaining budget to the next engine.
                        _ if engine_name == "PDR_HOPELESS" => {
                            super::types::EngineStopReason::Hopeless
                        }
                        _ => super::types::EngineStopReason::Unknown,
                    };
                    r.entries.push(super::types::EngineBudgetEntry {
                        engine: engine_type,
                        index: idx,
                        budget_allocated: engine_budget_allocated,
                        elapsed: engine_elapsed,
                        stop_reason,
                    });
                }
            }
        }

        PortfolioResult::Unknown
    }
}
