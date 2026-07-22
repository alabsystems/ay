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
/// cancellation, accepting any definitive result that arrives.
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

#[cfg(test)]
std::thread_local! {
    pub(super) static FORCE_SOLVER_THREAD_SPAWN_FAILURE: Cell<bool> = const { Cell::new(false) };
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
        // Set engine count for per-engine memory budgeting (#8600).
        ay_core::TermStore::set_engine_count(self.config.engines.len());
        let term_memory_budget = self.config.per_engine_term_budget();

        let engine_problem = self.engine_problem().clone();
        let (tx, rx) = mpsc::channel();

        // Use the portfolio's cancellation token for cooperative engine stopping.
        // This same token is checked by validation sub-solvers (validate_unsafe,
        // validate_safe, confirm_bv_abstracted_unsafe) so they bail cooperatively
        // when the portfolio is cancelled or times out (#8630).
        let cancellation_token = self.cancellation_token.clone();

        if self.config.verbose {
            safe_eprintln!(
                "Portfolio: Starting {} engines in parallel",
                self.config.engines.len()
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
        let start_time = ay_core::time::Instant::now();

        // Budget/engine-type metadata needed only for reporting paths.
        let parallel_budget = self
            .config
            .parallel_timeout
            .unwrap_or(Duration::from_secs(u64::MAX));
        let engine_types: Vec<super::types::EngineType> = self
            .config
            .engines
            .iter()
            .map(|e| e.engine_type())
            .collect();

        // Spawn threads for each engine. The message tuple always carries the
        // per-engine elapsed duration; callers without a report simply ignore it.
        let handles: Vec<_> = self
            .config
            .engines
            .iter()
            .enumerate()
            .filter_map(|(idx, engine_config)| {
                let tx = tx.clone();
                let problem = engine_problem.clone();
                let mut engine_config = engine_config.clone();

                // Prepare engine with cross-engine sharing (#7946).
                Self::prepare_engine(
                    &mut engine_config,
                    &blackboard,
                    None,
                    idx,
                    self.config.strict_proofs,
                );

                let verbose = self.config.verbose;
                let token = cancellation_token.clone();
                let engine_name = engine_config.name();

                match Self::spawn_solver_thread(move || {
                    let engine_start = ay_core::time::Instant::now();
                    let mut config = engine_config;
                    config.inject_cancellation_token(token);
                    let result =
                        Self::run_engine_guarded(config, problem, idx, verbose, term_memory_budget);
                    let engine_elapsed = engine_start.elapsed();
                    // Ignore send errors - receiver might have dropped if another engine won
                    let _ = tx.send((idx, result, engine_elapsed));
                }) {
                    Ok(handle) => Some(handle),
                    Err(err) => {
                        safe_eprintln!(
                            "Portfolio: Failed to spawn engine {} ({}): {}, treating as Unknown",
                            idx,
                            engine_name,
                            err
                        );
                        None
                    }
                }
            })
            .collect();

        if handles.is_empty() {
            if self.config.verbose {
                safe_eprintln!("Portfolio: Failed to spawn all engines, returning Unknown");
            }
            return PortfolioResult::Unknown;
        }

        // Drop original sender so channel closes when all threads finish
        drop(tx);

        // Wait for results with optional timeout
        let best_result = PortfolioResult::Unknown;
        let mut timed_out = false;
        let mut memory_exceeded = false;

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
            // Calculate remaining timeout (if any)
            let recv_result = if let Some(timeout) = self.config.parallel_timeout {
                let elapsed = start_time.elapsed();
                if elapsed >= timeout {
                    // Validate any deferred witness-less Unsafe cexs BEFORE
                    // cancelling: accept_or_reject early-bails on a cancelled
                    // token (#8630), so a stashed genuine Unsafe would be lost
                    // if we cancelled first.
                    accepted_deferred = self.accept_first_deferred_witnessless(std::mem::take(
                        &mut deferred_witnessless,
                    ));
                    // Timeout expired - cancel all engines and return Unknown
                    cancellation_token.cancel();
                    if self.config.verbose {
                        safe_eprintln!(
                            "Portfolio: Timeout ({:?}) expired, cancelling all engines",
                            timeout
                        );
                    }
                    timed_out = true;
                    break;
                }
                let remaining = timeout.saturating_sub(elapsed);
                if remaining.is_zero() {
                    accepted_deferred = self.accept_first_deferred_witnessless(std::mem::take(
                        &mut deferred_witnessless,
                    ));
                    cancellation_token.cancel();
                    timed_out = true;
                    break;
                }
                rx.recv_timeout(remaining)
            } else {
                // No timeout - blocking recv
                rx.recv().map_err(|_| mpsc::RecvTimeoutError::Disconnected)
            };

            match recv_result {
                Ok((idx, result, engine_elapsed)) => {
                    let (portfolio_result, needs_validation, engine_name) =
                        self.convert_engine_result(result);

                    // Reporting: record this engine's entry before routing.
                    if let Some(r) = report.as_deref_mut() {
                        let stop_reason = match &portfolio_result {
                            PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_) => {
                                super::types::EngineStopReason::Completed
                            }
                            PortfolioResult::Unknown => super::types::EngineStopReason::Unknown,
                            PortfolioResult::NotApplicable => {
                                super::types::EngineStopReason::NotApplicable
                            }
                        };
                        r.entries.push(super::types::EngineBudgetEntry {
                            engine: engine_types
                                .get(idx)
                                .copied()
                                .unwrap_or(super::types::EngineType::Pdr),
                            index: idx,
                            budget_allocated: parallel_budget,
                            elapsed: engine_elapsed,
                            stop_reason,
                        });
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

                                // Reporting: drain any already-buffered results
                                // and mark unreported engines as superseded.
                                if let Some(r) = report.as_deref_mut() {
                                    while let Ok((other_idx, _, other_elapsed)) = rx.try_recv() {
                                        let et = engine_types
                                            .get(other_idx)
                                            .copied()
                                            .unwrap_or(super::types::EngineType::Pdr);
                                        r.entries.push(super::types::EngineBudgetEntry {
                                            engine: et,
                                            index: other_idx,
                                            budget_allocated: parallel_budget,
                                            elapsed: other_elapsed,
                                            stop_reason: super::types::EngineStopReason::Superseded,
                                        });
                                    }
                                    for (i, engine_type) in engine_types.iter().enumerate() {
                                        if !r.entries.iter().any(|e| e.index == i) {
                                            r.entries.push(super::types::EngineBudgetEntry {
                                                engine: *engine_type,
                                                index: i,
                                                budget_allocated: parallel_budget,
                                                elapsed: start_time.elapsed(),
                                                stop_reason:
                                                    super::types::EngineStopReason::Superseded,
                                            });
                                        }
                                    }
                                    r.entries.sort_by_key(|e| e.index);
                                }

                                return accepted;
                            }
                            AcceptDecision::Reject => continue,
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
                    // Validate any deferred witness-less Unsafe cexs BEFORE
                    // cancelling (accept_or_reject early-bails on cancel, #8630).
                    accepted_deferred = self.accept_first_deferred_witnessless(std::mem::take(
                        &mut deferred_witnessless,
                    ));
                    // Timeout expired - cancel all engines and return Unknown
                    cancellation_token.cancel();
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
                    accepted_deferred = self.accept_first_deferred_witnessless(std::mem::take(
                        &mut deferred_witnessless,
                    ));
                    break;
                }
            }
        }

        // Grace period drain (#7899): after the main loop exits early (timeout
        // or memory exceeded), drain the channel briefly to capture definitive
        // results from engines that already completed. This eliminates verdict
        // non-determinism caused by:
        // 1. Timeout: engines finishing milliseconds after the deadline.
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

                // Reporting: fill any still-unreported engines as Timeout.
                if let Some(r) = report.as_deref_mut() {
                    for (i, engine_type) in engine_types.iter().enumerate() {
                        if !r.entries.iter().any(|e| e.index == i) {
                            r.entries.push(super::types::EngineBudgetEntry {
                                engine: *engine_type,
                                index: i,
                                budget_allocated: parallel_budget,
                                elapsed: start_time.elapsed(),
                                stop_reason: super::types::EngineStopReason::Timeout,
                            });
                        }
                    }
                    r.entries.sort_by_key(|e| e.index);
                }

                return accepted;
            }
        }

        // Reporting: fill any still-unreported engines with a reason matching
        // the loop exit condition, then sort for stable output.
        if let Some(r) = report {
            let overall_elapsed = start_time.elapsed();
            for (i, engine_type) in engine_types.iter().enumerate() {
                if !r.entries.iter().any(|e| e.index == i) {
                    let reason = if timed_out {
                        super::types::EngineStopReason::Timeout
                    } else {
                        super::types::EngineStopReason::Unknown
                    };
                    r.entries.push(super::types::EngineBudgetEntry {
                        engine: *engine_type,
                        index: i,
                        budget_allocated: parallel_budget,
                        elapsed: overall_elapsed,
                        stop_reason: reason,
                    });
                }
            }
            r.entries.sort_by_key(|e| e.index);
        }

        // Always join engine threads to prevent memory leaks. When engine
        // threads are detached (JoinHandle dropped without joining), they
        // continue running — holding their TermStore, SAT solver, theory
        // solvers, and ChcProblem clone — until they eventually observe
        // cancellation and exit. With several portfolios in parallel, delayed
        // reclamation can otherwise multiply memory use across engine sets.
        //
        // When not timed out, joining is cheap (all senders already
        // disconnected). When timed out or OOM, spawn a reaper thread
        // that joins in the background so the portfolio can return
        // immediately without violating its timeout contract.
        if !timed_out && !memory_exceeded {
            for (idx, handle) in handles.into_iter().enumerate() {
                if let Err(payload) = handle.join() {
                    let msg = panic_message(&*payload);
                    safe_eprintln!(
                        "Portfolio: Engine {} thread panicked outside catch_unwind: {}",
                        idx,
                        msg,
                    );
                }
            }
        } else {
            // Spawn a lightweight reaper thread that joins all engine threads.
            // This ensures their memory (TermStore, SAT solver, theory state)
            // is reclaimed when they eventually observe cancellation and exit.
            let verbose = self.config.verbose;
            thread::Builder::new()
                .name("ay-engine-reaper".to_string())
                .spawn(move || {
                    for (idx, handle) in handles.into_iter().enumerate() {
                        if let Err(payload) = handle.join() {
                            let msg = panic_message(&*payload);
                            safe_eprintln!(
                                "Portfolio: Engine {} (reaped) panicked outside catch_unwind: {}",
                                idx,
                                msg,
                            );
                        } else if verbose {
                            safe_eprintln!("Portfolio: Engine {} reaped after timeout/OOM", idx);
                        }
                    }
                })
                .ok(); // If reaper spawn fails, threads are still cancelled and will exit
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
    /// MUST be called BEFORE `cancellation_token.cancel()`: `accept_or_reject`
    /// early-bails on a cancelled token (#8630), which would reject a genuine
    /// deferred Unsafe without validating it.
    fn accept_first_deferred_witnessless(
        &self,
        deferred: Vec<(usize, PortfolioResult, bool, &'static str, Duration)>,
    ) -> Option<PortfolioResult> {
        for (idx, result, needs_validation, engine_name, _elapsed) in deferred {
            match self.accept_or_reject(result, needs_validation, engine_name, idx) {
                AcceptDecision::Accept(accepted) => return Some(accepted),
                AcceptDecision::Reject => {}
            }
        }
        None
    }

    /// Drain the result channel after the main loop exits early (#7899).
    ///
    /// Unified implementation shared by both reporting and non-reporting
    /// parallel solves (#8844). Accepts the first definitive (Safe/Unsafe)
    /// result already buffered in the channel or arriving within `grace`.
    ///
    /// Two calling modes:
    /// - **Timeout** (`grace > 0`): engines may be finishing their final SMT
    ///   check. Wait up to `grace` for a definitive result to arrive.
    /// - **Memory exceeded** (`grace == 0`): engines have already sent their
    ///   results. Do a non-blocking sweep of all buffered messages via
    ///   `try_recv` to catch definitive results that lost the mpsc delivery
    ///   race against the Unknown that triggered the OOM break.
    ///
    /// When `report` is `Some`, each drained engine produces a report entry.
    fn drain_channel_for_grace_period_impl(
        &self,
        rx: &mpsc::Receiver<(usize, super::types::EngineResult, Duration)>,
        grace: Duration,
        mut report: Option<&mut super::types::BudgetReport>,
        engine_types: &[super::types::EngineType],
        parallel_budget: Duration,
    ) -> Option<PortfolioResult> {
        // Record a drained engine in the report (if enabled).
        let record = |report: &mut Option<&mut super::types::BudgetReport>,
                      idx: usize,
                      engine_elapsed: Duration,
                      portfolio_result: &PortfolioResult| {
            if let Some(r) = report.as_deref_mut() {
                let stop_reason = match portfolio_result {
                    PortfolioResult::Safe(_) | PortfolioResult::Unsafe(_) => {
                        super::types::EngineStopReason::Completed
                    }
                    _ => super::types::EngineStopReason::Unknown,
                };
                r.entries.push(super::types::EngineBudgetEntry {
                    engine: engine_types
                        .get(idx)
                        .copied()
                        .unwrap_or(super::types::EngineType::Pdr),
                    index: idx,
                    budget_allocated: parallel_budget,
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
                    Ok((idx, result, engine_elapsed)) => {
                        let (portfolio_result, needs_validation, engine_name) =
                            self.convert_engine_result(result);
                        record(&mut report, idx, engine_elapsed, &portfolio_result);
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
                                AcceptDecision::Reject => continue,
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
                Ok((idx, result, engine_elapsed)) => {
                    let (portfolio_result, needs_validation, engine_name) =
                        self.convert_engine_result(result);
                    record(&mut report, idx, engine_elapsed, &portfolio_result);
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
                            AcceptDecision::Reject => continue,
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
    /// from the portfolio config. The policy minimum is applied as a floor
    /// on top of the equal-share computation, ensuring engines with
    /// `MinPercent` or `Fixed` policies are never starved.
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
            // Use the maximum of equal-share and policy budget.
            // This ensures the policy floor is respected without shrinking
            // engines that would get more from the equal-share algorithm.
            let remaining = deadline.saturating_duration_since(ay_core::time::Instant::now());
            base_budget.max(policy_budget).min(remaining)
        } else {
            // Engine is disabled (should not happen if apply_budget_policies ran).
            Duration::ZERO
        }
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
        ay_core::TermStore::set_engine_count(self.config.engines.len());
        let term_memory_budget = self.config.per_engine_term_budget();

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
        let deadline = self
            .config
            .timeout
            .map(|t| ay_core::time::Instant::now() + t);
        let num_engines = self.config.engines.len();

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

            // Track which engine type for validation
            let (result, needs_validation, engine_name) = if let Some(timeout) = self.config.timeout
            {
                // Compute this engine's budget share (#7932, #8418).
                // `budget_for_engine_with_policy` splits remaining wall-clock
                // budget across remaining engines, respecting per-engine
                // budget policies from #8418. Falls back to equal-share
                // allocation when no policies are set.
                let engines_remaining = num_engines - idx;
                let engine_budget = Self::budget_for_engine_with_policy(
                    timeout,
                    deadline.unwrap(),
                    engines_remaining,
                    engine_config,
                    &self.config,
                );

                if engine_budget.is_zero() {
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
                            stop_reason: super::types::EngineStopReason::Timeout,
                        });
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

                let problem = engine_problem.clone();
                let verbose = self.config.verbose;
                let engine_name = engine_config.name();

                if verbose && !lemma_cache.is_empty() {
                    safe_eprintln!(
                        "Portfolio: Engine {} ({}) seeded with {} cached lemmas (#7907)",
                        idx,
                        engine_name,
                        lemma_cache.len()
                    );
                }

                let handle = match Self::spawn_solver_thread(move || {
                    let result = Self::run_engine_guarded(
                        engine_config,
                        problem,
                        idx,
                        verbose,
                        term_memory_budget,
                    );
                    // Ignore send errors: receiver might stop waiting due to timeout.
                    let _ = tx.send(result);
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

                let engine_result = match rx.recv_timeout(engine_budget) {
                    Ok(result) => {
                        // Engine finished within budget — join to reclaim resources.
                        let _ = handle.join();
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
                            Ok(result) => {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "Portfolio: Engine {} completed during grace period after {:.1}s budget",
                                        idx,
                                        engine_budget.as_secs_f64()
                                    );
                                }
                                // Join now that engine has sent its result.
                                let _ = handle.join();
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
                                // Engine still running after grace — reap on background
                                // thread so we don't block the next engine launch.
                                thread::Builder::new()
                                    .name("ay-seq-reaper".to_string())
                                    .spawn(move || {
                                        let _ = handle.join();
                                    })
                                    .ok();
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
                        let _ = handle.join();
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

                if self.config.verbose && !lemma_cache.is_empty() {
                    safe_eprintln!(
                        "Portfolio: Engine {} ({}) seeded with {} cached lemmas (#7919)",
                        idx,
                        engine_name,
                        lemma_cache.len()
                    );
                }

                let result = Self::run_engine_guarded(
                    engine_config,
                    engine_problem.clone(),
                    idx,
                    self.config.verbose,
                    term_memory_budget,
                );
                self.convert_engine_result(result)
            };

            // Report-only: budget allocated for this engine's entry. The
            // allocation is re-computed here because inside the timeout branch
            // above the budget value was moved into the spawned thread's scope.
            let engine_budget_allocated = if let Some(timeout) = self.config.timeout {
                let engines_remaining = num_engines - idx;
                Self::budget_for_engine_with_policy(
                    timeout,
                    deadline.unwrap_or_else(|| ay_core::time::Instant::now() + timeout),
                    engines_remaining,
                    &self.config.engines[idx],
                    &self.config,
                )
            } else {
                Duration::from_secs(u64::MAX) // unbounded
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
