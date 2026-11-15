// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Direct-BMC ownership starts before cloning or portfolio preprocessing.
//! Polls delimit opaque transforms; this is not a per-allocation or hard
//! cancellation-latency guarantee. Replay retains its separately owned budget.

use super::*;
use crate::adaptive::ConstructionStage;
use crate::bmc::memory::Budget;
use ay_core::time::Instant;
use std::cell::Cell;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Stop {
    Cancellation,
    Deadline,
    Memory,
    DeadlineOverflow,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    SourceClone,
    Construction(ConstructionStage),
    Engine,
    Cleanup,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum EngineProgress {
    NotStarted,
    Started,
}

pub(super) struct Attempt {
    started_at: Instant,
    deadline: Option<Instant>,
    cancellation: CancellationToken,
    pub(super) memory: Budget,
    stopped: Cell<Option<Stop>>,
}

impl Attempt {
    pub(super) fn capture(config: &mut BmcConfig) -> Self {
        let started_at = Instant::now();
        let requested = config
            .time_budget
            .and_then(|budget| started_at.checked_add(budget));
        let overflow = config.time_budget.is_some() && requested.is_none();
        let deadline = [
            requested,
            crate::smt::current_thread_solve_deadline(),
            crate::smt::deadline::current_smt_deadline(),
        ]
        .into_iter()
        .flatten()
        .min();
        let cancellation = config
            .base
            .cancellation_token
            .as_ref()
            .map(CancellationToken::sticky_child)
            .unwrap_or_default();
        config.base.cancellation_token = Some(cancellation.clone());
        Self {
            started_at,
            deadline,
            cancellation,
            memory: Budget::capture(config.memory_budget, None),
            stopped: Cell::new(overflow.then_some(Stop::DeadlineOverflow)),
        }
    }

    fn open_at(&self, now: Instant) -> bool {
        if self.stopped.get().is_none() {
            let stop = if self.cancellation.is_cancelled() {
                Some(Stop::Cancellation)
            } else if self.deadline.is_some_and(|deadline| now >= deadline) {
                Some(Stop::Deadline)
            } else if !self.memory.open() {
                Some(Stop::Memory)
            } else {
                None
            };
            self.stopped.set(stop);
        }
        self.stopped.get().is_none()
    }

    fn open(&self) -> bool {
        self.open_at(Instant::now())
    }

    fn refusal(&self, max_depth: usize, engine: EngineProgress) -> VerifiedChcResult {
        use crate::engine_result::VerifiedUnknownMarker;
        // Only the constructor boundary knows the deepest reached level is
        // exactly zero. Do not invent a post-engine depth or label cancellation
        // as time-budget exhaustion; those retain the existing catch-all.
        let marker =
            if engine == EngineProgress::NotStarted && self.stopped.get() == Some(Stop::Deadline) {
                VerifiedUnknownMarker::bmc_budget_exhausted(0, max_depth)
            } else {
                VerifiedUnknownMarker::new()
            };
        VerifiedChcResult::Unknown(marker)
    }

    pub(super) fn solve(
        &self,
        problem: impl FnOnce() -> ChcProblem,
        config: BmcConfig,
    ) -> VerifiedChcResult {
        self.solve_observed(problem, config, &mut |_| {})
    }

    fn solve_observed(
        &self,
        problem: impl FnOnce() -> ChcProblem,
        config: BmcConfig,
        observe: &mut dyn FnMut(Phase),
    ) -> VerifiedChcResult {
        let _memory = self.memory.install();
        let max_depth = config.max_depth;
        let mut engine = EngineProgress::NotStarted;
        let result = (|| {
            if !self.open() {
                return self.refusal(max_depth, EngineProgress::NotStarted);
            }
            observe(Phase::SourceClone);
            if !self.open() {
                return self.refusal(max_depth, EngineProgress::NotStarted);
            }
            let problem = problem();
            let adaptive = AdaptivePortfolio::new_for_bmc_until(
                problem,
                self.started_at,
                self.deadline,
                &self.cancellation,
                &mut |stage| {
                    observe(Phase::Construction(stage));
                    self.open()
                },
            );
            if !self.open() {
                return self.refusal(max_depth, EngineProgress::NotStarted);
            }
            observe(Phase::Engine);
            if !self.open() {
                return self.refusal(max_depth, EngineProgress::NotStarted);
            }
            engine = EngineProgress::Started;
            // The portfolio inherits the original absolute boundary; its worker
            // clamps search to the remaining time without changing admission
            // policy (e.g. the existing >=20s condense gate).
            adaptive.solve_bmc_only(config)
        })();
        // The portfolio/problem and all worker-owned state are disposed before
        // the final observation. A reset cannot revive any previously seen stop.
        observe(Phase::Cleanup);
        if self.open()
            || (self.stopped.get() == Some(Stop::Deadline)
                && result.unknown_reason()
                    == Some(crate::VerifiedUnknownReason::BmcBudgetExhausted))
        {
            // Preserve an engine's actual reached-depth metadata when it
            // already reported this same deadline, never a bounded-search
            // completion or a candidate verdict after refusal.
            result
        } else {
            self.refusal(max_depth, engine)
        }
    }
}

#[cfg(test)]
mod tests;
