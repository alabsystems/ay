// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Captured original resources, not invariant/model/counterexample authority.

use super::{ExternalInvariantValidation as Kind, *};
use crate::smt::resource_observation::{current_refusal, ResourceRefusal};
use ay_core::resource::{current_check_stop, CheckStop, Exhausted, ResourceGuard};
use std::sync::{
    atomic::{AtomicBool, AtomicU8, Ordering},
    Arc,
};

/// Capture ONCE on the caller thread, before lowering or reading a cached answer.
/// Clones retain the SAME ticks, absolute wall, sticky refusals and term ceiling.
/// Move a clone into a worker; borrow it for every phase and the final seal fence.
/// Worker minima/handles remain retained through the post-TLS final phase fence.
///
/// No PdrConfig/builder or Eq contract changes. Memory bounds are per-context
/// term storage plus retained refusal, NOT aggregate RSS or worker group charging.
/// The original CheckStop callback is retained, never recovered from worker TLS.
/// A boolean callback stop has no precise cause and is Inconclusive. Polling and
/// callback checks are cooperative, not a hard worker-stop/drain guarantee.
#[derive(Clone)]
pub struct ExternalInvariantValidationOwner {
    inner: Arc<Original>,
}

struct Original {
    guard: ResourceGuard,
    deadline: Instant,
    cancellation: Option<CancellationToken>,
    memory: Budget,
    group: Option<ay_sys::MemoryGroupObservation>,
    stop: Option<CheckStop>,
    first: AtomicU8,
    running: AtomicBool,
    polling: AtomicBool,
}

impl ExternalInvariantValidationOwner {
    /// Capture original caller and ambient minima BEFORE any protected phase.
    /// None inherits the caller's term cap; Some(0) is terminal before work.
    /// A missing wall uses the existing validation default ONCE at capture.
    /// An already-observed TLS refusal is copied, never cleared or moved.
    pub fn capture(original: &ResourceGuard, config: &PdrConfig) -> Self {
        let now = Instant::now();
        let requested =
            now.checked_add(config.solve_timeout.unwrap_or(PDR_PROOF_VALIDATION_TIMEOUT));
        let deadline = [
            requested,
            original.effective_deadline(),
            crate::smt::deadline::effective_thread_deadline(),
        ]
        .into_iter()
        .flatten()
        .min()
        .unwrap_or(now);
        let lane = crate::smt::deadline::try_lane_cancellation();
        let (ambient, ambient_interrupt) = lane.clone().unwrap_or((None, None));
        let mut cancellation = config.effective_cancellation_token();
        if let Some(ambient) = ambient {
            cancellation
                .get_or_insert_with(CancellationToken::new)
                .link_upstream(&ambient);
        }
        let group = ay_sys::try_current_memory_group_observation();
        let stop = current_check_stop();
        let prior = current_refusal();
        let unavailable = lane.is_err() || group.is_err() || stop.is_err() || prior.is_err();
        for flag in [original.cancel_flag(), ambient_interrupt.as_ref()]
            .into_iter()
            .flatten()
        {
            cancellation
                .get_or_insert_with(CancellationToken::new)
                .link_interrupt_flag(flag);
        }
        let owner = Self {
            inner: Arc::new(Original {
                guard: original.clone(),
                deadline,
                cancellation: cancellation.as_ref().map(CancellationToken::sticky_child),
                memory: Budget::capture(config.memory_budget(), None),
                group: group.ok().flatten(),
                stop: stop.ok().flatten(),
                first: AtomicU8::new(0),
                running: AtomicBool::new(false),
                polling: AtomicBool::new(false),
            }),
        };
        if let Ok(Some(reason)) = prior {
            owner.inner.record(from_resource(reason));
        }
        if requested.is_none() || unavailable {
            owner.inner.record(Kind::Inconclusive);
        }
        let _ = owner.check();
        owner
    }

    /// The immutable original absolute wall; no phase starts a new clock.
    pub fn deadline(&self) -> Instant {
        self.inner.deadline
    }

    /// Original captured term-store ceiling, before further worker tightening.
    pub fn memory_budget(&self) -> Option<usize> {
        self.inner.memory.term_limit()
    }

    /// Required before consuming a cached result and AFTER final cleanup/sealing.
    /// Each live poll spends one shared ResourceGuard admission tick. This is
    /// not native SAT/replay work accounting or evidence that a phase completed.
    pub fn check(&self) -> Option<Kind> {
        self.inner.poll()
    }

    /// Protect lowering, cache adoption, replay or sealing with the SAME owner.
    /// The outer Err is a genuine internal error; inner Err is owner refusal.
    /// Caller must still check after its own later cleanup and final publication.
    /// Overlap/reentry refuses rather than creating an independent allowance.
    pub fn with_resources<T>(
        &self,
        operation: impl FnOnce() -> ChcResult<T>,
    ) -> ChcResult<Result<T, Kind>> {
        if let Some(reason) = self.check() {
            return Ok(Err(reason));
        }
        if self.inner.running.swap(true, Ordering::AcqRel) {
            self.inner.record(Kind::Inconclusive);
            return Ok(Err(self.check().unwrap_or(Kind::Inconclusive)));
        }
        let active = Active(&self.inner);
        let worker = match Worker::capture(&self.inner) {
            Ok(worker) => worker,
            Err(reason) => {
                self.inner.record(reason);
                return Ok(Err(reason));
            }
        };
        let result = ay_core::catch_ay_panics(
            AssertUnwindSafe(|| self.run_scoped(operation, &worker)),
            |reason| {
                self.inner.record(Kind::Inconclusive);
                Err(ChcError::Internal(reason))
            },
        );
        worker.observe(&self.inner);
        let _ = self.check(); // temporary TLS caps/control already dropped
        worker.observe(&self.inner); // retained worker-only causes survive cleanup
        let refusal = self.inner.observed();
        drop(active);
        match result {
            Err(error) => Err(error),
            Ok(Err(reason)) => Ok(Err(reason)),
            Ok(Ok(value)) => Ok(refusal.map_or(Ok(value), Err)),
        }
    }

    fn run_scoped<T>(
        &self,
        operation: impl FnOnce() -> ChcResult<T>,
        worker: &Worker,
    ) -> ChcResult<Result<T, Kind>> {
        let observation = ScopedResourceObservation::install();
        let _memory = worker.memory.install();
        let control =
            ScopedReplayControl::install_until(worker.deadline, worker.cancellation.as_ref());
        let _observed = Observe(&self.inner, &observation, worker);
        let original = Arc::clone(&self.inner);
        let phase = control.cancellation().cloned();
        let current_group = worker.group.clone();
        let worker_stop = worker.stop.clone();
        let _stop = ay_core::resource::enter_check_stop(Arc::new(move || {
            original.fold_group(current_group.as_ref());
            if phase.as_ref().is_some_and(CancellationToken::is_cancelled) {
                original.record(Kind::Cancelled);
            }
            original.poll().is_some() || original.boolean_stop(worker_stop.as_ref())
        }));
        if let Some(reason) = self.inner.observe(&control, &observation, worker) {
            return Ok(Err(reason));
        }
        let result = operation();
        let refusal = self.inner.observe(&control, &observation, worker);
        match result {
            Err(error) => Err(error),
            Ok(value) => Ok(refusal.map_or(Ok(value), Err)),
        }
    }
}

/// Full original checks under a BORROWED captured owner, not a fresh duration.
/// Refuted invalidates only the submitted model, never proves CHC/program Unsafe.
/// Healthy decisions/internal errors use the unchanged existing typed validator.
pub fn validate_external_invariant_model_with_owner(
    problem: &ChcProblem,
    model: &InvariantModel,
    config: &PdrConfig,
    owner: &ExternalInvariantValidationOwner,
) -> ChcResult<Kind> {
    match owner
        .with_resources(|| validate_external_invariant_model_typed(problem, model, config))?
    {
        Ok(result) => Ok(result),
        Err(refusal) => Ok(refusal),
    }
}

impl Original {
    fn record(&self, reason: Kind) {
        let code = match reason {
            Kind::Cancelled => 1,
            Kind::Timeout => 2,
            Kind::Memory => 3,
            Kind::WorkLimit => 5,
            _ => 4,
        };
        let _ = self
            .first
            .compare_exchange(0, code, Ordering::AcqRel, Ordering::Acquire);
    }

    fn observed(&self) -> Option<Kind> {
        match self.first.load(Ordering::Acquire) {
            0 => None,
            1 => Some(Kind::Cancelled),
            2 => Some(Kind::Timeout),
            3 => Some(Kind::Memory),
            5 => Some(Kind::WorkLimit),
            _ => Some(Kind::Inconclusive),
        }
    }

    fn poll(&self) -> Option<Kind> {
        if let Some(reason) = self.observed() {
            return Some(reason);
        }
        if self.polling.swap(true, Ordering::AcqRel) {
            self.record(Kind::Inconclusive);
            return self.observed();
        }
        let _poll = Clear(&self.polling);
        let prior = current_refusal();
        if let Ok(Some(reason)) = prior {
            self.record(from_resource(reason));
        } else if prior.is_err() {
            self.record(Kind::Inconclusive);
        } else if self
            .cancellation
            .as_ref()
            .is_some_and(CancellationToken::is_cancelled)
        {
            self.record(Kind::Cancelled);
        } else if self
            .group
            .as_ref()
            .is_some_and(ay_sys::MemoryGroupObservation::is_tripped)
            || !self.memory.open()
            || !Budget::capture(self.memory.term_limit(), None).open()
        {
            self.record(Kind::Memory);
        } else if Instant::now() >= self.deadline {
            self.record(Kind::Timeout);
        } else if let Some(reason) = self.guard.exhausted() {
            self.record(from_guard(reason));
        } else if let Err(reason) = self.guard.tick(1) {
            self.record(from_guard(reason));
        } else {
            self.boolean_stop(self.stop.as_ref());
        }
        self.observed()
    }

    fn boolean_stop(&self, stop: Option<&CheckStop>) -> bool {
        let refused = stop.is_some_and(|stop| {
            std::panic::catch_unwind(AssertUnwindSafe(|| stop())).unwrap_or(true)
        });
        if refused {
            self.record(Kind::Inconclusive);
        }
        refused
    }

    fn fold_group(&self, group: Option<&ay_sys::MemoryGroupObservation>) {
        if group.is_some_and(ay_sys::MemoryGroupObservation::is_tripped) {
            self.record(Kind::Memory);
        }
    }

    fn observe(
        &self,
        control: &ScopedReplayControl,
        observation: &ScopedResourceObservation,
        worker: &Worker,
    ) -> Option<Kind> {
        if let Some(reason) = observation.first() {
            self.record(from_resource(reason));
        }
        worker.observe(self);
        if control
            .cancellation()
            .is_some_and(CancellationToken::is_cancelled)
        {
            self.record(Kind::Cancelled);
        }
        if Instant::now() >= control.deadline() {
            self.record(Kind::Timeout);
        }
        self.poll()
    }
}

// Retained until AFTER temporary TLS cleanup; no caller/group scope is moved.
struct Worker {
    deadline: Instant,
    cancellation: Option<CancellationToken>,
    memory: Budget,
    group: Option<ay_sys::MemoryGroupObservation>,
    stop: Option<CheckStop>,
}

impl Worker {
    fn capture(original: &Original) -> Result<Self, Kind> {
        let (ambient, interrupt) =
            crate::smt::deadline::try_lane_cancellation().map_err(|()| Kind::Inconclusive)?;
        let group =
            ay_sys::try_current_memory_group_observation().map_err(|_| Kind::Inconclusive)?;
        let stop = current_check_stop().map_err(|_| Kind::Inconclusive)?;
        let mut cancellation = original.cancellation.as_ref().map(CancellationToken::child);
        if let Some(ambient) = ambient {
            cancellation
                .get_or_insert_with(CancellationToken::new)
                .link_upstream(&ambient);
        }
        if let Some(interrupt) = interrupt {
            cancellation
                .get_or_insert_with(CancellationToken::new)
                .link_interrupt_flag(&interrupt);
        }
        Ok(Self {
            deadline: crate::smt::deadline::effective_thread_deadline()
                .map_or(original.deadline, |ambient| ambient.min(original.deadline)),
            cancellation: cancellation.as_ref().map(CancellationToken::sticky_child),
            memory: Budget::capture(original.memory.term_limit(), None),
            group,
            stop,
        })
    }

    fn observe(&self, original: &Original) {
        if self
            .cancellation
            .as_ref()
            .is_some_and(CancellationToken::is_cancelled)
        {
            original.record(Kind::Cancelled);
        }
        original.fold_group(self.group.as_ref());
        if !self.memory.open() {
            original.record(Kind::Memory);
        }
        if Instant::now() >= self.deadline {
            original.record(Kind::Timeout);
        }
        original.boolean_stop(self.stop.as_ref());
    }
}

struct Active<'a>(&'a Original);

impl Drop for Active<'_> {
    fn drop(&mut self) {
        if std::thread::panicking() {
            self.0.record(Kind::Inconclusive);
        }
        self.0.running.store(false, Ordering::Release);
    }
}

struct Observe<'a>(&'a Original, &'a ScopedResourceObservation, &'a Worker);

impl Drop for Observe<'_> {
    fn drop(&mut self) {
        if let Some(reason) = self.1.first() {
            self.0.record(from_resource(reason));
        }
        self.2.observe(self.0);
    }
}

struct Clear<'a>(&'a AtomicBool);

impl Drop for Clear<'_> {
    fn drop(&mut self) {
        self.0.store(false, Ordering::Release);
    }
}

fn from_resource(reason: ResourceRefusal) -> Kind {
    match reason {
        ResourceRefusal::Cancelled => Kind::Cancelled,
        ResourceRefusal::Timeout => Kind::Timeout,
        ResourceRefusal::Memory => Kind::Memory,
    }
}

fn from_guard(reason: Exhausted) -> Kind {
    match reason {
        Exhausted::Cancelled => Kind::Cancelled,
        Exhausted::Deadline | Exhausted::Cpu => Kind::Timeout,
        Exhausted::Memory => Kind::Memory,
        Exhausted::Rlimit => Kind::WorkLimit,
    }
}

#[cfg(test)]
mod tests;
