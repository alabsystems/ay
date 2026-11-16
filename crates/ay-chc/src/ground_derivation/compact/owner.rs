// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{Error, Result};
use crate::smt::deadline::{effective_thread_deadline, try_lane_cancellation, ScopedSmtDeadline};
use ay_core::resource::{CheckStop, Guard};
use ay_core::time::Instant;
use std::cell::RefCell;
use std::sync::atomic::{AtomicU8, AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Duration;

thread_local! {
    static POLLING: RefCell<Vec<usize>> = const { RefCell::new(Vec::new()) };
}

pub(crate) struct Owner<'a> {
    state: Arc<State>,
    progress: Option<&'a mut dyn FnMut() -> bool>,
    memory: crate::bmc::memory::Budget,
    caller_guard: Option<Guard>,
    progress_guard: Option<Guard>,
}

/// Sendable retained authority; unlike a borrowed continuation it contains no
/// non-Send callback reference. Only an original static owner can create it.
pub(crate) struct RetainedOwner {
    state: Arc<State>,
    memory: crate::bmc::memory::Budget,
}

impl RetainedOwner {
    pub(crate) fn owner(&self) -> Owner<'static> {
        Owner {
            state: Arc::clone(&self.state),
            progress: None,
            memory: crate::bmc::memory::Budget::capture(self.memory.term_limit(), None),
            caller_guard: ay_core::resource::current_guard(),
            progress_guard: None,
        }
    }
}

struct State {
    original: Option<CheckStop>,
    observer: CheckStop,
    guard: Option<Guard>,
    lane: Option<crate::CancellationToken>,
    interrupt: Option<Arc<std::sync::atomic::AtomicBool>>,
    deadline: Option<Instant>,
    memory: crate::bmc::memory::Budget,
    refused: AtomicU8,
    work: AtomicUsize,
    storage: AtomicUsize,
}

impl Owner<'static> {
    pub(crate) fn into_retained(self) -> RetainedOwner {
        if self.progress.is_some() {
            self.state.latch(Error::Stopped);
        }
        RetainedOwner {
            state: self.state,
            memory: self.memory,
        }
    }

    pub(crate) fn capture() -> Result<Self> {
        let original = ay_core::resource::current_check_stop().map_err(|_| Error::Stopped)?;
        let guard = ay_core::resource::current_guard();
        let (lane, interrupt) = try_lane_cancellation().map_err(|()| Error::Stopped)?;
        let deadline = [
            effective_thread_deadline(),
            guard.as_ref().and_then(Guard::effective_deadline),
        ]
        .into_iter()
        .flatten()
        .min();
        let memory = crate::bmc::memory::Budget::capture(None, None);
        let mut out = Self {
            state: Arc::new_cyclic(|weak: &std::sync::Weak<State>| State {
                original,
                observer: {
                    let weak = weak.clone();
                    Arc::new(move || weak.upgrade().is_none_or(|state| state.poll().is_err()))
                },
                guard,
                lane,
                interrupt,
                deadline,
                memory,
                refused: AtomicU8::new(0),
                work: AtomicUsize::new(0),
                storage: AtomicUsize::new(0),
            }),
            progress: None,
            memory,
            caller_guard: None,
            progress_guard: None,
        };
        let _scope = out.enter();
        out.poll()?;
        Ok(out)
    }

    /// Retain the original allowance, not a new capture or fresh credit. This
    /// operation is unavailable on a borrowed-progress continuation.
    pub(crate) fn retained(&self) -> Self {
        if self.progress.is_some() {
            // Even an unusually static borrowed callback cannot be stripped
            // to manufacture an unchecked retained continuation.
            self.state.latch(Error::Stopped);
        }
        Self {
            state: Arc::clone(&self.state),
            progress: None,
            memory: self.memory,
            caller_guard: self.caller_guard.clone(),
            progress_guard: self.progress_guard.clone(),
        }
    }

    pub(crate) fn with_progress<'a>(&self, progress: &'a mut dyn FnMut() -> bool) -> Owner<'a> {
        if self.progress.is_some() {
            self.state.latch(Error::Stopped);
        }
        Owner {
            state: Arc::clone(&self.state),
            progress: Some(progress),
            memory: crate::bmc::memory::Budget::capture(self.memory.term_limit(), None),
            caller_guard: self.caller_guard.clone(),
            // Capture BEFORE either callback can replace the ambient scope.
            progress_guard: ay_core::resource::current_guard(),
        }
    }
}

impl Owner<'_> {
    /// No deadline or allowance is invented. Scope owns its Arc, not a borrow
    /// of this handle, so producer and verifier can debit the same owner.
    pub(crate) fn enter(&self) -> impl Drop {
        let memory = self.memory.install();
        let deadline = self.state.deadline.map(ScopedSmtDeadline::install_until);
        let callback = ay_core::resource::enter_check_stop(Arc::clone(&self.state.observer));
        Scope {
            _callback: callback,
            _deadline: deadline,
            _memory: memory,
            _state: Arc::clone(&self.state),
            _thread: std::marker::PhantomData,
        }
    }

    pub(crate) fn poll(&mut self) -> Result<()> {
        // Retain tightening BEFORE callbacks may replace the ambient scope.
        // The counter stays shared with the original solve; no fresh bytes.
        self.memory = crate::bmc::memory::Budget::capture(self.memory.term_limit(), None);
        self.state.outer()?;
        self.poll_callers()?;
        self.state.poll()?;
        self.poll_callers()?;
        if let Some(progress) = self.progress.as_mut() {
            let mut invocation = ProgressInvocation {
                state: &self.state,
                completed: false,
            };
            if !progress() {
                self.state.latch(Error::Stopped);
            }
            invocation.completed = true;
        }
        self.poll_callers()?;
        self.state.outer()
    }

    pub(crate) fn remaining(&mut self) -> Option<Duration> {
        if self.poll().is_err() {
            return Some(Duration::ZERO);
        }
        self.state
            .deadline
            .map(|end| end.saturating_duration_since(Instant::now()))
    }

    pub(crate) fn refuse<T>(&mut self, error: Error) -> Result<T> {
        if matches!(error, Error::Stopped | Error::Resource) {
            self.state.latch(error);
        }
        Err(error)
    }

    pub(crate) fn admit(&mut self, work: usize, bytes: usize) -> Result<()> {
        self.poll()?;
        // This structural safety bound is cumulative, not fresh caller credit.
        let work_ok = self
            .state
            .work
            .fetch_update(Ordering::AcqRel, Ordering::Acquire, |old| {
                old.checked_add(work)
                    .filter(|n| *n <= crate::expr::MAX_PREPROCESSING_NODES)
            });
        let bytes_ok =
            self.state
                .storage
                .fetch_update(Ordering::AcqRel, Ordering::Acquire, |old| {
                    old.checked_add(bytes)
                        .filter(|n| self.memory.term_limit().is_none_or(|m| *n <= m))
                });
        if work_ok.is_err() || bytes_ok.is_err() {
            return self.refuse(Error::Resource);
        }
        let cost = match u64::try_from(work) {
            Ok(n) => n,
            Err(_) => return self.refuse(Error::Resource),
        };
        self.charge_guards(cost)?;
        self.poll()
    }

    fn poll_callers(&self) -> Result<()> {
        if !self.memory.open()
            || self
                .memory
                .term_limit()
                .is_some_and(|limit| self.state.storage.load(Ordering::Acquire) > limit)
        {
            self.state.latch(Error::Resource);
            return Err(Error::Resource);
        }
        for guard in [&self.caller_guard, &self.progress_guard]
            .into_iter()
            .flatten()
        {
            if let Some(reason) = guard.poll() {
                let error = guard_error(reason);
                self.state.latch(error);
                return Err(error);
            }
        }
        Ok(())
    }

    fn charge_guards(&self, cost: u64) -> Result<()> {
        let guards = [&self.state.guard, &self.caller_guard, &self.progress_guard];
        // Coverage is not transitive: a child charges its actual parent, and
        // that parent's counter is shared by a later sibling view, but the
        // child's deferred settlement does not charge that view live. With
        // three retained handles, enumerate the eight possible debit sets.
        let mut selected = 0b111u8;
        for mask in 0u8..8 {
            let covers_all = guards.into_iter().flatten().all(|guard| {
                guards.iter().enumerate().any(|(index, other)| {
                    mask & (1 << index) != 0
                        && other
                            .as_ref()
                            .is_some_and(|other| other.charges_against(guard))
                })
            });
            if covers_all && mask.count_ones() < selected.count_ones() {
                selected = mask;
            }
        }
        for (index, guard) in guards.iter().enumerate() {
            let Some(guard) = guard else { continue };
            if selected & (1 << index) != 0 {
                if let Err(reason) = guard.tick(cost) {
                    let error = guard_error(reason);
                    self.state.latch(error);
                    return Err(error);
                }
            }
        }
        // Same-counter views and Full ancestors are not ticked twice, but
        // both limits remain live. Unrelated/sibling grants each debit their
        // own allowance; a common ancestor conservatively settles both.
        self.poll_callers()?;
        self.state.outer()
    }

    #[cfg(test)]
    pub(crate) fn admitted_storage_for_test(&self) -> usize {
        self.state.storage.load(Ordering::Acquire)
    }
}

struct ProgressInvocation<'a> {
    state: &'a State,
    completed: bool,
}
impl Drop for ProgressInvocation<'_> {
    fn drop(&mut self) {
        if !self.completed {
            self.state.latch(Error::Stopped);
        }
    }
}

struct Scope<M> {
    _callback: ay_core::resource::CheckStopScope,
    _deadline: Option<ScopedSmtDeadline>,
    _memory: M,
    _state: Arc<State>,
    _thread: std::marker::PhantomData<std::rc::Rc<()>>,
}

#[expect(
    clippy::empty_drop,
    reason = "the explicit Drop bound keeps every owned scope guard alive behind the returned impl Drop"
)]
impl<M> Drop for Scope<M> {
    fn drop(&mut self) {}
}

impl State {
    fn latch(&self, error: Error) {
        let code = if error == Error::Resource { 2 } else { 1 };
        let _ = self
            .refused
            .compare_exchange(0, code, Ordering::AcqRel, Ordering::Acquire);
    }

    fn outer(&self) -> Result<()> {
        match self.refused.load(Ordering::Acquire) {
            1 => return Err(Error::Stopped),
            2 => return Err(Error::Resource),
            _ => {}
        }
        if !self.memory.open() {
            self.latch(Error::Resource);
            return Err(Error::Resource);
        }
        if let Some(reason) = self.guard.as_ref().and_then(Guard::poll) {
            let error = guard_error(reason);
            self.latch(error);
            return Err(error);
        }
        if self.deadline.is_some_and(|d| Instant::now() >= d)
            || self
                .lane
                .as_ref()
                .is_some_and(crate::CancellationToken::is_cancelled)
            || self
                .interrupt
                .as_ref()
                .is_some_and(|f| f.load(Ordering::Acquire))
            || ay_core::resource::process_cancelled()
        {
            self.latch(Error::Stopped);
            return Err(Error::Stopped);
        }
        Ok(())
    }

    fn poll(&self) -> Result<()> {
        self.outer()?;
        let identity = std::ptr::from_ref(self) as usize;
        let entered = POLLING
            .try_with(|active| {
                let Ok(mut active) = active.try_borrow_mut() else {
                    return false;
                };
                if active.contains(&identity) || active.try_reserve(1).is_err() {
                    return false;
                }
                active.push(identity);
                true
            })
            .unwrap_or(false);
        if !entered {
            self.latch(Error::Stopped);
            return Err(Error::Stopped);
        }
        let mut invocation = Invocation {
            state: self,
            identity,
            completed: false,
        };
        // A direct poll is safe even without enter(): callback reentry observes
        // this retained owner, not the raw callback recursively installed by its
        // caller. The observer has a Weak back-reference and cannot form a cycle.
        let _callback_scope = ay_core::resource::enter_check_stop(Arc::clone(&self.observer));
        if self.original.as_ref().is_some_and(|callback| callback()) {
            self.latch(Error::Stopped);
        }
        let result = self.outer();
        invocation.completed = true;
        result
    }
}

fn guard_error(reason: ay_core::resource::Exhausted) -> Error {
    use ay_core::resource::Exhausted;
    match reason {
        Exhausted::Rlimit | Exhausted::Memory => Error::Resource,
        Exhausted::Cancelled | Exhausted::Deadline | Exhausted::Cpu => Error::Stopped,
    }
}

struct Invocation<'a> {
    state: &'a State,
    identity: usize,
    completed: bool,
}
impl Drop for Invocation<'_> {
    fn drop(&mut self) {
        if !self.completed {
            self.state.latch(Error::Stopped);
        }
        let restored = POLLING
            .try_with(|active| {
                let Ok(mut active) = active.try_borrow_mut() else {
                    return false;
                };
                if active.last() != Some(&self.identity) {
                    return false;
                }
                active.pop();
                true
            })
            .unwrap_or(false);
        if !restored {
            self.state.latch(Error::Stopped);
        }
    }
}
