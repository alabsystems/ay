// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Captured original controls: no new deadline, grant, or counter.

use ay_core::resource::{CheckStop, Guard};
use ay_core::time::Instant;
use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};
use std::sync::{Arc, OnceLock};

/// An observed original control refusal, not a local trace-storage limit.
#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum ConsumingTraceStop {
    /// An opaque callback, capture, reentrant poll, or unwind refused.
    #[error("original trace caller refused")]
    Observer,
    /// The original interrupt or process cancellation was observed.
    #[error("original trace caller was interrupted")]
    Interrupt,
    /// The original deadline expired.
    #[error("original trace caller deadline expired")]
    Deadline,
    /// The original Guard's work allowance was exhausted.
    #[error("original trace caller work allowance exhausted")]
    Work,
    /// The original Guard's memory allowance was exhausted.
    #[error("original trace caller memory allowance exhausted")]
    Memory,
}

impl From<ay_core::resource::Exhausted> for ConsumingTraceStop {
    fn from(reason: ay_core::resource::Exhausted) -> Self {
        use ay_core::resource::Exhausted;
        match reason {
            Exhausted::Cancelled => Self::Interrupt,
            Exhausted::Deadline | Exhausted::Cpu => Self::Deadline,
            Exhausted::Rlimit => Self::Work,
            Exhausted::Memory => Self::Memory,
        }
    }
}

struct Inner {
    stop: Option<CheckStop>,
    guard: Option<Guard>,
    interrupt: Option<Arc<AtomicBool>>,
    deadline_interrupt: Option<Arc<AtomicBool>>,
    deadline: Option<Instant>,
    state: AtomicU8,
    unavailable: AtomicBool,
    refusal: OnceLock<ConsumingTraceStop>,
}

#[derive(Clone)]
pub(crate) struct OriginalControl(Arc<Inner>);

struct WorkFence<'a> {
    control: &'a OriginalControl,
    completed: bool,
}

impl Drop for WorkFence<'_> {
    fn drop(&mut self) {
        if !self.completed {
            self.control.stop(ConsumingTraceStop::Observer);
        }
    }
}

impl std::fmt::Debug for OriginalControl {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        out.debug_struct("OriginalControl")
            .field("state", &self.0.state.load(Ordering::Acquire))
            .finish()
    }
}

impl OriginalControl {
    pub(crate) fn capture(
        interrupt: Option<Arc<AtomicBool>>,
        deadline_interrupt: Option<Arc<AtomicBool>>,
        deadline: Option<Instant>,
    ) -> Option<Self> {
        Some(Self(Arc::new(Inner {
            stop: ay_core::resource::current_check_stop().ok()?,
            guard: ay_core::resource::current_guard(),
            interrupt,
            deadline_interrupt,
            deadline,
            state: AtomicU8::new(0),
            unavailable: AtomicBool::new(false),
            refusal: OnceLock::new(),
        })))
    }

    pub(crate) fn refuse(&self) {
        self.0.unavailable.store(true, Ordering::Release);
    }

    pub(crate) fn stop(&self, reason: ConsumingTraceStop) {
        let _ = self.0.refusal.set(reason);
        self.0.state.store(2, Ordering::Release);
    }

    pub(crate) fn stop_reason(&self) -> Option<ConsumingTraceStop> {
        self.0.refusal.get().copied()
    }

    pub(crate) fn work(&self, units: u64, admission: &mut dyn FnMut(u64) -> bool) -> bool {
        if !self.open() {
            return false;
        }
        let mut fence = WorkFence {
            control: self,
            completed: false,
        };
        let admitted = admission(units);
        fence.completed = true;
        if !admitted {
            // The callback debits the existing local bookkeeping quota. Its
            // ordinary false result poisons this capture, not the caller.
            self.refuse();
            return false;
        }
        if let Some(reason) = self
            .0
            .guard
            .as_ref()
            .and_then(|guard| guard.tick(units).err())
        {
            self.stop(reason.into());
            return false;
        }
        self.open()
    }

    pub(crate) fn open(&self) -> bool {
        !self.0.unavailable.load(Ordering::Acquire) && self.caller_open()
    }

    /// Remains observable after a semantic/storage decline of this capture.
    pub(crate) fn caller_open(&self) -> bool {
        // Arm before opaque code. A panic or recursive observation cannot
        // revive this capture even when a surrounding caller catches unwind.
        if self
            .0
            .state
            .compare_exchange(0, 1, Ordering::AcqRel, Ordering::Acquire)
            .is_err()
        {
            self.stop(ConsumingTraceStop::Observer);
            return false;
        }
        let mut fence = WorkFence {
            control: self,
            completed: false,
        };
        let clear = self.outer_open()
            && !self.0.stop.as_ref().is_some_and(|stop| stop())
            && self.outer_open();
        fence.completed = true;
        if !clear
            || self
                .0
                .state
                .compare_exchange(1, 0, Ordering::AcqRel, Ordering::Acquire)
                .is_err()
        {
            self.stop(ConsumingTraceStop::Observer);
            return false;
        }
        true
    }

    fn outer_open(&self) -> bool {
        let raised = |flag: &Option<Arc<AtomicBool>>| {
            flag.as_ref()
                .is_some_and(|flag| flag.load(Ordering::Acquire))
        };
        let reason = if self.stop_reason().is_some() {
            return false;
        } else if ay_core::resource::process_cancelled() || raised(&self.0.interrupt) {
            Some(ConsumingTraceStop::Interrupt)
        } else if raised(&self.0.deadline_interrupt)
            || self.0.deadline.is_some_and(|end| Instant::now() >= end)
        {
            Some(ConsumingTraceStop::Deadline)
        } else {
            self.0.guard.as_ref().and_then(Guard::poll).map(Into::into)
        };
        if let Some(reason) = reason {
            self.stop(reason);
            return false;
        }
        true
    }
}
