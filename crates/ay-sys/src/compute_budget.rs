// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Process-wide cooperative computational concurrency.
//!
//! This is a ceiling, not machine admission or a reservation. Independent
//! computations share one bank; nested work reuses its calling thread's unit.
//! Extra workers never wait for capacity: the owner must run work inline when
//! an extra unit is unavailable. A computational closure retains its unit
//! through return or unwind, including when its join handle is detached.

use std::cell::RefCell;
use std::collections::VecDeque;
use std::io;
use std::marker::PhantomData;
use std::num::NonZeroUsize;
use std::rc::Rc;
use std::sync::{Arc, Condvar, Mutex, OnceLock};

struct State {
    ceiling: usize,
    active: usize,
    next_ticket: u64,
    waiting: VecDeque<u64>,
}

struct Bank {
    state: Mutex<State>,
    changed: Condvar,
}

#[derive(Clone, Copy)]
enum Acquisition {
    Wait,
    Try,
}

impl Bank {
    fn new(ceiling: NonZeroUsize) -> Arc<Self> {
        Arc::new(Self {
            state: Mutex::new(State {
                ceiling: ceiling.get(),
                active: 0,
                next_ticket: 0,
                waiting: VecDeque::new(),
            }),
            changed: Condvar::new(),
        })
    }

    fn acquire(self: &Arc<Self>, acquisition: Acquisition) -> io::Result<Option<Unit>> {
        self.acquire_with(acquisition, None)
    }

    fn acquire_with(
        self: &Arc<Self>,
        acquisition: Acquisition,
        mut stopped: Option<&mut dyn FnMut() -> bool>,
    ) -> io::Result<Option<Unit>> {
        if stopped.as_mut().is_some_and(|stopped| stopped()) {
            return Ok(None);
        }
        let mut state = self
            .state
            .lock()
            .map_err(|_| io::Error::other("CPU budget poisoned"))?;
        let ticket = match acquisition {
            Acquisition::Try => {
                if state.active >= state.ceiling || !state.waiting.is_empty() {
                    return Ok(None);
                }
                None
            }
            Acquisition::Wait => {
                let ticket = state.next_ticket;
                state.next_ticket = ticket
                    .checked_add(1)
                    .ok_or_else(|| io::Error::other("CPU admission ticket exhausted"))?;
                state.waiting.push_back(ticket);
                Some(ticket)
            }
        };
        let mut queued = QueuedBase {
            bank: Arc::clone(self),
            ticket,
        };
        while state.active >= state.ceiling
            || ticket.is_some_and(|ticket| state.waiting.front() != Some(&ticket))
        {
            if matches!(acquisition, Acquisition::Try) {
                return Ok(None);
            }
            if let Some(stopped) = stopped.as_mut() {
                // Original caller polling may run arbitrary code or unwind.
                // Its queued claim is retained, but no bank lock is held.
                drop(state);
                if stopped() {
                    return Ok(None);
                }
                state = self
                    .state
                    .lock()
                    .map_err(|_| io::Error::other("CPU budget poisoned"))?;
                if state.active < state.ceiling && state.waiting.front() == ticket.as_ref() {
                    continue;
                }
                state = self
                    .changed
                    .wait_timeout(state, std::time::Duration::from_millis(10))
                    .map_err(|_| io::Error::other("CPU budget poisoned"))?
                    .0;
            } else {
                state = self
                    .changed
                    .wait(state)
                    .map_err(|_| io::Error::other("CPU budget poisoned"))?;
            }
        }
        if ticket.is_some() {
            state.waiting.pop_front();
        }
        queued.ticket = None;
        state.active += 1;
        // More than one unit may be available; let the next queued base
        // recheck its turn without requiring another worker to finish first.
        self.changed.notify_all();
        Ok(Some(Unit {
            bank: Arc::clone(self),
            active: true,
        }))
    }
}

/// Cancellation or callback unwind removes exactly this unstarted base claim.
struct QueuedBase {
    bank: Arc<Bank>,
    ticket: Option<u64>,
}

impl Drop for QueuedBase {
    fn drop(&mut self) {
        if let Some(ticket) = self.ticket {
            let mut state = self
                .bank
                .state
                .lock()
                .unwrap_or_else(|error| error.into_inner());
            state.waiting.retain(|waiting| *waiting != ticket);
            self.bank.changed.notify_all();
        }
    }
}

struct Unit {
    bank: Arc<Bank>,
    active: bool,
}

impl Unit {
    fn suspend(&mut self) {
        if self.active {
            let mut state = self
                .bank
                .state
                .lock()
                .unwrap_or_else(|error| error.into_inner());
            state.active = state.active.saturating_sub(1);
            self.active = false;
            self.bank.changed.notify_all();
        }
    }

    fn restore(&mut self) {
        if !self.active {
            // Rejoin ordinary FIFO admission without manufacturing capacity.
            // Unknown internal state cannot permit computational cleanup.
            let Ok(Some(mut admitted)) = self.bank.acquire(Acquisition::Wait) else {
                std::process::abort();
            };
            admitted.active = false;
            self.active = true;
        }
    }
}

impl Drop for Unit {
    fn drop(&mut self) {
        self.suspend();
    }
}

/// Owns the SAME caller unit while it is temporarily not runnable. Keeping
/// the TLS entry (with no active unit) prevents nested entry from bypassing
/// admission. Restoration precedes the wait result and unwind of its caller.
struct Suspended {
    unit: Option<Unit>,
    depth: usize,
}

impl Drop for Suspended {
    fn drop(&mut self) {
        let Some(mut unit) = self.unit.take() else {
            return;
        };
        unit.restore();
        ENTERED.with(|entered| {
            let mut entered = entered.borrow_mut();
            let Some((bank, depth, slot)) = entered.as_mut() else {
                std::process::abort();
            };
            if *depth != self.depth || slot.is_some() || !Arc::ptr_eq(bank, &unit.bank) {
                std::process::abort();
            }
            *slot = Some(unit);
        });
    }
}

/// Release this thread's computational occupancy only for a passive wait,
/// then restore its original scope before returning or unwinding to its caller.
///
/// The closure must contain ONLY known passive wait state. Its own captures
/// and locals may be destroyed before restoration, so it must not own user
/// computation, writers or their cleanup. Drop all wait locks before returning.
/// No original deadline is reset. Restoration queues for real capacity and may
/// outlast a wait timeout; this is cooperative accounting, not a hard deadline.
/// A thread without a scope simply waits. Suspended computation cannot reenter.
pub fn with_suspended_current<R>(wait: impl FnOnce() -> R) -> io::Result<R> {
    let mut suspended = ENTERED.with(|entered| -> io::Result<Option<Suspended>> {
        let mut entered = entered.borrow_mut();
        let Some((_, depth, slot)) = entered.as_mut() else {
            return Ok(None);
        };
        let unit = slot
            .take()
            .ok_or_else(|| io::Error::other("CPU scope is suspended"))?;
        Ok(Some(Suspended {
            unit: Some(unit),
            depth: *depth,
        }))
    })?;
    if let Some(suspended) = suspended.as_mut() {
        if let Some(unit) = suspended.unit.as_mut() {
            unit.suspend();
        }
    }
    let result = wait();
    drop(suspended);
    Ok(result)
}

static PROCESS: OnceLock<Arc<Bank>> = OnceLock::new();

fn process() -> &'static Arc<Bank> {
    PROCESS.get_or_init(|| {
        Bank::new(std::thread::available_parallelism().unwrap_or(NonZeroUsize::MIN))
    })
}

thread_local! {
    static ENTERED: RefCell<Option<(Arc<Bank>, usize, Option<Unit>)>> = const { RefCell::new(None) };
}

/// Tighten the process ceiling. Calling this before computational work starts
/// establishes its maximum width. Later calls cannot raise it or forcibly
/// revoke running work; new units wait until occupancy falls below the limit.
/// A numeric value here supplies no Host or machine admission authority.
pub fn tighten(ceiling: NonZeroUsize) -> io::Result<()> {
    let mut state = process()
        .state
        .lock()
        .map_err(|_| io::Error::other("CPU budget poisoned"))?;
    state.ceiling = state.ceiling.min(ceiling.get());
    Ok(())
}

/// One computational caller. This is thread-bound; moving work to another
/// thread requires an explicitly owned extra unit, rather than sharing this
/// scope between two simultaneously executing threads.
/// Acquire entry outside context and cross-worker locks.
#[must_use]
pub struct ComputeScope {
    _thread: PhantomData<Rc<()>>,
}

impl ComputeScope {
    /// Acquire one base unit, or reuse this thread's existing unit for nested
    /// computation. Only independent callers wait; nested work never waits
    /// while retaining a unit needed by its children.
    pub fn enter() -> io::Result<Self> {
        Self::enter_on(process())
    }

    /// Try to enter without waiting. A caller with a deadline or cancellation
    /// must keep polling its original owner while capacity is unavailable, or
    /// return no answer. Lack of capacity never authorizes uncounted work.
    pub fn try_enter() -> io::Result<Option<Self>> {
        Self::enter_on_mode(process(), Acquisition::Try)
    }

    /// Queue for a base unit while polling the original solve's cancellation
    /// or deadline. Refusal removes this request's queue entry; it does not
    /// release any running computation or reset the caller's timeout.
    /// Call this outside context and cross-worker locks.
    pub fn enter_until(mut stopped: impl FnMut() -> bool) -> io::Result<Option<Self>> {
        // Reject suspended reentry before invoking any caller callback.
        if ENTERED.with(|entered| {
            entered
                .borrow()
                .as_ref()
                .is_some_and(|(_, _, unit)| unit.is_none())
        }) {
            return Err(io::Error::other("CPU scope is suspended"));
        }
        if stopped() {
            return Ok(None);
        }
        Self::enter_on_progress(process(), Acquisition::Wait, Some(&mut stopped))
    }

    fn enter_on(bank: &Arc<Bank>) -> io::Result<Self> {
        Self::enter_on_mode(bank, Acquisition::Wait)?
            .ok_or_else(|| io::Error::other("CPU base acquisition did not complete"))
    }

    fn enter_on_mode(bank: &Arc<Bank>, acquisition: Acquisition) -> io::Result<Option<Self>> {
        Self::enter_on_progress(bank, acquisition, None)
    }

    fn enter_on_progress(
        bank: &Arc<Bank>,
        acquisition: Acquisition,
        stopped: Option<&mut dyn FnMut() -> bool>,
    ) -> io::Result<Option<Self>> {
        let nested = ENTERED.with(|entered| {
            let mut entered = entered.borrow_mut();
            match entered.as_mut() {
                Some((current, depth, unit)) if Arc::ptr_eq(current, bank) => {
                    if unit.is_none() {
                        return Err(io::Error::other("CPU scope is suspended"));
                    }
                    *depth = depth
                        .checked_add(1)
                        .ok_or_else(|| io::Error::other("CPU scope depth overflow"))?;
                    Ok(true)
                }
                Some(_) => Err(io::Error::other("CPU scope belongs to another bank")),
                None => Ok(false),
            }
        })?;
        let unit = if nested {
            None
        } else {
            match bank.acquire_with(acquisition, stopped)? {
                Some(unit) => Some(unit),
                None => return Ok(None),
            }
        };
        if !nested {
            ENTERED.with(|entered| *entered.borrow_mut() = Some((Arc::clone(bank), 1, unit)));
        }
        Ok(Some(Self {
            _thread: PhantomData,
        }))
    }

    /// Try to reserve one additional worker. Failure to find capacity is
    /// ordinary: run the remaining work inline, without waiting for extras.
    pub fn try_extra(&self) -> io::Result<Option<ExtraPermit>> {
        try_extra()
    }
}

/// Try an extra unit for work nested beneath the currently entered caller.
/// This supports coordinators whose backfill helpers run deeper in the same
/// call stack. An actual caller scope must remain entered; no scope is an
/// error, and a queued independent caller keeps priority over these extras.
pub fn try_extra() -> io::Result<Option<ExtraPermit>> {
    let bank = ENTERED
        .with(|entered| {
            entered
                .borrow()
                .as_ref()
                .and_then(|(bank, _, unit)| unit.as_ref().map(|_| Arc::clone(bank)))
        })
        .ok_or_else(|| io::Error::other("CPU scope is not entered"))?;
    Ok(bank.acquire(Acquisition::Try)?.map(ExtraPermit))
}

impl Drop for ComputeScope {
    fn drop(&mut self) {
        let unit = ENTERED.with(|entered| {
            let mut entered = entered.borrow_mut();
            if let Some((_, depth, unit)) = entered.as_mut() {
                if unit.is_none() {
                    std::process::abort();
                }
                *depth = depth.saturating_sub(1);
                if *depth == 0 {
                    return entered.take().and_then(|(_, _, unit)| unit);
                }
            }
            None
        });
        // The last nested scope returns the actual unit, regardless of the
        // order in which same-thread scopes are dropped.
        drop(unit);
    }
}

/// An actual extra unit, retained through the computational closure's exit.
#[must_use]
pub struct ExtraPermit(Unit);

impl ExtraPermit {
    /// Enter a reserved unit on a worker thread. Nested pools on that thread
    /// reuse it and can only obtain further workers by try-only acquisition.
    pub fn run<T>(self, work: impl FnOnce() -> T) -> io::Result<T> {
        let bank = Arc::clone(&self.0.bank);
        let vacant = ENTERED.with(|entered| entered.borrow().is_none());
        if !vacant {
            return Err(io::Error::other(
                "extra CPU unit entered on an occupied thread",
            ));
        }
        ENTERED.with(|entered| *entered.borrow_mut() = Some((bank, 1, Some(self.0))));
        let scope = ComputeScope {
            _thread: PhantomData,
        };
        let result = work();
        drop(scope);
        Ok(result)
    }
}

#[cfg(test)]
mod tests;
