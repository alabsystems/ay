// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A deadline a timer watches, so a hot poll reads a flag instead of the
//! clock (DR-34 in the development design notes).
//!
//! [`SolveDeadlineCell::expired`] takes the cell's lock and reads the clock.
//! The strict checker's walks poll their stop at every callback, and their
//! callbacks come from the proof producer's innermost loops (one per hint,
//! per literal, per resolution step). Sampled on ay main 2026-10-08 under the
//! producer's refutations of external-codegen's coroutine-slot row, that poll took
//! 22-35% of the producer's time, nearly all of it `mach_absolute_time`
//! under `clock_gettime`.
//!
//! [`DeadlineAlarm`] is one deadline and a flag a timer thread raises once
//! the clock reads it as passed. The bit-blast SAT searches arm one per
//! search (`theories/sat_stop.rs`). [`DeadlinePoll`] arms one only for a walk
//! that keeps polling: its first [`EXACT_POLLS`] polls read the cell as
//! `expired` does, so a short walk starts no thread, and a walk still polling
//! after that reads the alarm's flag and the cell's generation, two atomic
//! loads, and the clock once per [`ARMED_CLOCK_POLLS`] polls. The cell's
//! generation moves at every `set`, and the next poll reads the cell again,
//! so a deadline installed, moved or cleared mid-walk is seen at once, as
//! before.
//!
//! WHAT THE STOP MEANS IS UNCHANGED. A poll can only stop work, and every
//! stop is fail-closed. An armed poll sees a passed deadline at the first of
//! two events: the timer thread raising its flag, or its own clock read,
//! which it still makes every [`ARMED_CLOCK_POLLS`] polls. The timer bounds
//! the delay by its wake-up latency whatever the walk's callback rate (a
//! timed condvar wait on macOS returned 3.7-7 ms late, measured 2026-10-09
//! at load 24-28); the clock read bounds it by 4,096 callbacks of a dense
//! walk. Where no thread can watch the clock (wasm32, or a failed spawn) the
//! poll keeps reading the cell.
//!
//! The cell's `expired` also answers a reached work ceiling
//! (`ay_core::resource::work_ceiling_reached`), and so does an armed poll, at
//! each of its clock reads, with or without a deadline. The stride is a count
//! of polls, so a counted ceiling still stops a long walk at a poll the input
//! fixes, at most [`ARMED_CLOCK_POLLS`] polls after the ceiling is reached.

use super::SolveDeadlineCell;
use ay_core::time::{ClockStride, Instant};
use std::cell::{Cell, RefCell};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
#[cfg(not(target_arch = "wasm32"))]
use std::sync::{Condvar, Mutex, PoisonError};
#[cfg(not(target_arch = "wasm32"))]
use std::thread::JoinHandle;

/// Polls a [`DeadlinePoll`] answers by reading the cell before it arms an
/// alarm. At the 25-60 ns a locked clock read costs, a walk has spent at
/// least 1.6 ms polling by then, so the alarm thread (tens of microseconds to
/// start and to join) is paid only by walks it saves milliseconds on.
pub(crate) const EXACT_POLLS: u32 = 1 << 16;

/// Polls between two clock reads of an armed poll: one read per 4,096
/// polls costs well under a nanosecond a poll, and bounds a dense walk's
/// delay far below the timer's wake-up latency.
const ARMED_CLOCK_POLLS: u32 = 1 << 12;

/// A flag raised once a deadline has passed, by a timer thread that the
/// alarm stops and joins when it is dropped.
pub(crate) struct DeadlineAlarm {
    raised: Arc<AtomicBool>,
    watched: bool,
    #[cfg(not(target_arch = "wasm32"))]
    timer: Option<Timer>,
}

#[cfg(not(target_arch = "wasm32"))]
struct Timer {
    stop: Arc<(Mutex<bool>, Condvar)>,
    handle: JoinHandle<()>,
}

impl DeadlineAlarm {
    /// Watch `deadline`: the flag is raised at once if it has passed, else
    /// by a timer thread once the clock reads it as passed.
    pub(crate) fn arm(deadline: Instant) -> Self {
        let raised = Arc::new(AtomicBool::new(false));
        if Instant::now() >= deadline {
            raised.store(true, Ordering::Relaxed);
            return Self::without_timer(raised, true);
        }
        // wasm32 has no threads; the callers' own clock reads, through the
        // ay-core clock shim, still honour the deadline.
        #[cfg(target_arch = "wasm32")]
        {
            Self::without_timer(raised, false)
        }
        #[cfg(not(target_arch = "wasm32"))]
        {
            let stop = Arc::new((Mutex::new(false), Condvar::new()));
            let (timer_stop, timer_flag) = (Arc::clone(&stop), Arc::clone(&raised));
            let spawned = std::thread::Builder::new()
                .name("ay-deadline-alarm".to_string())
                .spawn(move || watch(&timer_stop, &timer_flag, deadline));
            match spawned {
                Ok(handle) => Self {
                    raised,
                    watched: true,
                    timer: Some(Timer { stop, handle }),
                },
                Err(_) => Self::without_timer(raised, false),
            }
        }
    }

    fn without_timer(raised: Arc<AtomicBool>, watched: bool) -> Self {
        Self {
            raised,
            watched,
            #[cfg(not(target_arch = "wasm32"))]
            timer: None,
        }
    }

    /// The flag, for a consumer that polls it itself.
    pub(crate) fn flag(&self) -> Arc<AtomicBool> {
        Arc::clone(&self.raised)
    }

    /// Whether the deadline has been seen to pass.
    pub(crate) fn raised(&self) -> bool {
        self.raised.load(Ordering::Relaxed)
    }

    /// Whether the flag will rise at the deadline: false where no timer
    /// thread runs and the deadline had not passed when it was armed.
    pub(crate) fn watched(&self) -> bool {
        self.watched
    }
}

/// The timer thread: a timed wait can return early, so the flag goes up only
/// once the clock reads the deadline as passed.
#[cfg(not(target_arch = "wasm32"))]
fn watch(stop: &(Mutex<bool>, Condvar), raised: &AtomicBool, deadline: Instant) {
    let (lock, cvar) = stop;
    let mut stopped = lock.lock().unwrap_or_else(PoisonError::into_inner);
    while !*stopped {
        let now = Instant::now();
        if now >= deadline {
            raised.store(true, Ordering::Relaxed);
            return;
        }
        stopped = cvar
            .wait_timeout(stopped, deadline.saturating_duration_since(now))
            .unwrap_or_else(PoisonError::into_inner)
            .0;
    }
}

impl Drop for DeadlineAlarm {
    fn drop(&mut self) {
        #[cfg(not(target_arch = "wasm32"))]
        if let Some(Timer { stop, handle }) = self.timer.take() {
            let (lock, cvar) = &*stop;
            *lock.lock().unwrap_or_else(PoisonError::into_inner) = true;
            cvar.notify_one();
            let _ = handle.join();
        }
    }
}

/// A [`SolveDeadlineCell`] polled at every callback of one walk (module
/// docs). Single-threaded: the walk that polls it owns it.
pub(crate) struct DeadlinePoll {
    cell: SolveDeadlineCell,
    exact_polls: Cell<u32>,
    armed: RefCell<Option<Armed>>,
}

/// What a poll armed for one generation of the cell: its deadline and an
/// alarm for it, or nothing when that generation has none.
struct Armed {
    generation: u64,
    deadline: Option<(Instant, DeadlineAlarm)>,
    clock: ClockStride,
}

impl Armed {
    /// Whether the deadline has passed, or a work ceiling over this thread
    /// is reached. Both are read once per [`ARMED_CLOCK_POLLS`] polls, the
    /// ceiling with or without a deadline; the alarm's flag at every poll.
    fn expired(&self) -> bool {
        let due = self.clock.due();
        if due && ay_core::resource::work_ceiling_reached() {
            return true;
        }
        let Some((deadline, alarm)) = &self.deadline else {
            return false;
        };
        alarm.raised() || (due && Instant::now() >= *deadline)
    }
}

impl DeadlinePoll {
    pub(crate) fn new(cell: SolveDeadlineCell) -> Self {
        Self {
            cell,
            exact_polls: Cell::new(0),
            armed: RefCell::new(None),
        }
    }

    /// [`SolveDeadlineCell::expired`], answered from an alarm once this
    /// poll has read the cell [`EXACT_POLLS`] times; the work ceiling the
    /// cell's poll also reads is then read on the alarm's clock stride.
    pub(crate) fn expired(&self) -> bool {
        let generation = self.cell.generation();
        if let Some(armed) = self.armed.borrow().as_ref() {
            if armed.generation == generation {
                return armed.expired();
            }
        }
        // Unarmed, or armed for a deadline the cell no longer holds.
        self.armed.replace(None);
        let polls = self.exact_polls.get().saturating_add(1);
        self.exact_polls.set(polls);
        if polls >= EXACT_POLLS {
            self.exact_polls.set(0);
            if let Some(armed) = self.arm(generation) {
                let expired = armed.expired();
                self.armed.replace(Some(armed));
                return expired;
            }
        }
        self.cell.expired()
    }

    /// Arm for the deadline the cell holds now, read after `generation`: a
    /// `set` in between moves the generation, and the next poll re-arms.
    /// `None` when no thread can watch it.
    fn arm(&self, generation: u64) -> Option<Armed> {
        let deadline = match self.cell.get() {
            None => None,
            Some(deadline) => {
                let alarm = DeadlineAlarm::arm(deadline);
                if !alarm.watched() {
                    return None;
                }
                Some((deadline, alarm))
            }
        };
        Some(Armed {
            generation,
            deadline,
            clock: ClockStride::new(ARMED_CLOCK_POLLS),
        })
    }

    /// Whether the poll reads an alarm rather than the cell.
    #[cfg(test)]
    pub(crate) fn is_armed(&self) -> bool {
        self.armed.borrow().is_some()
    }
}

#[cfg(test)]
#[path = "alarm_tests.rs"]
mod tests;
