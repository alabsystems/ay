// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A ladder race's settlement: whether it already holds its verdict, visible
//! on every participant's thread ([`race_settled`]).

use std::cell::RefCell;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

/// A race's "decided" flag, chained to the races enclosing it (a race nested
/// in another race's participant is settled when either is decided).
pub(super) struct Settlement {
    decided: AtomicBool,
    outer: Option<Arc<Settlement>>,
}

impl Settlement {
    /// An open settlement nested in the thread's current one (if any).
    pub(super) fn nested() -> Self {
        Self {
            decided: AtomicBool::new(false),
            outer: current_settlement(),
        }
    }

    /// Record the verdict; call before the participants' tokens are cancelled,
    /// so a participant that observes its cancellation sees the race settled.
    pub(super) fn settle(&self) {
        self.decided.store(true, Ordering::Release);
    }

    fn reached(&self) -> bool {
        self.decided.load(Ordering::Acquire)
            || self.outer.as_ref().is_some_and(|outer| outer.reached())
    }
}

thread_local! {
    /// The settlement of the ladder race whose participant runs on this thread.
    static THREAD_SETTLEMENT: RefCell<Option<Arc<Settlement>>> = const { RefCell::new(None) };
}

fn current_settlement() -> Option<Arc<Settlement>> {
    THREAD_SETTLEMENT
        .try_with(|cell| cell.try_borrow().ok().and_then(|slot| slot.clone()))
        .ok()
        .flatten()
}

/// Binds a race's settlement to the participant's thread; restores on drop.
pub(super) struct ScopedSettlement {
    prev: Option<Arc<Settlement>>,
}

impl ScopedSettlement {
    pub(super) fn install(settlement: Arc<Settlement>) -> Self {
        let prev = THREAD_SETTLEMENT.with(|cell| cell.replace(Some(settlement)));
        Self { prev }
    }
}

impl Drop for ScopedSettlement {
    fn drop(&mut self) {
        let prev = self.prev.take();
        let _ = THREAD_SETTLEMENT.try_with(|cell| {
            cell.replace(prev);
        });
    }
}

/// True when a ladder race this thread participates in (directly or through an
/// enclosing race) already holds its verdict. Whatever the thread still
/// computes is discarded, so a join inside it may treat its cancelled workers
/// like losers after a validated verdict — a bounded join, then detach
/// (`ParallelWorkerGroup::reap_after_verdict`) — instead of waiting out a
/// worker stuck in a stage with no cancellation boundary. Measured on
/// graham-scan-full.31: the cyclic-consistency member certified Safe while the
/// BV dual lane (foreground) joined a BvToBool lane inside a 40 s
/// constant-resimplification pass; the run hit the 62 s hard exit and printed
/// `unknown`.
pub(crate) fn race_settled() -> bool {
    current_settlement().is_some_and(|settlement| settlement.reached())
}
