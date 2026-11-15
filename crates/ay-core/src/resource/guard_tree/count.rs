// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The count of a GuardTree node (GT2): its allotment, its ticks and what
//! its children hold, and `tick`.
//!
//! A node's own ticks are `own`. What its `Full` children take from the
//! allotment is `held`: an open child's grant, and from its close on what
//! it spent. A close swaps the one for the other in a single
//! atomic step, so no reader ever finds a closing child's spend in neither
//! place (GT2), and `tick` reads `own` and `held` and takes no lock. The
//! spend alone of the closed children, for polls and statistics, is
//! `closed_full`.
//!
//! A grant reads `own` and reserves with a compare-exchange on `held`, so
//! two grants and a close never overcommit. A tick of the parent itself
//! that runs at the same instant as a grant to its child, on another
//! thread, can: its add and the grant's read are not ordered, and ordering
//! them would cost every tick an acquiring add (2 ns, M2). The tree never
//! does both at once: a node's own work and the children it opens run on
//! the thread that entered it; were it to, the overcommit is at most the
//! cost of the parent ticks in flight.
//!
//! Counts saturate: a count at or past [`SATURATED`] reads as `u64::MAX`,
//! which reaches every limit, so a huge cost can never wrap a count back to
//! a small one and read an exhausted subtree as unspent.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use super::node::Node;
use super::{ChildSpec, Inherit, TICKS_PER_CLOCK_READ};
use crate::resource::Exhausted;

/// A count at or past this reads as `u64::MAX` ([`saturated`]).
pub(super) const SATURATED: u64 = 1 << 63;

/// The largest cost `tick` adds with one `fetch_add`; the rest of a larger
/// one is added by a saturating compare-exchange. A count stays below
/// `SATURATED` plus one such add per thread ticking it at once, so it never
/// wraps.
const FAST_COST: u64 = 1 << 32;

/// A count as read: at or past [`SATURATED`] it is `u64::MAX`.
#[inline]
pub(super) const fn saturated(count: u64) -> u64 {
    if count >= SATURATED {
        u64::MAX
    } else {
        count
    }
}

/// The smaller of two limits, either of which may be absent.
fn tighter(a: Option<u64>, b: Option<u64>) -> Option<u64> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    }
}

impl Node {
    /// A view of `node` (a setter on a shared guard): a `Full` child that
    /// spends `node`'s count and caps it at `spec`'s rlimit, if any, and at
    /// the cap of the view it is taken of. Its own deadline and flag are
    /// `spec`'s; every limit of `node` still applies through the chain.
    pub(super) fn view(node: &Arc<Self>, spec: ChildSpec) -> Self {
        let counter = Arc::clone(node.count_in.as_ref().unwrap_or(node));
        let mut view = Self::build(None, ChildSpec::new(spec.label));
        view.parent = Some(Arc::clone(node));
        view.count_in = Some(counter);
        view.external = spec.external;
        view.deadline = spec.deadline;
        view.allotment = tighter(spec.rlimit, node.view_cap());
        view
    }

    /// A view's own cap (`None` for a node that is not a view).
    fn view_cap(&self) -> Option<u64> {
        self.count_in.as_ref().and(self.allotment)
    }

    /// The allotment of a child built under this node (GT2, with DR-39's
    /// clause), and what it took from the remainder.
    ///
    /// A `Full` child's is reserved out of the remainder: a request is
    /// capped by it, and no request draws all of it. A `CancelOnly` child's
    /// is its request, deducted from nothing (DR-39); with no request under
    /// a node that counts it is 0, since DR-39 sizes Certify by its creator
    /// and rejects a `CancelOnly` node without a count. Under a node that
    /// counts nothing, a child keeps its request.
    pub(super) fn allot(&self, inherit: Inherit, requested: Option<u64>) -> (Option<u64>, u64) {
        let Some(limit) = self.limit() else {
            return (requested, 0);
        };
        if inherit == Inherit::CancelOnly {
            return (Some(requested.unwrap_or(0)), 0);
        }
        let counter = self.counter();
        let mut held = counter.held.load(Ordering::Relaxed);
        loop {
            let own = saturated(counter.own.load(Ordering::Relaxed));
            let left = limit.saturating_sub(own.saturating_add(held));
            let grant = requested.map_or(left, |wanted| wanted.min(left));
            // `left` is a function of `held`'s value alone, so a swap that
            // finds the value it read is exact, whatever ran in between.
            match counter.held.compare_exchange_weak(
                held,
                held.saturating_add(grant),
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => return (Some(grant), grant),
                Err(seen) => held = seen,
            }
        }
    }

    /// Replace the allotment of a node nobody else holds yet: give back what
    /// it was granted, then take the new one under the same rule. A view's
    /// cap stays within the cap of the view it was taken of.
    pub(super) fn regrant(&mut self, requested: Option<u64>) {
        let Some(parent) = self.parent.as_deref() else {
            self.allotment = requested;
            return;
        };
        if self.count_in.is_some() {
            self.allotment = tighter(requested, parent.view_cap());
            return;
        }
        if self.granted != 0 {
            parent.counter().settle(self.granted, 0);
        }
        (self.allotment, self.granted) = parent.allot(self.inherit, requested);
    }

    /// A `Full` child that was granted `granted` closes having spent `spent`:
    /// swap the one for the other in `held`, in one step, then add the
    /// spend to `closed_full` (GT2). Saturated stays saturated.
    pub(super) fn close_child(&self, granted: u64, spent: u64) {
        self.settle(granted, spent);
        update(&self.closed_full, |closed| closed.saturating_add(spent));
    }

    /// Swap a grant for a spend in `held`, in one step.
    fn settle(&self, granted: u64, spent: u64) {
        update(&self.held, |held| match held.saturating_add(spent) {
            u64::MAX => u64::MAX,
            // `held` holds the grant until this close.
            sum => sum.saturating_sub(granted),
        });
    }

    /// The node that keeps this node's count: itself, or a view's node.
    #[inline]
    pub(super) fn counter(&self) -> &Self {
        self.count_in.as_deref().unwrap_or(self)
    }

    /// The limit on the count it spends: its allotment, and a view's node's.
    #[inline]
    pub(super) fn limit(&self) -> Option<u64> {
        match self.count_in.as_deref() {
            None => self.allotment,
            Some(counter) => tighter(counter.allotment, self.allotment),
        }
    }

    /// `Guard::tick`: spend `cost` ticks, then say whether the node must
    /// stop. The latched reason, the cancel chain and the limit are read on
    /// every call; the clock, the CPU slices and the memory budget once per
    /// stride (GT3), when the ticks also go up to the ancestors' ledgers.
    /// Every failure is the latched reason (GT7).
    #[inline]
    pub(super) fn tick(&self, cost: u64) -> Result<(), Exhausted> {
        // A branch, not a select: the add below must not wait for a load.
        match self.count_in.as_deref() {
            None => self.tick_against(self, self.allotment, cost),
            Some(counter) => self.tick_view(counter, cost),
        }
    }

    /// `Guard::record_ticks`: `tick`'s spend and its stride flush, without
    /// any of its reads.
    pub(super) fn record_ticks(&self, cost: u64) {
        let counter = self.counter();
        let (after, stride) = counter.spend(cost);
        if stride {
            counter.flush(after);
        }
    }

    #[cold]
    #[inline(never)]
    fn tick_view(&self, counter: &Self, cost: u64) -> Result<(), Exhausted> {
        self.tick_against(counter, self.limit(), cost)
    }

    /// `tick` on the count `counter` keeps, against `limit`.
    #[inline(always)]
    fn tick_against(&self, counter: &Self, limit: Option<u64>, cost: u64) -> Result<(), Exhausted> {
        let (after, stride) = counter.spend(cost);
        if let Some(&why) = self.stopped.get() {
            return Err(why);
        }
        if let Some(why) = self.cancellation() {
            return Err(self.latch(why));
        }
        // An overdraw: what it spent plus what its children hold reaches
        // the limit.
        if limit.is_some_and(|limit| {
            after.saturating_add(counter.held.load(Ordering::Relaxed)) >= limit
        }) {
            return Err(self.latch(Exhausted::Rlimit));
        }
        if stride {
            counter.flush(after);
            if let Some(why) = self.limits() {
                return Err(self.latch(why));
            }
        }
        Ok(())
    }

    /// Add `cost` to its own count, saturating. Returns the count after,
    /// and whether this add crossed a clock stride (GT3); once the count is
    /// saturated every add does, so the clock is still read.
    ///
    /// One add and one branch on the common path (M2: at these costs `tick`
    /// is bound by its branches): a count already saturated and a cost past
    /// [`FAST_COST`] both leave it for [`Self::spend_slow`].
    #[inline(always)]
    fn spend(&self, cost: u64) -> (u64, bool) {
        let fast = cost.min(FAST_COST);
        let before = self.own.fetch_add(fast, Ordering::Relaxed);
        if ((before >> 63) | (cost - fast)) != 0 {
            return self.spend_slow(before, fast, cost);
        }
        let after = before + cost;
        (
            saturated(after),
            before / TICKS_PER_CLOCK_READ != after / TICKS_PER_CLOCK_READ,
        )
    }

    /// `spend`'s rare cases, after it added `fast` to a count that read
    /// `before`. A saturated count takes the add back, so it stays below
    /// `SATURATED` plus one `FAST_COST` per thread adding at once; a cost
    /// past `FAST_COST` adds the rest with a compare-exchange that stops at
    /// `SATURATED`.
    #[cold]
    #[inline(never)]
    fn spend_slow(&self, before: u64, fast: u64, cost: u64) -> (u64, bool) {
        if before >= SATURATED {
            self.own.fetch_sub(fast, Ordering::Relaxed);
            return (u64::MAX, true);
        }
        let rest = cost - fast;
        let mut seen = self.own.load(Ordering::Relaxed);
        loop {
            if seen >= SATURATED {
                return (u64::MAX, true);
            }
            let next = seen.saturating_add(rest).min(SATURATED);
            match self
                .own
                .compare_exchange_weak(seen, next, Ordering::Relaxed, Ordering::Relaxed)
            {
                Ok(_) => return (saturated(next), true),
                Err(now) => seen = now,
            }
        }
    }

    /// Ticks spent against the allotment: its own and its closed `Full`
    /// children's.
    pub(super) fn spent(&self) -> u64 {
        saturated(self.own.load(Ordering::Relaxed))
            .saturating_add(self.closed_full.load(Ordering::Relaxed))
    }

    /// What is left of the limit that no open child holds.
    pub(super) fn remaining(&self) -> Option<u64> {
        let limit = self.limit()?;
        let counter = self.counter();
        let own = saturated(counter.own.load(Ordering::Relaxed));
        Some(limit.saturating_sub(own.saturating_add(counter.held.load(Ordering::Relaxed))))
    }

    /// A poll's view of the limit: spent ticks reach it. What open children
    /// hold is lent, not spent, so a node waiting on its children does not
    /// read as out of ticks.
    pub(super) fn over_allotment(&self) -> bool {
        self.limit()
            .is_some_and(|limit| self.counter().spent() >= limit)
    }
}

/// `counter = f(counter)`, atomically. A compare-exchange loop: the std
/// helper is spelled differently on the toolchains ay-core builds with
/// (`fetch_update` is deprecated for `try_update` on Trust, which the kept
/// Kani baseline lacks; see `term/mod.rs`).
fn update(counter: &AtomicU64, f: impl Fn(u64) -> u64) {
    let mut current = counter.load(Ordering::Relaxed);
    while let Err(seen) =
        counter.compare_exchange_weak(current, f(current), Ordering::Relaxed, Ordering::Relaxed)
    {
        current = seen;
    }
}
