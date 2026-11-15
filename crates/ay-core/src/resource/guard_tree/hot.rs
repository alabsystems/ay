// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! [`Guard::poll`] and [`Guard::cancelled`] for a walk that polls at every
//! step: the strict checker's offers (DR-34, DR-AY-STOPPOLL-HOT-20261031).
//!
//! Both reads walk the node's chain at every call: every node's flags and
//! latched stop, the counts, the lane share and, for [`Guard::poll`], the
//! clock against every deadline the node obeys, its CPU slice and the
//! process memory budget. The strict checker offers once per propagation
//! round of the proof producer's SAT search, and the walk, the proof-repair
//! continuation and the trace caller each read their stop at every offer:
//! 911 M offers on the 44-bit division refutation `qb44` (2026-10-30), where
//! those reads took 60 s of a 108 s run.
//!
//! A [`HotWatch`] is the part of those reads that changes without the
//! clock. The sources only this crate writes (a node's own flag raised by
//! [`Guard::cancel`], a latched stop, a live deadline set) bump one word,
//! `STOP_EPOCH`, after the write; the watch reads that word and every
//! other source itself: the process cancel, the chain's external flags,
//! the own flag of a node whose memory share raises it from ay-sys (GT8),
//! the counts a node stops on (its allotment, every work cap of its chain)
//! and the polling thread's lane share where the chain reads one.
//! [`HotWatch::disturbed`] reads them with relaxed loads: no lock, no clock
//! and no read-modify-write.
//!
//! A [`HotStride`] says when a poll reads whole all the same: at each of its
//! first [`HotStride::EXACT`] polls, then once per [`HotStride::STRIDE`].
//!
//! [`GuardPoll`] answers [`Guard::poll`] with a whole read when its stride
//! is due or its watch is disturbed, and "no stop" otherwise. So everything
//! [`Guard::poll`] reads off a flag, a latch, a count, a lane share or a
//! moved deadline is read at the next poll on the thread that wrote it, and
//! at a poll after the write is visible on another, with [`Guard::poll`]'s
//! own reason. What only the clock, a CPU slice or the process memory
//! budget reveals is read at every poll of a walk's first
//! [`HotStride::EXACT`] polls, then within [`HotStride::STRIDE`] polls:
//! [`Guard::tick`] reads those once per 1024 ticks (GT3), and the proof
//! producer whose rounds make the offers reads its own deadline once per 64
//! checks. The strided whole read also bounds the delay of any write a
//! watch might miss. A poll only ever stops work and every stop is
//! fail-closed (GT9): a condition read a stride later changes when a long
//! walk stops, never what it decides.

use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, Ordering};
use std::sync::Arc;

use super::node::{Flag, Memory, Node};
use super::{Guard, PROCESS_CANCEL};
use crate::resource::Exhausted;

/// Bumped after every write of a stop source that only this crate writes: a
/// node's own flag raised by [`Guard::cancel`], a stop latched (GT7), a live
/// deadline set. A hot watch reads this one word for all of them, and every
/// other source itself (module docs).
static STOP_EPOCH: AtomicU64 = AtomicU64::new(0);

/// Call after writing a stop source `STOP_EPOCH` stands for. Release: a
/// watch that reads the bump reads the write.
pub(crate) fn stop_source_moved() {
    STOP_EPOCH.fetch_add(1, Ordering::Release);
}

/// What a hot poll reads at every poll (module docs): the reads of
/// [`Guard::poll`] or [`Guard::cancelled`] on some nodes, and some extra
/// flags, that change without the clock. `Sync`: an opaque check stop that
/// holds one may be polled from any thread.
pub struct HotWatch {
    /// `STOP_EPOCH` at the last whole read.
    seen: AtomicU64,
    /// The watched flags this crate does not write, each once: the chains'
    /// external flags, the own flags of nodes a memory share raises, and the
    /// extra flags.
    flags: Vec<Arc<AtomicBool>>,
    /// Whether a watched chain stops on the polling thread's lane share:
    /// read inline, one relaxed load while no lane share is entered.
    lane: bool,
    /// Whether any count below is watched.
    counted: bool,
    /// The nodes whose allotment [`Guard::poll`] reads.
    allotted: Vec<Arc<Node>>,
    /// The nodes whose work cap [`Guard::poll`] reads.
    capped: Vec<Arc<Node>>,
}

impl Default for HotWatch {
    fn default() -> Self {
        Self::new()
    }
}

impl HotWatch {
    /// A watch of nothing but the sources `STOP_EPOCH` stands for.
    #[must_use]
    pub fn new() -> Self {
        Self {
            seen: AtomicU64::new(STOP_EPOCH.load(Ordering::Acquire)),
            flags: Vec::new(),
            lane: false,
            counted: false,
            allotted: Vec::new(),
            capped: Vec::new(),
        }
    }

    /// Also watch what [`Guard::poll`] on `guard` reads without the clock:
    /// the cancel chain's flags, every latched stop on it, the node's
    /// allotment, every work cap on the chain, the lane share, and the live
    /// deadlines it obeys (moved only by [`super::LiveDeadline::set`]).
    #[must_use]
    pub fn poll_of(mut self, guard: &Guard) -> Self {
        let node = &guard.node;
        if node.limit().is_some() && !self.allotted.iter().any(|seen| Arc::ptr_eq(seen, node)) {
            self.allotted.push(Arc::clone(node));
        }
        let mut at = Some(node);
        while let Some(link) = at {
            self.chain_link(link);
            if link.cap.is_some() && !self.capped.iter().any(|seen| Arc::ptr_eq(seen, link)) {
                self.capped.push(Arc::clone(link));
            }
            at = link.parent.as_ref();
        }
        self.counted = !self.allotted.is_empty() || !self.capped.is_empty();
        self
    }

    /// Also watch what [`Guard::cancelled`] on `guard` reads: the cancel
    /// chain's flags and the lane share. It reads no clock, so this part of
    /// the watch is exact.
    #[must_use]
    pub fn cancelled_of(mut self, guard: &Guard) -> Self {
        let mut at = Some(&guard.node);
        while let Some(link) = at {
            self.chain_link(link);
            at = link.parent.as_ref();
        }
        self
    }

    /// Also watch `flag`.
    #[must_use]
    pub fn flag(mut self, flag: &Arc<AtomicBool>) -> Self {
        self.add_flag(flag);
        self
    }

    /// One link of a cancel chain (`Node::cancellation`, `lane_tripped`).
    /// Its own flag is [`Guard::cancel`]'s, which bumps `STOP_EPOCH`,
    /// unless its memory share raises it too (GT8).
    fn chain_link(&mut self, link: &Node) {
        if let (Flag::Own(flag), Memory::Share(_)) = (&link.cancel, &link.memory) {
            self.add_flag(flag);
        }
        if let Some(flag) = &link.external {
            self.add_flag(flag);
        }
        self.lane |= matches!(link.memory, Memory::Lane);
    }

    fn add_flag(&mut self, flag: &Arc<AtomicBool>) {
        if !self.flags.iter().any(|seen| Arc::ptr_eq(seen, flag)) {
            self.flags.push(Arc::clone(flag));
        }
    }

    /// Whether something the watched reads see may have changed since the
    /// last whole read: a source `STOP_EPOCH` stands for written (anywhere
    /// in the process), the process cancel or a watched flag raised, a count
    /// reached, or the lane share tripped. Relaxed loads only (module docs).
    #[inline]
    #[must_use]
    pub fn disturbed(&self) -> bool {
        STOP_EPOCH.load(Ordering::Relaxed) != self.seen.load(Ordering::Relaxed)
            || PROCESS_CANCEL.load(Ordering::Relaxed)
            || self.flags.iter().any(|flag| flag.load(Ordering::Relaxed))
            || (self.lane && ay_sys::current_memory_group_soft_tripped())
            || (self.counted && self.counts_disturbed())
    }

    #[inline(never)]
    fn counts_disturbed(&self) -> bool {
        self.allotted.iter().any(|node| node.over_allotment())
            || self.capped.iter().any(|node| node.cap_reached())
    }

    /// Call right before a whole read: note the epoch it reads at, so that
    /// only a later write disturbs the watch, and synchronize with the
    /// writes the epoch counts, so the whole read sees them. A whole read
    /// that answers a stop must be followed by another
    /// ([`HotStride::again`]).
    pub fn note(&self) {
        self.seen
            .store(STOP_EPOCH.load(Ordering::Acquire), Ordering::Relaxed);
    }
}

/// When a hot poll reads whole all the same (module docs). Relaxed loads
/// and stores: a poll another thread makes at once can move a whole read by
/// a poll, never skip one for more than a stride.
pub struct HotStride {
    /// Polls made, up to [`Self::EXACT`]; then [`Self::EXACT`] plus the
    /// polls made since the last strided whole read.
    polls: AtomicU32,
}

impl Default for HotStride {
    fn default() -> Self {
        Self::new()
    }
}

impl HotStride {
    /// Polls read whole at every poll: a short walk reads exactly what it
    /// read before hot polls (`DeadlinePoll`'s `EXACT_POLLS`).
    pub const EXACT: u32 = 1 << 16;
    /// Polls per whole read after [`Self::EXACT`]: the proof producer's own
    /// clock stride (`CHECK_CLOCK_STRIDE`, DR-34).
    pub const STRIDE: u32 = 64;

    /// A stride whose first [`Self::EXACT`] polls are due.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            polls: AtomicU32::new(0),
        }
    }

    /// Count a poll; whether it reads whole.
    #[inline]
    #[must_use]
    pub fn due(&self) -> bool {
        let polls = self.polls.load(Ordering::Relaxed);
        if polls < Self::EXACT {
            self.polls.store(polls + 1, Ordering::Relaxed);
            return true;
        }
        let since = polls - Self::EXACT;
        let next = if since + 1 >= Self::STRIDE {
            Self::EXACT
        } else {
            polls + 1
        };
        self.polls.store(next, Ordering::Relaxed);
        since == 0
    }

    /// Whether every poll still reads whole, counting none.
    #[inline]
    #[must_use]
    pub fn exact(&self) -> bool {
        self.polls.load(Ordering::Relaxed) < Self::EXACT
    }

    /// Make the next poll read whole: a whole read answered a stop, which
    /// may be a clock condition no watched read shows.
    pub fn again(&self) {
        let polls = self.polls.load(Ordering::Relaxed);
        self.polls.store(polls.min(Self::EXACT), Ordering::Relaxed);
    }
}

/// One node, polled at every step of a hot walk (module docs). `Sync`.
pub struct GuardPoll {
    guard: Guard,
    watch: HotWatch,
    stride: HotStride,
}

impl Guard {
    /// A [`GuardPoll`] of this node.
    #[must_use]
    pub fn hot_poll(&self) -> GuardPoll {
        GuardPoll::new(self.clone())
    }
}

impl GuardPoll {
    /// Poll `guard`'s node. Allocates the watch once, here.
    #[must_use]
    pub fn new(guard: Guard) -> Self {
        let watch = HotWatch::new().poll_of(&guard);
        Self {
            guard,
            watch,
            stride: HotStride::new(),
        }
    }

    /// The polled node.
    #[must_use]
    pub fn guard(&self) -> &Guard {
        &self.guard
    }

    /// [`Guard::poll`]'s answer, read whole only when due or disturbed.
    #[inline]
    #[must_use]
    pub fn poll(&self) -> Option<Exhausted> {
        if !self.stride.due() && !self.watch.disturbed() {
            return None;
        }
        self.whole()
    }

    #[cold]
    #[inline(never)]
    fn whole(&self) -> Option<Exhausted> {
        self.watch.note();
        let reason = self.guard.poll();
        if reason.is_some() {
            self.stride.again();
        }
        reason
    }
}

#[cfg(test)]
mod tests;
