// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One node of the GuardTree: its limits, its links and its stop rule. Its
//! count, and `tick`, are in `count.rs`.

use std::ops::Deref;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, OnceLock};

use ay_sys::MemoryGroup;

use super::cap::{self, CapKind, WorkCap};
use super::count::saturated;
use super::cpu::CpuBudget;
use super::root::{PROCESS_CANCEL, ROOT, WORK};
use super::{ChildSpec, DeadlineSource, Inherit, MemorySpec, NodeLabel};
use crate::resource::{Exhausted, WorkLedger, WorkSnapshot};
use crate::time::Instant;

/// A node's own cancel flag.
pub(super) enum Flag {
    /// The root's: the process cancel, [`PROCESS_CANCEL`].
    Process,
    /// Any other node's, shared with its memory share (GT8).
    Own(Arc<AtomicBool>),
}

impl Flag {
    pub(super) fn get(&self) -> &AtomicBool {
        match self {
            Self::Process => &PROCESS_CANCEL,
            Self::Own(flag) => flag,
        }
    }
}

/// A node's memory.
pub(super) enum Memory {
    /// None of its own: a thread that enters it enters the nearest
    /// ancestor's share, so its allocations stay charged there (§6).
    Inherited,
    /// Its own share (GT8).
    Share(Arc<MemoryGroup>),
    /// The root's: the process budget. Its bytes stay in ay-sys, whose
    /// counting allocator reads them for the hard ceiling at every
    /// allocation and which cannot depend on this crate; the root's
    /// condition is ay-sys's 95 % check, [`ay_sys::process_memory_exceeded`].
    Process,
    /// None of its own, but the share of the portfolio lane the POLLING
    /// thread runs in stops it (`ChildSpec::with_lane_share`): that lane's
    /// group is already current on the thread, so entering the node enters
    /// none, as for [`Self::Inherited`].
    Lane,
}

/// A node's ledger.
pub(super) enum Ledger {
    /// The root's: the process-wide ledger, [`WORK`].
    Process,
    /// Any other node's.
    Own(WorkLedger),
}

impl Deref for Ledger {
    type Target = WorkLedger;

    fn deref(&self) -> &WorkLedger {
        match self {
            Self::Process => &WORK,
            Self::Own(ledger) => ledger,
        }
    }
}

pub(super) struct Node {
    /// The node it hangs from; `None`: the root (for the root itself,
    /// nothing). The root is no `Arc`, so the hot walk of `tick` follows
    /// these links and reads the root's flag last.
    pub(super) parent: Option<Arc<Node>>,
    /// A view's counting node: a setter on a shared [`super::Guard`] moves
    /// its handle to a view of the node, which keeps no count of its own and
    /// spends the node's (`Guard::set_rlimit`). Never itself a view. `None`:
    /// the node keeps its own count.
    pub(super) count_in: Option<Arc<Node>>,
    pub(super) inherit: Inherit,
    pub(super) label: NodeLabel,
    /// Its own flag (GT1): raised by [`super::Guard::cancel`] and by its
    /// memory share's soft trip (GT8). A parent never reads a child's.
    pub(super) cancel: Flag,
    /// An owner's flag the node also stops on (an executor interrupt).
    pub(super) external: Option<Arc<AtomicBool>>,
    pub(super) deadline: DeadlineSource,
    /// The rlimit allotment (GT2); `None`: no count of its own. A view's:
    /// its own cap on the count it spends.
    pub(super) allotment: Option<u64>,
    /// What the allotment took from the parent's remainder: the whole
    /// allotment of a `Full` child of a parent that has one, else 0.
    pub(super) granted: u64,
    /// Ticks of this node's own `tick` calls (and its views').
    pub(super) own: AtomicU64,
    /// How many of them the ancestors' ledgers have seen ([`Self::flush`]).
    pub(super) flushed: AtomicU64,
    /// Ticks its closed `Full` children spent; they count against this
    /// node's allotment from their close on.
    pub(super) closed_full: AtomicU64,
    /// What its `Full` children take from the allotment: the open ones'
    /// grants and the closed ones' spend. Saturates.
    pub(super) held: AtomicU64,
    pub(super) cpu: Option<CpuBudget>,
    pub(super) memory: Memory,
    /// A cap on the work its ledger counts (a work ceiling or grant, `cap.rs`).
    pub(super) cap: Option<WorkCap>,
    /// Work of this node and its descendants (GT5). Its tick count holds
    /// the descendants' flushed ticks; the node's own are in `own`.
    pub(super) ledger: Ledger,
    /// The first stop reason it observed (GT7). The root latches nothing:
    /// nobody polls it, and its conditions are the process's, read live.
    pub(super) stopped: OnceLock<Exhausted>,
}

/// `Instant::now`, read at most once per evaluation and only if a deadline
/// asks for it.
#[derive(Default)]
struct Clock(Option<Instant>);

impl Clock {
    fn now(&mut self) -> Instant {
        *self.0.get_or_insert_with(Instant::now)
    }
}

impl Node {
    /// The root (GuardTree step S1): the process. Its flag, its ledger and
    /// its memory are the process's; it has no deadline, no count and no
    /// CPU slice of its own (the CLI's watchdogs end the run by raising its
    /// flag).
    pub(super) const fn root() -> Self {
        Self {
            parent: None,
            count_in: None,
            inherit: Inherit::Full,
            label: NodeLabel::Root,
            cancel: Flag::Process,
            external: None,
            deadline: DeadlineSource::None,
            allotment: None,
            granted: 0,
            own: AtomicU64::new(0),
            flushed: AtomicU64::new(0),
            closed_full: AtomicU64::new(0),
            held: AtomicU64::new(0),
            cpu: None,
            memory: Memory::Process,
            cap: None,
            ledger: Ledger::Process,
            stopped: OnceLock::new(),
        }
    }

    pub(super) fn build(parent: Option<Arc<Self>>, spec: ChildSpec) -> Self {
        let cancel = Arc::new(AtomicBool::new(false));
        let memory = match spec.memory {
            MemorySpec::Inherited => Memory::Inherited,
            MemorySpec::Share(share) => Memory::Share(MemoryGroup::named(
                spec.label.name(),
                share.soft_bytes,
                share.hard_bytes,
                Arc::clone(&cancel),
            )),
            MemorySpec::Lane => Memory::Lane,
        };
        if let Some(cap) = spec.cap {
            cap::opened(cap);
        }
        // The root lends nothing (it has no count), so a child of the root
        // keeps what it asked for.
        let (allotment, granted) = match parent.as_deref() {
            Some(parent) => parent.allot(spec.inherit, spec.rlimit),
            None => (spec.rlimit, 0),
        };
        Self {
            parent,
            count_in: None,
            inherit: spec.inherit,
            label: spec.label,
            cancel: Flag::Own(cancel),
            external: spec.external,
            deadline: spec.deadline,
            allotment,
            granted,
            own: AtomicU64::new(0),
            flushed: AtomicU64::new(0),
            closed_full: AtomicU64::new(0),
            held: AtomicU64::new(0),
            cpu: spec.cpu.map(CpuBudget::new),
            memory,
            cap: spec.cap,
            ledger: Ledger::Own(WorkLedger::new()),
            stopped: OnceLock::new(),
        }
    }

    /// The node it hangs from (`None`: it is the root).
    pub(super) fn up(&self) -> Option<&Self> {
        match self.parent.as_deref() {
            Some(parent) => Some(parent),
            None if std::ptr::eq(self, &raw const ROOT) => None,
            None => Some(&ROOT),
        }
    }

    /// Ancestors, nearest first, the root last.
    pub(super) fn ancestors(&self) -> impl Iterator<Item = &Self> {
        std::iter::successors(self.up(), |node| node.up())
    }

    /// Its own memory share, if it has one.
    pub(super) fn share(&self) -> Option<&Arc<MemoryGroup>> {
        match &self.memory {
            Memory::Share(group) => Some(group),
            Memory::Inherited | Memory::Process | Memory::Lane => None,
        }
    }

    /// The share a thread that enters it is charged to: its own, else the
    /// nearest ancestor's (§6).
    pub(super) fn charged_share(&self) -> Option<&Arc<MemoryGroup>> {
        std::iter::once(self)
            .chain(self.ancestors())
            .find_map(Self::share)
    }

    /// Pass the node's own ticks that its ancestors' ledgers have not seen
    /// yet up to every one of them (GT5). `tick` calls it once per clock
    /// stride (GT3) and the node's close calls it last, so each tick reaches
    /// each ancestor exactly once: an ancestor's count trails an open
    /// descendant's by less than one stride and is exact once it closes.
    pub(super) fn flush(&self, own: u64) {
        let seen = self.flushed.fetch_max(own, Ordering::Relaxed);
        if own > seen {
            for node in self.ancestors() {
                node.ledger.add_ticks(own - seen);
            }
        }
    }

    /// Add work to this node's ledger and every ancestor's (GT5).
    pub(super) fn record(&self, work: &WorkSnapshot) {
        self.ledger.absorb(work);
        for node in self.ancestors() {
            node.ledger.absorb(work);
        }
    }

    pub(super) fn latch(&self, why: Exhausted) -> Exhausted {
        let mut latched = false;
        let first = *self.stopped.get_or_init(|| {
            latched = true;
            why
        });
        if latched {
            super::hot::stop_source_moved();
        }
        first
    }

    /// This node's flags: its own (its memory share's trip reads as
    /// `Memory`, GT8), then the external one.
    fn flags(&self) -> Option<Exhausted> {
        if self.cancel.get().load(Ordering::Relaxed) {
            // A trip marks the share before it raises the flag (`Release`),
            // so a raised flag reads the mark.
            std::sync::atomic::fence(Ordering::Acquire);
            let memory = self
                .share()
                .is_some_and(|group| group.soft_tripped() || group.was_shed());
            return Some(if memory {
                Exhausted::Memory
            } else {
                Exhausted::Cancelled
            });
        }
        self.external
            .as_ref()
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
            .then_some(Exhausted::Cancelled)
    }

    /// Whether it, or any ancestor, stops on the lane share of the polling
    /// thread ([`Memory::Lane`]), and that share has tripped. A memory
    /// condition, so `tick` reads it on the stride (GT3); like a share's
    /// trip, which raises a flag (GT8), it reaches every descendant,
    /// `CancelOnly` ones included.
    pub(super) fn lane_tripped(&self) -> bool {
        std::iter::once(self)
            .chain(self.ancestors())
            .any(|node| matches!(node.memory, Memory::Lane))
            && ay_sys::current_memory_group_soft_tripped()
    }

    /// GT1, the cancel chain: its own flags, then each ancestor's, the
    /// root's (the process cancel) last. Every node sees every ancestor's
    /// flags, whatever it inherits.
    pub(super) fn cancellation(&self) -> Option<Exhausted> {
        let mut node = self;
        loop {
            if let Some(why) = node.flags() {
                return Some(why);
            }
            match node.parent.as_deref() {
                Some(parent) => node = parent,
                None => break,
            }
        }
        // The root's flag (`ROOT.flags()`, read without the walk).
        PROCESS_CANCEL
            .load(Ordering::Relaxed)
            .then_some(Exhausted::Cancelled)
    }

    /// Its own limits read on the stride: the deadline, the CPU slice and,
    /// for the root, the process memory budget.
    fn clock_limits(&self, clock: &mut Clock) -> Option<Exhausted> {
        if self.deadline.get().is_some_and(|at| clock.now() >= at) {
            return Some(Exhausted::Deadline);
        }
        if self.cpu.as_ref().is_some_and(CpuBudget::exceeded) {
            return Some(Exhausted::Cpu);
        }
        (matches!(self.memory, Memory::Process) && ay_sys::process_memory_exceeded())
            .then_some(Exhausted::Memory)
    }

    /// GT1, the limits read on the clock stride (GT3): its own deadline and
    /// CPU, then each ancestor's while the chain is `Full`, up to the root's
    /// memory budget if the whole chain is. An ancestor's latched stop
    /// reaches a `Full` descendant, except `Rlimit`: an ancestor's count
    /// reaches its subtree through the allotments it lent (GT2), so a
    /// child's stop point depends on its own ticks alone. A latched
    /// `Cancelled` reaches every descendant. A work cap reached on it or on
    /// any ancestor reads as `Rlimit`, whatever it inherits (`cap.rs`); a
    /// tripped lane share it or an ancestor reads, as `Memory`.
    pub(super) fn limits(&self) -> Option<Exhausted> {
        let mut clock = Clock::default();
        if let Some(why) = self.clock_limits(&mut clock) {
            return Some(why);
        }
        if self.lane_tripped() {
            return Some(Exhausted::Memory);
        }
        if self.cap_reached() {
            return Some(Exhausted::Rlimit);
        }
        let mut full = self.inherit == Inherit::Full;
        for node in self.ancestors() {
            match node.stopped.get() {
                Some(&Exhausted::Cancelled) => return Some(Exhausted::Cancelled),
                Some(&why) if full && why != Exhausted::Rlimit => return Some(why),
                _ => {}
            }
            if full {
                if let Some(why) = node.clock_limits(&mut clock) {
                    return Some(why);
                }
            }
            if node.cap_reached() {
                return Some(Exhausted::Rlimit);
            }
            full &= node.inherit == Inherit::Full;
        }
        None
    }

    /// The earliest deadline it obeys: its own, and its ancestors' while the
    /// chain is `Full`.
    pub(super) fn effective_deadline(&self) -> Option<Instant> {
        let mut earliest = self.deadline.get();
        let mut full = self.inherit == Inherit::Full;
        for node in self.ancestors() {
            if !full {
                break;
            }
            earliest = match (earliest, node.deadline.get()) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (a, b) => a.or(b),
            };
            full = node.inherit == Inherit::Full;
        }
        earliest
    }

    /// A share closes spent when its count or its deadline is (GT6), or
    /// when a work ceiling over it is reached: the executor's deadline polls
    /// report a reached ceiling as a passed deadline, and so did its count of
    /// spent shares before the shares were nodes (step S3).
    fn share_spent(&self) -> bool {
        self.over_allotment()
            || self.deadline.get().is_some_and(|at| Instant::now() >= at)
            || self.chain_cap_reached(CapKind::Units)
    }
}

/// Closing a node (GT2): its last handle is gone, so nothing can spend in it
/// any more. A `Full` child gives its parent's counting node back what it
/// was granted for what it spent; a `CancelOnly` child moves nothing
/// (DR-39), its ticks are already in the ledgers above it. A view moves
/// nothing either: its ticks are its node's.
impl Drop for Node {
    fn drop(&mut self) {
        if let Some(cap) = self.cap {
            cap::closed(cap);
        }
        self.flush(saturated(self.own.load(Ordering::Relaxed)));
        let Some(parent) = self.up() else {
            return;
        };
        if self.count_in.is_some() {
            return;
        }
        if self.label == NodeLabel::Share && self.share_spent() {
            parent.record(&WorkSnapshot {
                deadline_shares_spent: 1,
                ..WorkSnapshot::default()
            });
        }
        // The root keeps no count: nothing to give back or charge there.
        if self.inherit == Inherit::Full && !std::ptr::eq(parent, &raw const ROOT) {
            parent.counter().close_child(self.granted, self.spent());
        }
    }
}
