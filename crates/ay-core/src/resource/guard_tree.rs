// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The GuardTree: one resource tree per check (the development design notes,
//! KC6; amended by the development design notes DR-38 and DR-39). Steps S0, the
//! types; S1, the root; and S2's parts here: the reads that latch nothing
//! and the lane share the executor's nodes read (`read.rs`), and the work
//! ceiling and grant as nodes (`cap.rs`).
//!
//! A [`Guard`] is a handle on a node; clones share the node. Each node owns
//! its cancel flag, its deadline, its rlimit allotment, its CPU slice, its
//! memory share, its ledger and its latched stop reason, and it is linked to
//! its parent. The rules, by the design's names:
//!
//! * **GT1.** A node stops when it, or an ancestor it inherits from, stops.
//!   Every node sees every ancestor's cancel flags. An [`Inherit::Full`]
//!   node also sees their deadlines and CPU slices, their latched stops and
//!   the process memory budget; an [`Inherit::CancelOnly`] node (Certify)
//!   sees only their flags.
//! * **GT2.** Ticks are per node, never shared between siblings. A child's
//!   allotment is fixed when it is built. A `Full` child's is deducted from
//!   its parent's remainder, and its close (its last handle dropping)
//!   returns what it did not spend; a caller that needs a deterministic
//!   remainder closes children in a fixed order (sequential slices, joins in
//!   worker-index order). A `CancelOnly` child's allotment is its own and
//!   moves nothing (DR-39); under a node that counts, it is the child's
//!   request, or 0 without one. A tick that overdraws (what the node spent
//!   plus what its children hold reaches the allotment) latches `Rlimit`,
//!   even when the overdraw is only lent ticks.
//! * **GT3.** The clock, the CPU slice and the memory budget are read once
//!   per 1024 ticks (`TICKS_PER_CLOCK_READ`), or by [`Guard::exhausted`].
//! * **GT4.** [`Guard::enter`] makes the node the thread's current guard.
//! * **GT5.** Work is added to the node's ledger and every ancestor's.
//!   Ticks go up once per clock stride and at the node's close, not one
//!   atomic add per level per tick: M2 measured the per-tick adds at 1.8x
//!   the old guard's `tick` at depth 3 before the root became a node, and
//!   every worker's tick would hit the root's one counter. An ancestor's
//!   tick count trails an open descendant's by less than a stride and is
//!   exact once the descendant closes (the amendment to GT5 in
//!   the development design notes).
//! * **GT6.** [`Guard::share`] builds a `Share` child; the parent's
//!   deadline is never written. Under a tick budget it shares ticks and
//!   leaves the deadline whole (DR-38 rule 7).
//! * **GT7.** The first stop reason is latched per node, by
//!   [`Guard::exhausted`] and [`Guard::tick`], where a stop is acted on;
//!   [`Guard::poll`] latches nothing (`read.rs`).
//! * **GT8.** A memory share's soft trip raises the node's own flag.
//! * **GT9.** Nothing here decides a verdict: a stop is only ever `unknown`.
//!
//! The root is the process (S1, `root.rs`): its flag is the process cancel,
//! its ledger the process work ledger and its memory the process budget, so
//! [`super::cancel_process`], [`super::process_cancelled`] and
//! [`super::work`] read and write the root. Every other node hangs below it,
//! and work reported on the root's ledger is charged to the reporting
//! thread's current node first (GT5).

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use super::{Exhausted, WorkSnapshot};
use crate::time::Instant;

mod cap;
mod count;
mod cpu;
mod deadline;
mod hot;
mod node;
mod read;
mod root;
mod scope;
mod spec;
#[cfg(test)]
mod tests;

pub(crate) use cap::{current_cap_reached, enter_cap, CapKind, WorkCap};
pub use deadline::{DeadlineSource, LiveDeadline};
pub use hot::{GuardPoll, HotStride, HotWatch};
pub use read::WeakGuard;
pub(crate) use root::{PROCESS_CANCEL, WORK};
pub use scope::{current_guard, with_current_guard, EnterScope};
use spec::MemorySpec;
pub use spec::{ChildSpec, MemoryShare};

use node::Node;

/// How many ticks pass between two reads of the clock, the CPU slices and
/// the memory budget in [`Guard::tick`] (GT3).
pub(crate) const TICKS_PER_CLOCK_READ: u64 = 1024;

/// What a node inherits from its ancestors (GT1).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Inherit {
    /// Everything: every ancestor's stop reaches the node, and its allotment
    /// is deducted from its parent's remainder. The default (DR-39).
    #[default]
    Full,
    /// Only the ancestors' cancel flags: the node keeps its own deadline
    /// (the certification envelope) and its own allotment (DR-39).
    CancelOnly,
}

/// The index of a worker below its check.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WorkerId(pub usize);

/// What a node is for (design §2).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NodeLabel {
    /// The root: the process. No [`Guard`] holds it.
    Root,
    /// One check-sat.
    Check,
    /// A run of several checks that meters them (a CHC proof run,
    /// the development design notes §13). It is not a check: a search for
    /// the nearest `Check` (Certify's sizing) passes over it to the check
    /// around it, or finds none.
    Run,
    /// The search wall of a check.
    Search,
    /// One worker of a search.
    Worker(WorkerId),
    /// A certification envelope.
    Certify,
    /// A deadline slicer's share (GT6).
    Share,
    /// A work ceiling (a DR-stalls-1 retry's): a cap on the work units its
    /// subtree reports (GuardTree step S2; DR-37 makes it an allotment).
    Ceiling,
    /// A counted work grant (a metered probe's): a cap on the split-loop
    /// round trips its subtree reports (step S2; DR-37 likewise).
    Grant,
}

impl NodeLabel {
    /// The name its memory share reports to the memory governor.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::Root => "root",
            Self::Check => "check",
            Self::Run => "run",
            Self::Search => "search",
            Self::Worker(_) => "worker",
            Self::Certify => "certify",
            Self::Share => "share",
            Self::Ceiling => "ceiling",
            Self::Grant => "grant",
        }
    }
}

/// How much of a node a share gets (GT6).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Portion {
    /// Half of what is left.
    Half,
}

/// A handle on one node of the GuardTree. Clones share the node: its
/// ticks, its flag and its latched reason.
#[derive(Clone)]
pub struct Guard {
    node: Arc<Node>,
}

impl Default for Guard {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for Guard {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Guard")
            .field("label", &self.node.label)
            .field("inherit", &self.node.inherit)
            .field("allotment", &self.node.limit())
            .field("ticks", &self.ticks())
            .field("deadline", &self.deadline())
            .field("stopped", &self.stopped())
            .finish_non_exhaustive()
    }
}

impl Guard {
    /// A `Check` node under the root with no limits of its own: it stops
    /// only for the process-wide cancel and memory budget
    /// ([`super::ResourceGuard::new`]).
    #[must_use]
    pub fn new() -> Self {
        Self::root_child(ChildSpec::new(NodeLabel::Check))
    }

    /// A node directly under the root.
    #[must_use]
    pub fn root_child(spec: ChildSpec) -> Self {
        Self {
            node: Arc::new(Node::build(None, spec)),
        }
    }

    /// A child of this node (GT1, GT2).
    #[must_use]
    pub fn child(&self, spec: ChildSpec) -> Self {
        Self {
            node: Arc::new(Node::build(Some(Arc::clone(&self.node)), spec)),
        }
    }

    /// A `Share` child (GT6) of what is left to this node:
    /// [`Self::share_of`] its effective deadline.
    #[must_use]
    pub fn share(&self, portion: Portion) -> Option<Self> {
        Self::share_of(Some(self), portion, self.node.effective_deadline())
    }

    /// A `Share` child (GT6): under a tick budget, `portion` of the ticks
    /// left and the deadline whole (DR-38 rule 7); otherwise its own
    /// deadline at `portion` of the time left before `deadline` (an owner
    /// that keeps a deadline of its own, the executor, divides that one).
    /// That deadline is a live cell of the share's own
    /// ([`Self::live_deadline`]): its owner may move it while the share is
    /// open, and the parent's is never written. Counted in `deadline_shares`
    /// now and in `deadline_shares_spent` at its close if it spent its share.
    /// `None` when there is nothing to divide: no ticks and no deadline. A
    /// share without a parent hangs from the root, which counts nothing.
    #[must_use]
    pub fn share_of(
        parent: Option<&Self>,
        portion: Portion,
        deadline: Option<Instant>,
    ) -> Option<Self> {
        let spec = ChildSpec::new(NodeLabel::Share);
        let spec = if let Some(left) = parent.and_then(Self::remaining) {
            spec.with_rlimit(Some(match portion {
                Portion::Half => left / 2,
            }))
        } else {
            let now = Instant::now();
            let left = deadline?.saturating_duration_since(now);
            let at = now.checked_add(match portion {
                Portion::Half => left / 2,
            })?;
            spec.with_deadline(DeadlineSource::Live(LiveDeadline::new(Some(at))))
        };
        let share = match parent {
            Some(parent) => parent.child(spec),
            None => Self::root_child(spec),
        };
        share.record_work(&WorkSnapshot {
            deadline_shares: 1,
            ..WorkSnapshot::default()
        });
        Some(share)
    }

    /// Raise this node's own flag: it and its descendants stop.
    pub fn cancel(&self) {
        self.node.cancel.get().store(true, Ordering::Relaxed);
        hot::stop_source_moved();
    }

    /// Spend `cost` ticks. Fails once the node must stop: the latched
    /// reason, the cancel chain and the allotment are read on every call;
    /// the clock, the CPU slices and the memory budget once per 1024 ticks
    /// (GT3), when the ticks are also passed up to the ancestors' ledgers.
    /// Every failure is the latched reason (GT7). The count saturates.
    pub fn tick(&self, cost: u64) -> Result<(), Exhausted> {
        #[cfg(any(test, feature = "determinism-seams"))]
        super::test_seams::delay_these_ticks(cost);
        self.node.tick(cost)
    }

    /// Spend `cost` ticks and read nothing: no limit is checked and no
    /// reason is latched, so the count decides nothing here. A meter's
    /// charge (ay-chc's CHC run node, guard-tree.md §13). The ticks reach the
    /// ancestors' ledgers on the clock stride and at the node's close, as a
    /// [`Self::tick`]'s do (GT5). Under an allotment they count against it,
    /// and the next [`Self::tick`] or poll of the node reads them.
    pub fn record_ticks(&self, cost: u64) {
        self.node.record_ticks(cost);
        #[cfg(any(test, feature = "determinism-seams"))]
        {
            super::test_seams::delay_this_charge();
            super::test_seams::delay_these_ticks(cost);
        }
    }

    /// Why the node must stop now, if it must: every condition is read, in
    /// the order cancelled, rlimit, deadline, CPU, memory; the first reason
    /// observed is latched and reported from then on (GT7).
    #[must_use]
    pub fn exhausted(&self) -> Option<Exhausted> {
        let node = &*self.node;
        if let Some(&why) = node.stopped.get() {
            return Some(why);
        }
        let why = node
            .cancellation()
            .or_else(|| node.over_allotment().then_some(Exhausted::Rlimit))
            .or_else(|| node.limits())?;
        Some(node.latch(why))
    }

    /// The search's stop question.
    #[must_use]
    pub fn should_stop(&self) -> bool {
        self.exhausted().is_some()
    }

    /// The latched stop reason, without reading anything else.
    #[must_use]
    pub fn stopped(&self) -> Option<Exhausted> {
        self.node.stopped.get().copied()
    }

    /// Ticks spent against the allotment: this node's own and those its
    /// closed `Full` children spent (a view's: its node's). All work below
    /// it, `CancelOnly` children's included, is [`Self::ledger_ticks`].
    #[must_use]
    pub fn ticks(&self) -> u64 {
        self.node.counter().spent()
    }

    /// The allotment (`None`: no count of its own). A view's is the tighter
    /// of its node's and its own cap ([`Self::set_rlimit`]).
    #[must_use]
    pub fn allotment(&self) -> Option<u64> {
        self.node.limit()
    }

    /// What is left of the allotment that no open child holds.
    #[must_use]
    pub fn remaining(&self) -> Option<u64> {
        self.node.remaining()
    }

    /// The node's own deadline now.
    #[must_use]
    pub fn deadline(&self) -> Option<Instant> {
        self.node.deadline.get()
    }

    /// The nearest original external cancellation flag, if present.
    ///
    /// Adapters may link this same flag to a child, never set or reset it.
    /// This is not the complete tree stop: retain the guard and poll it too,
    /// since ancestors, its own cancellation and other limits still apply.
    #[must_use]
    pub fn cancel_flag(&self) -> Option<&Arc<AtomicBool>> {
        let mut node = &*self.node;
        loop {
            if let Some(flag) = &node.external {
                return Some(flag);
            }
            node = node.parent.as_deref()?;
        }
    }

    /// The cell of its own deadline, when it reads one live (a share's, or
    /// a node built on an owner's cell).
    #[must_use]
    pub fn live_deadline(&self) -> Option<LiveDeadline> {
        match &self.node.deadline {
            DeadlineSource::Live(cell) => Some(cell.clone()),
            DeadlineSource::None | DeadlineSource::Fixed(_) => None,
        }
    }

    /// The earliest deadline the node obeys, its ancestors' included.
    #[must_use]
    pub fn effective_deadline(&self) -> Option<Instant> {
        self.node.effective_deadline()
    }

    /// What the node is for.
    #[must_use]
    pub fn label(&self) -> NodeLabel {
        self.node.label
    }

    /// What it inherits.
    #[must_use]
    pub fn inherit(&self) -> Inherit {
        self.node.inherit
    }

    /// The work of this node and everything below it (GT5).
    #[must_use]
    pub fn ledger(&self) -> WorkSnapshot {
        self.node.ledger.snapshot()
    }

    /// Every tick spent in this node and below it, `CancelOnly` children's
    /// included (GT5, DR-39): what `rlimit-count` reports from S6 on. Its
    /// own ticks count at once, an open descendant's at each of its clock
    /// strides and at its close. A view reads its node's.
    #[must_use]
    pub fn ledger_ticks(&self) -> u64 {
        let counter = self.node.counter();
        count::saturated(counter.own.load(Ordering::Relaxed)).saturating_add(counter.ledger.ticks())
    }

    /// Add `work` to this node's ledger and every ancestor's (GT5). The work
    /// ceiling and grant are nodes whose caps read their own ledgers
    /// (`cap.rs`, step S2), so work recorded at or below a Ceiling or Grant
    /// spends that cap, as work reported through [`super::work`] on a thread
    /// inside it does. The thread counters (`thread_work_units`,
    /// `thread_round_trips`) do not move.
    pub fn record_work(&self, work: &WorkSnapshot) {
        self.node.record(work);
    }

    /// Stop once this instant passes (`None`: no deadline of its own).
    /// [`super::ResourceGuard`]'s setter: see [`Self::set_rlimit`].
    pub fn set_deadline(&mut self, deadline: Option<Instant>) {
        let source = DeadlineSource::from(deadline);
        match Arc::get_mut(&mut self.node) {
            Some(node) => node.deadline = source,
            None => self.become_view(ChildSpec::new(self.label()).with_deadline(source)),
        }
    }

    /// Stop once this flag is raised (`None`: no external flag).
    /// [`super::ResourceGuard`]'s setter: see [`Self::set_rlimit`].
    pub fn set_cancel(&mut self, cancel: Option<Arc<AtomicBool>>) {
        match Arc::get_mut(&mut self.node) {
            Some(node) => node.external = cancel,
            None => {
                let mut spec = ChildSpec::new(self.label());
                spec.external = cancel;
                self.become_view(spec);
            }
        }
    }

    /// Stop once this many ticks are spent (`None`: no count of its own).
    ///
    /// The setters are [`super::ResourceGuard`]'s and configure a node no
    /// one else holds yet. On a node that is shared (cloned, entered, or
    /// given a child) this handle becomes a VIEW of the node instead: it
    /// spends the node's one count, as clones of the old guard shared one,
    /// and it obeys every limit the node has plus the setting, for this
    /// handle alone (an rlimit caps the shared count). The other holders
    /// keep their limits and the count. So a setter adds a stop and never
    /// lifts one: `None` lifts only a limit this handle set while it alone
    /// held its node.
    pub fn set_rlimit(&mut self, rlimit: Option<u64>) {
        match Arc::get_mut(&mut self.node) {
            Some(node) => node.regrant(rlimit),
            None => self.become_view(ChildSpec::new(self.label()).with_rlimit(rlimit)),
        }
    }

    fn become_view(&mut self, spec: ChildSpec) {
        self.node = Arc::new(Node::view(&self.node, spec));
    }
}
