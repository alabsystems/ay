// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Work caps: the work ceiling and the counted work grant as nodes
//! (the development design notes, step S2).
//!
//! Before S2 each was a thread-local: a ceiling on the work units (CDCL
//! conflicts plus split-loop round trips) and a grant of split-loop round
//! trips, both counted on the thread that entered them. Each is now a node:
//! a `Full` child of the thread's current node, entered on the thread
//! (GT4), whose cap is read off its own ledger. Work is charged to the
//! thread's current node and every ancestor (GT5), so the ledger of a cap
//! entered on a thread holds the work that thread reported inside it, the
//! work of every node below it included, as the thread's counters did. A
//! worker that enters a node below the cap now spends it too (GT4).
//!
//! The units stay the ones the executor counted: DR-37 turns both into
//! allotments of the check's tick budget in step S6.
//!
//! A cap reaches every node below it, a `CancelOnly` one included (S2's
//! choice, recorded in guard-tree.md §12). GT1 hides an ancestor's deadline
//! and rlimit from `CancelOnly`, but Certify has no count of its own until
//! S6 (DR-39), and a certification bounded by a clock alone is what DR-39
//! rejects: so, as before S2, the work a certification runs inside a retry
//! or a metered probe is still bounded, and counted, by that cap.

use std::sync::atomic::{AtomicUsize, Ordering};

use super::node::Node;
use super::{current_guard, with_current_guard, ChildSpec, EnterScope, Guard, NodeLabel};
use crate::resource::WorkLedger;

/// A cap on the work a node's ledger counts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum WorkCap {
    /// A work ceiling: reached once this many work units are counted.
    Units(u64),
    /// A work grant: spent once more than this many round trips are counted
    /// (the round trip after the last granted one still starts, and finds it
    /// spent at its first poll).
    RoundTrips(u64),
}

/// Which kind of cap a poll asks about.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CapKind {
    /// [`WorkCap::Units`].
    Units,
    /// [`WorkCap::RoundTrips`].
    RoundTrips,
}

impl WorkCap {
    const fn kind(self) -> CapKind {
        match self {
            Self::Units(_) => CapKind::Units,
            Self::RoundTrips(_) => CapKind::RoundTrips,
        }
    }

    fn reached(self, ledger: &WorkLedger) -> bool {
        match self {
            Self::Units(allowance) => ledger.work_units() >= allowance,
            Self::RoundTrips(grant) => ledger.round_trips() > grant,
        }
    }
}

/// Caps of each kind open in the process, so a poll with none open reads
/// one atomic and nothing else.
static OPEN: [AtomicUsize; 2] = [AtomicUsize::new(0), AtomicUsize::new(0)];

const fn slot(kind: CapKind) -> usize {
    match kind {
        CapKind::Units => 0,
        CapKind::RoundTrips => 1,
    }
}

/// A node with `cap` was built.
pub(super) fn opened(cap: WorkCap) {
    OPEN[slot(cap.kind())].fetch_add(1, Ordering::Relaxed);
}

/// A node with `cap` closed.
pub(super) fn closed(cap: WorkCap) {
    OPEN[slot(cap.kind())].fetch_sub(1, Ordering::Relaxed);
}

impl Node {
    /// Whether this node's own cap is reached.
    pub(super) fn cap_reached(&self) -> bool {
        self.cap.is_some_and(|cap| cap.reached(&self.ledger))
    }

    /// Whether a cap of `kind` on this node or on any ancestor is reached.
    pub(super) fn chain_cap_reached(&self, kind: CapKind) -> bool {
        std::iter::once(self).chain(self.ancestors()).any(|node| {
            node.cap
                .is_some_and(|cap| cap.kind() == kind && cap.reached(&node.ledger))
        })
    }
}

impl Guard {
    /// Whether this node's own cap is reached (`false` without one).
    pub(crate) fn own_cap_reached(&self) -> bool {
        self.node.cap_reached()
    }
}

/// Whether a cap of `kind` on the calling thread's current node, or on any
/// of its ancestors, is reached. `false` on a thread in no node, and at the
/// cost of one atomic load while no cap of that kind is open in the process.
#[inline]
pub(crate) fn current_cap_reached(kind: CapKind) -> bool {
    if OPEN[slot(kind)].load(Ordering::Relaxed) == 0 {
        return false;
    }
    with_current_guard(|guard| guard.node.chain_cap_reached(kind)).unwrap_or(false)
}

/// Open a node labelled `label` with `cap` (`None`: no cap of its own) as a
/// `Full` child of the calling thread's current node, or of the root on a
/// thread in none, and enter it there.
pub(crate) fn enter_cap(label: NodeLabel, cap: Option<WorkCap>) -> EnterScope {
    let mut spec = ChildSpec::new(label);
    spec.cap = cap;
    let node = match current_guard() {
        Some(parent) => parent.child(spec),
        None => Guard::root_child(spec),
    };
    node.enter()
}
