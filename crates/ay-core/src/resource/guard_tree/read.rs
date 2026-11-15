// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Reads of a node that latch nothing, and what an owner keeps of one
//! (GuardTree step S2).
//!
//! [`Guard::exhausted`] and [`Guard::tick`] latch the first reason they see
//! (GT7): they are where a stop is acted on and published. A Check node's
//! deadline is the executor's live cell, which the executor tightens,
//! restores and extends in the middle of a call (the S1 note's known risk,
//! guard-tree.md §11): a node that latched `Deadline` on a tightened wall
//! would stay stopped after the restore. [`Guard::poll`] is the read for a
//! loop that only ends its own work with "no answer" (the theory loops that
//! poll `check_stop_requested`), so it latches nothing and reads a moved
//! deadline again at the next poll, as the closures before S2 did.

use std::sync::{Arc, Weak};

use super::node::Node;
use super::{Guard, Inherit, NodeLabel};
use crate::resource::Exhausted;

impl Guard {
    /// Why the node would stop now, latching nothing: a reason already
    /// latched, else every condition [`Self::exhausted`] reads, in its
    /// order, read now.
    #[must_use]
    pub fn poll(&self) -> Option<Exhausted> {
        let node = &*self.node;
        node.stopped
            .get()
            .copied()
            .or_else(|| node.cancellation())
            .or_else(|| node.over_allotment().then_some(Exhausted::Rlimit))
            .or_else(|| node.limits())
    }

    /// GT1's cancel chain alone, latching nothing: the node's flags (its
    /// own and its external flag), every ancestor's and the root's, and the
    /// lane share of the polling thread if it or an ancestor reads one. No
    /// clock and no count: the read of a `CancelOnly` node whose owner reads
    /// its envelope through a poll of its own (Certify, DR-39 and DR-34).
    #[must_use]
    pub fn cancelled(&self) -> Option<Exhausted> {
        let node = &*self.node;
        node.cancellation()
            .or_else(|| node.lane_tripped().then_some(Exhausted::Memory))
    }

    /// This node, or its nearest ancestor, labelled `label` (`None` up to
    /// the root, which no handle holds).
    #[must_use]
    pub fn nearest(&self, label: NodeLabel) -> Option<Self> {
        let mut node = &self.node;
        loop {
            if node.label == label {
                return Some(Self {
                    node: Arc::clone(node),
                });
            }
            node = node.parent.as_ref()?;
        }
    }

    /// Whether this node is `node` or a descendant of it.
    #[must_use]
    pub fn is_within(&self, node: &Self) -> bool {
        let mut at = &self.node;
        loop {
            if Arc::ptr_eq(at, &node.node) {
                return true;
            }
            let Some(parent) = at.parent.as_ref() else {
                return false;
            };
            at = parent;
        }
    }

    /// Whether ticking this handle also spends `other`'s allowance: either
    /// both use the same counter, or `other` is an actual ancestor reached
    /// solely through `Full` edges. Full-child spend settles on close; callers
    /// must still poll BOTH handles to enforce live flags and tighter views.
    ///
    /// This allocation-free query walks at most this handle's ancestor chain.
    /// A sibling view of an ancestor is deliberately not an ancestor: its
    /// tighter live cap does not count an open child's eventual settlement.
    /// `CancelOnly` breaks settlement, even though ledger statistics propagate.
    #[must_use]
    pub fn charges_against(&self, other: &Self) -> bool {
        if std::ptr::eq(self.node.counter(), other.node.counter()) {
            return true;
        }
        let mut at = &self.node;
        loop {
            if at.inherit != Inherit::Full {
                return false;
            }
            let Some(parent) = at.parent.as_ref() else {
                return false;
            };
            if Arc::ptr_eq(parent, &other.node) {
                return true;
            }
            at = parent;
        }
    }

    /// A handle that does not keep the node open (GT2: a node closes when
    /// its last handle drops).
    #[must_use]
    pub fn downgrade(&self) -> WeakGuard {
        WeakGuard {
            node: Arc::downgrade(&self.node),
        }
    }
}

#[cfg(test)]
mod tests;

/// A handle on a node that does not keep it open ([`Guard::downgrade`]).
#[derive(Clone, Debug, Default)]
pub struct WeakGuard {
    node: Weak<Node>,
}

impl WeakGuard {
    /// The node, while it is open.
    #[must_use]
    pub fn upgrade(&self) -> Option<Guard> {
        self.node.upgrade().map(|node| Guard { node })
    }
}
