// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The reserved enode fields (multi-engine design §3.3) and the enode mode
//! (KC24): read access for the plug-ins that will consume them (E-matching
//! reads the label sets and the parent lists per (symbol, argument)), and
//! the relevancy bit the kernel's service sets (KC21). The fields are
//! maintained by `merge.rs` and undone with every other hub change.
//!
//! - `generation` (u32): the instantiation depth that created the node; 0
//!   for every input term (no instance creates nodes yet);
//! - the relevancy bit (KC21): set by the kernel's relevancy service;
//! - the MAM label sets: per class, an approximate set (a 64-bit Bloom word
//!   over function ids) of the functions of its members (`lbls`) and of its
//!   parents (`plbls`), merged by union;
//! - parent lists per (symbol, argument): each class's parent entry carries
//!   the argument position, and [`Hub::parents_at`] reads the parents of
//!   one function symbol at one position.

use super::{EnodeMode, Hub, NodeId, Undo};

/// The approximate-set bit of a function id (z3's `approx_set`, one word).
pub(super) const fn label_bit(func: u32) -> u64 {
    if func == 0 {
        0
    } else {
        1u64 << (func % 64)
    }
}

impl Hub {
    /// The congruence function id of a node (0 outside the table).
    pub(crate) fn func_of(&self, n: NodeId) -> u32 {
        self.node(n).func
    }

    /// The check's enode mode (KC24).
    pub(crate) const fn mode(&self) -> EnodeMode {
        self.mode
    }

    /// The node's instantiation generation (reserved, §3.3).
    pub(crate) fn generation(&self, n: NodeId) -> u32 {
        self.node(n).generation
    }

    /// Whether the relevancy service marked the node (KC21).
    pub(crate) fn is_relevant(&self, n: NodeId) -> bool {
        self.node(n).relevant
    }

    /// Mark a node relevant until the current scope pops (KC21).
    pub(crate) fn set_relevant(&mut self, n: NodeId) {
        if self.node(n).relevant {
            return;
        }
        self.node_mut(n).relevant = true;
        self.record(Undo::Relevant(n));
    }

    /// The approximate label sets of a node's class: its members' function
    /// ids and its parents' (the MAM's fast filters, §3.3).
    pub(crate) fn labels(&self, n: NodeId) -> (u64, u64) {
        let r = self.node(self.root(n));
        (r.lbls, r.plbls)
    }

    /// The parents of a node's class that apply function `func` with a
    /// member of the class at argument position `arg`: the parent list per
    /// (symbol, argument) of §3.3, read off the class's one parent list.
    pub(crate) fn parents_at(
        &self,
        n: NodeId,
        func: u32,
        arg: u32,
    ) -> impl Iterator<Item = NodeId> + '_ {
        let r = self.node(self.root(n));
        let filter = label_bit(func);
        let any = r.plbls & filter != 0;
        r.parents
            .iter()
            .filter(move |p| any && p.arg == arg)
            .map(|p| p.node)
            .filter(move |&p| self.node(p).func == func && self.node(p).attached)
    }
}
