// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! What a plug-in may read of the hub through [`Ctx`] (design H1, §3.3):
//! classes, the enode mode (KC24) and the reserved enode fields.

use ay_core::TermId;

use super::Ctx;
use crate::hub::Hub;

impl Ctx<'_> {
    /// The check's hub enode mode (KC24); `None` outside a check.
    pub fn enode_mode(&self) -> Option<crate::engine::EnodeMode> {
        self.hub.map(Hub::mode)
    }

    /// A hub node's instantiation generation (reserved enode field, §3.3).
    pub fn generation(&self, term: TermId) -> Option<u32> {
        let hub = self.hub?;
        hub.node_of(term).map(|n| hub.generation(n))
    }

    /// Whether a hub node carries the relevancy bit (KC21; the bit follows
    /// the relevancy service when the engine runs it).
    pub fn node_relevant(&self, term: TermId) -> Option<bool> {
        let hub = self.hub?;
        hub.node_of(term).map(|n| hub.is_relevant(n))
    }

    /// The approximate label sets of a term's hub class: its members'
    /// function symbols and its parents' (the MAM filters, §3.3).
    pub fn class_labels(&self, term: TermId) -> Option<(u64, u64)> {
        let hub = self.hub?;
        hub.node_of(term).map(|n| hub.labels(n))
    }

    /// The applications of `app`'s function symbol that hold a member of
    /// `term`'s hub class at argument position `arg`: the parent list per
    /// (symbol, argument) of §3.3. Empty when either is not a hub node.
    pub fn parents_at(&self, term: TermId, app: TermId, arg: u32) -> Vec<TermId> {
        let Some(hub) = self.hub else {
            return Vec::new();
        };
        let (Some(n), Some(f)) = (hub.node_of(term), hub.node_of(app)) else {
            return Vec::new();
        };
        hub.parents_at(n, hub.func_of(f), arg)
            .map(|p| hub.term(p))
            .collect()
    }

    /// The hub class of a term (its representative node), if the term is a
    /// hub node (design H1). Two terms are equal in the current assignment's
    /// congruence closure iff their classes are the same.
    pub fn class_of(&self, term: TermId) -> Option<u32> {
        let hub = self.hub?;
        hub.node_of(term).map(|n| hub.root(n))
    }
}
