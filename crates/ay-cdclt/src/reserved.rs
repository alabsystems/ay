// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Types of the reserved, defaulted plug-in slots (interface freeze v2,
//! multi-engine design §3.3 and §3.6).
//!
//! The slots exist so that the features that will fill them (theory-driven
//! decisions, cores, splitting, clause sharing, asynchronous work, garbage
//! collection) do not change the trait again. The kernel calls none of them
//! yet, except where the development design notes "Freeze v2" says so; every
//! default answers "nothing to offer".

use ay_core::{AtomHandle, TheoryLit};

use crate::engine::Guard;
use crate::plugin::Lemma;

/// A plug-in's conjunctive core: asserted literals whose conjunction the
/// theory alone refutes, or which alone entail what it reports (the
/// `conjunctive_core` slot).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConjCore {
    /// The literals, each true on the trail when the core was taken.
    pub lits: Vec<TheoryLit>,
}

/// The atoms still live in the search, by handle (the `gc` slot): a plug-in
/// may drop state for every atom not in the set.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AtomSet {
    live: Vec<bool>,
}

impl AtomSet {
    /// Mark `handle` live.
    pub fn insert(&mut self, handle: AtomHandle) {
        let idx = handle.index();
        if self.live.len() <= idx {
            self.live.resize(idx + 1, false);
        }
        if let Some(slot) = self.live.get_mut(idx) {
            *slot = true;
        }
    }

    /// Whether `handle` is live.
    #[must_use]
    pub fn contains(&self, handle: AtomHandle) -> bool {
        self.live.get(handle.index()).copied().unwrap_or(false)
    }
}

/// Whether a lemma may leave its worker (the `share_policy` slot; design
/// §5's exchange port).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Share {
    /// The kernel's policy decides.
    Default,
    /// Never exported: the lemma depends on this worker's state.
    Local,
    /// Worth exporting whenever an exchange port is attached.
    Export,
}

/// Work a plug-in hands off the search thread (the `async_job` slot, KC14):
/// it runs under the check's guard and returns lemmas, which must be T-valid
/// (K4) because they arrive at an arbitrary later point of the search.
pub trait AsyncJob: Send {
    /// Run the job to completion or until `guard` says stop.
    fn run(self: Box<Self>, guard: &Guard) -> Vec<Lemma>;
}
