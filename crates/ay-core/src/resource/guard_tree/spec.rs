// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! What a node is built with: [`ChildSpec`] and its parts.

use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::Duration;

use super::{DeadlineSource, Inherit, NodeLabel, WorkCap};

/// A node's memory share: the limits of its own `MemoryGroup` (GT8).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemoryShare {
    /// Live bytes past which the share trips and raises the node's flag.
    pub soft_bytes: usize,
    /// Live bytes past which code without a checkpoint unwinds.
    pub hard_bytes: usize,
}

/// Where a node's memory stop comes from, as built.
#[derive(Clone, Copy, Debug)]
pub(super) enum MemorySpec {
    /// None of its own (§6).
    Inherited,
    /// Its own share (GT8).
    Share(MemoryShare),
    /// The share of the portfolio lane the polling thread runs in
    /// ([`ChildSpec::with_lane_share`]).
    Lane,
}

/// What a node is built with ([`Guard::root_child`], [`Guard::child`]).
#[derive(Clone, Debug)]
pub struct ChildSpec {
    pub(super) label: NodeLabel,
    pub(super) inherit: Inherit,
    pub(super) external: Option<Arc<AtomicBool>>,
    pub(super) deadline: DeadlineSource,
    pub(super) rlimit: Option<u64>,
    pub(super) cpu: Option<Duration>,
    pub(super) memory: MemorySpec,
    pub(super) cap: Option<WorkCap>,
}

impl ChildSpec {
    /// A `Full` node with nothing of its own.
    #[must_use]
    pub fn new(label: NodeLabel) -> Self {
        Self {
            label,
            inherit: Inherit::Full,
            external: None,
            deadline: DeadlineSource::None,
            rlimit: None,
            cpu: None,
            memory: MemorySpec::Inherited,
            cap: None,
        }
    }

    /// See only the ancestors' cancel flags (GT1; Certify, DR-39).
    #[must_use]
    pub fn cancel_only(mut self) -> Self {
        self.inherit = Inherit::CancelOnly;
        self
    }

    /// Also stop once `flag` is raised (an executor interrupt).
    #[must_use]
    pub fn with_external(mut self, flag: Arc<AtomicBool>) -> Self {
        self.external = Some(flag);
        self
    }

    /// Its own deadline.
    #[must_use]
    pub fn with_deadline(mut self, deadline: DeadlineSource) -> Self {
        self.deadline = deadline;
        self
    }

    /// The allotment it asks for. `None`: a `Full` child takes its parent's
    /// whole remainder; a `CancelOnly` child under a node that counts gets
    /// 0 (DR-39 has no `CancelOnly` node without a count, and sizes Certify
    /// by its creator); a node under one that counts nothing has no count.
    #[must_use]
    pub fn with_rlimit(mut self, rlimit: Option<u64>) -> Self {
        self.rlimit = rlimit;
        self
    }

    /// A CPU slice for the thread that enters it.
    #[must_use]
    pub fn with_cpu(mut self, slice: Duration) -> Self {
        self.cpu = Some(slice);
        self
    }

    /// A memory share of its own.
    #[must_use]
    pub fn with_memory(mut self, share: MemoryShare) -> Self {
        self.memory = MemorySpec::Share(share);
        self
    }

    /// Stop, as `Memory`, once the memory share of the portfolio lane the
    /// POLLING thread runs in has tripped (`ay_sys::current_memory_group_soft_tripped`),
    /// instead of a share of its own. A lane's `MemoryGroup` is not a node
    /// until step S5, and its trip raises the lane's own token, not this
    /// node's flag; the executor's Check and Certify nodes read it the way
    /// its stop closures do (design §3: "memory = the lane's group if one is
    /// current").
    #[must_use]
    pub fn with_lane_share(mut self) -> Self {
        self.memory = MemorySpec::Lane;
        self
    }
}
