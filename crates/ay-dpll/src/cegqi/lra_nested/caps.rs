// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resource caps of the nested CEGQI lane (plan §7).
//!
//! Every cap DECLINES: the lane hands the query back to the legacy path with
//! nothing published. A cap can never shorten a `Sat` into a partial answer.

/// Refinement rounds per check-sat.
pub(crate) const MAX_QLRA_ROUNDS: usize = 4096;
/// Logged instances per node.
pub(crate) const MAX_INSTANCES_PER_NODE: usize = 512;
/// Logged instances across all nodes.
pub(crate) const MAX_TOTAL_INSTANCES: usize = 8192;
/// Quantifier nodes in one problem.
pub(crate) const MAX_NODES: usize = 256;
/// Implicant/evaluation work units per selection call.
pub(crate) const MAX_SELECT_WORK: usize = 1 << 20;
/// Instances the M1 publication route (authored consequence replay) accepts.
/// The replay itself caps its plan at 64 instances; logging more than that
/// can only produce a refutation the route cannot carry, so the lane declines
/// as soon as the log outgrows it.
pub(crate) const M1_PUBLISHABLE_INSTANCES: usize = 64;
/// Alternation depth of the nested tree (merged blocks).
pub(crate) const MAX_DEPTH: usize = 32;
/// Approximation-builder work units (memo misses) between two changes of Γ.
pub(crate) const MAX_APPROX_NODES: usize = 1 << 20;
