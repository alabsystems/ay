// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! What a nested search run reports: outcome, final main query, counters,
//! the observable trace, and the caps it ran under.

use ay_core::TermId;

use super::approx::NInstance;
use super::caps::{MAX_INSTANCES_PER_NODE, MAX_QLRA_ROUNDS, MAX_TOTAL_INSTANCES};
use super::QlraOutcome;

/// One observable step of the search (tests assert exact traces).
#[cfg(test)]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum TraceStep {
    /// The main query `⌊roots⌋Γ` and its answer.
    Main { sat: bool },
    /// A counterexample query: node, whether in the main context, answer.
    Check {
        node: usize,
        context: bool,
        sat: bool,
    },
    /// A logged instance.
    Instance { node: usize, tuple: Vec<TermId> },
    /// A node became exact (standalone).
    Exact { node: usize },
}

/// Search counters for `--stats`.
#[derive(Clone, Debug, Default)]
pub(crate) struct NestedStats {
    pub(crate) rounds: usize,
    pub(crate) oracle_calls: usize,
    pub(crate) instances: usize,
    pub(crate) exact_nodes: usize,
    /// Largest oracle query, in DAG nodes.
    pub(crate) approx_max: usize,
    /// Wall spent inside the oracle, milliseconds.
    pub(crate) oracle_ms: u64,
    /// The slowest oracle calls: (node or `usize::MAX` for the main query,
    /// milliseconds, query DAG size), at most [`SLOW_CALLS`].
    pub(crate) slow_calls: Vec<(usize, u64, usize)>,
}

/// Slow oracle calls kept for diagnostics.
pub(super) const SLOW_CALLS: usize = 8;

/// Everything a nested run produced.
#[derive(Clone, Debug)]
pub(crate) struct NestedRun {
    pub(crate) outcome: QlraOutcome,
    /// The last main query; on `Sat` every model of it satisfies the roots
    /// (no top node's instances changed during the round that built it).
    pub(crate) main: Vec<TermId>,
    pub(crate) stats: NestedStats,
    #[cfg(test)]
    pub(crate) trace: Vec<TraceStep>,
    /// The final instance log Γ, per node, indexed like the tree's nodes:
    /// the UNSAT expansion certificate is built from it and the SAT route
    /// turns it into untrusted expansion hints (hints only, both ways).
    pub(crate) gamma: Vec<Vec<NInstance>>,
    /// The final exact flags, indexed like the tree's nodes (the session
    /// cache keeps them, `session.rs`).
    pub(crate) exact: Vec<bool>,
}

/// The search's resource caps (plan §7). Every cap DECLINES.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct NestedCaps {
    pub(crate) rounds: usize,
    pub(crate) instances_per_node: usize,
    pub(crate) instances: usize,
}

impl Default for NestedCaps {
    fn default() -> Self {
        Self {
            rounds: MAX_QLRA_ROUNDS,
            instances_per_node: MAX_INSTANCES_PER_NODE,
            instances: MAX_TOTAL_INSTANCES,
        }
    }
}
