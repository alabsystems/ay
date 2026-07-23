// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solve options.

use std::time::{Duration, Instant};

/// Options for a session's solves.
///
/// `#[non_exhaustive]` with builder methods so the engine can grow options
/// without breaking callers.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct SolveOpts {
    /// Hard wall-clock deadline. Checked inside solve loops; expiry yields
    /// `Outcome::Unknown { reason: Timeout }`, never a partial verdict.
    pub deadline: Option<Instant>,
    /// Per-solve time limit; combines with `deadline` (the earlier wins).
    pub time_limit: Option<Duration>,
    /// Per-node time limit for a warm LP attempt in branch-and-bound. When the
    /// limit expires, the node discards its warm-start hint and retries cold
    /// exactly once under the solve's outer deadline. `None` disables the
    /// warm-only limit; it never extends the outer deadline.
    pub node_warm_time_limit: Option<Duration>,
    /// Worker threads a session may use. Advice at L0 (single-threaded).
    pub threads: u32,
    /// When true (default), identical inputs give identical outcomes
    /// run-to-run.
    pub determinism: bool,
    /// Seed for randomized heuristics (unused while `determinism` holds all
    /// current lanes fixed; reserved for the native engine).
    pub seed: u64,
    /// When true, a verdict whose certificate cannot be produced degrades to
    /// `Outcome::Unknown { reason: CertificateUnavailable }` instead of being
    /// reported bare. Off by default: bare verdicts from the exact lanes are
    /// sound, just unevidenced.
    pub require_certificates: bool,
    /// Bytes the branch-and-bound may RETAIN in its open node set (the
    /// dominant memory at scale: parked warm-start bases). Crossing half the
    /// budget stops new parked nodes from carrying warm hints; crossing the
    /// budget stops the frontier growing at all (depth-first from there, which
    /// holds O(depth)). Running into the budget can cost time and can degrade
    /// an exhausted search to `Feasible`/`Unknown` — never a wrong verdict.
    /// `None` disables the guard.
    pub memory_budget: Option<usize>,
    /// Leaf budget for capturing a whole-tree
    /// [`crate::MilpInfeasibilityCertificate`] on `Infeasible` verdicts from
    /// the native branch-and-bound. The capture is fail-closed: a tree that
    /// needs more leaves, outlives the deadline, or cannot be re-derived in
    /// the caller's model frame yields `tree_cert: None` and the verdict is
    /// unaffected. `0` disables capture entirely.
    pub tree_cert_leaves: usize,
}

impl Default for SolveOpts {
    fn default() -> Self {
        Self {
            deadline: None,
            time_limit: None,
            node_warm_time_limit: None,
            threads: 1,
            determinism: true,
            seed: 0,
            require_certificates: false,
            memory_budget: Some(2 << 30), // 2 GiB
            tree_cert_leaves: 256,
        }
    }
}

impl SolveOpts {
    /// Default options.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Set a hard wall-clock deadline.
    #[must_use]
    pub fn with_deadline(mut self, deadline: Instant) -> Self {
        self.deadline = Some(deadline);
        self
    }

    /// Set a per-solve time limit.
    #[must_use]
    pub fn with_time_limit(mut self, limit: Duration) -> Self {
        self.time_limit = Some(limit);
        self
    }

    /// Set (or disable, with `None`) the per-node warm LP time limit.
    ///
    /// A zero duration is normalized to `None`, matching the historical
    /// zero-means-disabled configuration.
    #[must_use]
    pub fn with_node_warm_time_limit(mut self, limit: Option<Duration>) -> Self {
        self.node_warm_time_limit = limit.filter(|limit| !limit.is_zero());
        self
    }

    /// Set the thread budget.
    #[must_use]
    pub fn with_threads(mut self, threads: u32) -> Self {
        self.threads = threads;
        self
    }

    /// Set determinism.
    #[must_use]
    pub fn with_determinism(mut self, determinism: bool) -> Self {
        self.determinism = determinism;
        self
    }

    /// Set the heuristic seed.
    #[must_use]
    pub fn with_seed(mut self, seed: u64) -> Self {
        self.seed = seed;
        self
    }

    /// Require certificates on certificate-bearing verdicts.
    #[must_use]
    pub fn with_require_certificates(mut self, require: bool) -> Self {
        self.require_certificates = require;
        self
    }

    /// Set (or disable, with `None`) the open-set memory budget in bytes.
    #[must_use]
    pub fn with_memory_budget(mut self, bytes: Option<usize>) -> Self {
        self.memory_budget = bytes;
        self
    }

    /// Set the tree-certificate leaf budget (`0` disables capture).
    #[must_use]
    pub fn with_tree_cert_leaves(mut self, leaves: usize) -> Self {
        self.tree_cert_leaves = leaves;
        self
    }

    /// The effective deadline as of `now`: the earlier of `deadline` and
    /// `now + time_limit`.
    #[must_use]
    pub fn effective_deadline(&self, now: Instant) -> Option<Instant> {
        let from_limit = self.time_limit.map(|l| now + l);
        match (self.deadline, from_limit) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn node_warm_time_limit_defaults_off() {
        assert_eq!(SolveOpts::new().node_warm_time_limit, None);
    }

    #[test]
    fn node_warm_time_limit_builder_normalizes_zero_and_none() {
        let finite = Duration::from_millis(250);
        assert_eq!(
            SolveOpts::new()
                .with_node_warm_time_limit(Some(finite))
                .node_warm_time_limit,
            Some(finite)
        );
        assert_eq!(
            SolveOpts::new()
                .with_node_warm_time_limit(Some(Duration::ZERO))
                .node_warm_time_limit,
            None
        );
        assert_eq!(
            SolveOpts::new()
                .with_node_warm_time_limit(None)
                .node_warm_time_limit,
            None
        );
    }
}
