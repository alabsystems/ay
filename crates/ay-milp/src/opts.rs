// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solve options.

use std::time::{Duration, Instant};

/// Default-off warm-start strategy for complete fixed assignment trees.
///
/// These modes change only how float advice is obtained before exact leaf
/// certification. Root and prefix statuses never contribute evidence. Ordinary
/// leaves exactify `Optimal` duals or `PrimalInfeasible` Farkas multipliers as
/// before. The first configured non-optimal leaf may instead exactify the
/// prefix candidate's cached true-objective duals under the fully fixed leaf;
/// only a strictly sufficient, independently verified row contributes to the
/// returned proof. Local durations are cooperative caps: zero requests an
/// immediate stop poll, finite values are intersected with the outer proof
/// deadline, and `Duration::MAX` removes only the local cap without extending
/// an outer deadline.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum FixedAssignmentTreeWarmStart {
    /// Solve progressively narrower prefixes before the first complete
    /// assignment, changing one split bound per warm solve. The Gray walk is
    /// translated by `start_assignment`, so it starts there while retaining
    /// one-bit transitions and complete coverage. Each prefix is capped by
    /// `prefix_time_limit` and continues primal phase I directly from the
    /// preceding basis; a locally stopped basis remains float advice only.
    /// The first complete proof leaf first attempts to exactify its cached
    /// true-objective row duals, then may continue that stopped primal state.
    /// Either route must pass independent exact leaf verification.
    ProgressivePrefix {
        prefix_time_limit: Duration,
        start_assignment: u8,
    },
    /// Bound the optional root-fast-path search, then bridge progressively to
    /// `start_assignment`.
    ///
    /// If the root reaches `Optimal` within `root_time_limit`, the historical
    /// exact root-row fast path is still attempted. If it stops at the local
    /// limit, its basis is advice only and complete exact leaf harvesting
    /// continues under the session's outer deadline. Each progressive prefix
    /// has its own `prefix_time_limit`.
    RootProbeThenProgressivePrefix {
        root_time_limit: Duration,
        prefix_time_limit: Duration,
        start_assignment: u8,
    },
}

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
    /// Admit the range-logical triangular-crash LP path for this solve.
    ///
    /// This is an advice-only, default-off path choice. The historical exact
    /// `AY_MILP_RANGE_LOGICAL_CRASH=1` process-environment opt-in remains an
    /// independent compatibility fallback.
    pub(crate) range_logical_triangular_crash: bool,
    /// Per-session override for the cold affine-chain distress-probe iteration
    /// budget. `None` preserves the historical
    /// `AY_MILP_CHAIN_PROBE`/20,000-iteration policy; `Some(0)` disables the
    /// probe for LPs lowered by this session.
    pub(crate) chain_distress_probe_iters: Option<u64>,
    /// Default-off float-basis strategy for the complete fixed assignment-tree
    /// proof API. This is advice only and is deliberately not consulted by the
    /// target-FSB or adaptive tree APIs.
    pub(crate) fixed_assignment_tree_warm_start: Option<FixedAssignmentTreeWarmStart>,
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
            range_logical_triangular_crash: false,
            chain_distress_probe_iters: None,
            fixed_assignment_tree_warm_start: None,
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

    /// Request the range-logical triangular-crash LP path for this solve.
    ///
    /// The option is scoped to sessions built from these options and does not
    /// mutate process environment or change the global default.
    #[must_use]
    pub fn with_range_logical_triangular_crash(mut self) -> Self {
        self.range_logical_triangular_crash = true;
        self
    }

    /// Whether this option explicitly requests the range-logical
    /// triangular-crash LP path.
    ///
    /// This reports only the typed per-session setting. The solver separately
    /// honors the historical exact `AY_MILP_RANGE_LOGICAL_CRASH=1`
    /// environment opt-in for compatibility.
    #[must_use]
    pub fn range_logical_triangular_crash(&self) -> bool {
        self.range_logical_triangular_crash
    }

    /// Override the cold affine-chain distress-probe iteration budget for LPs
    /// lowered by this session.
    ///
    /// `None` preserves the historical process policy
    /// (`AY_MILP_CHAIN_PROBE`, defaulting to 20,000 iterations). `Some(0)`
    /// disables the probe without mutating process-global environment.
    #[must_use]
    pub fn with_chain_distress_probe_iters(mut self, iters: Option<u64>) -> Self {
        self.chain_distress_probe_iters = iters;
        self
    }

    /// The typed per-session chain distress-probe override.
    ///
    /// This excludes the historical environment/default fallback, which the
    /// simplex resolves only when no typed override is present.
    #[must_use]
    pub fn chain_distress_probe_iters(&self) -> Option<u64> {
        self.chain_distress_probe_iters
    }

    /// Select a default-off warm-start strategy for complete fixed assignment
    /// trees.
    ///
    /// This option is proof-neutral: root probes and prefix solves supply float
    /// bases only, including when their local cap yields `Stopped`. Final
    /// leaves retain the same exactification and independent
    /// certificate-verification requirements as the default path.
    #[must_use]
    pub fn with_fixed_assignment_tree_warm_start(
        mut self,
        strategy: Option<FixedAssignmentTreeWarmStart>,
    ) -> Self {
        self.fixed_assignment_tree_warm_start = strategy;
        self
    }

    /// The typed per-session fixed assignment-tree warm-start strategy.
    #[must_use]
    pub fn fixed_assignment_tree_warm_start(&self) -> Option<FixedAssignmentTreeWarmStart> {
        self.fixed_assignment_tree_warm_start
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

    #[test]
    fn range_logical_triangular_crash_defaults_off_and_is_scoped() {
        let default = SolveOpts::new();
        let explicit = default.clone().with_range_logical_triangular_crash();

        assert!(!default.range_logical_triangular_crash());
        assert!(explicit.range_logical_triangular_crash());
        assert!(
            !default.range_logical_triangular_crash(),
            "building an opted-in sibling must not change the original options"
        );
    }

    #[test]
    fn chain_distress_probe_iters_defaults_to_historical_policy() {
        assert_eq!(SolveOpts::new().chain_distress_probe_iters(), None);
    }

    #[test]
    fn chain_distress_probe_iters_builder_is_typed_and_scoped() {
        let default = SolveOpts::new();
        let finite = default
            .clone()
            .with_chain_distress_probe_iters(Some(12_345));
        let disabled = default.clone().with_chain_distress_probe_iters(Some(0));

        assert_eq!(finite.chain_distress_probe_iters(), Some(12_345));
        assert_eq!(disabled.chain_distress_probe_iters(), Some(0));
        assert_eq!(
            finite
                .with_chain_distress_probe_iters(None)
                .chain_distress_probe_iters(),
            None
        );
        assert_eq!(
            default.chain_distress_probe_iters(),
            None,
            "building configured siblings must not mutate the original options"
        );
    }

    #[test]
    fn fixed_assignment_tree_warm_start_defaults_off_and_is_scoped() {
        let default = SolveOpts::new();
        let bridge = default.clone().with_fixed_assignment_tree_warm_start(Some(
            FixedAssignmentTreeWarmStart::ProgressivePrefix {
                prefix_time_limit: Duration::from_millis(100),
                start_assignment: 1,
            },
        ));
        let probe = default.clone().with_fixed_assignment_tree_warm_start(Some(
            FixedAssignmentTreeWarmStart::RootProbeThenProgressivePrefix {
                root_time_limit: Duration::from_millis(250),
                prefix_time_limit: Duration::from_millis(100),
                start_assignment: 9,
            },
        ));

        assert_eq!(default.fixed_assignment_tree_warm_start(), None);
        assert_eq!(
            bridge.fixed_assignment_tree_warm_start(),
            Some(FixedAssignmentTreeWarmStart::ProgressivePrefix {
                prefix_time_limit: Duration::from_millis(100),
                start_assignment: 1,
            })
        );
        assert_eq!(
            probe.fixed_assignment_tree_warm_start(),
            Some(
                FixedAssignmentTreeWarmStart::RootProbeThenProgressivePrefix {
                    root_time_limit: Duration::from_millis(250),
                    prefix_time_limit: Duration::from_millis(100),
                    start_assignment: 9,
                }
            )
        );
        assert_eq!(
            probe
                .with_fixed_assignment_tree_warm_start(None)
                .fixed_assignment_tree_warm_start(),
            None
        );
        assert_eq!(
            default.fixed_assignment_tree_warm_start(),
            None,
            "building configured siblings must not mutate the original options"
        );
    }
}
