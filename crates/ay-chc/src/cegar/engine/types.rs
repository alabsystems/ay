// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Types and helper functions for the CEGAR engine.
//!
//! Extracted from `mod.rs` to keep the main engine implementation focused
//! on the CEGAR loop, expansion, and refinement logic.

use crate::cegar::abstract_state::AbstractState;
use crate::{ChcExpr, ChcVar, ClauseHead, HornClause, InvariantModel, PredicateId};
use ay_core::kani_compat::DetHashSet as FxHashSet;

/// Maximum number of times template-only refinement may reset the skip counter
/// before the solver stops treating template success as genuine progress.
/// After this count, further resets are allowed only when the predicate store
/// has grown since the last reset (genuine progress).
/// Prevents O(template_space × skip_budget × expansion_cost) stall cycles (#3085)
/// while allowing extended refinement when templates produce novel predicates (#3121).
pub(super) const MIN_TEMPLATE_RESETS: usize = 3;

/// Result of building tree symbolic constraints: (node_substs, node_constraints, links).
pub(super) type TreeSymbolicResult = (
    Vec<Vec<(ChcVar, ChcExpr)>>,
    Vec<ChcExpr>,
    Vec<TraceTreeLink>,
);

/// CEGAR configuration
#[derive(Clone, Debug)]
pub struct CegarConfig {
    /// Common engine settings (verbose, cancellation).
    pub(crate) base: crate::engine_config::ChcEngineConfig,

    /// Maximum CEGAR refinement iterations before giving up
    pub(crate) max_iterations: usize,

    /// Maximum abstract states per relation.
    /// Prevents unbounded memory growth on hard problems.
    pub(crate) max_states_per_relation: usize,

    /// Timeout per SMT query. Prevents individual check_sat calls from
    /// blocking the engine indefinitely on hard formulas.
    pub(crate) query_timeout: std::time::Duration,

    /// Cooperative blackboard for cross-engine predicate sharing (#7910).
    /// When set, newly discovered predicates are published to the blackboard
    /// so PDR engines can consume them as lemma hints.
    pub(crate) blackboard: Option<std::sync::Arc<crate::blackboard::SharedBlackboard>>,

    /// Engine index in the portfolio, used for blackboard publish tagging.
    pub(crate) engine_idx: usize,
}

impl Default for CegarConfig {
    fn default() -> Self {
        Self {
            base: crate::engine_config::ChcEngineConfig::default(),
            max_iterations: 100,
            max_states_per_relation: 10000,
            query_timeout: std::time::Duration::from_secs(5),
            blackboard: None,
            engine_idx: 0,
        }
    }
}

/// CEGAR result
#[derive(Clone, Debug)]
#[must_use = "CEGAR results must be checked — ignoring Safe/Unsafe loses correctness"]
pub(crate) enum CegarResult {
    /// Found inductive invariants (safe)
    Safe(InvariantModel),

    /// Found counterexample trace (unsafe)
    Unsafe(CegarCounterexample),

    /// Could not determine (resource exhausted)
    Unknown,
}

/// A counterexample trace from CEGAR
#[derive(Clone, Debug)]
pub(crate) struct CegarCounterexample {
    /// Sequence of (clause_index, state) pairs forming the trace
    pub(crate) trace: Vec<(usize, Option<AbstractState>)>,
}

#[derive(Clone, Debug)]
pub(super) struct TraceTreeNode {
    pub(super) edge_idx: usize,
    pub(super) parent: Option<usize>,
    pub(super) parent_body_pos: Option<usize>,
    pub(super) children: Vec<usize>,
}

#[derive(Clone, Debug)]
pub(super) struct TraceTreeLink {
    pub(super) child: usize,
    pub(super) parent: usize,
    pub(super) equalities: Vec<ChcExpr>,
}

/// A link between two steps in a trace, carrying renamed equality constraints.
/// Shared struct unifying `SeqLink` and `Link` from sequence/pointwise interpolation.
pub(super) struct TraceLink {
    pub(super) from_step: usize,
    pub(super) to_step: usize,
    pub(super) equalities: Vec<ChcExpr>,
}

/// Collect all variables in a clause and build a renaming substitution.
///
/// Each variable `v` becomes `{prefix}_{step}_{v.name}`, preventing
/// name collisions across steps in a trace encoding.
pub(super) fn rename_clause_vars(
    clause: &HornClause,
    prefix: &str,
    step: usize,
) -> Vec<(ChcVar, ChcExpr)> {
    let mut clause_vars = FxHashSet::default();
    if let Some(ref c) = clause.body.constraint {
        for v in c.vars() {
            clause_vars.insert(v);
        }
    }
    for (_, args) in &clause.body.predicates {
        for arg in args {
            for v in arg.vars() {
                clause_vars.insert(v);
            }
        }
    }
    if let ClauseHead::Predicate(_, ref args) = clause.head {
        for arg in args {
            for v in arg.vars() {
                clause_vars.insert(v);
            }
        }
    }
    clause_vars
        .iter()
        .map(|v| {
            let new_name = format!("{prefix}_{step}_{}", v.name);
            (
                v.clone(),
                ChcExpr::var(ChcVar::new(new_name, v.sort.clone())),
            )
        })
        .collect()
}

pub(super) enum ExpandResult {
    QueueEmpty,
    Counterexample(usize),
    Cancelled,
    IterationLimit,
}

pub(super) enum CexAnalysis {
    Genuine(Vec<(usize, Option<AbstractState>)>),
    Spurious(Vec<(PredicateId, ChcExpr)>),
    AnalysisFailed,
}
