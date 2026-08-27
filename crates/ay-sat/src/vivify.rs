// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Vivification - clause strengthening via unit propagation
//!
//! Vivification is an inprocessing technique that strengthens clauses by testing
//! if literals can be removed. For each clause C = (l1 ∨ l2 ∨ ... ∨ ln):
//!
//! 1. For each literal l_i in order:
//!    - Temporarily assume ¬l_i
//!    - Propagate unit clauses
//!    - If conflict or another literal in C becomes unit, the clause can be shortened
//!
//! The actual vivification loop lives in `solver/inprocessing.rs` where it has
//! direct access to solver state. This module provides supporting types.
//!
//! Reference:
//! - Piette, Hamadi, Saïs: "Vivification" (SAT 2008)
//! - CaDiCaL implementation (src/vivify.cpp)

/// Clause tier ordering used by vivification.
///
/// The three learned tiers are split by LBD, while `Irredundant` covers
/// original clauses. This mirrors CaDiCaL's dedicated irredundant pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum VivifyTier {
    /// Learned clauses with LBD <= 2 (glue/core)
    LearnedCore,
    /// Learned clauses with 2 < LBD <= 6
    LearnedTier2,
    /// Learned clauses with LBD > 6
    LearnedOther,
    /// Original (non-learned) clauses
    Irredundant,
}

/// Statistics for vivification
#[derive(Debug, Default, Clone)]
#[non_exhaustive]
pub struct VivifyStats {
    /// Number of clauses examined
    pub clauses_examined: u64,
    /// Number of clauses strengthened
    pub clauses_strengthened: u64,
    /// Number of clauses deleted because a conflict clause directly subsumed them
    pub inline_subsumed: u64,
    /// Number of clauses deleted because a reason clause during backward
    /// analysis subsumed them (CaDiCaL vivify_analyze subsumption path)
    pub analysis_subsumed: u64,
    /// Total literals removed
    pub literals_removed: u64,
    /// Number of clauses found to be satisfied
    pub clauses_satisfied: u64,
    /// Decisions reused from previous candidate's trail (prefix sharing)
    pub decisions_reused: u64,

    // ── Irredundant-tier split (asymmetric-tautology convergence work) ──
    //
    // The aggregate counters above sum every tier, so a run in which the
    // IRREDUNDANT tier does nothing at all is indistinguishable from one in
    // which it does all the work. The campaign's repeated lesson is that a
    // detector's yield is invisible until it is counted, so the irredundant
    // tier gets its own split.
    /// Clauses examined by the `Irredundant` tier only.
    pub irred_examined: u64,
    /// Clauses strengthened by the `Irredundant` tier only.
    pub irred_strengthened: u64,
    /// Literals removed by the `Irredundant` tier only.
    pub irred_literals_removed: u64,
    /// Clauses deleted (satisfied or subsumed) by the `Irredundant` tier only.
    pub irred_deleted: u64,
    /// `vivify_tier(Irredundant, ..)` invocations from `vivify_preprocess`.
    pub irred_calls_preprocess: u64,
    /// `vivify_tier(Irredundant, ..)` invocations from the inprocessing
    /// `vivify_body`. Zero means irredundant vivification never ran during
    /// search (for example because `VivifySkipReason::SmallDenseSkip` gated
    /// every attempt).
    pub irred_calls_inproc: u64,

    // ── Preprocessing convergence-loop termination ──
    /// Rounds executed by the `vivify_preprocess` convergence loop.
    pub preprocess_rounds: u64,
    /// Loop stopped because a round strengthened nothing — a true fixed point.
    pub preprocess_stop_converged: u64,
    /// Loop stopped because the total tick budget was exhausted.
    pub preprocess_stop_budget: u64,
    /// Loop stopped because the round cap was reached.
    pub preprocess_stop_rounds: u64,
    /// Loop stopped because the wall-clock deadline tripped.
    pub preprocess_stop_deadline: u64,
    /// Total vivification ticks consumed by the preprocessing loop.
    pub preprocess_ticks: u64,

    // ── Inprocessing admission (why a scheduled vivify did not run) ──
    /// Inprocessing rounds that admitted vivification.
    pub inproc_admitted: u64,
    /// Inprocessing rounds that skipped vivification: pass disabled.
    pub inproc_skip_disabled: u64,
    /// Inprocessing rounds that skipped vivification: interval not due.
    pub inproc_skip_interval: u64,
    /// Inprocessing rounds that skipped vivification: tick threshold delay.
    pub inproc_skip_threshold: u64,
    /// Inprocessing rounds that skipped vivification because of the
    /// small-dense guard (`num_vars < 1000` and density > 30). On the
    /// asymmetric-tautology families this is the dominant reason.
    pub inproc_skip_small_dense: u64,
}

/// Vivification engine — holds statistics across vivification rounds.
///
/// The vivification loop itself is implemented inline in
/// `solver/inprocessing.rs::vivify_tier()` where it has direct access
/// to solver state (assignment, watches, clause DB).
pub(crate) struct Vivifier {
    /// Vivification statistics
    pub(crate) stats: VivifyStats,
}

impl Vivifier {
    /// Create a new vivifier.
    pub(crate) fn new() -> Self {
        Self {
            stats: VivifyStats::default(),
        }
    }

    /// Get vivification statistics.
    pub(crate) fn stats(&self) -> &VivifyStats {
        &self.stats
    }
}
