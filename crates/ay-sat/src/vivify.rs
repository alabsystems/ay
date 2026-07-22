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
