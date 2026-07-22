// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Base solver: equivalence class initialization and constant conflict detection.
//!
//! This is the first step in the string theory check pipeline.
//! It scans equivalence classes for:
//! 1. Conflicting constants (two distinct string constants in the same EQC).
//! 2. Indexing concat terms for downstream normal form computation.
//!
//! Reference: `reference/cvc5/src/theory/strings/base_solver.h`
//! Reference: `reference/cvc5/src/theory/strings/base_solver.cpp:54` (checkInit)

use crate::infer::{InferenceKind, InferenceManager};
use crate::state::SolverState;
// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::{Constant, TermData, TermId, TermStore};
use ay_core::TheoryLit;

/// Base solver: handles EQC initialization and constant conflict detection.
#[derive(Debug, Default)]
pub(crate) struct BaseSolver;

impl BaseSolver {
    /// Create a new base solver.
    pub(crate) fn new() -> Self {
        Self
    }

    /// Check for constant conflicts in equivalence classes.
    ///
    /// If `merge()` detected conflicting constants (two distinct string
    /// constants in the same EQC), the pending conflict is converted to
    /// a theory conflict here.
    ///
    /// Returns `true` if a conflict was found.
    pub(crate) fn check_init(
        &self,
        terms: &TermStore,
        state: &SolverState,
        infer: &mut InferenceManager,
    ) -> bool {
        if let Some((a, b)) = state.pending_conflict() {
            let mut explanation = state.explain_or_all(a, b);
            let mut seen: HashSet<TheoryLit> = explanation.iter().copied().collect();

            // Strengthen pending-conflict explanations with the merge paths from
            // each conflicting endpoint to its concrete constant term.
            // This prevents under-explained unit conflicts such as
            // (x = "a"), (y = "b"), (x = y) -> [¬(x = y)].
            //
            // After the merge, find(a) == find(b) == winner, so we must
            // use the original a,b endpoints. We explain paths from each
            // endpoint to every string constant in the merged EQC.
            let winner = state.find(a);
            if let Some(eqc) = state.eqc_members(winner) {
                let const_terms: Vec<TermId> = eqc
                    .iter()
                    .copied()
                    .filter(|&m| matches!(terms.get(m), TermData::Const(Constant::String(_))))
                    .collect();
                for endpoint in <[TermId; 2]>::from((a, b)) {
                    for &ct in &const_terms {
                        for lit in state.explain(endpoint, ct) {
                            if seen.insert(lit) {
                                explanation.push(lit);
                            }
                        }
                    }
                }
            }

            // Soundness guard (#3826): skip conflict if explanation is empty.
            // An empty explanation would produce a vacuous blocking clause.
            if !explanation.is_empty() {
                infer.add_conflict(InferenceKind::ConstantConflict, explanation);
                return true;
            }
        }
        infer.has_conflict()
    }

    /// Check for conflicting constants between two equivalence classes
    /// that are about to be merged.
    ///
    /// Returns `true` if merging would create a conflict.
    #[cfg(test)]
    pub(crate) fn check_constant_merge(
        &self,
        state: &SolverState,
        rep1: &TermId,
        rep2: &TermId,
        infer: &mut InferenceManager,
    ) -> bool {
        let c1 = state.get_constant(rep1);
        let c2 = state.get_constant(rep2);
        if let (Some(s1), Some(s2)) = (c1, c2) {
            if s1 != s2 {
                infer.add_conflict(
                    InferenceKind::ConstantConflict,
                    vec![TheoryLit::new(*rep1, true)],
                );
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
#[path = "base_tests.rs"]
mod tests;
