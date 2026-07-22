// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural invariant synthesis for patterned CHC problems.
//!
//! This module recognizes common patterns in CHC problems and synthesizes
//! candidate invariants directly, bypassing expensive PDR search. For
//! simple problems (bounded loops, constant stride), this provides 10-100x
//! speedup.
//!
//! # Patterns Recognized
//!
//! - **Bounded increment**: `x' = x + K` with `x < N` guard -> `x <= N - 1 + K`
//! - **Bounded decrement**: `x' = x - K` with `x > L` guard -> `x >= L + 1 - K`
//! - **Interval bounds**: Combined init and guard analysis -> `L <= x <= U`
//!
//! # Submodules
//!
//! - `types`: Type definitions (SynthesisResult, SynthesisPattern, etc.)
//! - `detection`: Pattern detection from transition clauses
//! - `building`: Candidate construction and inductive verification
//!
//! # Reference
//!
//! Part of #1869 - Structural invariant synthesis for patterned problems.
//! See also: Spacer's `expand_bnd_generalizer.cpp` for post-hoc bound expansion.

mod building;
mod detection;
mod types;

pub(crate) use types::{SynthesisPattern, SynthesisResult, SynthesizedInvariant};

use crate::classifier::{ProblemClass, ProblemClassifier};
use crate::ChcProblem;
use std::time::Duration;

/// Structural invariant synthesizer.
pub(crate) struct StructuralSynthesizer<'a> {
    problem: &'a ChcProblem,
}

impl<'a> StructuralSynthesizer<'a> {
    /// Create a new structural synthesizer for the given problem.
    pub(crate) fn new(problem: &'a ChcProblem) -> Self {
        Self { problem }
    }

    /// Attempt structural synthesis.
    ///
    /// Returns `Success` with a verified invariant, `NotInductive` if pattern
    /// was recognized but candidate failed verification, or `NoPattern` if
    /// no recognizable pattern was found.
    pub(crate) fn try_synthesize(&self) -> SynthesisResult {
        // Only attempt synthesis for simple problems
        let features = ProblemClassifier::classify(self.problem);
        if !matches!(
            features.class,
            ProblemClass::Trivial | ProblemClass::SimpleLoop | ProblemClass::MultiPredLinear
        ) {
            return SynthesisResult::NoPattern;
        }

        if let Some(candidate) = self.build_mod1000_split_triangle_candidate() {
            let synthesized = SynthesizedInvariant {
                interpretations: candidate,
                pattern: SynthesisPattern::QuerySafetyCondition,
            };
            if self.structurally_validates_query_safety_candidate(&synthesized) {
                return SynthesisResult::Success(synthesized);
            }
        }

        // Try to detect loop patterns
        let patterns = self.detect_patterns();
        if patterns.is_empty() {
            if let Some(candidate) = self.build_verified_threshold_ite_candidate() {
                return SynthesisResult::Success(SynthesizedInvariant {
                    interpretations: candidate,
                    pattern: SynthesisPattern::ThresholdIteEquality,
                });
            }
            return SynthesisResult::NoPattern;
        }

        // Build candidate invariant from patterns
        let candidate = self.build_candidate(&patterns);
        if candidate.is_empty() {
            return SynthesisResult::NoPattern;
        }

        // Verify the candidate is inductive
        if self.verify_inductive_with_timeout(&candidate, Duration::from_millis(250)) {
            // Determine primary pattern for reporting
            let primary_pattern = patterns
                .first()
                .map_or(SynthesisPattern::IntervalBounds, |p| p.pattern);

            SynthesisResult::Success(SynthesizedInvariant {
                interpretations: candidate,
                pattern: primary_pattern,
            })
        } else if let Some(candidate) = self.build_verified_threshold_ite_candidate() {
            SynthesisResult::Success(SynthesizedInvariant {
                interpretations: candidate,
                pattern: SynthesisPattern::ThresholdIteEquality,
            })
        } else {
            SynthesisResult::NotInductive
        }
    }

    /// Build a threshold-ITE candidate without the module-local SMT proof.
    ///
    /// The adaptive portfolio uses this as a fail-closed fallback: the candidate
    /// is still routed through the external Safe-model validator before it can
    /// be promoted.
    pub(crate) fn try_threshold_ite_candidate(&self) -> Option<SynthesizedInvariant> {
        self.build_threshold_ite_candidate()
            .map(|interpretations| SynthesizedInvariant {
                interpretations,
                pattern: SynthesisPattern::ThresholdIteEquality,
            })
    }

    /// Cheap guard for the CHC-COMP split-triangle modulo family.
    ///
    /// The adaptive dispatcher uses this to run structural synthesis before the
    /// heavier LIA/Farkas pre-pass on matching multi-predicate encodings.
    pub(crate) fn has_fast_mod1000_split_triangle_chc_shape(&self) -> bool {
        self.has_mod1000_split_triangle_chc_shape()
    }

    /// Build query-derived candidates for the adaptive fail-closed validator.
    ///
    /// These candidates may be too strong or non-inductive. The adaptive layer
    /// must route them through full model validation before accepting Safe.
    pub(crate) fn try_query_safety_candidates(&self) -> Vec<SynthesizedInvariant> {
        let mut candidates = Vec::new();

        for interpretations in self.build_chc_comp_safe_summary_candidates() {
            candidates.push(SynthesizedInvariant {
                interpretations,
                pattern: SynthesisPattern::QuerySafetyCondition,
            });
        }

        if let Some(interpretations) = self.build_query_safety_candidate() {
            candidates.push(SynthesizedInvariant {
                interpretations,
                pattern: SynthesisPattern::QuerySafetyCondition,
            });
        }

        candidates
    }
}

#[cfg(test)]
mod tests;
