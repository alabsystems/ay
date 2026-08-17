// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Abductive reasoning for automatic vulnerability patch synthesis.
//!
//! Given a vulnerability condition (SAT result showing an exploit) and a set of
//! candidate patch points (guards that could be inserted), find the weakest
//! combination of guards that eliminates the vulnerability.
//!
//! ## Algorithm
//!
//! The approach is based on incremental assumption-based checking:
//!
//! 1. For each patch point, check whether `assertions AND patch_point => NOT(vuln_condition)`
//!    by checking SAT of `assertions AND patch_point AND vuln_condition`.
//! 2. If UNSAT, the patch point eliminates the vulnerability on its own.
//! 3. Among all valid single patches, pick the weakest (fewest assumptions).
//! 4. If no single patch suffices, try minimal combinations.
//!
//! Uses incremental push/pop for efficiency: the base assertions are shared
//! across all patch-point trials.
//!
//! ## References
//!
//! - Dillig, Dillig, and Aiken, "Automated error diagnosis using abductive
//!   inference", PLDI 2012.
//! - Albarghouthi et al., "Beautiful interpolants", CAV 2013.

use crate::api::types::{SolverError, Term};
use crate::api::Solver;

/// Classification of how aggressive a patch is.
///
/// Minimal patches change the least behavior; aggressive patches add
/// stronger guards that may reject more inputs than strictly necessary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum PatchStrength {
    /// The patch is the weakest sufficient guard (fewest assumptions).
    Minimal,
    /// The patch uses a moderate number of guards.
    Moderate,
    /// The patch uses the strongest available guard (most restrictive).
    Aggressive,
}

impl std::fmt::Display for PatchStrength {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Minimal => write!(f, "minimal"),
            Self::Moderate => write!(f, "moderate"),
            Self::Aggressive => write!(f, "aggressive"),
        }
    }
}

/// A suggested patch that eliminates a vulnerability.
///
/// Contains the guard expression to insert, the patch point index, and a
/// classification of the patch strength.
#[derive(Debug, Clone)]
pub struct PatchSuggestion {
    /// The guard condition to add at the patch point.
    /// When this condition holds, the vulnerability is unreachable.
    pub guard: Term,
    /// Index into the `patch_points` slice identifying where to insert the guard.
    pub location: usize,
    /// Classification of how restrictive the patch is.
    pub strength: PatchStrength,
}

impl Solver {
    /// Perform abductive reasoning to find the weakest formula over the given
    /// vocabulary that, combined with existing assertions, implies the goal.
    ///
    /// Given a goal formula (e.g., "vulnerability is unreachable") and a set of
    /// vocabulary terms (candidate conditions), find a subset of vocabulary terms
    /// whose conjunction, together with the current assertions, implies the goal.
    ///
    /// Returns `Some(guard)` where `guard` is a conjunction of vocabulary terms
    /// such that `assertions AND guard => goal`. Returns `None` if no such guard
    /// exists within the vocabulary, or if the goal is already implied.
    ///
    /// # Algorithm
    ///
    /// 1. Check if `assertions AND NOT(goal)` is already UNSAT (goal already implied).
    /// 2. For each vocabulary term, check if it alone suffices as a guard.
    /// 3. Return the first sufficient single-term guard found.
    /// 4. If no single term suffices, try pairwise combinations.
    ///
    /// Uses incremental push/pop for efficiency.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if the goal is not Bool.
    #[must_use = "this returns a Result that must be checked"]
    pub fn abduce(&mut self, goal: Term, vocabulary: &[Term]) -> Result<Option<Term>, SolverError> {
        self.expect_bool("abduce", goal)?;
        for v in vocabulary {
            self.expect_bool("abduce", *v)?;
        }
        self.clear_last_solve_state(true, false);
        self.reject_composite_bv_cnf_export("abduce")?;

        // Step 1: Check if goal is already implied by current assertions.
        // If assertions AND NOT(goal) is UNSAT, the goal is already implied.
        let not_goal = self.try_not(goal)?;
        self.try_push()?;
        self.try_assert_term(not_goal)?;

        let baseline = self.check_sat_internal_api();
        if baseline.is_unsat() {
            // Goal is already implied — no guard needed.
            self.try_pop()?;
            return Ok(None);
        }
        self.try_pop()?;

        // Step 2: Try each vocabulary term individually.
        // For each vocab term v, check if: assertions AND v AND NOT(goal) is UNSAT.
        // If so, v is a sufficient guard (assertions AND v => goal).
        let mut sufficient_singles: Vec<(usize, Term)> = Vec::new();

        for (i, &vocab_term) in vocabulary.iter().enumerate() {
            self.try_push()?;
            self.try_assert_term(not_goal)?;
            self.try_assert_term(vocab_term)?;

            let result = self.check_sat_internal_api();
            self.try_pop()?;

            if result.is_unsat() {
                sufficient_singles.push((i, vocab_term));
            }
        }

        // If we found sufficient single-term guards, return the first one
        // (weakest = single term).
        if let Some((_idx, guard)) = sufficient_singles.first() {
            return Ok(Some(*guard));
        }

        // Step 3: Try pairwise combinations.
        // For each pair (v_i, v_j), check if: assertions AND v_i AND v_j AND NOT(goal) is UNSAT.
        if vocabulary.len() >= 2 {
            for i in 0..vocabulary.len() {
                for j in (i + 1)..vocabulary.len() {
                    self.try_push()?;
                    self.try_assert_term(not_goal)?;
                    self.try_assert_term(vocabulary[i])?;
                    self.try_assert_term(vocabulary[j])?;

                    let result = self.check_sat_internal_api();
                    self.try_pop()?;

                    if result.is_unsat() {
                        // Found a pair that works. Build the conjunction.
                        let guard = self.try_and(vocabulary[i], vocabulary[j])?;
                        return Ok(Some(guard));
                    }
                }
            }
        }

        // No guard found in the vocabulary.
        Ok(None)
    }

    /// Synthesize a patch to eliminate a vulnerability.
    ///
    /// Given a vulnerability condition (a Boolean expression that is true when
    /// the vulnerability is exploitable) and a set of candidate patch points
    /// (guard conditions that could be inserted), find the weakest patch that
    /// makes the vulnerability unreachable.
    ///
    /// The algorithm checks each patch point to see if asserting it would make
    /// `NOT(vuln_condition)` implied by the assertions. Among valid patches,
    /// it picks the weakest (single-point patches preferred over combinations).
    ///
    /// # Arguments
    ///
    /// * `vuln_condition` - Boolean expression that is true when the vulnerability
    ///   is exploitable. The patch goal is `NOT(vuln_condition)`.
    /// * `patch_points` - Candidate guard conditions. Each is a Boolean expression
    ///   representing a check that could be inserted (e.g., `bounds_check(ptr)`).
    ///
    /// # Returns
    ///
    /// `Ok(Some(PatchSuggestion))` if a valid patch is found.
    /// `Ok(None)` if no patch point or combination eliminates the vulnerability.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if any term is not Bool.
    #[must_use = "this returns a Result that must be checked"]
    pub fn synthesize_patch(
        &mut self,
        vuln_condition: Term,
        patch_points: &[Term],
    ) -> Result<Option<PatchSuggestion>, SolverError> {
        self.expect_bool("synthesize_patch", vuln_condition)?;
        for pp in patch_points {
            self.expect_bool("synthesize_patch", *pp)?;
        }
        self.clear_last_solve_state(true, false);
        self.reject_composite_bv_cnf_export("synthesize_patch")?;

        if patch_points.is_empty() {
            return Ok(None);
        }

        // Check if vulnerability is already unreachable.
        self.try_push()?;
        self.try_assert_term(vuln_condition)?;
        let baseline = self.check_sat_internal_api();
        self.try_pop()?;

        if baseline.is_unsat() {
            // Vulnerability is already unreachable — no patch needed.
            return Ok(None);
        }

        // Phase 1: Try each patch point individually.
        // Check: assertions AND patch_point AND vuln_condition is UNSAT?
        // Equivalently: assertions AND patch_point => NOT(vuln_condition)?
        let mut valid_singles: Vec<usize> = Vec::new();

        for (i, &patch) in patch_points.iter().enumerate() {
            self.try_push()?;
            self.try_assert_term(patch)?;
            self.try_assert_term(vuln_condition)?;

            let result = self.check_sat_internal_api();
            self.try_pop()?;

            if result.is_unsat() {
                valid_singles.push(i);
            }
        }

        // Return the first valid single patch (minimal strength).
        if let Some(&idx) = valid_singles.first() {
            return Ok(Some(PatchSuggestion {
                guard: patch_points[idx],
                location: idx,
                strength: PatchStrength::Minimal,
            }));
        }

        // Phase 2: Try pairwise combinations.
        if patch_points.len() >= 2 {
            for i in 0..patch_points.len() {
                for j in (i + 1)..patch_points.len() {
                    self.try_push()?;
                    self.try_assert_term(patch_points[i])?;
                    self.try_assert_term(patch_points[j])?;
                    self.try_assert_term(vuln_condition)?;

                    let result = self.check_sat_internal_api();
                    self.try_pop()?;

                    if result.is_unsat() {
                        let combined = self.try_and(patch_points[i], patch_points[j])?;
                        return Ok(Some(PatchSuggestion {
                            guard: combined,
                            location: i, // primary patch location
                            strength: PatchStrength::Moderate,
                        }));
                    }
                }
            }
        }

        // Phase 3: Try the conjunction of all patch points (aggressive).
        if patch_points.len() >= 2 {
            self.try_push()?;
            for &patch in patch_points {
                self.try_assert_term(patch)?;
            }
            self.try_assert_term(vuln_condition)?;

            let result = self.check_sat_internal_api();
            self.try_pop()?;

            if result.is_unsat() {
                // Build conjunction of all patch points.
                let mut guard = patch_points[0];
                for &pp in &patch_points[1..] {
                    guard = self.try_and(guard, pp)?;
                }
                return Ok(Some(PatchSuggestion {
                    guard,
                    location: 0,
                    strength: PatchStrength::Aggressive,
                }));
            }
        }

        // No valid patch found.
        Ok(None)
    }
}
