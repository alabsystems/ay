// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Interpolation diagnostics: per-POB failure classification and aggregate telemetry.
// The `InterpolationFailure` enum and `InterpolationDiagnostics` are used per-POB.
// `InterpolationStats` aggregates success/failure counts across the full solve.
//! Structured diagnostics for interpolation pipeline failures.
//!
//! When PDR's interpolation-based lemma learning fails, this module provides
//! detailed information about *why* each method failed, enabling better
//! debugging and analysis.

/// Diagnostic information about why an interpolation method failed.
///
/// Variants cover the active interpolation cascade failures per #799.
/// Add new variants as cascade methods are implemented.
#[derive(Debug, Clone)]
pub(super) enum InterpolationFailure {
    /// No shared variables between A and B (interpolant cannot bind anything).
    SharedVarsEmpty { a_vars: usize, b_vars: usize },

    /// Method not applicable to this query structure.
    NotApplicable { reason: String },
}

impl std::fmt::Display for InterpolationFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SharedVarsEmpty { a_vars, b_vars } => {
                write!(f, "shared_vars empty (A: {a_vars} vars, B: {b_vars} vars)")
            }
            Self::NotApplicable { reason } => {
                write!(f, "not applicable: {reason}")
            }
        }
    }
}

/// Aggregated diagnostics from all interpolation methods for a single POB.
#[derive(Debug, Default)]
pub(super) struct InterpolationDiagnostics {
    /// Failure from Golem-style syntactic A/B interpolation.
    pub(super) golem_sat: Option<InterpolationFailure>,
    /// Failure from N1 per-clause interpolation.
    pub(super) n1_per_clause: Option<InterpolationFailure>,
    /// Failure from proof-based Farkas certificates.
    pub(super) lia_farkas: Option<InterpolationFailure>,
    /// Failure from syntactic Farkas-based interpolation.
    pub(super) syntactic_farkas: Option<InterpolationFailure>,
    /// Failure from IUC shrink B + retry Farkas.
    pub(super) iuc_farkas: Option<InterpolationFailure>,
}

impl InterpolationDiagnostics {
    /// Create empty diagnostics.
    pub(super) fn new() -> Self {
        Self::default()
    }

    /// Returns a compact single-line summary for logging.
    pub(super) fn summary(&self) -> String {
        let mut parts = Vec::new();

        if let Some(ref f) = self.golem_sat {
            parts.push(format!("golem:{f}"));
        }
        if let Some(ref f) = self.n1_per_clause {
            parts.push(format!("n1:{f}"));
        }
        if let Some(ref f) = self.lia_farkas {
            parts.push(format!("lia:{f}"));
        }
        if let Some(ref f) = self.syntactic_farkas {
            parts.push(format!("syn:{f}"));
        }
        if let Some(ref f) = self.iuc_farkas {
            parts.push(format!("iuc:{f}"));
        }

        if parts.is_empty() {
            "no failures recorded".to_string()
        } else {
            parts.join(" | ")
        }
    }

    /// Returns a detailed multi-line summary for verbose output.
    pub(super) fn detailed_summary(&self) -> String {
        let mut lines = Vec::new();

        if let Some(ref f) = self.golem_sat {
            lines.push(format!("  - golem_sat: {f}"));
        }
        if let Some(ref f) = self.n1_per_clause {
            lines.push(format!("  - n1_per_clause: {f}"));
        }
        if let Some(ref f) = self.lia_farkas {
            lines.push(format!("  - lia_farkas: {f}"));
        }
        if let Some(ref f) = self.syntactic_farkas {
            lines.push(format!("  - syntactic_farkas: {f}"));
        }
        if let Some(ref f) = self.iuc_farkas {
            lines.push(format!("  - iuc_farkas: {f}"));
        }

        if let Some(dominant) = self.dominant_failure() {
            lines.push(format!("  - dominant: {dominant}"));
        }

        lines.join("\n")
    }

    /// Returns the most actionable failure reason.
    ///
    /// Priority: SharedVarsEmpty (fundamental A/B partition issue) > others.
    pub(super) fn dominant_failure(&self) -> Option<&InterpolationFailure> {
        let failures: Vec<&InterpolationFailure> = [
            self.golem_sat.as_ref(),
            self.n1_per_clause.as_ref(),
            self.lia_farkas.as_ref(),
            self.syntactic_farkas.as_ref(),
            self.iuc_farkas.as_ref(),
        ]
        .into_iter()
        .flatten()
        .collect();

        if failures.is_empty() {
            return None;
        }

        // SharedVarsEmpty takes priority — it's a fundamental A/B partition issue
        for f in &failures {
            if matches!(f, InterpolationFailure::SharedVarsEmpty { .. }) {
                return Some(f);
            }
        }

        // Return first failure if no priority match
        failures.into_iter().next()
    }

    /// Returns true if all methods failed.
    pub(super) fn all_failed(&self) -> bool {
        self.golem_sat.is_some()
            && self.n1_per_clause.is_some()
            && self.lia_farkas.is_some()
            && self.syntactic_farkas.is_some()
            && self.iuc_farkas.is_some()
    }

    /// Returns count of failures recorded.
    pub(super) fn failure_count(&self) -> usize {
        [
            self.golem_sat.is_some(),
            self.n1_per_clause.is_some(),
            self.lia_farkas.is_some(),
            self.syntactic_farkas.is_some(),
            self.iuc_farkas.is_some(),
        ]
        .into_iter()
        .filter(|&b| b)
        .count()
    }
}

/// Aggregate interpolation telemetry across the entire solve.
///
/// Tracks how many times each method in the 5-method cascade succeeded or was
/// attempted, providing the signal needed to diagnose interpolation quality gaps.
/// Part of #2450 (USER M1 milestone: interpolation-path telemetry).
#[derive(Debug, Default, Clone)]
pub(super) struct InterpolationStats {
    /// Total POBs where interpolation was attempted (transition_constraints non-empty).
    pub(super) attempts: usize,
    /// Conjunctive interpolation skips where conjunction(A) was UNSAT.
    pub(super) golem_a_unsat_skips: usize,
    /// Successes per cascade method (first method to succeed wins).
    pub(super) golem_sat_successes: usize,
    pub(super) n1_per_clause_successes: usize,
    pub(super) lia_farkas_successes: usize,
    pub(super) syntactic_farkas_successes: usize,
    pub(super) iuc_farkas_successes: usize,
    /// Total POBs where ALL 5 methods failed (fell back to heuristic generalization).
    pub(super) all_failed: usize,
}

impl InterpolationStats {
    pub(super) fn total_successes(&self) -> usize {
        self.golem_sat_successes
            + self.n1_per_clause_successes
            + self.lia_farkas_successes
            + self.syntactic_farkas_successes
            + self.iuc_farkas_successes
    }

    /// Assert accounting invariants for interpolation telemetry.
    ///
    /// `golem_a_unsat_skips` is not disjoint from successes/failures:
    /// when conjunctive A-side is UNSAT we skip only method 1, then continue
    /// to method 2..5 for the same attempt.
    #[inline]
    pub(super) fn debug_assert_consistency(&self) {
        let terminal_outcomes = self.total_successes().saturating_add(self.all_failed);
        debug_assert!(
            terminal_outcomes <= self.attempts,
            "BUG: interpolation accounting mismatch: successes({}) + all_failed({}) = {} > attempts({})",
            self.total_successes(),
            self.all_failed,
            terminal_outcomes,
            self.attempts,
        );
        debug_assert!(
            self.golem_a_unsat_skips <= self.attempts,
            "BUG: interpolation accounting mismatch: golem_a_unsat_skips({}) > attempts({})",
            self.golem_a_unsat_skips,
            self.attempts,
        );
    }

    /// Returns a compact summary string for verbose output.
    pub(super) fn summary(&self) -> String {
        if self.attempts == 0 {
            return "no interpolation attempts".to_string();
        }
        let success_rate = (self.total_successes() as f64 / self.attempts as f64) * 100.0;
        format!(
            "attempts={}, success={:.0}% (golem={}, n1={}, lia_farkas={}, syn_farkas={}, iuc={}), golem_a_unsat_skips={}, all_failed={}",
            self.attempts,
            success_rate,
            self.golem_sat_successes,
            self.n1_per_clause_successes,
            self.lia_farkas_successes,
            self.syntactic_farkas_successes,
            self.iuc_farkas_successes,
            self.golem_a_unsat_skips,
            self.all_failed,
        )
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "interpolation_failure_tests.rs"]
mod tests;
