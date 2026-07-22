// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model provenance API types.
//!
//! Provides [`ModelProvenance`] which exposes why each variable in a satisfying
//! model received its value.  The provenance is extracted from the solver's
//! internal state after a SAT result and describes the assignment source for
//! each declared variable.
//!
//! # Design
//!
//! When the solver returns SAT, each variable's value was determined by one of:
//!
//! - **Decision:** the SAT solver chose this value heuristically during search.
//! - **Propagation:** the value was forced by unit propagation (Boolean
//!   constraint propagation).
//! - *(Future: TheoryImplied — a theory solver determines the value. Not yet
//!   supported; will be added when theory solver integration is available.)*
//! - **Default:** the variable was unconstrained and received a default value.
//!
//! Part of #8153 (Phase 5 Explainability).

use super::Term;

/// Why a variable received its value in the satisfying model.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum AssignmentReason {
    /// The SAT solver chose this value during search.
    ///
    /// The decision level indicates the depth in the search tree at which the
    /// decision was made (level 0 is the root).
    Decision {
        /// Search tree depth at which the decision was made.
        level: u32,
    },

    /// The value was forced by Boolean constraint propagation.
    ///
    /// The `antecedent_terms` lists the other terms whose values implied this
    /// assignment.
    Propagation {
        /// Terms whose values forced this assignment (the "reason" clause).
        antecedent_terms: Vec<Term>,
    },

    /// The variable was not constrained and received a default value.
    Default,
}

impl std::fmt::Display for AssignmentReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Decision { level } => write!(f, "decision at level {level}"),
            Self::Propagation { antecedent_terms } => {
                write!(f, "propagation ({} antecedents)", antecedent_terms.len())
            }
            Self::Default => write!(f, "default (unconstrained)"),
        }
    }
}

/// Provenance record for a single variable in the model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariableProvenance {
    /// Variable name.
    pub name: String,
    /// The Term handle for this variable.
    pub term: Term,
    /// Why this variable received its value.
    pub reason: AssignmentReason,
}

/// Provenance information for all variables in a satisfying model.
///
/// After `check_sat()` returns `Sat`, call
/// [`Solver::model_provenance()`](crate::api::Solver::model_provenance)
/// to obtain a record of why each declared variable received its value.
///
/// # Example
///
/// ```no_run
/// # use ay_dpll::api::{Solver, Sort, Logic, SolveResult};
/// let mut solver = Solver::new(Logic::QfLia);
/// // ... declare variables and assert constraints ...
/// if solver.check_sat().is_sat() {
///     if let Some(provenance) = solver.model_provenance() {
///         for entry in provenance.entries() {
///             println!("{}: {:?}", entry.name, entry.reason);
///         }
///     }
/// }
/// ```
#[derive(Debug, Clone)]
pub struct ModelProvenance {
    /// Provenance entries, one per declared variable.
    entries: Vec<VariableProvenance>,
}

impl std::fmt::Display for VariableProvenance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}: {}", self.name, self.reason)
    }
}

impl std::fmt::Display for ModelProvenance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let decisions = self
            .entries
            .iter()
            .filter(|e| matches!(e.reason, AssignmentReason::Decision { .. }))
            .count();
        let propagations = self
            .entries
            .iter()
            .filter(|e| matches!(e.reason, AssignmentReason::Propagation { .. }))
            .count();
        let defaults = self
            .entries
            .iter()
            .filter(|e| matches!(e.reason, AssignmentReason::Default))
            .count();
        write!(
            f,
            "ModelProvenance({} vars: {} decisions, {} propagations, {} default)",
            self.entries.len(),
            decisions,
            propagations,
            defaults,
        )
    }
}

impl ModelProvenance {
    /// Create a new model provenance.
    pub(crate) fn new(entries: Vec<VariableProvenance>) -> Self {
        Self { entries }
    }

    /// The provenance entries.
    #[must_use]
    pub fn entries(&self) -> &[VariableProvenance] {
        &self.entries
    }

    /// Consume and return the provenance entries.
    #[must_use]
    pub fn into_entries(self) -> Vec<VariableProvenance> {
        self.entries
    }

    /// Number of entries.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether there are no entries.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Look up provenance for a variable by name.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&VariableProvenance> {
        self.entries.iter().find(|e| e.name == name)
    }

    /// All variables that were decided (not propagated or theory-implied).
    #[must_use]
    pub fn decisions(&self) -> Vec<&VariableProvenance> {
        self.entries
            .iter()
            .filter(|e| matches!(e.reason, AssignmentReason::Decision { .. }))
            .collect()
    }
}
