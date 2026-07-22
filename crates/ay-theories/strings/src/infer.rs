// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inference manager for the string theory solver.
//!
//! Collects conflicts, propagations, and lemma requests from sub-solvers
//! and converts them into `TheoryResult` / `TheoryPropagation` for the
//! DPLL(T) framework.
//!
//! Reference: `reference/cvc5/src/theory/strings/inference_manager.h`

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermId;
use ay_core::{TheoryLit, TheoryPropagation, TheoryResult};

/// The kind of inference produced by a string sub-solver.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum InferenceKind {
    /// Conflict: two constants in the same equivalence class differ.
    ConstantConflict,
    /// Conflict: evaluated extf predicate contradicts asserted polarity
    /// using ground-only (EQC constant) resolution.
    PredicateConflict,
    /// Conflict: evaluated extf predicate contradicts asserted polarity
    /// using NF-derived resolution. NOT classified as ground (#6309).
    PredicateConflictNfDerived,
    /// Conflict: same-EQC disequality violation — terms asserted disequal
    /// are in the same equivalence class. Unconditionally sound (#3875).
    DisequalityViolation,
    /// Normal form endpoint-empty inference.
    EndpointEmpty,
    /// Normal form unification by equal length.
    Unify,
    /// Normal form endpoint equality.
    EndpointEq,
    /// Cycle-derived empty inference: x = str.++(y,x) → y = "".
    /// The I_CYCLE rule from CVC5. Sound by construction (#3875).
    CycleEmpty,
    /// Normal form constant split/conflict.
    ConstantSplit,
}

/// A pending inference collected by the inference manager.
#[derive(Debug, Clone)]
pub(crate) struct PendingInference {
    /// Whether this is a conflict (vs. a propagation or lemma).
    pub is_conflict: bool,
    /// Explanation: the asserted literals that justify this inference.
    pub explanation: Vec<TheoryLit>,
}

/// A pending internal equality fact from the core solver.
///
/// These facts are asserted back into [`crate::state::SolverState`] during the
/// same string-theory check round (CVC5-style doPending loop), before results
/// are surfaced to the DPLL(T) layer.
#[derive(Debug, Clone)]
pub(crate) struct PendingEquality {
    /// Left-hand side of an inferred string equality.
    pub lhs: TermId,
    /// Right-hand side of an inferred string equality.
    pub rhs: TermId,
    /// Explanation literals justifying the inferred equality.
    pub explanation: Vec<TheoryLit>,
}

/// Inference manager: collects inferences from sub-solvers.
///
/// After a `check()` round, the DPLL(T) layer queries the inference manager
/// to convert collected inferences into `TheoryResult` and `TheoryPropagation`.
#[derive(Debug, Default)]
pub(crate) struct InferenceManager {
    /// Pending inferences from the current check round.
    pending: Vec<PendingInference>,
    /// Pending propagations (non-conflict inferences with conclusions).
    propagations: Vec<TheoryPropagation>,
    /// Pending internal equalities to assert into string solver state.
    internal_equalities: Vec<PendingEquality>,
    /// Whether a conflict has been found in this round.
    has_conflict: bool,
    /// Whether the conflict came from a ground evaluation (constant conflicts,
    /// extf predicate/reduction evaluation) vs NF-dependent reasoning.
    /// Ground conflicts are trustworthy; NF-dependent conflicts may be spurious
    /// due to incomplete normal form computation (#6275).
    ground_conflict: bool,
    /// Whether cycle detection (I_CYCLE) produced internal equalities in this
    /// or a prior round. When true, subsequent NF-based conflicts are
    /// trustworthy because they follow from sound cycle-derived inferences
    /// (e.g., x = str.++(y,x) → y = ""). Not cleared between rounds —
    /// cleared only on full `clear()`. (#3875)
    cycle_inferences_fired: bool,
}

impl InferenceManager {
    /// Create a new, empty inference manager.
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Record a conflict inference.
    ///
    /// `explanation` contains the asserted TheoryLits whose conjunction
    /// is inconsistent. The DPLL(T) layer will negate these to form a
    /// blocking clause.
    pub(crate) fn add_conflict(&mut self, kind: InferenceKind, explanation: Vec<TheoryLit>) {
        self.has_conflict = true;
        // Ground conflicts come from constant evaluation and extf predicate
        // checks — these are always trustworthy. NF-dependent conflicts
        // (ConstantSplit, EndpointEmpty) may be spurious (#6275).
        self.ground_conflict = matches!(
            kind,
            InferenceKind::ConstantConflict
                | InferenceKind::PredicateConflict
                | InferenceKind::DisequalityViolation
        );
        self.pending.push(PendingInference {
            is_conflict: true,
            explanation,
        });
    }

    /// Record a propagation inference (a new fact derived from existing equalities).
    #[cfg(test)]
    pub(crate) fn add_propagation(
        &mut self,
        _kind: InferenceKind,
        conclusion: TheoryLit,
        explanation: Vec<TheoryLit>,
    ) {
        self.propagations.push(TheoryPropagation {
            literal: conclusion,
            reason: explanation,
            reason_data: None,
        });
    }

    /// Record an internal equality fact to be asserted in string state.
    pub(crate) fn add_internal_equality(
        &mut self,
        kind: InferenceKind,
        lhs: TermId,
        rhs: TermId,
        explanation: Vec<TheoryLit>,
    ) {
        // Track cycle-derived equalities (#3875): CycleEmpty from cycle
        // detection (I_CYCLE) means subsequent NF conflicts are sound.
        if matches!(kind, InferenceKind::CycleEmpty) {
            self.cycle_inferences_fired = true;
        }
        self.internal_equalities.push(PendingEquality {
            lhs,
            rhs,
            explanation,
        });
    }

    /// Drain internal equalities for solver-internal fact assertion.
    pub(crate) fn drain_internal_equalities(&mut self) -> Vec<PendingEquality> {
        std::mem::take(&mut self.internal_equalities)
    }

    /// Whether there are internal equality facts pending.
    pub(crate) fn has_internal_equalities(&self) -> bool {
        !self.internal_equalities.is_empty()
    }

    /// Number of internal equality facts currently pending.
    ///
    /// Used by the core check pipeline to detect whether a specific pass
    /// queued new equalities (delta of this count across the pass).
    pub(crate) fn internal_equality_count(&self) -> usize {
        self.internal_equalities.len()
    }

    /// Whether any conflict was found in this round.
    pub(crate) fn has_conflict(&self) -> bool {
        self.has_conflict
    }

    /// Whether the current conflict came from ground evaluation (constant
    /// conflicts, extf predicate/reduction checks). Ground conflicts are
    /// trustworthy; NF-dependent conflicts may be spurious (#6275).
    pub(crate) fn is_ground_conflict(&self) -> bool {
        self.ground_conflict
    }

    /// Whether cycle detection (I_CYCLE) fired internal equalities in this
    /// check sequence. Conflicts after cycle-derived equalities are
    /// trustworthy because the cycle inference is sound (#3875).
    pub(crate) fn has_cycle_inferences(&self) -> bool {
        self.cycle_inferences_fired
    }

    /// Whether there are any pending inferences.
    #[allow(clippy::panic)]
    #[cfg(test)]
    pub(crate) fn has_pending(&self) -> bool {
        !self.pending.is_empty()
            || !self.propagations.is_empty()
            || !self.internal_equalities.is_empty()
    }

    /// Convert the first conflict into a `TheoryResult::Unsat`.
    ///
    /// The explanation literals are returned directly as the conflict clause.
    /// If the explanation is empty, the conflict is dropped (returns Sat).
    /// An unexplainable conflict is not a proof of UNSAT — the theory will
    /// either explain it on a subsequent check after more N-O propagation,
    /// or the CEGAR loop will add split lemmas that make it explainable.
    /// The previous fallback to all assertions caused false UNSAT (#3826).
    pub(crate) fn to_theory_result(&self) -> TheoryResult {
        if let Some(conflict) = self.pending.iter().find(|p| p.is_conflict) {
            // Deduplicate explanation literals. Multiple inference steps may
            // contribute overlapping assertions when using broad explanations.
            let mut seen = HashSet::default();
            let deduped: Vec<TheoryLit> = conflict
                .explanation
                .iter()
                .filter(|lit| seen.insert((lit.term, lit.value)))
                .copied()
                .collect();
            // Drop unexplainable conflicts: an empty explanation would produce
            // a vacuously-true blocking clause, causing false UNSAT. Sound to
            // drop — the theory will re-derive this conflict with a proper
            // explanation after more EQC merges or split lemmas (#3826, #4025).
            if deduped.is_empty() {
                return TheoryResult::Sat;
            }
            TheoryResult::Unsat(deduped)
        } else {
            TheoryResult::Sat
        }
    }

    /// Drain collected propagations for the DPLL layer.
    pub(crate) fn drain_propagations(&mut self) -> Vec<TheoryPropagation> {
        std::mem::take(&mut self.propagations)
    }

    /// Clear all pending inferences for the next round.
    pub(crate) fn clear(&mut self) {
        self.pending.clear();
        self.propagations.clear();
        self.internal_equalities.clear();
        self.has_conflict = false;
        self.ground_conflict = false;
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "infer_tests.rs"]
mod tests;
