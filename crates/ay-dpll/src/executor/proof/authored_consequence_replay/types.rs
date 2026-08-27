// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Provenance plans and authored-conjunct inventory for consequence replay.

use ay_core::TermId;

/// How one non-authored consequence formula is derived from the authored
/// scope. Every variant's steps have strict validators; the plan itself
/// carries no authority.
#[derive(Clone)]
pub(super) enum ConsequencePlan {
    ForallInstance {
        quantifier: TermId,
        binding: Vec<TermId>,
    },
    SkolemInstance {
        source: TermId,
        quantified: TermId,
        witness: TermId,
        instance: TermId,
        positive: bool,
    },
    NegatedExistsDual {
        not_exists_root: TermId,
        exists: TermId,
    },
    /// The CONSEQUENT of an authored implication whose antecedent is itself
    /// derivable: `(=> A F)` (or its desugared `(or F (not A))`) plus `A`
    /// yields `F` by `implies_pos` and two resolutions.
    ImpliedConsequent {
        implication: TermId,
        antecedent: TermId,
    },
}

/// One authored implication root `(=> A F)` — or its desugared two-literal
/// `or` — whose consequent is a `forall`, together with the antecedent that
/// makes the consequent a top-level consequence.
///
/// The record is only a hint: `consequence_unit` must independently derive a
/// unit clause for BOTH the implication root and the antecedent from the
/// authored scope, and the emitted `implies_pos` step is re-derived by the
/// strict checker from the implication's own structure.
#[derive(Clone, Copy)]
pub(in crate::executor) struct ImpliedForall {
    pub implication: TermId,
    pub antecedent: TermId,
    pub forall: TermId,
}

/// One authored `(not (exists ...))` root and its exact De Morgan dual.
/// The record is only a hint; strict replay re-derives the duality.
#[derive(Clone, Copy)]
pub(in crate::executor) struct NegatedExistsDual {
    pub not_exists_root: TermId,
    pub exists: TermId,
    pub forall: TermId,
}

/// Ordered members of the authored `and`-conjunct closure.
#[derive(Default)]
pub(super) struct AndConjunctClosure {
    pub(super) members: ay_core::kani_compat::DetHashSet<TermId>,
    pub(super) ordered: Vec<TermId>,
}

impl AndConjunctClosure {
    pub(super) fn contains(&self, term: &TermId) -> bool {
        self.members.contains(term)
    }
}
