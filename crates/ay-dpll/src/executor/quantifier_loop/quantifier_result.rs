// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier-preprocessing result data and exact-rewrite provenance.

use ay_core::TermId;

use super::exact_array_negation::ExactArrayNegationEvidence;
use crate::cegqi::CegqiInstantiator;

/// Exact preprocessing snapshot retained when canonical finite-domain
/// expansion removes every quantifier before E-matching starts.
///
/// The records are producer provenance, not SAT authority. Result mapping must
/// still replay the canonical expander, prove complete coverage of the authored
/// quantified roots, validate the retained model against `expanded_assertions`,
/// and bind any grant to that exact model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct FiniteExpansionRecord {
    /// Exact authored top-level quantifier replaced by the finite expander.
    pub(super) original: TermId,
    /// Position of that root in the immutable authored assertion window.
    pub(super) assertion_index: usize,
    /// Exact ground replacement consumed by the ground solver after the
    /// equivalence-preserving post-expansion rewrites tracked by the producer.
    pub(super) expanded: TermId,
}

pub(in crate::executor) struct ExactFiniteExpansionEvidence {
    pub(super) expanded_assertions: Box<[TermId]>,
    pub(super) records: Box<[FiniteExpansionRecord]>,
}

/// Result of quantifier preprocessing: flags consumed by `map_quantifier_result`.
pub(in crate::executor) struct QuantifierProcessingResult {
    /// Whether any quantifiers had no E-matching instantiations.
    pub has_uninstantiated_quantifiers: bool,
    /// Whether E-matching hit its round or per-round budget.
    pub reached_instantiation_limit: bool,
    /// Whether deferred instantiations remain.
    pub has_deferred: bool,
    /// Whether CEGQI handled at least one forall quantifier.
    pub cegqi_has_forall: bool,
    /// Whether CEGQI handled at least one exists quantifier.
    pub cegqi_has_exists: bool,
    /// Whether E-matching added any new ground instantiations.
    pub ematching_added_instantiations: bool,
    /// Assertion snapshot after finite-domain expansion and Skolemization but
    /// before stripping quantified formulas. Interleaved refinement should use
    /// this preprocessed view instead of reintroducing the original shapes.
    pub refinement_assertions: Option<Vec<TermId>>,
    /// CE lemma TermIds added by CEGQI, tracked by ID for position-independent
    /// filtering. Refinement rounds push ground instantiations after CE lemmas,
    /// so positional slicing from the end is incorrect (#5975 offset bug).
    pub cegqi_ce_lemma_ids: Vec<TermId>,
    /// Per-universal CE-conjunct groups (#cegqi-per-universal): for each
    /// CEGQI-handled quantifier, the surviving AND-conjuncts of ITS CE lemma —
    /// the sound unit for the disambiguation SAT flip's refutation.
    pub cegqi_ce_lemma_groups: Vec<(TermId, Vec<TermId>)>,
    /// Whether any quantifiers are completely unhandled (neither E-matching nor CEGQI).
    pub has_completely_unhandled_quantifiers: bool,
    /// Quantifiers not handled by either E-matching or CEGQI (#5971).
    /// Passed to MBQI for model-based counterexample checking.
    pub unhandled_quantifiers: Vec<TermId>,
    /// Whether E-matching processed any exists quantifiers (#3593).
    /// When true, UNSAT results are unreliable because E-matching adds exists
    /// instances as conjunctive assertions (all must hold), but exists semantics
    /// require a disjunction (at least one must hold).
    pub ematching_has_exists: bool,
    /// Number of E-matching rounds completed (#8614).
    pub ematching_rounds_completed: u64,
    /// Number of quantifier instances created by E-matching (#8614).
    pub ematching_instances_created: u64,
    /// Original assertions snapshot (before E-matching modifications).
    /// `Some` when quantifiers were present; used to restore assertions after solving.
    pub original_assertions: Option<Vec<TermId>>,
    /// Canonical finite-expansion provenance for the early fully-ground exit.
    /// Kept separate from `original_assertions`: restoration state alone is
    /// never evidence that an expansion was exact or exhaustive.
    pub exact_finite_expansion: Option<ExactFiniteExpansionEvidence>,
    /// Independently replayable provenance for the one exact pointwise array
    /// inequality rewrite accepted by the SAT-only completeness lane.
    pub exact_array_negation: Option<ExactArrayNegationEvidence>,
    /// CEGQI state for refinement: (quantifier_id, instantiator) pairs.
    /// Used by `map_quantifier_result` to compute model-based instantiations
    /// when the CE lemma yields SAT (counterexample found).
    pub cegqi_state: Vec<(TermId, CegqiInstantiator)>,
    /// Any original assertion contains a `forall` whose binder sort MBQI
    /// cannot synthesize (Array, FP, Seq, RegLan). SAT results for such
    /// problems are unsound unless CEGQI refinement already forced UNSAT,
    /// because the ground solver only sees a finite set of E-matched
    /// instances of an infinite-domain quantifier (ay #8729, Z3 #6303).
    pub has_unsafe_partial_quantifiers: bool,
    /// True when every collected universal quantifier is a syntactic
    /// UF-completion candidate.
    ///
    /// This is only a refinement hint. It is not SAT authority: the classifier
    /// does not construct one shared interpretation for all accepted atoms, and
    /// E-matching having produced an instance is not domain coverage.
    pub quantifiers_supported_by_uf_completion: bool,
}

impl QuantifierProcessingResult {
    /// Create a no-op result for the case when no quantifiers are present.
    pub(super) fn no_quantifiers() -> Self {
        Self {
            has_uninstantiated_quantifiers: false,
            reached_instantiation_limit: false,
            has_deferred: false,
            cegqi_has_forall: false,
            cegqi_has_exists: false,
            ematching_added_instantiations: false,
            refinement_assertions: None,
            cegqi_ce_lemma_ids: Vec::new(),
            cegqi_ce_lemma_groups: Vec::new(),
            has_completely_unhandled_quantifiers: false,
            unhandled_quantifiers: Vec::new(),
            ematching_has_exists: false,
            ematching_rounds_completed: 0,
            ematching_instances_created: 0,
            original_assertions: None,
            exact_finite_expansion: None,
            exact_array_negation: None,
            cegqi_state: Vec::new(),
            has_unsafe_partial_quantifiers: false,
            quantifiers_supported_by_uf_completion: false,
        }
    }

    /// Preserve the exact before/after expansion relation when preprocessing
    /// has made the solve entirely ground. Returning `no_quantifiers()` here
    /// used to discard both the authored roots and their authenticated
    /// finite-expansion lineage records, so restoration could only fail closed
    /// after a valid ground SAT.
    pub(super) fn fully_expanded(
        original_assertions: Vec<TermId>,
        expanded_assertions: Vec<TermId>,
        records: Vec<FiniteExpansionRecord>,
    ) -> Self {
        let exact_finite_expansion = (!records.is_empty()).then(|| ExactFiniteExpansionEvidence {
            expanded_assertions: expanded_assertions.clone().into_boxed_slice(),
            records: records.into_boxed_slice(),
        });
        let mut result = Self::no_quantifiers();
        result.refinement_assertions = Some(expanded_assertions);
        result.original_assertions = Some(original_assertions);
        result.exact_finite_expansion = exact_finite_expansion;
        result
    }

    /// Preserve the exact authored/rewrite relation for the narrow pointwise
    /// array inequality lane. The evidence remains non-authoritative until
    /// result mapping independently replays it and validates the retained model.
    pub(super) fn exact_array_negation(evidence: ExactArrayNegationEvidence) -> Self {
        let mut result = Self::no_quantifiers();
        result.refinement_assertions = Some(evidence.rewritten_assertions.to_vec());
        result.original_assertions = Some(evidence.original_assertions.to_vec());
        result.exact_array_negation = Some(evidence);
        result
    }
}
