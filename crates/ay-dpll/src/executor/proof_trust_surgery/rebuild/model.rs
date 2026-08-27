// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed transactional state for the proof-surgery pipeline.

use super::super::*;

pub(super) type SurfaceOverrides = HashMap<TermId, String>;

/// Immutable proof/source inputs shared by every planning phase.
pub(super) struct SurgeryInput<'a> {
    pub(super) proof: &'a Proof,
    pub(super) originals: &'a [(TermId, FrontendTerm)],
    pub(super) source_index: &'a OriginalSourceIndex,
    pub(super) live: &'a [bool],
    pub(super) consumers: &'a [Vec<usize>],
}

impl SurgeryInput<'_> {
    pub(super) fn step_count(&self) -> usize {
        self.proof.steps.len()
    }
}

/// Every proof-authority decision made before mutation begins.
///
/// Invariant: this ledger is completed and volume-checked before a
/// [`RebuildState`] exists. Emission may read it but never add authority or
/// reinterpret a leaf. The maps are separated by proof-rule family so the
/// ordered recognizer cannot silently replace one certificate class with
/// another during rebuilding.
#[derive(Default)]
pub(super) struct SurgeryPlans {
    pub(super) trichotomies: HashMap<usize, TrichotomyPlan>,
    pub(super) ite_lifts: HashMap<usize, IteLiftPlan>,
    pub(super) provenance_ite_lifts: HashMap<usize, ProvenanceItePlan>,
    pub(super) exact_provenance_or_assumes: HashMap<usize, TermId>,
    pub(super) provenance_or_plans: HashMap<usize, ProvenanceOrPlan>,
    pub(super) or_units: HashMap<usize, OrUnitPlan>,
    pub(super) normalized_authored_ors: HashMap<usize, NormalizedAuthoredOrPlan>,
    pub(super) authored_array_ites: HashMap<usize, AuthoredArrayItePlan>,
    pub(super) taut_units: HashMap<usize, OrTautologyPlan>,
    pub(super) euf_lemmas: HashMap<usize, EufLemmaPlan>,
    pub(super) quant_negations: HashMap<usize, QuantNegationPlan>,
    pub(super) quant_consequences: HashMap<usize, QuantConsequencePlan>,
    pub(super) subst_eqs: HashMap<usize, SubstEqPlan>,
    pub(super) deferred_leaves: HashSet<usize>,
    pub(super) or_split_of: HashMap<usize, usize>,
    pub(super) assume_plans: HashMap<usize, AssumePlan>,
    pub(super) quant_source_replacements: HashMap<TermId, TermId>,
    pub(super) unit_patterns: HashMap<usize, (usize, usize)>,
    pub(super) dropped_and_pos: Vec<bool>,
    pub(super) quant_chains: HashMap<(usize, usize), QuantInstanceChain>,
    pub(super) keeps_surface_overrides: bool,
    pub(super) has_ite_lift_plans: bool,
    pub(super) has_quant_plans: bool,
    pub(super) prepared_surface_overrides: Option<SurfaceOverrides>,
    pub(super) prepared_quant_surface_overrides: Option<SurfaceOverrides>,
}

impl SurgeryPlans {
    pub(super) fn has_repairs(&self) -> bool {
        !self.trichotomies.is_empty()
            || !self.ite_lifts.is_empty()
            || !self.provenance_ite_lifts.is_empty()
            || !self.exact_provenance_or_assumes.is_empty()
            || !self.provenance_or_plans.is_empty()
            || !self.or_units.is_empty()
            || !self.assume_plans.is_empty()
            || !self.normalized_authored_ors.is_empty()
            || !self.authored_array_ites.is_empty()
            || !self.taut_units.is_empty()
            || !self.euf_lemmas.is_empty()
            || !self.subst_eqs.is_empty()
            || !self.quant_negations.is_empty()
            || !self.quant_consequences.is_empty()
    }
}

/// Mutable output graph and deterministic sharing caches for the ordered walk.
///
/// Invariant: `map[i]` is assigned only after old step `i` has been rebuilt,
/// and every cached `ProofId` belongs to `new_proof`. None of these caches
/// confer source/proof authority; they only share derivations already present
/// in the immutable [`SurgeryPlans`] ledger.
pub(super) struct RebuildState {
    pub(super) new_proof: Proof,
    pub(super) map: Vec<Option<ProofId>>,
    pub(super) assume_new_id: HashMap<usize, ProofId>,
    pub(super) lift_assume: HashMap<TermId, ProofId>,
    pub(super) distinct_unit: HashMap<usize, ProofId>,
    pub(super) anddistinct_units: HashMap<usize, Vec<ProofId>>,
    pub(super) trichotomy_clause: HashMap<usize, ProofId>,
    pub(super) taut_unit_of_term: HashMap<TermId, ProofId>,
    pub(super) euf_unit_of_term: HashMap<TermId, ProofId>,
    pub(super) quant_units_emitted: HashMap<(usize, usize), ProofId>,
}

impl RebuildState {
    pub(super) fn new(step_count: usize) -> Self {
        Self {
            new_proof: Proof::new(),
            map: vec![None; step_count],
            assume_new_id: HashMap::default(),
            lift_assume: HashMap::default(),
            distinct_unit: HashMap::default(),
            anddistinct_units: HashMap::default(),
            trichotomy_clause: HashMap::default(),
            taut_unit_of_term: HashMap::default(),
            euf_unit_of_term: HashMap::default(),
            quant_units_emitted: HashMap::default(),
        }
    }
}

/// Three-way result keeps “not this shape” distinct from fail-closed rejection.
pub(super) enum EmitDecision {
    NotApplicable,
    Emitted,
    Reject,
}

impl EmitDecision {
    pub(super) fn resolved(self) -> Option<bool> {
        match self {
            Self::NotApplicable => None,
            Self::Emitted => Some(true),
            Self::Reject => Some(false),
        }
    }
}

/// Borrowed view used only during the single forward rebuild walk.
///
/// Invariant: methods inspect plan families in the same priority order as the
/// planner and either emit one complete replacement for the current old step
/// or reject. They never advance to a later old index themselves.
pub(super) struct RebuildWalk<'a, 'input> {
    pub(super) executor: &'a mut Executor,
    pub(super) input: &'a SurgeryInput<'input>,
    pub(super) plans: &'a SurgeryPlans,
    pub(super) state: &'a mut RebuildState,
}
