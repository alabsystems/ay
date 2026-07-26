// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CHC problem transformations
//!
//! This module provides transformations that convert CHC problems into equivalent
//! forms that are more amenable to solving.
//!
//! # Architecture
//!
//! Based on Golem's transformer framework:
//! - `reference/golem/src/transformers/Transformer.h`
//! - `reference/golem/src/transformers/TransformationPipeline.h`
//!
//! Each transformer takes a CHC problem and returns a transformed problem plus
//! a back-translator for converting witnesses (invariants or counterexamples)
//! back to the original problem's vocabulary.

// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

pub(crate) mod array_ghost_pairs;
// Clause-local constant-address store-to-load forwarding + dead-store
// elimination over Array store/select chains (model-checker-consumer parity item 4a: makes
// threaded memory arrays dead so DeadParamEliminator can collapse relation
// arity). Routed inside the condense superpass round and as a bounded
// explicit stage in `PreprocessSummary::build*`. Kill switch
// AY_CHC_DISABLE_ARRAY_STORE_FORWARDING.
mod array_store_forwarding;
mod bv_to_bool;
mod bv_to_int;
// Catamorphism abstraction lane for recursive-ADT CHCs (CHC-COMP agenda #7).
// Routed via `AdaptivePortfolio::try_cata_abstraction_route` (adaptive_cata.rs).
pub(crate) mod cata_abstract;
mod clause_inlining;
// Unified fixpoint condense superpass (reachability + constant propagation +
// equality propagation + size-capped inlining + parallel-edge merging +
// argument-COI slicing iterated to size stability). Routed as stage -1 of
// every `PreprocessSummary::build*` pipeline behind AY_CHC_DISABLE_CONDENSE.
pub(crate) mod condense;
mod dead_param_elimination;
mod dt_flatten;
// Ground-table read concretization (model-checker-consumer parity item 4 Stage 1): global
// proof that array "tables" are only read at ground constant indices via
// positive-polarity ground pins, then pin elimination so DeadParamEliminator
// can slice the table argument positions. Routed after ArrayStoreForwarder in
// the build*/forwarding-only pre-pipelines and the condense superpass round.
// Kill switch AY_CHC_DISABLE_GROUND_TABLE_CONCRETIZATION.
mod ground_table_read_concretization;
mod interval_propagation;
mod local_var_elimination;
// Routed into portfolio preprocessing behind AY_GRAPH_COLLAPSE=1 (graph
// collapse for multi-predicate linear CHC), both directly and as the
// parallel-edge merging half of the NodeEliminator loop.
pub(crate) mod multi_edge_merger;
mod node_eliminator;
// SLayerCF-shaped pc-directed location splitting (campaign recon lever 8):
// specializes predicates whose arg0 is a constraint-pinned program counter
// into per-pc-value location predicates. Kill switch AY_CHC_DISABLE_PC_SPLIT.
mod pc_split;
// Prototype module is unit-tested but intentionally not routed into the solver yet.
#[allow(dead_code)]
mod solidity_array_dt_projection;
// SPLIT-SYM symbol splitter (CHC-COMP agenda #9): clones predicates whose
// argument is a constraint-implied constant in every occurrence. Routed right
// after the condense superpass in `portfolio/preprocess.rs::condense_stage`
// behind AY_CHC_DISABLE_SPLIT_SYM.
pub(crate) mod split_sym;

use crate::{ChcExpr, ChcProblem, ChcSort, Counterexample, InvariantModel};

pub(crate) use array_ghost_pairs::{
    ghost_pair_replay_obligations, recheck_ghost_pair_certificate, ArrayGhostPairTransformer,
    GhostPairCertificate, GhostPairSpec,
};
pub(crate) use array_store_forwarding::{array_store_forwarding_enabled, ArrayStoreForwarder};
pub(crate) use bv_to_bool::BvToBoolBitBlaster;
pub(crate) use bv_to_int::BvToIntAbstractor;
pub(crate) use clause_inlining::{accept_profile_enabled, ClauseInliner};
pub(crate) use condense::{condense_enabled, CondenseSuperpass};
pub(crate) use dead_param_elimination::DeadParamEliminator;
pub(crate) use dt_flatten::{DtFlattener, DT_FLATTEN_APPROX_OBLIGATION};
pub(crate) use ground_table_read_concretization::GroundTableReadConcretizer;
pub(crate) use interval_propagation::IntervalPropagator;
pub(crate) use local_var_elimination::LocalVarEliminator;
pub(crate) use multi_edge_merger::MultiEdgeMerger;
pub(crate) use node_eliminator::NodeEliminator;
pub(crate) use pc_split::PcSplitter;
#[allow(unused_imports)]
pub(crate) use solidity_array_dt_projection::{
    SolidityArrayDtProjectionRoute, SolidityArrayDtProjectionStats,
    SolidityArrayDtProjectionTransformer, SolidityArrayDtProjector,
};
pub(crate) use split_sym::{split_sym_enabled, SymbolSplitter};

/// Kill-switch for the WORD-BV lane hardening (item #8): lazy bounded bitwise
/// atoms in `bv_to_int` and the post-BvToInt interval-propagation pass.
/// Set `AY_CHC_DISABLE_WORD_BV=1` to restore the pre-hardening behavior
/// (plain UF fallbacks, no interval strengthening / mod discharge).
pub(crate) fn word_bv_hardening_disabled() -> bool {
    std::env::var("AY_CHC_DISABLE_WORD_BV")
        .map(|v| v != "0" && !v.is_empty())
        .unwrap_or(false)
}

// ============================================================================
// Type Aliases for Witnesses
// ============================================================================

/// Witness that the CHC system is satisfiable (safe).
/// Contains inductive interpretations for each predicate.
pub(crate) type ValidityWitness = InvariantModel;

/// Witness that the CHC system is unsatisfiable (unsafe).
/// Contains a concrete counterexample trace.
pub(crate) type InvalidityWitness = Counterexample;

// ============================================================================
// Transformation Result
// ============================================================================

/// Explicit memory/correctness summary attached to a preprocessing transform.
///
/// The report is intentionally compact, but it is executable metadata rather
/// than a comment: portfolio/adaptive validation uses it to decide whether a
/// transformed witness needs original validation and whether an Unsafe witness
/// can even be replayed in the original problem.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TransformMemoryReport {
    transform: String,
    reversible: bool,
    validates_on_original: bool,
    safe_requires_original_validation: bool,
    unsafe_backtranslation_complete: bool,
    obligations: Vec<TransformObligation>,
    facts: Vec<TransformMemoryFact>,
}

impl TransformMemoryReport {
    /// Report for the identity transform.
    pub(crate) fn identity() -> Self {
        Self {
            transform: "identity".to_string(),
            reversible: true,
            validates_on_original: true,
            safe_requires_original_validation: false,
            unsafe_backtranslation_complete: true,
            obligations: Vec::new(),
            facts: Vec::new(),
        }
    }

    /// Report for a transform whose witness translation is exactly reversible.
    pub(crate) fn reversible(transform: impl Into<String>) -> Self {
        Self {
            transform: transform.into(),
            reversible: true,
            validates_on_original: true,
            safe_requires_original_validation: true,
            unsafe_backtranslation_complete: true,
            obligations: Vec::new(),
            facts: Vec::new(),
        }
    }

    /// Report for a transform that is not reversible but is checked against the
    /// original problem by a named validation path.
    #[cfg(test)]
    pub(crate) fn validates_on_original(transform: impl Into<String>) -> Self {
        Self {
            transform: transform.into(),
            reversible: false,
            validates_on_original: true,
            safe_requires_original_validation: true,
            unsafe_backtranslation_complete: true,
            obligations: Vec::new(),
            facts: Vec::new(),
        }
    }

    /// Report for a transform that still has correctness obligations before it
    /// can be trusted by the CHC correctness firewall.
    #[cfg(test)]
    pub(crate) fn with_obligations(
        transform: impl Into<String>,
        obligations: impl IntoIterator<Item = TransformObligation>,
    ) -> Self {
        Self {
            transform: transform.into(),
            reversible: false,
            validates_on_original: false,
            safe_requires_original_validation: true,
            unsafe_backtranslation_complete: false,
            obligations: obligations.into_iter().collect(),
            facts: Vec::new(),
        }
    }

    /// Add explicit obligations to an otherwise original-validated transform.
    pub(crate) fn with_original_validation_obligations(
        transform: impl Into<String>,
        obligations: impl IntoIterator<Item = TransformObligation>,
    ) -> Self {
        Self {
            transform: transform.into(),
            reversible: false,
            validates_on_original: true,
            safe_requires_original_validation: true,
            unsafe_backtranslation_complete: true,
            obligations: obligations.into_iter().collect(),
            facts: Vec::new(),
        }
    }

    /// Attach a concrete fact observed while preprocessing or backtranslating.
    pub(crate) fn with_fact(mut self, name: impl Into<String>, value: impl Into<String>) -> Self {
        self.facts.push(TransformMemoryFact {
            name: name.into(),
            value: value.into(),
        });
        self
    }

    /// Mark an original-validated transform as unable to reconstruct Unsafe
    /// witnesses without falling back to original replay.
    pub(crate) fn with_incomplete_unsafe_backtranslation(mut self) -> Self {
        self.unsafe_backtranslation_complete = false;
        self
    }

    fn compose(transform: impl Into<String>, reports: impl IntoIterator<Item = Self>) -> Self {
        let mut reports = reports.into_iter();
        let Some(first) = reports.next() else {
            return Self {
                transform: transform.into(),
                ..Self::identity()
            };
        };

        let mut reversible = first.reversible;
        let mut validates_on_original = first.validates_on_original;
        let mut safe_requires_original_validation = first.safe_requires_original_validation;
        let mut unsafe_backtranslation_complete = first.unsafe_backtranslation_complete;
        let mut obligations = first.obligations;
        let mut facts = first.facts;

        for report in reports {
            reversible &= report.reversible;
            validates_on_original &= report.validates_on_original;
            safe_requires_original_validation |= report.safe_requires_original_validation;
            unsafe_backtranslation_complete &= report.unsafe_backtranslation_complete;
            obligations.extend(report.obligations);
            facts.extend(report.facts);
        }

        Self {
            transform: transform.into(),
            reversible,
            validates_on_original,
            safe_requires_original_validation,
            unsafe_backtranslation_complete,
            obligations,
            facts,
        }
    }

    #[cfg(test)]
    pub(crate) fn transform(&self) -> &str {
        &self.transform
    }

    #[cfg(test)]
    pub(crate) fn is_reversible(&self) -> bool {
        self.reversible
    }

    #[cfg(test)]
    pub(crate) fn validates_original(&self) -> bool {
        self.validates_on_original
    }

    #[cfg(test)]
    pub(crate) fn safe_requires_original_validation(&self) -> bool {
        self.safe_requires_original_validation
    }

    pub(crate) fn unsafe_backtranslation_complete(&self) -> bool {
        self.unsafe_backtranslation_complete
    }

    /// True when the composed transform stack is identity-grade: no transform
    /// requires original validation or witness reconstruction and there are no
    /// outstanding obligations, so a verdict established on the TRANSFORMED
    /// clauses transfers to the original problem without original-clause
    /// replay. Any real (problem-changing) transform reports
    /// `safe_requires_original_validation = true` and therefore fails this
    /// check — fail closed (rank-6 review must-fixes A/B).
    pub(crate) fn is_identity_grade(&self) -> bool {
        self.reversible
            && self.validates_on_original
            && !self.safe_requires_original_validation
            && self.unsafe_backtranslation_complete
            && self.obligations.is_empty()
    }

    /// True when the composed transform stack is EQUISAT-grade: every
    /// constituent transform preserves the sat/unsat verdict exactly (the
    /// transformed problem is safe iff the original is), so a verdict
    /// established on the transformed clauses transfers to the original even
    /// when the WITNESS cannot be reconstructed there.
    ///
    /// Strictly weaker than [`Self::is_identity_grade`] (which additionally
    /// requires witness-level reversibility) and strictly stronger than
    /// "validates on original": obligations are checked against a fail-closed
    /// ALLOWLIST of equivalence-preserving passes. Any unknown obligation
    /// name — including every abstraction-grade pass (BvToInt UF fallback,
    /// array scalarization, DT flattening, clause inlining's synthesized
    /// interpretations) — fails the check.
    ///
    /// Consumed by the #9227 re-keyed empty-model acyclic BMC promotion
    /// (item 4 Stage 0): promotion additionally requires an independent
    /// fresh-executor re-run, so this check is a necessary, not sufficient,
    /// condition for accepting transformed evidence.
    pub(crate) fn is_equisat_grade(&self) -> bool {
        /// Obligations attached by passes whose rewrites are equivalence-
        /// preserving on the clause system (verdicts cannot flip):
        /// - `clause-local-store-forwarding`: ArrayStoreForwarder (pointwise
        ///   array identities + local existential projection).
        /// - `ground-table-read-concretization`: GroundTableReadConcretizer
        ///   (positive-polarity ground pin elimination; single-table
        ///   instantiation argument, see the pass docs).
        /// - `original-validation-on-safe` / `original-replay-on-unsafe`:
        ///   generic fail-closed validation markers, not abstractions.
        const EQUISAT_OBLIGATIONS: [&str; 4] = [
            "clause-local-store-forwarding",
            "ground-table-read-concretization",
            "original-validation-on-safe",
            "original-replay-on-unsafe",
        ];
        self.validates_on_original
            && self.unsafe_backtranslation_complete
            && self
                .obligations
                .iter()
                .all(|obligation| EQUISAT_OBLIGATIONS.contains(&obligation.name()))
    }

    #[cfg(test)]
    pub(crate) fn obligations(&self) -> &[TransformObligation] {
        &self.obligations
    }

    #[cfg(test)]
    pub(crate) fn fact_value(&self, name: &str) -> Option<&str> {
        self.facts
            .iter()
            .find(|fact| fact.name == name)
            .map(|fact| fact.value.as_str())
    }

    pub(crate) fn has_obligation(&self, name: &str) -> bool {
        self.obligations
            .iter()
            .any(|obligation| obligation.name() == name)
    }

    pub(crate) fn diagnostic_summary(&self) -> String {
        let obligations = if self.obligations.is_empty() {
            "none".to_string()
        } else {
            self.obligations
                .iter()
                .map(|obligation| obligation.name())
                .collect::<Vec<_>>()
                .join(",")
        };
        let facts = if self.facts.is_empty() {
            "none".to_string()
        } else {
            self.facts
                .iter()
                .map(|fact| format!("{}={}", fact.name, fact.value))
                .collect::<Vec<_>>()
                .join(",")
        };
        format!(
            "transform={}, reversible={}, validates_original={}, safe_requires_original_validation={}, unsafe_backtranslation_complete={}, obligations={}, facts={}",
            self.transform,
            self.reversible,
            self.validates_on_original,
            self.safe_requires_original_validation,
            self.unsafe_backtranslation_complete,
            obligations,
            facts
        )
    }
}

/// Concrete fact attached to a transform-memory report.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TransformMemoryFact {
    name: String,
    value: String,
}

/// A named correctness obligation that must be discharged for a transform.
#[allow(dead_code)] // Future-facing CHC correctness firewall substrate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct TransformObligation {
    name: String,
}

#[allow(dead_code)] // Accessors are opt-in until transforms start reporting memory.
impl TransformObligation {
    pub(crate) fn named(name: impl Into<String>) -> Self {
        Self { name: name.into() }
    }

    pub(crate) fn name(&self) -> &str {
        &self.name
    }
}

/// Result of applying a transformation to a CHC problem.
pub(crate) struct TransformationResult {
    /// The transformed CHC problem.
    pub(crate) problem: ChcProblem,
    /// Back-translator for converting witnesses from the transformed problem
    /// back to the original problem.
    pub(crate) back_translator: Box<dyn BackTranslator>,
}

impl TransformationResult {
    /// Correctness memory reported by the transform's back-translator.
    #[allow(dead_code)] // Exposed for the next CHC correctness firewall wiring slice.
    pub(crate) fn transform_memory(&self) -> TransformMemoryReport {
        self.back_translator.transform_memory()
    }
}

// ============================================================================
// Back Translator Trait
// ============================================================================

/// Translates witnesses from a transformed problem back to the original problem.
///
/// Reference: `reference/golem/src/transformers/Transformer.h:WitnessBackTranslator`
pub(crate) trait BackTranslator: Send {
    /// Translate an invariant model from the transformed problem
    /// back to the original problem's predicate vocabulary.
    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness;

    /// Translate a counterexample from the transformed problem
    /// back to the original problem's state vocabulary.
    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness;

    /// Translate a fully-ground derivation over this transform's OUTPUT
    /// problem into a fully-ground derivation over its INPUT problem.
    ///
    /// This is the fallible sibling of [`Self::translate_invalidity`], and it
    /// exists because that method has no failure channel: it takes and returns
    /// an owned witness, so a pass that cannot map a derivation step has no way
    /// to say so and silently passes transformed evidence through. Ground
    /// back-translation must never do that, so the contract here is inverted —
    /// the DEFAULT IS FAILURE, and a pass opts in only by proving it can
    /// reconstruct the input-space derivation.
    ///
    /// # Contract
    ///
    /// - `derivation` is a derivation over this pass's OUTPUT problem, already
    ///   validated there. Implementations retain whatever they need of their
    ///   INPUT problem themselves (the composite chain does not keep the
    ///   intermediate problems around).
    /// - A returned derivation is a CANDIDATE only. It is re-validated against
    ///   the input problem by pure ground evaluation — implementations do this
    ///   themselves before returning, and the top-level caller re-validates the
    ///   final result against the ORIGINAL problem. A buggy or stale
    ///   implementation can therefore only cause a rejection, never a wrong
    ///   verdict.
    /// - `None` means "this pass cannot map this derivation" and the caller
    ///   falls back to its pre-existing behavior.
    fn translate_ground_derivation(
        &self,
        _derivation: &crate::ground_derivation::GroundDerivation,
    ) -> Option<crate::ground_derivation::GroundDerivation> {
        None
    }

    /// Human-readable name used when logging which pass failed ground
    /// back-translation.
    fn ground_translation_name(&self) -> &'static str {
        "unnamed-pass"
    }

    /// Whether this transform used UF fallback for any variable-variable
    /// bitwise operation. Default: false. Override in BvToInt (#8289).
    fn had_bitwise_uf_fallback(&self) -> bool {
        false
    }

    /// Correctness memory attached to this transform.
    fn transform_memory(&self) -> TransformMemoryReport {
        TransformMemoryReport::identity()
    }

    /// Finite array indices observed during backtranslation and available for
    /// CEGAR-style scalarization refinement.
    fn array_refinement_indices(&self) -> Vec<(ChcSort, ChcExpr)> {
        Vec::new()
    }
}

/// Identity back-translator that passes witnesses through unchanged.
///
/// Used for transformations that don't change the witness representation.
pub(crate) struct IdentityBackTranslator;

impl BackTranslator for IdentityBackTranslator {
    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness {
        witness
    }

    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness {
        witness
    }

    /// A pass that returned this translator left the problem UNCHANGED (the
    /// transform bailed), so its input and output clause lists are the same
    /// object and the derivation carries over verbatim. This is the one
    /// legitimate identity: it is not "pass transformed evidence through", it
    /// is "there was no transform".
    fn translate_ground_derivation(
        &self,
        derivation: &crate::ground_derivation::GroundDerivation,
    ) -> Option<crate::ground_derivation::GroundDerivation> {
        Some(derivation.clone())
    }

    fn ground_translation_name(&self) -> &'static str {
        "identity"
    }
}

/// Identity witness translator with explicit transform memory.
///
/// Used by transforms that rewrite the problem but do not need to rewrite
/// witnesses beyond the mandatory original-problem validation gate.
pub(crate) struct MemoryBackTranslator {
    report: TransformMemoryReport,
    /// The INPUT problem, retained for ground back-translation only.
    ///
    /// These passes rewrite clause CONSTRAINTS in place (store forwarding,
    /// ground-table read concretization, local-variable projection) without
    /// changing the derivation shape, so a ground derivation maps across by
    /// keeping the step structure and re-completing each environment against
    /// the richer input clause. `None` disables ground back-translation.
    input_problem: Option<std::sync::Arc<ChcProblem>>,
    /// Exact OUTPUT clause index -> INPUT clause index map for passes that may
    /// delete clauses while rewriting the survivors. `None` means indices are
    /// preserved.
    output_to_input: Option<Vec<usize>>,
    /// Name used in ground back-translation diagnostics.
    name: &'static str,
}

impl MemoryBackTranslator {
    pub(crate) fn new(report: TransformMemoryReport) -> Self {
        Self {
            report,
            input_problem: None,
            output_to_input: None,
            name: "memory-pass",
        }
    }

    /// Enable ground back-translation for this pass by retaining its input
    /// problem. The clone is only taken when the feature is on.
    pub(crate) fn with_ground_input(mut self, name: &'static str, problem: &ChcProblem) -> Self {
        self.name = name;
        if crate::ground_derivation::ground_backtranslation_enabled() {
            self.input_problem = Some(std::sync::Arc::new(problem.clone()));
        }
        self
    }

    /// Enable ground back-translation with an exact surviving-clause map.
    pub(crate) fn with_ground_index_map(
        mut self,
        name: &'static str,
        problem: &ChcProblem,
        output_to_input: Vec<usize>,
    ) -> Self {
        self.name = name;
        if crate::ground_derivation::ground_backtranslation_enabled() {
            self.input_problem = Some(std::sync::Arc::new(problem.clone()));
            self.output_to_input = Some(output_to_input);
        }
        self
    }
}

impl BackTranslator for MemoryBackTranslator {
    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness {
        witness
    }

    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness {
        witness
    }

    fn translate_ground_derivation(
        &self,
        derivation: &crate::ground_derivation::GroundDerivation,
    ) -> Option<crate::ground_derivation::GroundDerivation> {
        let input_problem = self.input_problem.clone()?;
        // Index-preserving rewrite: try each step's own clause index first.
        // The mapping is only a hint — the translator self-validates on the
        // input problem, and the final result is validated again on the
        // ORIGINAL problem, so a shifted index can only cause a rejection.
        let candidates = self.output_to_input.as_ref().map_or_else(
            || {
                (0..input_problem.clauses().len())
                    .map(|index| vec![index])
                    .collect()
            },
            |map| map.iter().map(|index| vec![*index]).collect(),
        );
        crate::ground_derivation::clause_map::ClauseMapGroundTranslator::new(
            self.name,
            input_problem,
            candidates,
        )
        .translate(derivation)
    }

    fn ground_translation_name(&self) -> &'static str {
        self.name
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        self.report.clone()
    }
}

// ============================================================================
// Transformer Trait
// ============================================================================

/// A transformation that converts a CHC problem into an equivalent form.
///
/// Reference: `reference/golem/src/transformers/Transformer.h:Transformer`
///
/// Transformers must be consumed when applied (hence `self: Box<Self>`),
/// because they may need to move internal state into the back-translator.
pub(crate) trait Transformer {
    /// Apply the transformation to a CHC problem.
    ///
    /// Returns the transformed problem and a back-translator.
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult;
}

// ============================================================================
// Transformation Pipeline
// ============================================================================

/// A pipeline of transformations applied in sequence.
///
/// Reference: `reference/golem/src/transformers/TransformationPipeline.h`
///
/// The pipeline applies transformations in order, composing their back-translators
/// so that witnesses can be translated back through the entire pipeline.
pub(crate) struct TransformationPipeline {
    transformers: Vec<Box<dyn Transformer>>,
}

impl Default for TransformationPipeline {
    fn default() -> Self {
        Self::new()
    }
}

impl TransformationPipeline {
    /// Create a new empty pipeline.
    pub(crate) fn new() -> Self {
        Self {
            transformers: Vec::new(),
        }
    }

    /// Add a transformer to the end of the pipeline.
    pub(crate) fn with<T: Transformer + 'static>(mut self, transformer: T) -> Self {
        self.transformers.push(Box::new(transformer));
        self
    }

    /// Number of transformers in the pipeline.
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.transformers.len()
    }

    /// Apply all transformations in sequence.
    ///
    /// Returns the final transformed problem and a composite back-translator
    /// that will translate witnesses back through all transformations in
    /// reverse order.
    pub(crate) fn transform(self, mut problem: ChcProblem) -> TransformationResult {
        let mut back_translators: Vec<Box<dyn BackTranslator>> = Vec::new();

        for transformer in self.transformers {
            let result = transformer.transform(problem);
            problem = result.problem;
            back_translators.push(result.back_translator);
        }

        // Reverse the back-translators so they're applied in reverse order
        back_translators.reverse();

        TransformationResult {
            problem,
            back_translator: Box::new(CompositeBackTranslator {
                inner: back_translators,
            }),
        }
    }
}

// ============================================================================
// Composite Back Translator
// ============================================================================

/// Composes multiple back-translators into a single translator.
///
/// Applies back-translators in order (which should be reverse of transformation order).
pub(crate) struct CompositeBackTranslator {
    pub(crate) inner: Vec<Box<dyn BackTranslator>>,
}

impl BackTranslator for CompositeBackTranslator {
    fn translate_validity(&self, mut witness: ValidityWitness) -> ValidityWitness {
        for translator in &self.inner {
            witness = translator.translate_validity(witness);
        }
        witness
    }

    fn translate_invalidity(&self, mut witness: InvalidityWitness) -> InvalidityWitness {
        for translator in &self.inner {
            witness = translator.translate_invalidity(witness);
        }
        witness
    }

    /// Fold the ground derivation through the inner translators in the same
    /// order `translate_invalidity` uses (reverse of transformation order).
    ///
    /// Unlike that fold, this one PROPAGATES FAILURE: the first inner pass that
    /// cannot map the derivation aborts the whole chain. There is no
    /// "pass it through unchanged" fallback, because a derivation that still
    /// addresses a downstream problem's clauses is not evidence about the
    /// original problem.
    fn translate_ground_derivation(
        &self,
        derivation: &crate::ground_derivation::GroundDerivation,
    ) -> Option<crate::ground_derivation::GroundDerivation> {
        let mut current = derivation.clone();
        for translator in &self.inner {
            match translator.translate_ground_derivation(&current) {
                Some(next) => current = next,
                None => {
                    crate::ground_derivation::log_ground_translation_failure(
                        translator.ground_translation_name(),
                    );
                    return None;
                }
            }
        }
        Some(current)
    }

    fn ground_translation_name(&self) -> &'static str {
        "composite"
    }

    fn had_bitwise_uf_fallback(&self) -> bool {
        self.inner.iter().any(|t| t.had_bitwise_uf_fallback())
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        TransformMemoryReport::compose(
            "composite",
            self.inner
                .iter()
                .map(|translator| translator.transform_memory()),
        )
    }

    fn array_refinement_indices(&self) -> Vec<(ChcSort, ChcExpr)> {
        self.inner
            .iter()
            .flat_map(|translator| translator.array_refinement_indices())
            .collect()
    }
}

/// Shares one back-translator between multiple probe summaries (item 4
/// Stage 4 probe reorder: the scalarized chain feeds both the
/// inline-collapse lane and the exact-DAG lane). `BackTranslator` methods
/// take `&self` but implementations are only `Send`, so the shared box sits
/// behind a mutex; translation calls are short and never reentrant.
pub(crate) struct SharedBackTranslator(
    pub(crate) std::sync::Arc<std::sync::Mutex<Box<dyn BackTranslator>>>,
);

impl SharedBackTranslator {
    fn inner(&self) -> std::sync::MutexGuard<'_, Box<dyn BackTranslator>> {
        self.0
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
    }
}

impl BackTranslator for SharedBackTranslator {
    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness {
        self.inner().translate_validity(witness)
    }

    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness {
        self.inner().translate_invalidity(witness)
    }

    fn translate_ground_derivation(
        &self,
        derivation: &crate::ground_derivation::GroundDerivation,
    ) -> Option<crate::ground_derivation::GroundDerivation> {
        self.inner().translate_ground_derivation(derivation)
    }

    fn ground_translation_name(&self) -> &'static str {
        "shared"
    }

    fn had_bitwise_uf_fallback(&self) -> bool {
        self.inner().had_bitwise_uf_fallback()
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        self.inner().transform_memory()
    }

    fn array_refinement_indices(&self) -> Vec<(ChcSort, ChcExpr)> {
        self.inner().array_refinement_indices()
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "mod_tests.rs"]
mod tests;

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "soundness_tests.rs"]
mod soundness_tests;
