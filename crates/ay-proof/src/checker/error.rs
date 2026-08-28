// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed failures from strict and ordinary proof validation.

use ay_core::{ProofId, TermId, TheoryLemmaKind};
use thiserror::Error;

/// Validation failure returned by [`super::check_proof`].
///
/// `Clone` exists for one consumer: the executor-side strict-walk memo
/// (`ay-dpll` #strict-walk-memo) replays a stored verdict for a
/// byte-identical document instead of re-walking it. Cloning changes no
/// validation semantics; every variant carries only plain data.
#[derive(Debug, Clone, Error, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofCheckError {
    /// A caller-owned proof-validation envelope refused a work or scratch-space charge.
    ///
    /// This is a CALIBRATION verdict. The proof may be perfectly checkable; the
    /// envelope simply is not wide enough, and the remedy lives in the charge
    /// model or the envelope constant.
    #[error("proof validation resource envelope exhausted")]
    ResourceLimit,
    /// The caller asked the check to stop: interrupt, solve deadline, or memory
    /// ceiling.
    ///
    /// Kept SEPARATE from [`ProofCheckError::ResourceLimit`] because the two
    /// have opposite remedies and mandatory certification degrades the verdict
    /// for either one. Collapsing them made every downgrade look like a
    /// calibration problem even when the caller had simply run out of time.
    #[error("proof validation cancelled by the caller (interrupt, deadline, or memory limit)")]
    Cancelled,
    /// The proof has no steps.
    #[error("proof is empty")]
    EmptyProof,
    /// A serialized proof bundle carried an unrecognized schema tag (a version
    /// skew that could mis-decode); the bundle is rejected rather than trusted.
    #[error("proof bundle schema mismatch: expected {expected}, found {found}")]
    BundleSchemaMismatch {
        /// The schema tag this build understands.
        expected: String,
        /// The schema tag found in the bundle.
        found: String,
    },
    /// A serialized proof bundle violated the structural invariants required
    /// before its untrusted term/proof tables can be indexed safely.
    #[error("malformed proof bundle: {reason}")]
    MalformedProofBundle {
        /// Description of the first rejected structural invariant.
        reason: String,
    },
    /// The exact datatype constructor/selector/tester signature table was
    /// missing, incomplete, internally inconsistent, or contradicted a term.
    #[error("invalid typed datatype signature context: {reason}")]
    InvalidDatatypeSignatureContext {
        /// Description of the first rejected context invariant.
        reason: String,
    },
    /// A context-bound proof used a free assumption outside the supplied
    /// problem obligation.
    #[error("step {step} assumes term {term} outside the supplied problem obligation")]
    UnauthorizedAssumption {
        /// The unauthorized `Assume` step.
        step: ProofId,
        /// The term admitted as an unsupported hypothesis.
        term: TermId,
    },
    /// The proof has steps but none of them produce a clause.
    #[error("proof has no clause-producing steps")]
    NoClauseProducingSteps,
    /// A premise index is outside the proof range.
    #[error("step {step} references missing premise {premise}")]
    MissingPremise {
        /// Step containing the invalid premise reference.
        step: ProofId,
        /// Referenced premise ID.
        premise: ProofId,
    },
    /// A premise points to the current step or a future step.
    #[error("step {step} references non-prior premise {premise}")]
    NonPriorPremise {
        /// Step containing the invalid premise reference.
        step: ProofId,
        /// Referenced premise ID.
        premise: ProofId,
    },
    /// A premise points to an anchor (no clause).
    #[error("step {step} premise {premise} does not produce a clause")]
    PremiseHasNoClause {
        /// Step containing the invalid premise reference.
        step: ProofId,
        /// Referenced premise ID.
        premise: ProofId,
    },
    /// A resolution-style step does not match its premises.
    #[error("step {step} has invalid {rule} derivation")]
    InvalidResolution {
        /// Invalid step ID.
        step: ProofId,
        /// Rule name (`resolution` or `th_resolution`).
        rule: String,
    },
    /// A DRUP step is not reverse-unit-propagation valid.
    #[error("step {step} has invalid drup derivation")]
    InvalidDrup {
        /// Invalid step ID.
        step: ProofId,
    },
    /// Hole steps are placeholders and are never valid final proofs.
    #[error("step {step} uses unsupported hole rule")]
    HoleStep {
        /// Invalid step ID.
        step: ProofId,
    },
    /// The step's premise count cannot denote a resolution at all. Arity 2 is
    /// checked binarily and arity > 2 as a left-to-right chain
    /// (#dt-premise-binding), so this now fires only for 0 or 1 premises.
    #[error("step {step} uses {rule} with unsupported premise count {premise_count}")]
    UnsupportedResolutionArity {
        /// Invalid step ID.
        step: ProofId,
        /// Rule name.
        rule: String,
        /// Number of premises provided by the step.
        premise_count: usize,
    },
    /// A `resolution` / `th_resolution` step carries `:args`, but they are not
    /// a well-formed Alethe pivot list.
    ///
    /// Alethe's argument-directed resolution takes a `(pivot, polarity)` PAIR
    /// per link, i.e. `2 * (premises - 1)` arguments, with each polarity a
    /// Boolean constant. carcara 1.1.0 routes any non-empty `:args` to that
    /// checker and rejects the step outright when the count is wrong
    /// (`expected 4 arguments, got 1`), so accepting a malformed list here is
    /// exactly how AY would ship a proof carcara refuses. Distinct from
    /// [`Self::InvalidResolution`] so the diagnostic names the count carcara
    /// will demand instead of reporting a pivot search that never ran.
    #[error(
        "step {step} uses {rule} with malformed :args \
         (expected {expected} pivot/polarity terms for {premise_count} premises, got {got})"
    )]
    MalformedResolutionArgs {
        /// Invalid step ID.
        step: ProofId,
        /// Rule name (`resolution` or `th_resolution`).
        rule: String,
        /// Number of premises the step lists.
        premise_count: usize,
        /// Required argument count (`2 * (premise_count - 1)`).
        expected: usize,
        /// Argument count actually supplied.
        got: usize,
    },
    /// The terminal clause-producing step must derive the empty clause.
    #[error("final clause-producing step {step} is not the empty clause")]
    FinalClauseNotEmpty {
        /// Final clause-producing step ID.
        step: ProofId,
    },
    /// Trust steps are unverified and rejected in strict mode.
    #[error("step {step} uses unverified trust rule")]
    TrustStep {
        /// Invalid step ID.
        step: ProofId,
    },
    /// A generic Alethe rule lacks semantic validation and is rejected in strict mode.
    #[error("step {step} uses unvalidated rule {rule} in strict mode")]
    UnvalidatedRule {
        /// Invalid step ID.
        step: ProofId,
        /// Rule name.
        rule: String,
    },
    /// Theory lemmas without a strict-mode semantic validator are rejected.
    #[error("step {step} uses unsupported theory lemma kind {kind:?} in strict mode")]
    UnsupportedTheoryLemmaKind {
        /// Invalid step ID.
        step: ProofId,
        /// Rejected theory lemma kind.
        kind: TheoryLemmaKind,
    },
    /// A theory lemma failed strict semantic validation.
    #[error("step {step} has invalid theory lemma: {reason}")]
    InvalidTheoryLemma {
        /// Invalid step ID.
        step: ProofId,
        /// Semantic validation failure detail.
        reason: String,
    },
    /// A Boolean tautology or clausification rule failed structural validation.
    #[error("step {step} has invalid {rule} rule: {reason}")]
    InvalidBooleanRule {
        /// Invalid step ID.
        step: ProofId,
        /// Rule name.
        rule: String,
        /// Validation failure detail.
        reason: String,
    },
    /// Strict proof mode rejects proofs containing any trust steps (#8076).
    ///
    /// When `produce-proofs` is enabled with strict proof mode, every theory
    /// must produce proper proof rules instead of falling back to `trust`.
    /// The reason string identifies which theory lemma kinds triggered the
    /// trust fallback.
    #[error("{reason}")]
    StrictProofModeTrust {
        /// Description of which trust steps were found and their sources.
        reason: String,
    },
}
