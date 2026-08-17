// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof structure validation for premise linkage, resolution, DRUP, and terminal empty-clause derivation.
mod array_axiom;
pub(crate) use array_axiom::{
    array_row_chain_printer_terms, array_select_store_printer_terms,
    array_store_permutation_printer_terms, ArrayRowChainPrinterTerms, ArraySelectStorePrinterTerms,
    RowChainEnd, RowChainPath,
};
pub use array_axiom::{
    recognize_array_extensionality, recognize_array_extensionality_chain,
    recognize_array_select_store, recognize_array_theory_lemma,
    recognize_array_theory_lemma_with_typed_context, recognize_folded_array_extensionality,
    ExtDiffRegistry,
};
mod array_finite;
pub use array_finite::{
    recognize_array_finite_extensionality,
    recognize_array_finite_extensionality_with_typed_context,
    recognize_array_finite_select_expansion,
    recognize_array_finite_select_expansion_with_typed_context,
};
mod boolean;
mod boolean_derived;
mod boolean_negation;
mod bv_bitblast;
mod bv_lia_query;
pub use bv_bitblast::{
    authenticate_bool_bv_unsat_query, authenticate_uf_leaf_bool_bv_unsat_query,
    bv_bitblast_requires_proof_producer, recognize_bool_tautology, recognize_bv_bitblast,
    recognize_bv_ground_evaluate, AuthenticatedBoolBvUnsatQuery, BoolBvUnsatAuthenticationError,
    MAX_EXPENSIVE_BV_BYTES_PER_LEMMA, MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF,
    MAX_EXPENSIVE_BV_WORK_PER_LEMMA, MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA,
    MAX_PROOF_PRODUCING_BV_LEMMAS_PER_PROOF, MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA,
};
pub(crate) use bv_bitblast::{validate_expensive_bv_budget, MAX_BOUNDED_ASSIGNMENT_BITS};
pub use bv_lia_query::{
    authenticate_bv_lia_unsat_query, AuthenticatedBvLiaUnsatQuery, BvLiaUnsatAuthenticationError,
    MAX_BV_LIA_QUERY_ROOTS, MAX_BV_LIA_TAUTOLOGY_BYTES_PER_LEMMA,
    MAX_BV_LIA_TAUTOLOGY_WORK_PER_LEMMA,
};
mod clausification;
mod datatype_axiom;
pub(crate) use datatype_axiom::validate_datatype_signature_context;
pub use datatype_axiom::{
    recognize_datatype_constructor_reconstruct, recognize_datatype_distinct,
    recognize_datatype_exhaustive, recognize_datatype_selector_project,
    recognize_datatype_tester_eval, recognize_datatype_tester_eval_with_selectors,
    DatatypeMemberSignature,
};
mod euf;
pub use euf::{
    recognize_euf_congruent, recognize_euf_congruent_pred, recognize_euf_reflexive,
    recognize_euf_transitive,
};
mod euf_step_rules;
mod ite_axiom;
pub use ite_axiom::recognize_ite_same;
mod nia_linear_ideal;
mod nra_interval;
mod nra_poly;
mod nra_univariate;
pub use nra_interval::recognize_nra_interval_unsat;
pub use nra_univariate::recognize_nra_univariate_unsat;
mod order_ite;
pub(crate) use order_ite::assignment_count as order_ite_assignment_count;
pub use order_ite::recognize_order_ite_tautology;
mod regex_empty;
pub use regex_empty::recognize_regex_intersect_empty;
mod regex_length;
pub use regex_length::{recognize_regex_length_lower_bound, regex_min_length};
mod rounding_mode;
mod seq_extensional_companion;
pub use seq_extensional_companion::recognize as recognize_seq_extensional_companion_contradiction;
#[path = "set_axiom.rs"]
mod set_axiom;
#[path = "set_card_chain.rs"]
mod set_card_chain;
#[path = "subset_axiom.rs"]
mod subset_axiom;
pub use rounding_mode::recognize_rounding_mode_domain;
pub(crate) use set_axiom::EmptySetRegistry;
pub use set_card_chain::recognize_set_card_chain_recurrence;
pub use string_ground::recognize_string_ground_eval;
pub(crate) use string_ground::{
    STRING_CHAR_ALLOCATION_LIMIT, STRING_EVAL_WORK_LIMIT, STRING_NUMERIC_BIT_ALLOCATION_LIMIT,
    STRING_NUMERIC_WORK_LIMIT,
};
pub use subset_axiom::recognize_subset_theory_lemma;
mod fp_bounded;
pub use fp_bounded::{
    recognize_fp_classification, recognize_fp_classification_op, recognize_fp_rounding_mode_domain,
};
mod fp_forward_error;
pub use fp_forward_error::recognize_fp_forward_error;
mod fp_ground;
pub use fp_ground::recognize_fp_ground_eval;
pub(crate) use fp_ground::FP_GROUND_WORK_LIMIT;
mod fp_to_bv;
mod ground_evaluate;
pub use ground_evaluate::recognize_ground_evaluate;
pub(crate) use ground_evaluate::validate_ground_evaluate as validate_ground_evaluate_for_printer;
mod lia;
mod lra_farkas;
pub(crate) use lra_farkas::uses_progress_metered_path as farkas_uses_progress_meter;
pub(crate) mod quantifier;
mod resolution;
mod string_axiom;
mod string_ground;
mod string_length_identity;
pub use string_length_identity::recognize_string_length_lemma;
mod string_word_identity;
use ay_core::{
    AletheRule, FarkasAnnotation, LiaAnnotation, Proof, ProofId, ProofStep, TermId, TermStore,
    TheoryLemmaKind,
};
use euf::{validate_euf_congruent, validate_euf_congruent_pred, validate_euf_transitive};
pub(crate) use euf_step_rules::validate_symm;
use euf_step_rules::{validate_cong, validate_refl, validate_trans};
#[cfg(test)]
pub(crate) use nra_poly::{
    generic_rational_scratch_bytes, GENERIC_MONOMIAL_BYTES, GENERIC_MONOMIAL_WORK,
};
use quantifier::{validate_negated_exists_dual as qdual, validate_qnt_neg_exists as qne};
use resolution::{is_valid_binary_resolution, is_valid_rup_step, validate_resolution_rule};
pub use string_word_identity::{
    recognize_string_concat_cancellation, recognize_string_containment_identity,
    recognize_string_ground_factor_conflict,
};
use thiserror::Error;
/// Validation failure returned by [`check_proof`].
#[derive(Debug, Error, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofCheckError {
    /// A caller-owned aggregate proof-validation resource envelope refused a
    /// charge: the check needs more work or bytes than the caller reserved.
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

/// Validate proof structure: premise linkage, resolution, DRUP, and terminal empty clause.
/// Theory lemmas and trust-style rules are treated as axioms in this mode.
pub fn check_proof(proof: &Proof, terms: &TermStore) -> Result<(), ProofCheckError> {
    if proof.steps.is_empty() {
        return Err(ProofCheckError::EmptyProof);
    }

    debug_assert!(
        u32::try_from(proof.steps.len()).is_ok(),
        "BUG: proof has {} steps, exceeding ProofId(u32) capacity",
        proof.steps.len()
    );

    let mut derived_clauses: Vec<Option<Vec<TermId>>> = Vec::with_capacity(proof.steps.len());
    for (idx, step) in proof.steps.iter().enumerate() {
        validate_step(
            terms,
            &mut derived_clauses,
            ProofId(idx as u32),
            step,
            false,
            None,
        )?;
    }

    ensure_terminal_empty_clause(&derived_clauses)
}

/// Strict structural validation of `proof` that **defers** (rather than rejects)
/// `AletheRule::Trust` steps, returning the deferred trust clauses for an
/// independent semantic discharge.
///
/// Every non-trust step is validated at the full strict boundary (identical to
/// [`crate::check_proof_strict`]): any non-trust strict failure returns `Err`.
/// Each `AletheRule::Trust` step is recorded as `(step_id, clause.clone())` and
/// its conclusion clause is admitted into the derived-clause table so that
/// downstream resolution/DRUP linkage still type-checks — exactly as the
/// non-strict checker treats a trust step as an axiom. On success the returned
/// `Vec` lists every deferred trust clause; the caller MUST independently
/// re-discharge each one (e.g. via the BV / array semantic checkers) and accept
/// the proof ONLY if every collected clause is a genuine theory tautology.
/// Returning `Ok(vec![])` means the proof is fully strict-valid with no trust
/// steps at all.
///
/// This is fail-closed by construction: a caller that ignores the returned
/// clauses gains nothing (it would have to treat them as unverified), and a
/// caller that discharges them gains acceptance ONLY for clauses an independent
/// solver run confirms UNSAT-on-negation.
pub fn check_proof_collecting_trust(
    proof: &Proof,
    terms: &TermStore,
) -> Result<Vec<(ProofId, Vec<TermId>)>, ProofCheckError> {
    check_proof_collecting_trust_with_context(proof, terms, None, None, None)
}

/// As [`check_proof_collecting_trust`], but with the full declaration and
/// authored-assertion context used by [`crate::check_proof_strict_with_context`].
///
/// This compatibility form carries name registries for API stability but does
/// not authorize datatype lemmas without exact member signatures; use
/// [`check_proof_collecting_trust_with_typed_context`] for datatype authority.
/// `problem_assertions` allows [`ExtDiffRegistry`] to authenticate every
/// `TheoryLemmaKind::ArrayExtensionality` witness against the proof's
/// `array_ext_diff_intro` definitions and the problem's authored symbols.
/// Passing `None` for the problem assertions keeps array extensionality
/// fail-closed because witness freshness cannot then be established.
///
/// Only explicit trust steps (and trust-kind generic theory lemmas) are
/// deferred and returned to the caller. Every other step, including every
/// context-dependent theory lemma, must pass the same strict validation used
/// by [`crate::check_proof_strict_with_context`]. The caller MUST independently
/// discharge every returned clause before accepting the proof.
pub fn check_proof_collecting_trust_with_context(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    problem_assertions: Option<&[TermId]>,
) -> Result<Vec<(ProofId, Vec<TermId>)>, ProofCheckError> {
    check_proof_collecting_trust_with_context_impl(
        proof,
        terms,
        dt_decls,
        ctor_selectors,
        None,
        problem_assertions,
    )
}

/// Typed-context form of [`check_proof_collecting_trust_with_context`].
///
/// The exact member table is globally cross-checked against both datatype
/// registries and every constructor/selector/tester occurrence in `terms`
/// before any trust step may be collected.
pub fn check_proof_collecting_trust_with_typed_context(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    datatype_member_signatures: &[DatatypeMemberSignature],
    problem_assertions: Option<&[TermId]>,
) -> Result<Vec<(ProofId, Vec<TermId>)>, ProofCheckError> {
    check_proof_collecting_trust_with_context_impl(
        proof,
        terms,
        dt_decls,
        ctor_selectors,
        Some(datatype_member_signatures),
        problem_assertions,
    )
}

fn check_proof_collecting_trust_with_context_impl(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    datatype_member_signatures: Option<&[DatatypeMemberSignature]>,
    problem_assertions: Option<&[TermId]>,
) -> Result<Vec<(ProofId, Vec<TermId>)>, ProofCheckError> {
    if proof.steps.is_empty() {
        return Err(ProofCheckError::EmptyProof);
    }

    if let Some(signatures) = datatype_member_signatures {
        validate_datatype_signature_context(terms, dt_decls, ctor_selectors, signatures)?;
    }

    validate_expensive_bv_budget(proof, terms)?;

    if let Some(assertions) = problem_assertions {
        validate_problem_assumptions(proof, terms, assertions)?;
    }

    // Build the provenance registry before validating any step, exactly as
    // strict-with-context does. This rejects malformed, duplicate, cyclic, or
    // non-fresh introductions even when no extensionality lemma cites them.
    let ext_diff = match problem_assertions {
        Some(assertions) => Some(ExtDiffRegistry::collect(proof, terms, assertions)?),
        None => None,
    };
    // Same provenance discipline: built once from the PROBLEM, `None` without
    // it so `SetCardEmptyByAssertion` fails closed.
    let empty_sets =
        problem_assertions.map(|assertions| EmptySetRegistry::collect(terms, assertions));

    let mut derived_clauses: Vec<Option<Vec<TermId>>> = Vec::with_capacity(proof.steps.len());
    let mut collected: Vec<(ProofId, Vec<TermId>)> = Vec::new();

    for (idx, step) in proof.steps.iter().enumerate() {
        validate_step_with_datatypes(
            terms,
            &mut derived_clauses,
            ProofId(idx as u32),
            step,
            true,
            dt_decls,
            ctor_selectors,
            datatype_member_signatures,
            ext_diff.as_ref(),
            empty_sets.as_ref(),
            Some(&mut collected),
        )?;
    }

    quantifier::validate_sko_forall_uniqueness(proof, terms)?;
    ensure_terminal_empty_clause(&derived_clauses)?;
    Ok(collected)
}

pub(crate) fn validate_problem_assumptions(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
) -> Result<(), ProofCheckError> {
    let mut allowed: ay_core::kani_compat::DetHashSet<TermId> =
        problem_assertions.iter().copied().collect();
    let mut expanded = ay_core::kani_compat::DetHashSet::default();
    let mut stack = problem_assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !expanded.insert(term) {
            continue;
        }
        let ay_core::term::TermData::App(ay_core::Symbol::Named(name), args) = terms.get(term)
        else {
            continue;
        };
        if name != "and" {
            continue;
        }
        for &arg in args {
            allowed.insert(arg);
            stack.push(arg);
        }
    }
    for (index, step) in proof.steps.iter().enumerate() {
        if let ProofStep::Assume(term) = step {
            if !allowed.contains(term) {
                return Err(ProofCheckError::UnauthorizedAssumption {
                    step: ProofId(index as u32),
                    term: *term,
                });
            }
        }
    }
    Ok(())
}

/// Crate-internal re-export of the extensionality validator so the whole-proof
/// provenance pass in `quality.rs` re-uses the EXACT per-step check strict mode
/// applies — one implementation, no drift between the two acceptance paths.
/// Crate-internal re-export of the diff-witness introduction shape check for
/// the Alethe printer, so a malformed introduction is a typed print error
/// rather than a silently-rendered comment.
pub(crate) fn validate_ext_diff_intro_for_printer(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    premises: &[ProofId],
    args: &[TermId],
) -> Result<(), ProofCheckError> {
    array_axiom::validate_ext_diff_intro(terms, step_id, clause, premises, args).map(|_| ())
}

pub(crate) fn validate_array_extensionality_for_provenance(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    registry: Option<&ExtDiffRegistry>,
) -> Result<(), ProofCheckError> {
    array_axiom::validate_array_extensionality(terms, step_id, clause, registry)
}

pub(crate) fn validate_step(
    terms: &TermStore,
    derived_clauses: &mut Vec<Option<Vec<TermId>>>,
    step_id: ProofId,
    step: &ProofStep,
    strict: bool,
    // When `Some` AND a strict `AletheRule::Trust` step is encountered, the step
    // is DEFERRED (its clause is collected here and admitted as an axiom) instead
    // of being rejected. The collected clauses MUST be independently discharged
    // by the caller; this is never an unconditional accept.
    trust_collector: Option<&mut Vec<(ProofId, Vec<TermId>)>>,
) -> Result<(), ProofCheckError> {
    validate_step_with_datatypes(
        terms,
        derived_clauses,
        step_id,
        step,
        strict,
        None,
        None,
        None,
        None,
        None,
        trust_collector,
    )
}

/// As [`validate_step`], but with the datatype constructor registry threaded in
/// so strict mode can validate `TheoryLemmaKind::DatatypeDistinct` lemmas.
///
/// Runtime datatype terms carry `Sort::Uninterpreted`, so the checker cannot
/// recover constructor membership from the `TermStore` alone — the executor
/// supplies the `declare-datatype` declarations explicitly. When `dt_decls` is
/// `None`, datatype-distinctness lemmas fail closed in strict mode.
///
/// `datatype_member_signatures.is_some()` is only a dispatch marker here. The
/// caller MUST have run [`validate_datatype_signature_context`] over this exact
/// `TermStore` and exact registry slices first. This covers both datatype
/// lemmas and finite-array schemas over an enum index. All production callers
/// satisfy that precondition through the public typed whole-proof entry points;
/// direct calls are crate-private validator-shape tests and confer no proof
/// authority.
#[allow(clippy::too_many_arguments)]
pub(crate) fn validate_step_with_datatypes(
    terms: &TermStore,
    derived_clauses: &mut Vec<Option<Vec<TermId>>>,
    step_id: ProofId,
    step: &ProofStep,
    strict: bool,
    dt_decls: Option<datatype_axiom::DatatypeDecls<'_>>,
    ctor_selectors: Option<datatype_axiom::SelectorDecls<'_>>,
    datatype_member_signatures: Option<&[DatatypeMemberSignature]>,
    // Whole-proof extensionality diff-witness provenance, built once by the
    // caller from the proof's `array_ext_diff_intro` steps and the PROBLEM's
    // assertions. `None` (no problem assertion set available) keeps
    // `TheoryLemmaKind::ArrayExtensionality` fail-closed.
    ext_diff: Option<&ExtDiffRegistry>,
    // Problem-derived registry of sets asserted empty; `None` keeps
    // `SetCardEmptyByAssertion` fail-closed.
    empty_sets: Option<&EmptySetRegistry>,
    // Deferred-trust recovery (see [`validate_step`]): when `Some`, a strict
    // `Trust` step is collected for independent discharge instead of rejected.
    trust_collector: Option<&mut Vec<(ProofId, Vec<TermId>)>>,
) -> Result<(), ProofCheckError> {
    let mut unbounded = |_: usize, _: usize| true;
    validate_step_with_datatypes_and_progress(
        terms,
        derived_clauses,
        step_id,
        step,
        strict,
        dt_decls,
        ctor_selectors,
        datatype_member_signatures,
        ext_diff,
        empty_sets,
        trust_collector,
        &mut unbounded,
    )
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn validate_step_with_datatypes_and_progress(
    terms: &TermStore,
    derived_clauses: &mut Vec<Option<Vec<TermId>>>,
    step_id: ProofId,
    step: &ProofStep,
    strict: bool,
    dt_decls: Option<datatype_axiom::DatatypeDecls<'_>>,
    ctor_selectors: Option<datatype_axiom::SelectorDecls<'_>>,
    datatype_member_signatures: Option<&[DatatypeMemberSignature]>,
    ext_diff: Option<&ExtDiffRegistry>,
    empty_sets: Option<&EmptySetRegistry>,
    trust_collector: Option<&mut Vec<(ProofId, Vec<TermId>)>>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    debug_assert_eq!(
        step_id.0 as usize,
        derived_clauses.len(),
        "BUG: step_id {} does not match derived_clauses index {}",
        step_id.0,
        derived_clauses.len()
    );
    match step {
        ProofStep::Assume(term) => derived_clauses.push(Some(vec![*term])),
        ProofStep::TheoryLemma {
            clause,
            kind,
            farkas,
            lia,
            ..
        } => validate_theory_lemma(
            terms,
            derived_clauses,
            step_id,
            clause,
            farkas.as_ref(),
            *kind,
            lia.as_ref(),
            strict,
            dt_decls,
            ctor_selectors,
            datatype_member_signatures,
            ext_diff,
            empty_sets,
            trust_collector,
            progress,
        )?,
        // An `array_ext_diff_intro` is a DEFINITION, not an inference: it
        // records that a fresh symbol is the extensionality difference witness
        // for one array pair. It is validated for shape here and recorded as
        // producing NO clause (like an `anchor`), so it can never be resolved
        // against, never seed a RUP check, and never be mistaken for a derived
        // empty clause. The provenance conditions that make it MEAN anything
        // (freshness, bound-once) are whole-proof and live in
        // `ExtDiffRegistry::collect`.
        ProofStep::Step {
            rule: AletheRule::ArrayExtDiffIntro,
            clause,
            premises,
            args,
        } => {
            let _binding =
                array_axiom::validate_ext_diff_intro(terms, step_id, clause, premises, args)?;
            derived_clauses.push(None);
        }
        ProofStep::Resolution {
            clause,
            pivot,
            clause1,
            clause2,
        } => validate_resolution_step(
            terms,
            derived_clauses,
            step_id,
            clause,
            *pivot,
            *clause1,
            *clause2,
        )?,
        ProofStep::Step {
            rule,
            clause,
            premises,
            args,
        } => validate_alethe_step(
            terms,
            derived_clauses,
            step_id,
            rule,
            clause,
            premises,
            args,
            strict,
            trust_collector,
            progress,
        )?,
        ProofStep::Anchor { .. } => derived_clauses.push(None),
        _ => unreachable!("unexpected ProofStep variant"),
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn validate_alethe_step(
    terms: &TermStore,
    derived_clauses: &mut Vec<Option<Vec<TermId>>>,
    step_id: ProofId,
    rule: &AletheRule,
    clause: &[TermId],
    premises: &[ProofId],
    args: &[TermId],
    strict: bool,
    mut trust_collector: Option<&mut Vec<(ProofId, Vec<TermId>)>>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    // `Hole` belongs here alongside `Trust`. AY treats the two as one family:
    // a hole carries an obligation, not a placeholder. In deferred-trust mode
    // collect that obligation; plain strict mode keeps it a hard rejection.
    let deferrable = strict && matches!(rule, AletheRule::Trust | AletheRule::Hole);
    if deferrable {
        match &mut trust_collector {
            Some(collector) => collector.push((step_id, clause.to_vec())),
            None => {
                return Err(match rule {
                    AletheRule::Hole => ProofCheckError::HoleStep { step: step_id },
                    _ => ProofCheckError::TrustStep { step: step_id },
                })
            }
        }
    }
    validate_generic_step(
        terms,
        derived_clauses,
        step_id,
        rule,
        clause,
        premises,
        args,
        strict,
        // Only a hole that was collected may skip its own rejection.
        deferrable && trust_collector.is_some(),
        progress,
    )
}

#[allow(clippy::too_many_arguments)]
fn validate_theory_lemma(
    terms: &TermStore,
    derived_clauses: &mut Vec<Option<Vec<TermId>>>,
    step_id: ProofId,
    clause: &[TermId],
    farkas: Option<&FarkasAnnotation>,
    kind: TheoryLemmaKind,
    lia_ann: Option<&LiaAnnotation>,
    strict: bool,
    dt_decls: Option<datatype_axiom::DatatypeDecls<'_>>,
    ctor_selectors: Option<datatype_axiom::SelectorDecls<'_>>,
    datatype_member_signatures: Option<&[DatatypeMemberSignature]>,
    ext_diff: Option<&ExtDiffRegistry>,
    // Problem-derived registry of sets asserted empty. `None` keeps
    // `TheoryLemmaKind::SetCardEmptyByAssertion` fail-closed, exactly as a
    // `None` `ext_diff` does for array extensionality.
    empty_sets: Option<&EmptySetRegistry>,
    // When `Some` AND a strict trust-kind (`Generic`) theory lemma is encountered,
    // the lemma is DEFERRED (its clause collected for independent re-discharge)
    // instead of rejected — the theory-lemma analogue of the `Step{rule:Trust}`
    // deferral. The caller MUST re-discharge every collected clause.
    trust_collector: Option<&mut Vec<(ProofId, Vec<TermId>)>>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    if strict {
        // C3 EUF/DT authority comes from the clause and datatype registries.
        // Reject unused payload before other layers assign it new meanings.
        if (farkas.is_some() || lia_ann.is_some())
            && matches!(
                kind,
                TheoryLemmaKind::EufTransitive
                    | TheoryLemmaKind::EufReflexive
                    | TheoryLemmaKind::EufCongruent
                    | TheoryLemmaKind::EufCongruentPred
                    | TheoryLemmaKind::DatatypeDistinct
                    | TheoryLemmaKind::DatatypeEnumPigeonhole
                    | TheoryLemmaKind::DatatypeSelectorProject
                    | TheoryLemmaKind::DatatypeTesterEval
                    | TheoryLemmaKind::ArrayFiniteExtensionality
                    | TheoryLemmaKind::ArrayFiniteSelectExpansion
                    | TheoryLemmaKind::QuantifierNegatedExistsDual
            )
        {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: format!("{kind:?} must not carry unrelated Farkas/LIA evidence"),
            });
        }
        match kind {
            TheoryLemmaKind::EufTransitive => {
                validate_euf_transitive(terms, step_id, clause)?;
            }
            // Reflexivity is checked by the same routine that backs the
            // `eq_reflexive` Alethe rule: exactly one literal, a binary
            // equality, and both sides the SAME term. Nothing about the
            // conflict that produced it is taken on trust.
            TheoryLemmaKind::EufReflexive => {
                boolean_derived::validate_eq_reflexive(terms, step_id, clause)?;
            }
            TheoryLemmaKind::EufCongruent => {
                validate_euf_congruent(terms, step_id, clause)?;
            }
            TheoryLemmaKind::EufCongruentPred => {
                validate_euf_congruent_pred(terms, step_id, clause)?;
            }
            TheoryLemmaKind::LraFarkas => {
                lra_farkas::validate_metered(terms, step_id, clause, farkas, progress)?;
            }
            TheoryLemmaKind::LiaGeneric => {
                lia::validate_metered(terms, step_id, clause, farkas, lia_ann, progress)?;
            }
            TheoryLemmaKind::LiaModRange => {
                ay_core::proof_validation::validate_lia_mod_range(terms, clause).map_err(|e| {
                    ProofCheckError::InvalidTheoryLemma {
                        step: step_id,
                        reason: e.to_string(),
                    }
                })?;
            }
            TheoryLemmaKind::QuantifierNegatedExistsDual => qdual(terms, step_id, clause)?,
            TheoryLemmaKind::BvLiaTautology => {
                bv_lia_query::validate_bv_lia_tautology(
                    terms,
                    step_id,
                    clause,
                    farkas.is_some(),
                    lia_ann.is_some(),
                )?;
            }
            TheoryLemmaKind::SeqExtensionalCompanionContradiction => {
                seq_extensional_companion::validate(terms, step_id, clause)?;
            }
            // BV bit-blast lemmas: bounded semantic validation (#8820).
            // The previous checker accepted any non-empty clause, which let a
            // forged proof label arbitrary Boolean literals as a bit-blast
            // lemma. `validate_bv_bitblast` enforces:
            //  - every literal is Boolean-sorted;
            //  - the clause mentions at least one bitvector sub-term;
            //  - for `BvBitBlastGate`, the clause references the declared
            //    operator (`bvand`, `bvadd`, etc.).
            // Full proof-bitblaster coverage is still future work (#8071), so
            // strict mode fails closed for unsupported/too-wide clauses.
            TheoryLemmaKind::BvBitBlast => {
                bv_bitblast::validate_bv_bitblast(terms, step_id, clause, None)?;
            }
            // Boolean tautology: a propositional clause true under every bounded
            // assignment (e.g. `(= (not (not p)) p)`). Validated by the same
            // exhaustive bounded evaluator, without the bit-blast BV-content gate.
            TheoryLemmaKind::BoolTautology => {
                bv_bitblast::validate_bool_tautology(terms, step_id, clause)?;
            }
            TheoryLemmaKind::ArithEqTriangle => {
                lia::validate_arith_eq_triangle(terms, step_id, clause)?;
            }
            TheoryLemmaKind::ArithEqImpliesBound => {
                lia::validate_arith_eq_implies_bound(terms, step_id, clause)?;
            }
            TheoryLemmaKind::IntBoundsTautology => {
                lia::validate_int_bounds_tautology(terms, step_id, clause)?;
            }
            TheoryLemmaKind::ArithDisequalitySplit => {
                lia::validate_arith_disequality_split(terms, step_id, clause)?;
            }
            // If-then-else with identical branches: `(= (ite c x x) x)` — a
            // syntactic axiom valid for any condition and any sort of x.
            TheoryLemmaKind::IteSame => {
                ite_axiom::validate_ite_same(terms, step_id, clause)?;
            }
            // Exact bounded decision procedure for formulas whose numeric
            // terms are pure `ite` trees selecting Int/Real variables.  The
            // checker enumerates one representative of every total preorder;
            // anything outside that fragment fails closed.
            TheoryLemmaKind::OrderIteTautology => {
                order_ite::validate_order_ite_tautology(terms, step_id, clause)?;
            }
            TheoryLemmaKind::FpClassification { .. } => {
                fp_bounded::validate_fp_classification(terms, step_id, clause)?;
            }
            TheoryLemmaKind::FpRoundingModeDomain => {
                fp_bounded::validate_fp_rounding_mode_domain(terms, step_id, clause)?;
            }
            // Exact IEEE-754 evaluation (`fp_ground`): the clause is TRUE under
            // every assignment of whatever variables survive its own ground
            // bindings, decided by an INDEPENDENT correctly-rounded
            // integer/rational kernel — not by `f64`, and not by the solver's
            // evaluator. This is a full semantic validation rather than a
            // schema check; unsupported operators, unbounded variable domains
            // and budget exhaustion all fail closed.
            TheoryLemmaKind::FpGroundEval => {
                fp_ground::validate_fp_ground_eval(terms, step_id, clause)?;
            }
            TheoryLemmaKind::RoundingModeDomain => {
                rounding_mode::validate_rounding_mode_domain(terms, step_id, clause)?;
            }
            // FP forward-error lemma: the clause is the disjunction of the
            // NEGATED premises of a rounding-error refutation. The validator
            // independently re-derives the whole analysis from the clause —
            // fact mining, RNE/no-overflow side conditions, exact-rational
            // half-ulp enclosure propagation, mirror-polynomial identity, and
            // the strict claim contradiction — failing closed on anything
            // unrecognized.
            TheoryLemmaKind::FpForwardError => {
                fp_forward_error::validate_fp_forward_error(terms, step_id, clause)?;
            }
            TheoryLemmaKind::BvBitBlastGate { gate_type, width } => {
                bv_bitblast::validate_bv_bitblast(
                    terms,
                    step_id,
                    clause,
                    Some((gate_type, width)),
                )?;
            }
            // Array theory lemmas: semantic ROW validation (#8820).
            //
            // Enforces that read-over-write clauses mention
            // `(select (store ...) ...)` and that the negative case carries a
            // disequality between the indices. Extensionality clauses are
            // handled separately below: their soundness is provenance, not
            // shape, so they need the `ext_diff` registry.
            TheoryLemmaKind::ArraySelectStore { index_eq } => {
                array_axiom::validate_array_select_store(terms, step_id, clause, index_eq)?;
            }
            // n-ary store-commutativity and chain read-over-write: exact
            // schemas with fully-checked side conditions (see array_axiom.rs).
            TheoryLemmaKind::ArrayStorePermutation => {
                array_axiom::validate_array_store_permutation(terms, step_id, clause, progress)?;
            }
            TheoryLemmaKind::ArrayRowChain => {
                array_axiom::validate_array_row_chain(terms, step_id, clause, progress)?;
            }
            TheoryLemmaKind::ArrayDefaultConst => {
                array_axiom::validate_array_default_const(terms, step_id, clause)?;
            }
            TheoryLemmaKind::SetCardNonNegative => {
                set_axiom::validate_set_card_non_negative(terms, step_id, clause)?;
            }
            TheoryLemmaKind::SetCardMemberLowerBound => {
                set_axiom::validate_set_card_member_lower_bound(terms, step_id, clause)?;
            }
            TheoryLemmaKind::SetCardEmpty => {
                set_axiom::validate_set_card_empty(terms, step_id, clause)?;
            }
            TheoryLemmaKind::SetCardMemberCount => {
                set_axiom::validate_set_card_member_count(terms, step_id, clause)?;
            }
            TheoryLemmaKind::SetCardEmptyByAssertion => {
                set_axiom::validate_set_card_empty_by_assertion(
                    terms, step_id, clause, empty_sets,
                )?;
            }
            // Definitional set-cardinality recurrence over an EMPTY-ROOTED
            // store chain. The empty root confines the schema to the finite
            // fragment and is established by a walk of its own -- the
            // membership walk short-circuits at the probed index and can
            // answer without ever seeing the root. See set_card_chain.rs.
            TheoryLemmaKind::SetCardChainRecurrence => {
                set_card_chain::validate_set_card_chain_recurrence(terms, step_id, clause)?;
            }
            // Collection subset schemas: universally valid, re-derived from
            // the clause alone (exact operand identity, native array
            // signature, carrier element sort). See subset_axiom.rs.
            TheoryLemmaKind::SubsetReflexive => {
                subset_axiom::validate_subset_reflexive(terms, step_id, clause)?;
            }
            TheoryLemmaKind::SubsetElementInstance => {
                subset_axiom::validate_subset_element_instance(terms, step_id, clause)?;
            }
            // Transitivity of one collection subset predicate: the chain is
            // re-derived from the clause, so a triple that does not connect is
            // refused. See subset_axiom.rs.
            TheoryLemmaKind::SubsetTransitive => {
                subset_axiom::validate_subset_transitive(terms, step_id, clause)?;
            }
            // One subset atom DECIDED EXACTLY on ground carriers, under the
            // clause's own ground bindings. This is a full semantic decision
            // rather than a schema check: an unrecognized carrier, an unbound
            // operand the decision needs, or a polarity the pointwise decision
            // contradicts all fail closed. See subset_axiom.rs.
            TheoryLemmaKind::SubsetGroundEval => {
                subset_axiom::validate_subset_ground_eval(terms, step_id, clause)?;
            }
            // Skolemized extensionality: NOT a tautology, so shape alone can
            // never license it. Accepted only against the whole-proof
            // `array_ext_diff_intro` provenance registry; `None` (the caller
            // had no problem assertion set to check freshness against) fails
            // closed exactly as this kind always did.
            TheoryLemmaKind::ArrayExtensionality => {
                array_axiom::validate_array_extensionality(terms, step_id, clause, ext_diff)?;
            }
            // Complete finite-carrier array schemas. Unlike Skolemized
            // extensionality, these are theory tautologies and need no witness
            // provenance: the checker independently enumerates the entire
            // carrier from Bool/BV sorts or authenticated nullary constructors.
            TheoryLemmaKind::ArrayFiniteExtensionality => {
                array_finite::validate_array_finite_extensionality(
                    terms,
                    step_id,
                    clause,
                    dt_decls,
                    ctor_selectors,
                    datatype_member_signatures,
                )?;
            }
            TheoryLemmaKind::ArrayFiniteSelectExpansion => {
                array_finite::validate_array_finite_select_expansion(
                    terms,
                    step_id,
                    clause,
                    dt_decls,
                    ctor_selectors,
                    datatype_member_signatures,
                )?;
            }
            // FP→BV lemmas: fail-closed until semantic lowering exists (#8820).
            //
            // Enforces the cheap schema checks first, then rejects because
            // strict IEEE 754 re-verification against the BV circuit is #8075.
            TheoryLemmaKind::FpToBv { operation } => {
                fp_to_bv::validate_fp_to_bv(terms, step_id, clause, operation)?;
            }
            // String theory lemmas: fail-closed semantic validation (#8820).
            //
            // Length lemmas pass only when statically proven true. Content and
            // normal-form lemmas reject until full semantic validation exists
            // (#8074).
            TheoryLemmaKind::StringLengthAxiom => {
                string_axiom::validate_string_length_axiom(terms, step_id, clause)?;
            }
            // Universally-valid str.len theorem over symbolic subjects
            // (#selfcert-strlen): the clause carries a certified length identity
            // (concat-length sum, empty↔zero-length, non-negativity,
            // constant-length, equal-length congruence, or containment bound).
            // The INDEPENDENT structural checker re-derives the exact algebraic
            // identity and fails closed on any near-miss, so the injected length
            // axioms can carry a checkable rule instead of a bare foreign assume.
            TheoryLemmaKind::StringLengthLemma => {
                string_length_identity::validate_string_length_lemma(terms, step_id, clause)?;
            }
            TheoryLemmaKind::StringContentAxiom => {
                string_axiom::validate_string_content_axiom(terms, step_id, clause)?;
            }
            TheoryLemmaKind::StringNormalForm => {
                string_axiom::validate_string_normal_form(terms, step_id, clause)?;
            }
            // Ground string/regex evaluation (#8074 ground fragment): the
            // clause carries a literal whose leaves are all constants and
            // which the INDEPENDENT ground evaluator proves TRUE. A clause
            // with a true literal is a tautology, so this is a full semantic
            // validation — not a schema check. Fail-closed on anything the
            // evaluator cannot decide outright.
            TheoryLemmaKind::StringGroundEval => {
                string_ground::validate_string_ground_eval(terms, step_id, clause)?;
            }
            // Regex intersection-emptiness over a SYMBOLIC subject (#regex-cert):
            // the clause carries a `str.in_re` literal group over one common
            // term whose jointly-denied intersection is EMPTY, so no value of
            // the term falsifies the group and the clause is a tautology. The
            // INDEPENDENT derivative-product checker re-derives the whole
            // reachability argument — verified total alphabet partition,
            // closure, non-acceptance — and fails closed on anything it cannot
            // establish outright.
            TheoryLemmaKind::RegexIntersectEmpty => {
                regex_empty::validate_regex_intersect_empty(terms, step_id, clause)?;
            }
            // Universally-valid containment/order identity over a SYMBOLIC
            // subject: self-containment/prefix/suffix, `str.<=` reflexivity,
            // `str.<` irreflexivity, or an empty-word containment. The
            // INDEPENDENT structural checker re-derives the exact theorem —
            // the two positions must hold the SAME term, or the empty-string
            // constant in the operator's own contained-word position — and
            // fails closed on every near-miss.
            TheoryLemmaKind::StringContainmentIdentity => {
                string_word_identity::validate_string_containment_identity(terms, step_id, clause)?;
            }
            // Free-monoid cancellation for `str.++`: `u·w = v·w` forces
            // `u = v` and `w·u = w·v` forces `u = v`. The INDEPENDENT
            // structural checker re-derives the shared block and both
            // residuals from the clause alone; a block that is not
            // syntactically identical, sits at the wrong end, or does not
            // leave exactly the conclusion's two sides is rejected.
            TheoryLemmaKind::StringConcatCancellation => {
                string_word_identity::validate_string_concat_cancellation(terms, step_id, clause)?;
            }
            // A containment refuted by the GROUND blocks it names. The
            // INDEPENDENT factor scan re-derives the impossibility from the
            // clause's own constants — a ground block missing from a ground
            // container, or a ground pattern disagreeing with the container's
            // ground boundary block — and never reasons about the symbolic
            // parts.
            TheoryLemmaKind::StringGroundFactorConflict => {
                string_word_identity::validate_string_ground_factor_conflict(
                    terms, step_id, clause,
                )?;
            }
            // A regex membership bounding `str.len` below. The INDEPENDENT
            // compositional minimum-length computation re-derives the bound
            // from the ground regex tree and rejects `re.comp`, every
            // unmodelled operator, a non-ground leaf, a mismatched subject, and
            // any bound stronger than it can support.
            TheoryLemmaKind::RegexLengthLowerBound => {
                regex_length::validate_regex_length_lower_bound(terms, step_id, clause)?;
            }
            // Datatype constructor distinctness (#8419 / trust_count→0).
            //
            // `(not (= C1(..) C2(..)))` for two distinct constructors of the
            // same datatype is a tautology of datatype theory. The checker
            // cannot recover constructor membership from `TermStore` alone
            // (runtime datatype terms carry `Sort::Uninterpreted`), so the
            // executor supplies the `declare-datatype` registry. Without it
            // this kind fails closed rather than assuming distinctness by shape.
            TheoryLemmaKind::DatatypeDistinct => match (dt_decls, datatype_member_signatures) {
                (Some(decls), Some(_)) => {
                    datatype_axiom::validate_datatype_distinct(terms, step_id, clause, decls)?;
                }
                _ => {
                    return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                        step: step_id,
                        kind,
                    });
                }
            },
            // Finite-enum pigeonhole. Same fail-closed contract as the sibling
            // above: without the datatype registry the checker cannot establish
            // the constructor count or the nullarity the argument rests on, so
            // the kind is rejected rather than assumed.
            TheoryLemmaKind::DatatypeEnumPigeonhole => {
                match (dt_decls, datatype_member_signatures) {
                    (Some(decls), Some(_)) => {
                        datatype_axiom::validate_datatype_enum_pigeonhole(
                            terms,
                            step_id,
                            clause,
                            decls,
                            ctor_selectors,
                        )?;
                    }
                    _ => {
                        return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                            step: step_id,
                            kind,
                        });
                    }
                }
            }
            // Datatype selector projection (#trust-count→0).
            //
            // `(= (sel_i (C a_0 .. a_n)) a_i)` — reading field `i` of a
            // constructor application yields argument `i` — is a tautology of
            // datatype theory exactly when `sel_i` is `C`'s registered field-`i`
            // selector. The carrier sort is `Sort::Uninterpreted`, so the checker
            // is given the constructor→selector registry; without it this kind
            // fails closed rather than assuming the projection by shape.
            TheoryLemmaKind::DatatypeSelectorProject => {
                match (ctor_selectors, datatype_member_signatures) {
                    (Some(selectors), Some(_)) => {
                        datatype_axiom::validate_datatype_selector_project(
                            terms, step_id, clause, selectors,
                        )?;
                    }
                    _ => {
                        return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                            step: step_id,
                            kind,
                        });
                    }
                }
            }
            // Pure-NRA interval refutation (#nra-cert): the checker's OWN
            // bounded exact-rational interval propagation re-refutes the
            // negated clause from the terms alone — no payload, nothing to
            // forge. Fail-closed on any shape/degree/budget surprise.
            TheoryLemmaKind::NraIntervalUnsat => {
                nra_interval::validate_nra_interval_unsat(terms, step_id, clause)?;
            }
            // Pure-NRA univariate refutation (#nra-cert): the checker's OWN
            // exact Sturm-based cell decomposition re-decides the negated
            // one-variable system, algebraically correct at irrational roots
            // (the sqrt(2) trap). Fail-closed everywhere.
            TheoryLemmaKind::NraUnivariateUnsat => {
                nra_univariate::validate_nra_univariate_unsat(terms, step_id, clause)?;
            }
            TheoryLemmaKind::DatatypeTesterEval => match (dt_decls, datatype_member_signatures) {
                (Some(decls), Some(_)) => {
                    datatype_axiom::validate_datatype_tester_eval(
                        terms,
                        step_id,
                        clause,
                        decls,
                        ctor_selectors,
                        true,
                    )?;
                }
                _ => {
                    return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                        step: step_id,
                        kind,
                    });
                }
            },
            // Datatype constructor coverage (#trust-count→0, C5).
            //
            // `(is-C1 t) ∨ .. ∨ (is-Ck t)` over ALL declared constructors of
            // `t`'s datatype is a tautology of datatype theory — every value
            // is built by SOME constructor. The coverage list cannot be
            // recovered from the `TermStore` (carrier sorts are
            // `Sort::Uninterpreted`), so the executor supplies the registry;
            // without it this kind fails closed rather than trusting the
            // clause to have named every constructor.
            TheoryLemmaKind::DatatypeExhaustive => match (dt_decls, datatype_member_signatures) {
                (Some(decls), Some(_)) => {
                    datatype_axiom::validate_datatype_exhaustive(terms, step_id, clause, decls)?;
                }
                _ => {
                    return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                        step: step_id,
                        kind,
                    });
                }
            },
            // Guarded datatype constructor reconstruction (#trust-count→0, C5).
            //
            // `(not (is-C t)) ∨ (= t (C (sel_1 t) .. (sel_k t)))` is a
            // tautology exactly when `sel_1 .. sel_k` is `C`'s FULL declared
            // selector list in declared field order. Both the constructor
            // registry (tester authentication, sort matching) and the
            // constructor→selector registry (field list + order + nullarity)
            // are required; without either this kind fails closed.
            TheoryLemmaKind::DatatypeConstructorReconstruct => {
                match (dt_decls, ctor_selectors, datatype_member_signatures) {
                    (Some(decls), Some(selectors), Some(_)) => {
                        datatype_axiom::validate_datatype_constructor_reconstruct(
                            terms, step_id, clause, decls, selectors,
                        )?;
                    }
                    _ => {
                        return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                            step: step_id,
                            kind,
                        });
                    }
                }
            }
            other => {
                // Retired non-trust kinds, including the inert datatype C5b
                // tags, intentionally reach the fail-closed rejection below.
                // Before falling back to deferral/rejection, try to VALIDATE the
                // lemma outright: an arithmetic conflict whose refutation is a
                // linear combination of equalities over the monomial basis is
                // fully checkable here, and that is the dominant `Generic` shape
                // (loop-invariant consecution, where the nonlinear monomials
                // cancel). This only ever ACCEPTS what the checker reconstructs
                // itself — the lemma carries no payload to forge — and any other
                // outcome falls through to the pre-existing fail-closed handling
                // below, so nothing that used to be rejected becomes trusted.
                if other.is_trust() {
                    match nia_linear_ideal::validate_linear_ideal_refutation_with_progress(
                        terms, step_id, clause, progress,
                    ) {
                        Ok(()) => {
                            derived_clauses.push(Some(clause.to_vec()));
                            return Ok(());
                        }
                        Err(ProofCheckError::ResourceLimit) => {
                            return Err(ProofCheckError::ResourceLimit);
                        }
                        Err(_) => {}
                    }
                }
                // A trust-kind (`Generic`) theory lemma has no dedicated strict
                // validator (e.g. an integer-arithmetic lemma over an `ite` whose
                // proof is not Farkas-pure, so no typed LIA validator can discharge
                // it). In DEFERRED-trust mode (collector present) record its clause
                // for independent re-discharge and fall through to admit it —
                // exactly like a `Step{rule:Trust}`. In plain strict mode it stays
                // a hard rejection.
                match (other.is_trust(), trust_collector) {
                    (true, Some(collector)) => collector.push((step_id, clause.to_vec())),
                    _ => {
                        return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                            step: step_id,
                            kind: other,
                        });
                    }
                }
            }
        }
    }
    derived_clauses.push(Some(clause.to_vec()));
    Ok(())
}

fn validate_resolution_step(
    terms: &TermStore,
    derived_clauses: &mut Vec<Option<Vec<TermId>>>,
    step_id: ProofId,
    clause: &[TermId],
    pivot: TermId,
    clause1: ProofId,
    clause2: ProofId,
) -> Result<(), ProofCheckError> {
    let premise1 = premise_clause(derived_clauses, step_id, clause1)?;
    let premise2 = premise_clause(derived_clauses, step_id, clause2)?;

    if !is_valid_binary_resolution(terms, premise1, premise2, clause, Some(pivot)) {
        return Err(ProofCheckError::InvalidResolution {
            step: step_id,
            rule: AletheRule::Resolution.name().to_string(),
        });
    }

    derived_clauses.push(Some(clause.to_vec()));
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn validate_generic_step(
    terms: &TermStore,
    derived_clauses: &mut Vec<Option<Vec<TermId>>>,
    step_id: ProofId,
    rule: &AletheRule,
    clause: &[TermId],
    premises: &[ProofId],
    args: &[TermId],
    strict: bool,
    // The caller collected this step's clause for independent discharge, so the
    // by-name rejection below must not fire. Never set without a collector.
    deferred: bool,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let premise_clauses: Vec<&[TermId]> = premises
        .iter()
        .map(|premise| premise_clause(derived_clauses, step_id, *premise))
        .collect::<Result<_, _>>()?;

    match rule {
        // Alethe resolution is N-ARY (#dt-premise-binding). Arity 2 keeps the
        // binary check verbatim; other arities fold the chain, which is what
        // lets emitters replace an O(n^2)-text binary triangle with one step.
        AletheRule::Resolution | AletheRule::ThResolution => validate_resolution_rule(
            terms,
            step_id,
            rule,
            clause,
            &premise_clauses,
            args,
            progress,
        )?,
        AletheRule::Drup => {
            if !is_valid_rup_step(terms, clause, derived_clauses) {
                return Err(ProofCheckError::InvalidDrup { step: step_id });
            }
        }
        AletheRule::Hole if !deferred => return Err(ProofCheckError::HoleStep { step: step_id }),
        AletheRule::Hole | AletheRule::Trust => {}
        AletheRule::AndPos(i) if strict => {
            boolean::validate_and_pos(terms, step_id, clause, *i, args.first().copied())?;
        }
        AletheRule::AndNeg if strict => {
            boolean::validate_and_neg(terms, step_id, clause, args.first().copied())?;
        }
        AletheRule::OrPos(_) if strict => {
            boolean::validate_or_pos(terms, step_id, clause)?;
        }
        // Exact 0-variable validation rejects forged Tseitin constant units.
        AletheRule::True | AletheRule::False if strict => {
            bv_bitblast::validate_bool_tautology(terms, step_id, clause)?;
        }
        AletheRule::OrNeg if strict => {
            boolean::validate_or_neg(terms, step_id, clause)?;
        }
        AletheRule::ImpliesPos if strict => {
            boolean::validate_implies_pos(terms, step_id, clause)?;
        }
        AletheRule::ImpliesNeg1 if strict => {
            boolean::validate_implies_neg1(terms, step_id, clause)?;
        }
        AletheRule::ImpliesNeg2 if strict => {
            boolean::validate_implies_neg2(terms, step_id, clause)?;
        }
        AletheRule::EquivPos1 if strict => {
            boolean_derived::validate_equiv_pos1(terms, step_id, clause)?;
        }
        AletheRule::EquivPos2 if strict => {
            boolean_derived::validate_equiv_pos2(terms, step_id, clause)?;
        }
        AletheRule::EquivNeg1 if strict => {
            boolean_derived::validate_equiv_neg1(terms, step_id, clause)?;
        }
        AletheRule::EquivNeg2 if strict => {
            boolean_derived::validate_equiv_neg2(terms, step_id, clause)?;
        }
        AletheRule::ItePos1 if strict => {
            boolean_derived::validate_ite_pos1(terms, step_id, clause)?;
        }
        AletheRule::ItePos2 if strict => {
            boolean_derived::validate_ite_pos2(terms, step_id, clause)?;
        }
        AletheRule::IteNeg1 if strict => {
            boolean_derived::validate_ite_neg1(terms, step_id, clause)?;
        }
        AletheRule::IteNeg2 if strict => {
            boolean_derived::validate_ite_neg2(terms, step_id, clause)?;
        }
        AletheRule::XorPos1 if strict => {
            boolean_derived::validate_xor_pos1(terms, step_id, clause)?;
        }
        AletheRule::XorPos2 if strict => {
            boolean_derived::validate_xor_pos2(terms, step_id, clause)?;
        }
        AletheRule::XorNeg1 if strict => {
            boolean_derived::validate_xor_neg1(terms, step_id, clause)?;
        }
        AletheRule::XorNeg2 if strict => {
            boolean_derived::validate_xor_neg2(terms, step_id, clause)?;
        }
        AletheRule::EqReflexive if strict => {
            boolean_derived::validate_eq_reflexive(terms, step_id, clause)?;
        }
        AletheRule::EqSymmetric if strict => {
            boolean_derived::validate_eq_symmetric(terms, step_id, clause)?;
        }
        AletheRule::NotAnd if strict => {
            boolean_negation::validate_not_and(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::NotOr if strict => {
            boolean_negation::validate_not_or(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::NotImplies1 if strict => {
            boolean_negation::validate_not_implies1(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::NotImplies2 if strict => {
            boolean_negation::validate_not_implies2(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::NotEquiv1 if strict => {
            boolean_negation::validate_not_equiv1(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::NotEquiv2 if strict => {
            boolean_negation::validate_not_equiv2(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::NotIte1 if strict => {
            boolean_negation::validate_not_ite1(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::NotIte2 if strict => {
            boolean_negation::validate_not_ite2(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::Ite1 if strict => {
            boolean_negation::validate_ite1(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::Ite2 if strict => {
            boolean_negation::validate_ite2(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::IteIntro if strict => {
            boolean_negation::validate_ite_intro(terms, step_id, clause)?;
        }
        AletheRule::Or if strict => {
            clausification::validate_or_clausification(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::Contraction if strict => {
            boolean_negation::validate_contraction(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::Weakening if strict => {
            boolean_negation::validate_weakening(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::Refl if strict => {
            validate_refl(terms, step_id, clause)?;
        }
        AletheRule::Symm if strict => {
            validate_symm(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::Trans if strict => {
            validate_trans(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::Cong if strict => {
            validate_cong(terms, step_id, clause, &premise_clauses)?;
        }
        AletheRule::EqTransitive if strict => validate_euf_transitive(terms, step_id, clause)?,
        AletheRule::EqCongruent if strict => {
            validate_euf_congruent(terms, step_id, clause)?;
        }
        AletheRule::EqCongruentPred if strict => {
            validate_euf_congruent_pred(terms, step_id, clause)?;
        }
        AletheRule::DistinctElim if strict => {
            euf::validate_distinct_elim(terms, step_id, clause)?;
        }
        AletheRule::Evaluate if strict => {
            if ground_evaluate::validate_ground_evaluate(
                terms,
                step_id,
                clause,
                premises.len(),
                args,
            )
            .is_err()
            {
                // `evaluate` also has a deliberately separate closed-BV
                // concat fragment.  Both validators are independent and
                // fail-closed; admission by either exact semantics is enough.
                bv_bitblast::validate_bv_ground_evaluate(
                    terms,
                    step_id,
                    clause,
                    premises.len(),
                    args,
                )?;
            }
        }
        AletheRule::LaDisequality if strict => {
            lia::validate_la_disequality(terms, step_id, clause, premises.len(), args)?;
        }
        AletheRule::ForallInst if strict => {
            quantifier::validate_forall_inst(terms, step_id, clause, premises.len(), args)?;
        }
        AletheRule::QntNegExists if strict => qne(terms, step_id, clause, premises.len(), args)?,
        AletheRule::Skolem if strict => {
            quantifier::validate_sko_forall(terms, step_id, clause, premises.len(), args)?;
        }
        _ => {
            if strict {
                return Err(ProofCheckError::UnvalidatedRule {
                    step: step_id,
                    rule: rule.name().to_string(),
                });
            }
        }
    }

    derived_clauses.push(Some(clause.to_vec()));
    Ok(())
}

pub(crate) fn ensure_terminal_empty_clause(
    derived_clauses: &[Option<Vec<TermId>>],
) -> Result<(), ProofCheckError> {
    let Some((last_idx, last_clause)) = derived_clauses
        .iter()
        .enumerate()
        .rev()
        .find_map(|(idx, clause)| clause.as_deref().map(|clause| (idx, clause)))
    else {
        return Err(ProofCheckError::NoClauseProducingSteps);
    };

    if !last_clause.is_empty() {
        return Err(ProofCheckError::FinalClauseNotEmpty {
            step: ProofId(last_idx as u32),
        });
    }

    Ok(())
}

fn premise_clause(
    derived_clauses: &[Option<Vec<TermId>>],
    step: ProofId,
    premise: ProofId,
) -> Result<&[TermId], ProofCheckError> {
    let step_idx = step.0 as usize;
    let premise_idx = premise.0 as usize;

    if premise_idx >= derived_clauses.len() {
        return Err(ProofCheckError::MissingPremise { step, premise });
    }
    if premise_idx >= step_idx {
        return Err(ProofCheckError::NonPriorPremise { step, premise });
    }

    derived_clauses[premise_idx]
        .as_deref()
        .ok_or(ProofCheckError::PremiseHasNoClause { step, premise })
}

#[cfg(test)]
#[path = "tests.rs"]
mod tests;

// DRIFT-PROOF name-authority lint: every operator spelling a strict validator
// keys on must be one `ay-frontend` guarantees denotes the native theory
// operator. See the module docs for the bug class it kills.
#[cfg(test)]
#[path = "name_authority_tests.rs"]
mod name_authority_tests;

#[cfg(test)]
#[path = "bv_expensive_budget_tests.rs"]
mod expensive_bv_budget_tests;
