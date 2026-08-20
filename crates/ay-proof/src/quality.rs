// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof quality metrics and strict checking.
//!
//! Provides [`ProofQuality`] metrics counting each step type, plus
//! [`check_proof_with_quality`] and [`check_proof_strict`] for diagnosing
//! native proof completeness and rejecting unverified fallbacks. A native
//! semantic acceptance can still retain a diagnostic `Generic` producer tag
//! that renders as an honest Alethe `hole`; quality and wire completeness are
//! deliberately distinct.

use std::mem::size_of;

use ay_core::kani_compat::DetHashSet;
use ay_core::{
    AletheRule, Constant, DatatypeConstructor, DatatypeField, LiaAnnotation, Proof, ProofId,
    ProofStep, Sort, Symbol, TermData, TermId, TermStore, TheoryLemmaKind,
};

use crate::checker::{
    ensure_terminal_empty_clause, quantifier, validate_datatype_signature_context, validate_step,
    validate_step_with_datatypes_and_progress, DatatypeMemberSignature, ExtDiffRegistry,
    ProofCheckError,
};
use crate::partial::PartialProofCheck;

type DerivedClauses = Vec<Option<Vec<TermId>>>;
type DeferredGenericClauses = Vec<(ProofId, Vec<TermId>)>;
type StrictValidationArtifacts = (ProofQuality, DerivedClauses, DeferredGenericClauses);

#[path = "quality/authentication_payload.rs"]
mod authentication_payload;
mod farkas_meter;
mod semantic_payload;
use authentication_payload::meter_authentication_payload;
#[path = "quality/term_cost_memo.rs"]
mod term_cost_memo;
#[cfg(test)]
use term_cost_memo::TERM_COST_MEMO_POLL_INTERVAL;
use term_cost_memo::{unfolded_work_memoized, TermCostMemo};

#[path = "quality/semantic_charge.rs"]
mod semantic_charge;
use semantic_charge::semantic_validator_charge;

/// Proof quality metrics for diagnostic reporting.
///
/// Counts each step type in a proof to give visibility into proof completeness.
/// A high-quality proof has zero `trust_count` and zero `hole_count`.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct ProofQuality {
    /// Number of `assume` steps (input assertions).
    pub assume_count: u32,
    /// Number of verified `resolution` steps (binary resolution with valid resolvent).
    pub resolution_count: u32,
    /// Number of theory lemma steps (treated as axioms by the checker).
    pub theory_lemma_count: u32,
    /// Number of `trust` steps (unverified fallbacks from SAT proof reconstruction).
    pub trust_count: u32,
    /// Number of `trust` steps with premises (SAT hint reconstruction fallbacks).
    pub trust_fallback_count: u32,
    /// Number of `hole` steps (placeholder/incomplete proof).
    pub hole_count: u32,
    /// Number of `drup` steps (verified by reverse unit propagation).
    pub drup_count: u32,
    /// Number of `th_resolution` steps.
    pub th_resolution_count: u32,
    /// Number of other rule steps (not semantically checked).
    pub other_rule_count: u32,
    /// Total number of steps.
    pub total_steps: u32,
    /// Theory lemma kinds that produced `trust` steps in the proof.
    ///
    /// Populated during quality analysis to identify which theories still
    /// lack proper proof rules. Used by strict proof mode (#8076) to
    /// produce actionable error messages.
    pub trust_theory_kinds: Vec<TheoryLemmaKind>,
}

/// Clause conclusions authenticated by strict validation of a proof fragment.
///
/// This value can only be constructed by
/// [`authenticate_premise_clauses_strict_with_context`]. A clause returned by
/// [`clause`](Self::clause) is therefore bound to its exact [`ProofId`] in the
/// fragment that was checked, including authored-assumption authority and all
/// datatype, selector, and theory-lemma checks used by
/// [`check_proof_strict_with_context`].
///
/// This is **not a refutation certificate**. In particular, successful
/// construction does not require a terminal empty clause and cannot, by
/// itself, certify `UNSAT`. Its sole purpose is to let a caller match a
/// separately referenced premise ID to the exact clause whose derivation was
/// checked. Use [`check_proof_strict_with_context`] when the proof itself is
/// intended to certify `UNSAT`.
#[derive(Debug)]
pub struct AuthenticatedPremiseClauses {
    derived_clauses: DerivedClauses,
}

impl AuthenticatedPremiseClauses {
    /// Return the exact authenticated clause produced by `step`.
    ///
    /// Returns `None` when the ID is outside the checked fragment or names a
    /// non-clause-producing step such as an anchor. Literal order and
    /// multiplicity are preserved exactly as recorded in the proof.
    #[must_use]
    pub fn clause(&self, step: ProofId) -> Option<&[TermId]> {
        self.derived_clauses
            .get(step.0 as usize)
            .and_then(Option::as_deref)
    }

    /// Number of proof-step identities covered by this authentication result.
    #[must_use]
    pub fn step_count(&self) -> usize {
        self.derived_clauses.len()
    }
}

/// Premise clauses validated strictly except for explicitly separated
/// `TheoryLemmaKind::Generic` obligations.
///
/// This type deliberately has no general `clause` accessor. A caller must
/// choose between [`strictly_authenticated_clause`](Self::strictly_authenticated_clause)
/// and [`deferred_generic_clause`](Self::deferred_generic_clause), so a
/// deferred theory premise cannot accidentally be consumed as if the proof
/// kernel had authenticated it. Every deferred clause must be checked by an
/// independent semantic verifier before it is used in a larger certificate.
#[derive(Debug)]
pub struct PremiseClausesWithDeferredGeneric {
    derived_clauses: DerivedClauses,
    deferred_generic: DeferredGenericClauses,
}

impl PremiseClausesWithDeferredGeneric {
    /// Return a clause only when the strict proof kernel authenticated its
    /// exact producing step without deferral.
    #[must_use]
    pub fn strictly_authenticated_clause(&self, step: ProofId) -> Option<&[TermId]> {
        if self
            .deferred_generic
            .binary_search_by_key(&step.0, |(id, _)| id.0)
            .is_ok()
        {
            return None;
        }
        self.derived_clauses
            .get(step.0 as usize)
            .and_then(Option::as_deref)
    }

    /// Return the exact clause deferred at a `Generic` theory-lemma step.
    ///
    /// Presence here is an obligation, not evidence: the caller must validate
    /// the clause independently before relying on it.
    #[must_use]
    pub fn deferred_generic_clause(&self, step: ProofId) -> Option<&[TermId]> {
        self.deferred_generic
            .binary_search_by_key(&step.0, |(id, _)| id.0)
            .ok()
            .and_then(|index| self.deferred_generic.get(index))
            .map(|(_, clause)| clause.as_slice())
    }

    /// Iterate over every exact deferred step identity and clause.
    pub fn deferred_generic_clauses(&self) -> impl Iterator<Item = (ProofId, &[TermId])> {
        self.deferred_generic
            .iter()
            .map(|(step, clause)| (*step, clause.as_slice()))
    }

    /// Number of proof-step identities covered by this validation result.
    #[must_use]
    pub fn step_count(&self) -> usize {
        self.derived_clauses.len()
    }
}

impl ProofQuality {
    /// True if the proof has no trust or hole fallbacks.
    ///
    /// This is a diagnostic tag metric, neither the native strict checker's
    /// acceptance bit nor a guarantee that every native step has a hole-free
    /// wire lowering. In particular, the exact equality-span subset of a
    /// `Generic` theory lemma is independently re-derived and may pass strict
    /// checking while its producer tag still contributes `trust_count == 1`
    /// (and prints as an honest Alethe `hole`).
    #[must_use]
    pub fn is_complete(&self) -> bool {
        self.trust_count == 0 && self.hole_count == 0
    }

    /// Number of semantically verified steps (resolution + drup + th_resolution).
    #[must_use]
    pub fn verified_count(&self) -> u32 {
        self.resolution_count + self.drup_count + self.th_resolution_count
    }

    /// Number of axiom steps (assume + theory lemma) -- accepted without semantic check.
    #[must_use]
    pub fn axiom_count(&self) -> u32 {
        self.assume_count + self.theory_lemma_count
    }

    /// Number of unverified fallback steps (trust + hole).
    #[must_use]
    pub fn fallback_count(&self) -> u32 {
        self.trust_count + self.hole_count
    }

    /// True if any trust steps were found in the proof.
    ///
    /// This includes both explicit `trust` rule steps (from SAT proof
    /// reconstruction) and theory lemmas that export as `trust` in Alethe
    /// format (e.g., `Generic` kind).
    #[must_use]
    pub fn has_trust_steps(&self) -> bool {
        self.trust_count > 0
    }

    /// Validate that the proof has no trust steps, returning an error if
    /// strict proof mode is enabled and trust steps exist.
    ///
    /// This is the enforcement gate for Phase 1e (#8076): when
    /// `strict_proof_mode` is true, any trust fallback becomes a hard error.
    /// The error message identifies which `TheoryLemmaKind` produced the
    /// trust step(s) so developers know which theory needs proof coverage.
    ///
    /// When `strict_proof_mode` is false (the default during the transition
    /// period), this method always returns `Ok(())`.
    pub fn check_strict_proof_mode(&self, strict_proof_mode: bool) -> Result<(), ProofCheckError> {
        if !strict_proof_mode || !self.has_trust_steps() {
            return Ok(());
        }

        // Build a descriptive error identifying the trust sources.
        let kind_descriptions: Vec<String> = self
            .trust_theory_kinds
            .iter()
            .map(|k| format!("{k:?}"))
            .collect();

        let trust_from_theory = !self.trust_theory_kinds.is_empty();
        let trust_from_steps = self.trust_count > self.trust_theory_kinds.len() as u32;

        let mut reason = format!(
            "strict proof mode: {} trust step(s) found",
            self.trust_count
        );
        if trust_from_theory {
            reason.push_str(&format!(
                "; theory lemma kinds producing trust: [{}]",
                kind_descriptions.join(", ")
            ));
        }
        if trust_from_steps {
            reason.push_str("; additional trust steps from SAT proof reconstruction");
        }

        Err(ProofCheckError::StrictProofModeTrust { reason })
    }
}

impl std::fmt::Display for ProofQuality {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "steps={} verified={} axiom={} fallback={} (trust={} trust_fallback={} hole={}) \
             [assume={} resolution={} th_resolution={} theory_lemma={} drup={} other={}]",
            self.total_steps,
            self.verified_count(),
            self.axiom_count(),
            self.fallback_count(),
            self.trust_count,
            self.trust_fallback_count,
            self.hole_count,
            self.assume_count,
            self.resolution_count,
            self.th_resolution_count,
            self.theory_lemma_count,
            self.drup_count,
            self.other_rule_count,
        )
    }
}

/// Validate proof structure and collect quality metrics.
///
/// Performs the same checks as [`crate::check_proof`] but also returns a
/// [`ProofQuality`] summary counting each step type. Use this to diagnose
/// proof completeness.
pub fn check_proof_with_quality(
    proof: &Proof,
    terms: &TermStore,
) -> Result<ProofQuality, ProofCheckError> {
    if proof.steps.is_empty() {
        return Err(ProofCheckError::EmptyProof);
    }

    let mut quality = ProofQuality::default();
    let mut derived_clauses: Vec<Option<Vec<TermId>>> = Vec::with_capacity(proof.steps.len());

    for (idx, step) in proof.steps.iter().enumerate() {
        classify_step(step, &mut quality);
        validate_step(
            terms,
            &mut derived_clauses,
            ProofId(idx as u32),
            step,
            false,
            None,
        )?;
    }

    quality.total_steps = proof.steps.len() as u32;
    quantifier::validate_sko_forall_uniqueness(proof, terms)?;
    ensure_terminal_empty_clause(&derived_clauses)?;
    Ok(quality)
}

/// Single-pass fusion of [`crate::check_proof_partial`] and
/// [`check_proof_with_quality`] (#proof-tax).
///
/// The executor's UNSAT path used to run BOTH functions back to back; each
/// walks the whole proof through the identical `validate_step` call, so every
/// step was semantically checked twice. On resolution-heavy UNSAT proofs
/// (QF_UF `pgm_protocol` family) the double walk was roughly half of the
/// entire post-verdict proof tax. This walks once and returns everything both
/// callers need. The checking itself is UNCHANGED — same checker, same step
/// order, same hole handling, same first-error semantics — it simply runs
/// once instead of twice.
///
/// Returns `(partial_stats, quality, error)`:
/// * `partial_stats` — exactly what [`crate::check_proof_partial`] returns
///   (Hole steps skipped and counted; on error, `checked_steps` reflects only
///   the validated prefix).
/// * `quality` — `Some` only for hole-free proofs that validated cleanly:
///   exactly the cases where the legacy pair produced a `ProofQuality` (the
///   executor skipped quality measurement when any Hole step was present,
///   and a checker error yielded `None`).
/// * `error` — the first validation error, identical to the partial checker's.
pub fn check_proof_partial_with_quality(
    proof: &Proof,
    terms: &TermStore,
) -> (
    PartialProofCheck,
    Option<ProofQuality>,
    Option<ProofCheckError>,
) {
    let mut result = PartialProofCheck {
        total_steps: proof.steps.len() as u32,
        ..Default::default()
    };

    if proof.steps.is_empty() {
        return (result, None, Some(ProofCheckError::EmptyProof));
    }

    let mut quality = ProofQuality::default();
    let mut derived_clauses: Vec<Option<Vec<TermId>>> = Vec::with_capacity(proof.steps.len());

    for (idx, step) in proof.steps.iter().enumerate() {
        classify_step(step, &mut quality);

        let is_hole = matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Hole,
                ..
            }
        );
        if is_hole {
            result.skipped_hole_steps += 1;
            // Accept hole clause for linkage without semantic validation
            // (same contract as `check_proof_partial`).
            if let ProofStep::Step { clause, .. } = step {
                derived_clauses.push(Some(clause.clone()));
            } else {
                derived_clauses.push(None);
            }
            continue;
        }

        match validate_step(
            terms,
            &mut derived_clauses,
            ProofId(idx as u32),
            step,
            false,
            None,
        ) {
            Ok(()) => result.checked_steps += 1,
            Err(e) => return (result, None, Some(e)),
        }
    }

    quality.total_steps = proof.steps.len() as u32;
    if let Err(e) = ensure_terminal_empty_clause(&derived_clauses) {
        return (result, None, Some(e));
    }

    let quality = (result.skipped_hole_steps == 0).then_some(quality);
    (result, quality, None)
}

/// Strict proof validation rejecting unverified fallbacks.
///
/// Rejects `hole`/`trust` fallbacks, validates supported theory lemmas at the
/// strict semantic boundary, and fails closed on theory-lemma families that do
/// not yet have a semantic checker. Returns quality metrics on success.
///
/// Most `Generic` theory-lemma shapes and generic Alethe rules still lack a
/// semantic validator and are rejected. The deliberately narrow arithmetic
/// equality-span subset is accepted only after the checker re-derives the
/// exact rational combination itself; its `Generic` quality tag remains
/// diagnostic and does not claim a hole-free external presentation.
pub fn check_proof_strict(
    proof: &Proof,
    terms: &TermStore,
) -> Result<ProofQuality, ProofCheckError> {
    check_proof_strict_with_datatypes(proof, terms, None)
}

/// Compatibility wrapper carrying a name-only datatype constructor registry.
///
/// Name-only registries confer no datatype proof authority, so datatype kinds
/// and enum-backed finite-array kinds fail closed through this API. Use
/// [`check_proof_strict_with_typed_context`] with the exact member-signature
/// table to validate either family. Passing `None` remains equivalent to
/// [`check_proof_strict`].
pub fn check_proof_strict_with_datatypes(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
) -> Result<ProofQuality, ProofCheckError> {
    check_proof_strict_with_datatypes_and_selectors(proof, terms, dt_decls, None)
}

/// Compatibility wrapper additionally carrying a name-only
/// constructor-to-selector registry.
///
/// These registries likewise confer no datatype proof authority without exact
/// member signatures. Use [`check_proof_strict_with_typed_context`] for
/// datatype and enum-backed finite-array validation. Passing `None` is equivalent to
/// [`check_proof_strict_with_datatypes`].
pub fn check_proof_strict_with_datatypes_and_selectors(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
) -> Result<ProofQuality, ProofCheckError> {
    check_proof_strict_with_context(proof, terms, dt_decls, ctor_selectors, None)
}

/// Strictly authenticate every clause-producing step in a proof fragment.
///
/// Every step is checked by the same implementation used by
/// [`check_proof_strict_with_context`]: unverified `trust`/`hole` and generic
/// rules are rejected, while the exact semantically revalidated `Generic`
/// theory-lemma subset and other supported lemmas are checked independently,
/// name-only datatype contexts remain fail-closed, expensive BV budgets are
/// enforced, and every `assume` must belong to `problem_assertions` (or a
/// nested conjunct of one). Use
/// [`authenticate_premise_clauses_strict_with_typed_context`] for datatype
/// authority.
///
/// Unlike [`check_proof_strict_with_context`], this function deliberately does
/// **not** require the final clause to be empty. An `Ok` result therefore does
/// not establish a refutation and MUST NOT be used alone to certify `UNSAT`.
/// The returned opaque table is only authority for matching a separately
/// referenced [`ProofId`] to its exact, strictly checked premise clause.
///
/// Requiring the authored assertion slice (rather than accepting `None`) keeps
/// the premise-authentication API from silently treating arbitrary assumptions
/// as problem inputs.
///
/// # Errors
///
/// Returns the first [`ProofCheckError`] from strict step validation or context
/// construction. A non-empty terminal clause is intentionally not an error.
pub fn authenticate_premise_clauses_strict_with_context(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    problem_assertions: &[TermId],
) -> Result<AuthenticatedPremiseClauses, ProofCheckError> {
    let mut unbounded = |_: usize, _: usize| true;
    authenticate_premise_clauses_strict_with_context_and_progress(
        proof,
        terms,
        dt_decls,
        ctor_selectors,
        problem_assertions,
        &mut unbounded,
    )
}

/// Metered form of [`authenticate_premise_clauses_strict_with_context`].
///
/// `progress` receives `(work_delta, byte_delta)` charges before every
/// whole-proof prepass, dynamic payload allocation, and proof step. Returning
/// `false` rejects with
/// [`ProofCheckError::ResourceLimit`]. Callers retain ownership of the actual
/// deadline/interrupt/memory policy and can therefore share one envelope with
/// earlier certificate-conversion phases.
pub fn authenticate_premise_clauses_strict_with_context_and_progress(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    problem_assertions: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<AuthenticatedPremiseClauses, ProofCheckError> {
    let (_, derived_clauses, deferred_generic) = validate_strict_steps_with_context(
        proof,
        terms,
        dt_decls,
        ctor_selectors,
        None,
        Some(problem_assertions),
        GenericTheoryDeferral::Reject,
        progress,
    )?;
    debug_assert!(deferred_generic.is_empty());
    Ok(AuthenticatedPremiseClauses { derived_clauses })
}

/// Typed-context form of [`authenticate_premise_clauses_strict_with_context`].
pub fn authenticate_premise_clauses_strict_with_typed_context(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    datatype_member_signatures: &[DatatypeMemberSignature],
    problem_assertions: &[TermId],
) -> Result<AuthenticatedPremiseClauses, ProofCheckError> {
    let mut unbounded = |_: usize, _: usize| true;
    authenticate_premise_clauses_strict_with_typed_context_and_progress(
        proof,
        terms,
        dt_decls,
        ctor_selectors,
        datatype_member_signatures,
        problem_assertions,
        &mut unbounded,
    )
}

/// Metered typed-context premise authentication.
pub fn authenticate_premise_clauses_strict_with_typed_context_and_progress(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    datatype_member_signatures: &[DatatypeMemberSignature],
    problem_assertions: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<AuthenticatedPremiseClauses, ProofCheckError> {
    let (_, derived_clauses, deferred_generic) = validate_strict_steps_with_context(
        proof,
        terms,
        dt_decls,
        ctor_selectors,
        Some(datatype_member_signatures),
        Some(problem_assertions),
        GenericTheoryDeferral::Reject,
        progress,
    )?;
    debug_assert!(deferred_generic.is_empty());
    Ok(AuthenticatedPremiseClauses { derived_clauses })
}

/// Strictly authenticate a proof fragment while separating only `Generic`
/// theory lemmas for an independent semantic verifier.
///
/// Explicit `trust` and `hole` steps remain hard errors. Supported theory
/// lemmas and every structural proof step pass the ordinary strict checker.
/// Each `Generic` theory lemma not already accepted by the exact equality-span
/// validator is retained by exact [`ProofId`] and clause, but is inaccessible
/// through the strict-clause accessor on the returned type. The caller must
/// independently establish every deferred clause before using it as a premise
/// in a composed certificate.
///
/// `progress` covers the same full proof/checker envelope as strict premise
/// authentication, plus the retained deferred-clause storage.
pub fn authenticate_premise_clauses_with_deferred_generic_theory_and_progress(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    problem_assertions: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<PremiseClausesWithDeferredGeneric, ProofCheckError> {
    let (_, derived_clauses, deferred_generic) = validate_strict_steps_with_context(
        proof,
        terms,
        dt_decls,
        ctor_selectors,
        None,
        Some(problem_assertions),
        GenericTheoryDeferral::Collect,
        progress,
    )?;
    Ok(PremiseClausesWithDeferredGeneric {
        derived_clauses,
        deferred_generic,
    })
}

/// Typed-context form of
/// [`authenticate_premise_clauses_with_deferred_generic_theory_and_progress`].
pub fn authenticate_premise_clauses_with_deferred_generic_theory_and_typed_context_and_progress(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    datatype_member_signatures: &[DatatypeMemberSignature],
    problem_assertions: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<PremiseClausesWithDeferredGeneric, ProofCheckError> {
    let (_, derived_clauses, deferred_generic) = validate_strict_steps_with_context(
        proof,
        terms,
        dt_decls,
        ctor_selectors,
        Some(datatype_member_signatures),
        Some(problem_assertions),
        GenericTheoryDeferral::Collect,
        progress,
    )?;
    Ok(PremiseClausesWithDeferredGeneric {
        derived_clauses,
        deferred_generic,
    })
}

/// As [`check_proof_strict_with_datatypes_and_selectors`], but additionally
/// given the PROBLEM's assertion terms so strict mode can certify
/// `TheoryLemmaKind::ArrayExtensionality` lemmas.
///
/// The Skolemized extensionality clause
/// `(cl (= a b) (not (= (select a k) (select b k))))` is not a tautology — it
/// is sound only because `k` is a fresh witness minted for exactly `(a, b)`.
/// Deciding that needs two things the proof alone does not carry: the
/// `array_ext_diff_intro` steps that record which pair each witness was minted
/// for, and the problem's own symbols, against which the checker VERIFIES
/// freshness rather than taking it on faith. `problem_assertions` supplies the
/// second; passing `None` is equivalent to
/// [`check_proof_strict_with_datatypes_and_selectors`] and keeps extensionality
/// fail-closed.
///
/// `problem_assertions` must be the AUTHORED assertions, not the solver-time
/// assertion stack (which also holds the injected extensionality axioms and
/// would make every witness look non-fresh). A superset is always safe: extra
/// terms can only make the freshness test stricter.
///
/// # Errors
///
/// Returns the first [`ProofCheckError`] any step fails on, or a registry
/// construction failure (a malformed, duplicated, non-fresh, or
/// self-referential diff-witness introduction).
pub fn check_proof_strict_with_context(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    problem_assertions: Option<&[TermId]>,
) -> Result<ProofQuality, ProofCheckError> {
    let mut unbounded = |_: usize, _: usize| true;
    check_proof_strict_with_context_and_progress(
        proof,
        terms,
        dt_decls,
        ctor_selectors,
        problem_assertions,
        &mut unbounded,
    )
}

/// Strict proof validation with the exact typed datatype member context.
///
/// Unlike the compatibility API, this form can authorize concrete datatype
/// constructor, selector, and tester rules.  The signature table is validated
/// globally and every occurrence of a registered member in `terms` must match
/// its exact argument and result sorts.
pub fn check_proof_strict_with_typed_context(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    datatype_member_signatures: &[DatatypeMemberSignature],
    problem_assertions: Option<&[TermId]>,
) -> Result<ProofQuality, ProofCheckError> {
    let mut unbounded = |_: usize, _: usize| true;
    check_proof_strict_with_typed_context_and_progress(
        proof,
        terms,
        dt_decls,
        ctor_selectors,
        datatype_member_signatures,
        problem_assertions,
        &mut unbounded,
    )
}

/// Metered form of [`check_proof_strict_with_context`].
///
/// `progress` receives `(work_delta, byte_delta)` before each whole-proof
/// prepass, dynamic payload allocation, and proof step. Returning `false`
/// rejects with [`ProofCheckError::ResourceLimit`]. This is the strict,
/// terminal-empty-clause sibling of
/// [`authenticate_premise_clauses_strict_with_context_and_progress`].
///
/// # Errors
///
/// Returns the first strict validation error, a non-empty terminal-clause
/// error, or [`ProofCheckError::ResourceLimit`] when `progress` declines.
pub fn check_proof_strict_with_context_and_progress(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    problem_assertions: Option<&[TermId]>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<ProofQuality, ProofCheckError> {
    let (quality, derived_clauses, deferred_generic) = validate_strict_steps_with_context(
        proof,
        terms,
        dt_decls,
        ctor_selectors,
        None,
        problem_assertions,
        GenericTheoryDeferral::Reject,
        progress,
    )?;
    debug_assert!(deferred_generic.is_empty());
    ensure_terminal_empty_clause(&derived_clauses)?;
    Ok(quality)
}

/// Metered form of [`check_proof_strict_with_typed_context`].
pub fn check_proof_strict_with_typed_context_and_progress(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    datatype_member_signatures: &[DatatypeMemberSignature],
    problem_assertions: Option<&[TermId]>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<ProofQuality, ProofCheckError> {
    let (quality, derived_clauses, deferred_generic) = validate_strict_steps_with_context(
        proof,
        terms,
        dt_decls,
        ctor_selectors,
        Some(datatype_member_signatures),
        problem_assertions,
        GenericTheoryDeferral::Reject,
        progress,
    )?;
    debug_assert!(deferred_generic.is_empty());
    ensure_terminal_empty_clause(&derived_clauses)?;
    Ok(quality)
}

fn charge_progress(
    progress: &mut dyn FnMut(usize, usize) -> bool,
    work: usize,
    bytes: usize,
) -> Result<(), ProofCheckError> {
    if progress(work, bytes) {
        Ok(())
    } else {
        Err(ProofCheckError::ResourceLimit)
    }
}

fn checked_add_usize(left: usize, right: usize) -> Result<usize, ProofCheckError> {
    left.checked_add(right)
        .ok_or(ProofCheckError::ResourceLimit)
}

fn checked_mul_usize(left: usize, right: usize) -> Result<usize, ProofCheckError> {
    left.checked_mul(right)
        .ok_or(ProofCheckError::ResourceLimit)
}

fn charge_name_lists(
    lists: &[(String, Vec<String>)],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<RegistryPayloadStats, ProofCheckError> {
    let mut stats = RegistryPayloadStats::default();
    for (name, members) in lists {
        let member_slots = checked_mul_usize(members.capacity(), size_of::<String>())?;
        let work = checked_add_usize(name.len(), 1)?;
        let bytes = checked_add_usize(name.capacity(), member_slots)?;
        charge_progress(progress, work, bytes)?;
        stats.work = checked_add_usize(stats.work, work)?;
        stats.bytes = checked_add_usize(stats.bytes, bytes)?;
        for member in members {
            let work = checked_add_usize(member.len(), 1)?;
            let bytes = member.capacity();
            charge_progress(progress, work, bytes)?;
            stats.work = checked_add_usize(stats.work, work)?;
            stats.bytes = checked_add_usize(stats.bytes, bytes)?;
        }
    }
    Ok(stats)
}

fn push_term_slice(
    pending: &mut Vec<TermId>,
    terms: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    charge_progress(
        progress,
        terms.len(),
        checked_mul_usize(terms.len(), size_of::<TermId>())?,
    )?;
    pending.extend_from_slice(terms);
    Ok(())
}

fn push_term(
    pending: &mut Vec<TermId>,
    term: TermId,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    charge_progress(progress, 1, size_of::<TermId>())?;
    pending.push(term);
    Ok(())
}

#[derive(Debug, Clone, Copy, Default)]
struct PayloadStats {
    work: usize,
    bytes: usize,
    unfolded_work: usize,
    order_assignments: usize,
}

#[derive(Debug, Clone, Copy, Default)]
struct RegistryPayloadStats {
    work: usize,
    bytes: usize,
}

#[derive(Debug, Clone, Copy, Default)]
struct RegistryContextStats {
    datatype: RegistryPayloadStats,
    selectors: RegistryPayloadStats,
}

#[derive(Debug, Clone, Copy, Default)]
struct AuthenticationPayloadStats {
    aggregate: PayloadStats,
    datatype_registry: RegistryPayloadStats,
    selector_registry: RegistryPayloadStats,
}

fn push_sort<'a>(
    pending: &mut Vec<&'a Sort>,
    sort: &'a Sort,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    charge_progress(progress, 1, size_of::<&Sort>())?;
    pending.push(sort);
    Ok(())
}

pub(crate) fn meter_sort(
    root: &Sort,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let mut pending = Vec::new();
    push_sort(&mut pending, root, progress)?;
    while let Some(sort) = pending.pop() {
        charge_progress(progress, 1, size_of::<Sort>())?;
        match sort {
            Sort::Array(array) => {
                charge_progress(progress, 1, size_of::<ay_core::ArraySort>())?;
                push_sort(&mut pending, &array.index_sort, progress)?;
                push_sort(&mut pending, &array.element_sort, progress)?;
            }
            Sort::Uninterpreted(name) | Sort::TypeVar(name) => {
                charge_progress(progress, checked_add_usize(name.len(), 1)?, name.capacity())?;
            }
            Sort::Datatype(datatype) => {
                let constructors_bytes = checked_mul_usize(
                    datatype.constructors.capacity(),
                    size_of::<DatatypeConstructor>(),
                )?;
                charge_progress(
                    progress,
                    checked_add_usize(datatype.name.len(), 1)?,
                    checked_add_usize(datatype.name.capacity(), constructors_bytes)?,
                )?;
                for constructor in &datatype.constructors {
                    let fields_bytes = checked_mul_usize(
                        constructor.fields.capacity(),
                        size_of::<DatatypeField>(),
                    )?;
                    charge_progress(
                        progress,
                        checked_add_usize(constructor.name.len(), 1)?,
                        checked_add_usize(constructor.name.capacity(), fields_bytes)?,
                    )?;
                    for field in &constructor.fields {
                        charge_progress(
                            progress,
                            checked_add_usize(field.name.len(), 1)?,
                            field.name.capacity(),
                        )?;
                        push_sort(&mut pending, &field.sort, progress)?;
                    }
                }
            }
            Sort::Seq(element) => {
                charge_progress(progress, 1, size_of::<Sort>())?;
                push_sort(&mut pending, element, progress)?;
            }
            Sort::FiniteDomain(name, _) => {
                charge_progress(progress, checked_add_usize(name.len(), 1)?, name.capacity())?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn bigint_payload_bytes(value: &num_bigint::BigInt) -> Result<usize, ProofCheckError> {
    let bits = usize::try_from(value.bits()).map_err(|_| ProofCheckError::ResourceLimit)?;
    Ok(checked_add_usize(bits, 7)? / 8)
}

fn meter_bigint(
    value: &num_bigint::BigInt,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let bytes = bigint_payload_bytes(value)?;
    let limbs = checked_add_usize(bytes / size_of::<usize>(), 1)?;
    charge_progress(progress, limbs, bytes)
}

fn meter_symbol(
    symbol: &Symbol,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    match symbol {
        Symbol::Named(name) => {
            charge_progress(progress, checked_add_usize(name.len(), 1)?, name.capacity())
        }
        Symbol::Indexed(name, indices) => charge_progress(
            progress,
            checked_add_usize(checked_add_usize(name.len(), indices.len())?, 1)?,
            checked_add_usize(
                name.capacity(),
                checked_mul_usize(indices.capacity(), size_of::<u32>())?,
            )?,
        ),
        _ => charge_progress(progress, 1, 0),
    }
}

fn meter_constant(
    constant: &Constant,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    match constant {
        Constant::Int(value) | Constant::BitVec { value, .. } => meter_bigint(value, progress),
        Constant::Rational(value) => {
            meter_bigint(value.0.numer(), progress)?;
            meter_bigint(value.0.denom(), progress)
        }
        Constant::String(value) => charge_progress(progress, value.len(), value.capacity()),
        Constant::Bool(_) => charge_progress(progress, 1, 0),
        _ => charge_progress(progress, 1, 0),
    }
}

fn meter_reachable_terms(
    terms: &TermStore,
    mut pending: Vec<TermId>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let mut visited = DetHashSet::default();
    while let Some(term) = pending.pop() {
        // Charge the membership probe before it happens. Repeated roots/edges
        // still consume work but do not allocate a second visited entry.
        charge_progress(progress, 1, 0)?;
        if visited.contains(&term) {
            continue;
        }
        charge_progress(progress, 1, checked_add_usize(size_of::<TermId>(), 32)?)?;
        visited.insert(term);
        meter_reachable_node(terms, term, &mut pending, progress)?;
    }
    Ok(())
}

/// The per-unique-node payload charges of [`meter_reachable_terms`]: term
/// header and sort, the node's own content (names, constants, argument
/// slots), and the push charges for its children, which are appended to
/// `pending`. Factored out so [`charge_step_payload_walks`] emits EXACTLY the
/// same per-node content charges as the reachability walk itself — one code
/// path, no drift.
fn meter_reachable_node(
    terms: &TermStore,
    term: TermId,
    pending: &mut Vec<TermId>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    charge_progress(
        progress,
        1,
        checked_add_usize(size_of::<TermData>(), size_of::<Sort>())?,
    )?;
    meter_sort(terms.sort(term), progress)?;
    match terms.get(term) {
        TermData::Const(constant) => meter_constant(constant, progress)?,
        TermData::Var(name, _) => {
            charge_progress(progress, checked_add_usize(name.len(), 1)?, name.capacity())?
        }
        TermData::App(symbol, args) => {
            meter_symbol(symbol, progress)?;
            charge_progress(
                progress,
                1,
                checked_mul_usize(args.capacity(), size_of::<TermId>())?,
            )?;
            push_term_slice(pending, args, progress)?;
        }
        TermData::Let(bindings, body) => {
            charge_progress(
                progress,
                bindings.len(),
                checked_mul_usize(bindings.capacity(), size_of::<(String, TermId)>())?,
            )?;
            for (name, value) in bindings {
                charge_progress(progress, checked_add_usize(name.len(), 1)?, name.capacity())?;
                push_term(pending, *value, progress)?;
            }
            push_term(pending, *body, progress)?;
        }
        TermData::Not(inner) => push_term(pending, *inner, progress)?,
        TermData::Ite(condition, then_branch, else_branch) => {
            push_term(pending, *condition, progress)?;
            push_term(pending, *then_branch, progress)?;
            push_term(pending, *else_branch, progress)?;
        }
        TermData::Forall(variables, body, triggers)
        | TermData::Exists(variables, body, triggers) => {
            let variable_bytes =
                checked_mul_usize(variables.capacity(), size_of::<(String, Sort)>())?;
            let trigger_bytes = checked_mul_usize(triggers.capacity(), size_of::<Vec<TermId>>())?;
            charge_progress(
                progress,
                variables.len(),
                checked_add_usize(variable_bytes, trigger_bytes)?,
            )?;
            for (name, sort) in variables {
                charge_progress(progress, checked_add_usize(name.len(), 1)?, name.capacity())?;
                meter_sort(sort, progress)?;
            }
            push_term(pending, *body, progress)?;
            for trigger in triggers {
                charge_progress(
                    progress,
                    1,
                    checked_mul_usize(trigger.capacity(), size_of::<TermId>())?,
                )?;
                push_term_slice(pending, trigger, progress)?;
            }
        }
        _ => charge_progress(progress, 1, 0)?,
    }
    Ok(())
}

fn append_term_children(
    terms: &TermStore,
    term: TermId,
    children: &mut Vec<TermId>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    match terms.get(term) {
        TermData::App(_, args) => push_term_slice(children, args, progress)?,
        TermData::Let(bindings, body) => {
            for (_, value) in bindings {
                push_term(children, *value, progress)?;
            }
            push_term(children, *body, progress)?;
        }
        TermData::Not(inner) => push_term(children, *inner, progress)?,
        TermData::Ite(condition, then_branch, else_branch) => {
            push_term(children, *condition, progress)?;
            push_term(children, *then_branch, progress)?;
            push_term(children, *else_branch, progress)?;
        }
        TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
            push_term(children, *body, progress)?;
            for trigger in triggers {
                push_term_slice(children, trigger, progress)?;
            }
        }
        _ => {}
    }
    Ok(())
}

/// Per-step payload charge walk. Emits, for one step's `roots`, a charge
/// stream whose per-step totals are byte-identical to the two walks it
/// replaces (pinned by the
/// `a2_per_step_payload_stats_are_byte_identical_to_the_unmemoized_metering`
/// test):
///
/// * Phase 1 replicates the former `unfolded_term_work` traversal charge for
///   charge — same stack discipline, same charge sites — with a per-step
///   `completed` set standing in for the per-call cost-map membership that
///   steered the original traversal. The cost arithmetic itself is gone
///   (it moved, memoized, into [`unfolded_work_memoized`]).
/// * Phase 2 emits [`meter_reachable_terms`]'s charges over the SAME
///   per-step unique-node set without a second hash traversal: that walk pops
///   one pending entry per root and per child edge (a `(1, 0)` membership
///   probe each) and charges node content once per unique node via
///   [`meter_reachable_node`] — re-emitted here per node in phase-1 discovery
///   order, so the per-step charge totals are identical and one full
///   traversal (hash set, pending vector, probe loop) is saved.
///
/// Both phases use fresh per-step state on purpose; see [`TermCostMemo`] for
/// why per-step content charges are load-bearing and must not be memoized.
fn charge_step_payload_walks(
    terms: &TermStore,
    roots: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<usize, ProofCheckError> {
    let mut completed: DetHashSet<TermId> = DetHashSet::default();
    let mut active: DetHashSet<TermId> = DetHashSet::default();
    let mut stack: Vec<(TermId, bool)> = Vec::new();
    let mut discovered: Vec<TermId> = Vec::new();
    let mut children: Vec<TermId> = Vec::new();
    let mut order_variables = 0usize;

    for &root in roots {
        if completed.contains(&root) {
            continue;
        }
        charge_progress(progress, 1, size_of::<(TermId, bool)>())?;
        stack.push((root, false));
        while let Some((term, expanded)) = stack.pop() {
            charge_progress(progress, 1, 0)?;
            if completed.contains(&term) {
                continue;
            }
            if expanded {
                active.remove(&term);
                children.clear();
                append_term_children(terms, term, &mut children, progress)?;
                charge_progress(
                    progress,
                    1,
                    checked_add_usize(size_of::<(TermId, usize)>(), 32)?,
                )?;
                completed.insert(term);
                continue;
            }

            charge_progress(progress, 1, checked_add_usize(size_of::<TermId>(), 32)?)?;
            if !active.insert(term) {
                return Err(ProofCheckError::ResourceLimit);
            }
            charge_progress(progress, 1, size_of::<(TermId, bool)>())?;
            stack.push((term, true));
            discovered.push(term);
            if matches!(terms.sort(term), Sort::Int | Sort::Real)
                && matches!(terms.get(term), TermData::Var(_, _))
            {
                order_variables = checked_add_usize(order_variables, 1)?;
            }
            children.clear();
            append_term_children(terms, term, &mut children, progress)?;
            for index in (0..children.len()).rev() {
                let child = children[index];
                if active.contains(&child) {
                    return Err(ProofCheckError::ResourceLimit);
                }
                if !completed.contains(&child) {
                    charge_progress(progress, 1, size_of::<(TermId, bool)>())?;
                    stack.push((child, false));
                }
            }
        }
    }

    // Phase 2: `meter_reachable_terms` charges one `(1, 0)` pop probe per
    // initial root and per pushed child edge, then per unique node the
    // visited-set insert plus the node content. Same totals, one node at a
    // time, no second traversal.
    charge_progress(progress, roots.len(), 0)?;
    let mut pushed: Vec<TermId> = Vec::new();
    for &term in &discovered {
        charge_progress(progress, 1, checked_add_usize(size_of::<TermId>(), 32)?)?;
        pushed.clear();
        meter_reachable_node(terms, term, &mut pushed, progress)?;
        charge_progress(progress, pushed.len(), 0)?;
    }
    Ok(order_variables)
}

fn validate_problem_assumptions_metered(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let mut allowed = DetHashSet::default();
    let mut stack = Vec::new();
    for &assertion in problem_assertions {
        charge_progress(
            progress,
            1,
            checked_add_usize(checked_mul_usize(size_of::<TermId>(), 2)?, 32)?,
        )?;
        if allowed.insert(assertion) {
            stack.push(assertion);
        }
    }

    while let Some(term) = stack.pop() {
        charge_progress(progress, 1, 0)?;
        let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
            continue;
        };
        if name != "and" {
            continue;
        }
        for &arg in args {
            // Charge before the hash-set insertion and possible stack growth.
            // Duplicate conjunct edges are deliberately charged as work too.
            charge_progress(
                progress,
                1,
                checked_add_usize(checked_mul_usize(size_of::<TermId>(), 2)?, 32)?,
            )?;
            if allowed.insert(arg) {
                stack.push(arg);
            }
        }
    }

    for (index, step) in proof.steps.iter().enumerate() {
        charge_progress(progress, 1, 0)?;
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

fn ext_diff_registry_charge(
    proof: &Proof,
    terms: &TermStore,
    payload: PayloadStats,
) -> Result<(usize, usize), ProofCheckError> {
    let mut bindings = 0_usize;
    let mut max_name_bytes = 0_usize;
    for step in &proof.steps {
        let ProofStep::Step {
            rule: AletheRule::ArrayExtDiffIntro,
            args,
            ..
        } = step
        else {
            continue;
        };
        bindings = checked_add_usize(bindings, 1)?;
        if let Some(witness) = args.first() {
            if let TermData::Var(name, _) = terms.get(*witness) {
                max_name_bytes = max_name_bytes.max(name.capacity());
            }
        }
    }
    if bindings == 0 {
        return Ok((proof.steps.len(), 0));
    }

    // `ExtDiffRegistry::collect` traverses each binding's array pair with a
    // fresh visited set, then traverses the problem/assumptions once for
    // freshness. The dependency maps can be dense. Debit those worst cases
    // before entering the uninstrumented collector.
    let traversals = checked_add_usize(bindings, 1)?;
    let dependency_edges = checked_mul_usize(bindings, bindings)?;
    let mut work = checked_mul_usize(traversals, payload.work)?;
    work = checked_add_usize(work, dependency_edges)?;
    work = checked_add_usize(work, proof.steps.len())?;

    let mut bytes = checked_mul_usize(traversals, payload.bytes)?;
    let dependency_entry_bytes =
        checked_add_usize(checked_add_usize(max_name_bytes, size_of::<String>())?, 32)?;
    bytes = checked_add_usize(
        bytes,
        checked_mul_usize(dependency_edges, dependency_entry_bytes)?,
    )?;
    bytes = checked_add_usize(bytes, checked_mul_usize(bindings, 128)?)?;
    Ok((work, bytes))
}

fn proof_producing_bv_classifier_charge(
    proof: &Proof,
    payload: PayloadStats,
) -> Result<(usize, usize), ProofCheckError> {
    let mut tagged_lemmas = 0_usize;
    for step in &proof.steps {
        if matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::BvBitBlast | TheoryLemmaKind::BvBitBlastGate { .. },
                ..
            }
        ) {
            tagged_lemmas = checked_add_usize(tagged_lemmas, 1)?;
        }
    }

    // `bv_bitblast_requires_proof_producer` makes at most two memoized passes
    // over a tagged clause: one BV-content census and one bounded-variable
    // census. Charge two complete authentication payloads per tagged lemma.
    // This deliberately happens before the classifier is called.
    let passes = checked_mul_usize(tagged_lemmas, 2)?;
    Ok((
        checked_mul_usize(payload.work, passes)?,
        checked_mul_usize(payload.bytes, passes)?,
    ))
}

fn meter_step_term_payload(
    step: &ProofStep,
    terms: &TermStore,
    derived_clauses: &[Option<Vec<TermId>>],
    memo: &mut TermCostMemo,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<PayloadStats, ProofCheckError> {
    let mut stats = PayloadStats::default();
    let mut overflow = false;
    let unfolded_work = {
        let mut counting_progress = |work: usize, bytes: usize| {
            let Some(next_work) = stats.work.checked_add(work) else {
                overflow = true;
                return false;
            };
            let Some(next_bytes) = stats.bytes.checked_add(bytes) else {
                overflow = true;
                return false;
            };
            stats.work = next_work;
            stats.bytes = next_bytes;
            progress(work, bytes)
        };

        let mut roots = Vec::new();
        match step {
            ProofStep::Resolution {
                clause,
                pivot,
                clause1,
                clause2,
            } => {
                push_term_slice(&mut roots, clause, &mut counting_progress)?;
                push_term(&mut roots, *pivot, &mut counting_progress)?;
                for premise in [*clause1, *clause2] {
                    if let Some(Some(premise_clause)) = derived_clauses.get(premise.0 as usize) {
                        push_term_slice(&mut roots, premise_clause, &mut counting_progress)?;
                    }
                }
            }
            ProofStep::TheoryLemma { clause, .. } => {
                push_term_slice(&mut roots, clause, &mut counting_progress)?;
            }
            ProofStep::Step {
                clause,
                premises,
                args,
                ..
            } => {
                push_term_slice(&mut roots, clause, &mut counting_progress)?;
                push_term_slice(&mut roots, args, &mut counting_progress)?;
                for premise in premises {
                    if let Some(Some(premise_clause)) = derived_clauses.get(premise.0 as usize) {
                        push_term_slice(&mut roots, premise_clause, &mut counting_progress)?;
                    }
                }
            }
            _ => {}
        }
        stats.order_assignments = crate::checker::order_ite_assignment_count(
            charge_step_payload_walks(terms, &roots, &mut counting_progress)?,
        );
        unfolded_work_memoized(memo, terms, &roots, &mut counting_progress)?
    };
    if overflow {
        Err(ProofCheckError::ResourceLimit)
    } else {
        stats.unfolded_work = unfolded_work;
        Ok(stats)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SemanticChargeClass {
    General,
    ResolutionRoute,
    DatatypeEnumPigeonhole,
    ArrayClauseSchema,
    ProgressFarkas,
    /// The EUF identity/congruence family — `refl`, `symm`, `trans`, `cong`,
    /// `eq_transitive`, `eq_congruent`, `eq_congruent_pred` (as Alethe steps AND
    /// as the corresponding `Euf*` theory lemmas). Their strict validators
    /// compare argument and endpoint terms by `TermId` identity and BFS a
    /// `TermId`-keyed equality graph; NONE descends into an argument's subterms
    /// (verified: crates/ay-proof/src/checker/euf.rs,
    /// crates/ay-proof/src/checker/euf_step_rules.rs). Their worst-case work is
    /// therefore a constant number of passes over the step's reachable DAG,
    /// already metered by the base payload walk — NOT the tree-unfolded payload.
    /// Charging the `General` `unfolded_work^2` product here over-charges by the
    /// square of a store-chain's internal sharing and withheld correctly decided
    /// `storecomm` UNSAT results as `unknown`. See [`EUF_IDENTITY_WORK_FACTOR`].
    EufIdentityRoute,
    /// `TheoryLemmaKind::BoolTautology`, whose validator is the exhaustive
    /// bounded Bool/BV evaluator in [`crate::checker::bv_bitblast`].
    ///
    /// That evaluator enumerates at most `2^MAX_BOUNDED_ASSIGNMENT_BITS`
    /// assignments and, per assignment, walks each literal's TREE once while
    /// resolving every variable through an environment of at most
    /// `MAX_BOUNDED_ASSIGNMENT_BITS` entries (a variable needs at least one
    /// assignment bit). Its worst case is therefore
    /// `assignments * unfolded_work * min(unfolded_work, vars + 1)`, NOT
    /// `assignments * unfolded_work^2`: the second factor saturates at the
    /// environment width. The `General` product ignores that saturation, so any
    /// packed unit with `unfolded_work` above ~1,169 was refused BEFORE the
    /// evaluator ran — including single-literal Tseitin units the recognizer
    /// discharges structurally without evaluating anything at all.
    ///
    /// That threshold is `sqrt(350_000_000 / 256)`, NOT `sqrt(350_000_000)`:
    /// this family carried a private `1 << 8` scale, and dropping it inflates
    /// the figure 16x. (~18,708 IS correct — for the unscaled
    /// `UnorderedClauseMatch` class, not this one.) Measured: at
    /// `unfolded = 2,003` the legacy charge is already 1,027,074,304, i.e. 2.9x
    /// the whole envelope.
    /// See [`BOUNDED_EVAL_ENV_WIDTH`].
    BoundedAssignmentEval,
    /// `AletheRule::Or` (premise-based clause decomposition), whose validator is
    /// [`crate::checker::validate_or_clausification`]: O(1) shape checks and
    /// then `clause_matches_unordered`, which compares `TermId`s PAIRWISE and
    /// never descends into a literal. Its worst case is quadratic in the CLAUSE
    /// LENGTH — tens — while the `General` product bills it the square of the
    /// tree-unfolded term payload, which on heavily-shared BV formulas exceeds
    /// the whole envelope for a step that performs a few hundred integer
    /// comparisons.
    UnorderedClauseMatch,
    /// A TRUST-KIND theory lemma (`TheoryLemmaKind::is_trust()`, today exactly
    /// `Generic`), whose strict route has NO unmodelled cost at all.
    ///
    /// The route is, in order:
    ///
    ///  1. `nia_linear_ideal::validate_linear_ideal_refutation_with_progress`,
    ///     which builds its `WorkMeter` with `with_progress(progress)` and
    ///     debits every rational op, monomial, DAG node and container slot
    ///     through THIS SAME callback — and is additionally capped by that
    ///     meter's own `MAX_BIGRATIONAL_OPS` / `MAX_TOTAL_MONOMIALS` /
    ///     `MAX_DAG_NODES`, so it fails closed on its own;
    ///  2. otherwise an O(clause_len) clone into the deferred-trust collector,
    ///     or an O(1) `UnsupportedTheoryLemmaKind` rejection.
    ///
    /// `private_validator_charge` already says this — it returns `(0, 0)` for
    /// `Generic` with the note that the validator "debits its actual rational,
    /// DAG, and worst-case structural monomial work through the borrowed
    /// progress callback". But `semantic_validator_charge` then takes
    /// `base_work.max(private.0)`, so the `General` `work * unfolded_work`
    /// product was applied anyway and the `(0, 0)` had no effect.
    ///
    /// That double-charge is a live verdict loss, not a theoretical one.
    /// Measured on `array_interface_read_prune::forced_equal_read_distinct_
    /// arrays_remain_unsat` (QF_AX, 48 arrays read at one shared index): ONE
    /// `Generic` lemma with `payload(work = 47_284, unfolded_work = 9_030)`
    /// precharges `47_284 * 9_030 = 426_974_520` against a 350_000_000
    /// envelope — 1.22x the WHOLE envelope in a single charge, with 80_628
    /// consumed. The strict check therefore returned `ResourceLimit`, which is
    /// NOT a trust-kind rejection, so `discharge_trust_steps_for_certification`
    /// was never entered and a correct `unsat` published as `unknown`. With the
    /// charge modelled, the same proof reaches the funnel as
    /// `UnsupportedTheoryLemmaKind { Generic }` and the deferred-trust lane
    /// discharges it.
    ///
    /// Note the payload shape: `work` (47_284 DAG nodes) EXCEEDS
    /// `unfolded_work` (9_030) here, so this is not even the usual
    /// sharing-squared story — the product is simply unrelated to anything the
    /// validator does.
    TrustKindProgressMetered,
}

/// Constant factor over the array clause schemas' quadratic term.
///
/// [`crate::checker::array_axiom`]'s row-chain entry point tries eight
/// sub-schemas, the widest of which pairs every literal with every array-
/// equality premise at up to two witness indices and two orientations. Eight
/// covers that cross product, the two chain parses per candidate, the
/// `sort_unstable` log factor over one chain's entries, and per-node sort
/// comparisons.
const ARRAY_SCHEMA_WORK_FACTOR: usize = 8;

/// Per-unfolded-node allowance for the array schemas' live scratch.
///
/// A store-chain entry is `(TermId, TermId)`, an index/pair set entry is at
/// most that plus hash control bytes and growth slack, and every such entry
/// needs at least one unfolded node to exist. 128 bytes covers the widest
/// entry in any of the sub-schemas' live containers.
const ARRAY_SCHEMA_ENTRY_BYTES: usize = 128;

/// Work factor for [`SemanticChargeClass::EufIdentityRoute`], applied to the
/// step's DAG payload `work` (NOT the tree-unfolded payload).
///
/// The base per-step payload walk already debits `work` once. On top of that a
/// reclassified validator performs at most a small constant number of extra
/// linear passes over the same reachable DAG: decode each literal's leading-not
/// chain, clone the top-level argument lists, build a `TermId`-keyed adjacency
/// map, BFS it, and reconstruct one path — each `O(clause + premises)` and thus
/// `<= work`. Eight covers every such pass with room to spare while staying
/// LINEAR in `work`, so a genuinely wide EUF step still grows its charge and is
/// refused once its real DAG payload is large enough.
const EUF_IDENTITY_WORK_FACTOR: usize = 8;

/// Byte factor for [`SemanticChargeClass::EufIdentityRoute`]. The validators'
/// scratch (edge vector, two `TermId`-keyed hash maps, a BFS queue) is
/// `O(premises)` entries of a `TermId` plus small control words; four times the
/// step's DAG payload bytes dominates it.
const EUF_IDENTITY_BYTE_FACTOR: usize = 4;

/// Saturating second factor for [`SemanticChargeClass::BoundedAssignmentEval`].
///
/// `validate_bounded_clause_semantics` refuses any clause whose bounded
/// variables need more than `MAX_BOUNDED_ASSIGNMENT_BITS` assignment bits, and
/// every bounded variable consumes at least one bit, so the evaluation
/// environment holds at most that many entries. `eval_term` resolves a variable
/// by a LINEAR scan of that environment, and every other node kind is constant
/// work, so one assignment's pass over a literal tree costs at most
/// `unfolded_work * (MAX_BOUNDED_ASSIGNMENT_BITS + 1)`. The `+ 1` covers the
/// per-node dispatch itself, so the bound also holds for a tree with no
/// variables at all.
///
/// This is the ONLY difference from the `General` product, and it is a pure
/// TIGHTENING: `min(unfolded_work, BOUNDED_EVAL_ENV_WIDTH) <= unfolded_work`,
/// so this class never charges more than `General` did for the same step.
const BOUNDED_EVAL_ENV_WIDTH: usize = crate::checker::MAX_BOUNDED_ASSIGNMENT_BITS as usize + 1;

/// Assignment count enumerated by the bounded Bool/BV evaluator.
const BOUNDED_EVAL_ASSIGNMENTS: usize = 1 << crate::checker::MAX_BOUNDED_ASSIGNMENT_BITS;

fn datatype_registry_charge(
    step: &ProofStep,
    payload: PayloadStats,
    datatype_registry: RegistryPayloadStats,
    selector_registry: RegistryPayloadStats,
) -> Result<(usize, usize), ProofCheckError> {
    if matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::DatatypeEnumPigeonhole,
            ..
        }
    ) {
        // One datatype lookup, then one complete selector-registry scan per
        // constructor in the selected datatype. The validator establishes
        // `members > constructors` only after those scans, so malformed input
        // may name a tiny clause beside a huge declaration. Every constructor
        // contributes at least one unit to the retained registry census;
        // charging that full census as the scan count covers both paths.
        let selector_scans = datatype_registry.work.max(1);
        let work = checked_add_usize(
            datatype_registry.work,
            checked_mul_usize(selector_registry.work, selector_scans)?,
        )?;

        // Scratch retained by `flatten_clause_literals`, the member set, and
        // the unordered-pair set. Every accepted equality contributes at least
        // three units to `unfolded_work`, so this per-unit allowance also
        // covers hash-table control bytes and growth slack on malformed inputs.
        let entry_bytes = checked_add_usize(
            checked_add_usize(size_of::<(TermId, TermId)>(), size_of::<TermId>())?,
            64,
        )?;
        let bytes = checked_mul_usize(payload.unfolded_work.max(1), entry_bytes)?;
        return Ok((work, bytes));
    }

    if !matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::DatatypeDistinct
                | TheoryLemmaKind::DatatypeSelectorProject
                | TheoryLemmaKind::DatatypeTesterEval
                | TheoryLemmaKind::DatatypeExhaustive
                | TheoryLemmaKind::DatatypeConstructorReconstruct
                | TheoryLemmaKind::ArrayFiniteExtensionality
                | TheoryLemmaKind::ArrayFiniteSelectExpansion,
            ..
        }
    ) {
        return Ok((0, 0));
    }

    // Each declaration-backed validator can rescan a registry for each
    // decoded literal/constructor. Tester evaluation also has an exhaustive
    // lane with repeated constructor membership checks and may consult the
    // selector registry for a nullary sibling. The retained census charges
    // each UTF-8 comparison unit, and the per-step payload bounds the number
    // of such lookups. Using both registries for every declaration-backed kind
    // is conservative and keeps future accepted schema variants inside the
    // same envelope.
    let registry_work = checked_add_usize(datatype_registry.work, selector_registry.work)?;
    let lookups = payload.work.max(1);
    let work = checked_mul_usize(registry_work, lookups)?;

    // Registry scans borrow their input. Temporary clause/name/argument clones
    // come from the step's reachable payload; eight copies cover the two-way
    // selector projection and tester-exhaustiveness scratch structures.
    let bytes = checked_mul_usize(payload.bytes, 8)?;
    Ok((work, bytes))
}

fn step_clause_len(step: &ProofStep) -> usize {
    match step {
        ProofStep::Assume(_) => 1,
        ProofStep::Resolution { clause, .. }
        | ProofStep::TheoryLemma { clause, .. }
        | ProofStep::Step { clause, .. } => clause.len(),
        ProofStep::Anchor { .. } => 0,
        _ => 0,
    }
}

fn prior_clause_len(derived_clauses: &[Option<Vec<TermId>>], premise: ProofId) -> Option<usize> {
    derived_clauses
        .get(premise.0 as usize)
        .and_then(Option::as_ref)
        .map(Vec::len)
}

fn sort_comparison_bound(len: usize) -> Result<usize, ProofCheckError> {
    if len <= 1 {
        return Ok(len);
    }
    let levels = usize::BITS as usize - (len - 1).leading_zeros() as usize;
    checked_mul_usize(len, checked_add_usize(levels, 1)?)
}

fn binary_resolution_charge(
    left: usize,
    right: usize,
    conclusion: usize,
    literal_decode_work: usize,
) -> Result<(usize, usize), ProofCheckError> {
    let input = checked_add_usize(left, right)?;
    let total = checked_add_usize(input, conclusion)?;

    let mut work = checked_add_usize(sort_comparison_bound(left)?, sort_comparison_bound(right)?)?;
    work = checked_add_usize(work, sort_comparison_bound(conclusion)?)?;
    // The argument-DIRECTED validator (`resolution_exact`) additionally
    // constructs and sorts the resolvent, which has at most `total` literals and
    // receives no progress callback of its own; charge that fourth sort here so
    // the directed path stays covered without the dropped width term.
    work = checked_add_usize(work, sort_comparison_bound(total)?)?;
    // The pivot search itself is no longer precharged here. The argument-free
    // form is decided by `checker::resolution::argfree_binary_resolution_metered`,
    // which finds the pivot in O(total) on the common clean case (one LINEAR
    // difference merge, bounded by the `total`-sized trial charge it debits) and
    // debits any exhaustive fallback trial-by-trial through the strict-check
    // meter (failing closed). Precharging the former `input * (total + 1)` scan
    // worst case here over-charged every ordinary two-premise step by the clause
    // WIDTH — on `QF_AUFLIA/storecomm` 309 ~1000-literal `th_resolution` steps
    // consumed 259M of the 350M envelope and withheld a correctly decided UNSAT.
    // Literal decoding walks each literal's COMPLETE leading-not chain, then
    // treats the atom below it as an opaque `TermId` — it never descends into
    // the atom's arguments. `literal_decode_work` is the step's reachable-DAG
    // payload `work`, which counts every `Not` node once and therefore upper-
    // bounds the total leading-not length across the step's clauses; it is NOT
    // the tree-unfolded payload (that squared a store-chain's internal sharing
    // and withheld correct `storecomm` UNSAT results). Both routes make one
    // decoding pass per clause (`clause_as_set` for the argument-free form,
    // `clause_as_unique_set` plus one pivot per link for the argument-directed
    // one); four passes cover either with room to spare. Without this the
    // exemption in `SemanticChargeClass::ResolutionRoute` would leave deep
    // negation chains unpaid.
    work = checked_add_usize(work, checked_mul_usize(literal_decode_work, 4)?)?;

    // Exactly three decoded sets are built — both premises and the conclusion,
    // `total` literals in all — and `resolves_to` is documented and written to
    // merge them WITHOUT allocating a resolvent, which is why the byte term is
    // linear. Four copies cover the sets, the argument-directed form's one
    // resolvent per link, and `Vec` growth slack.
    //
    // The superseded `pairs * total * 36` term modelled one full resolvent
    // allocation per candidate pivot, which this path does not perform: on
    // `QF_AX/storecomm/storecomm_t1_np_nf_ai_00030_005.cvc` it demanded 6.7 MB
    // for one 23+23 -> 304 step, and such steps exhausted the 1.34 GB byte
    // envelope 568 steps into the proof.
    let decoded_bytes =
        checked_mul_usize(checked_mul_usize(total, 4)?, size_of::<(TermId, bool)>())?;
    Ok((work, decoded_bytes))
}

fn chain_resolution_charge(
    premises: &[ProofId],
    derived_clauses: &[Option<Vec<TermId>>],
    conclusion: usize,
    argument_free_unit_tail: bool,
    literal_decode_work: usize,
) -> Result<(usize, usize), ProofCheckError> {
    if premises.len() < 2 {
        return Ok((0, 0));
    }
    let mut total = conclusion;
    let mut max_premise = 0_usize;
    let mut first_premise = 0_usize;
    for (index, premise) in premises.iter().enumerate() {
        let Some(len) = prior_clause_len(derived_clauses, *premise) else {
            // Premise linkage rejects before entering chain search.
            return Ok((0, 0));
        };
        total = checked_add_usize(total, len)?;
        max_premise = max_premise.max(len);
        if index == 0 {
            first_premise = len;
        }
    }

    if argument_free_unit_tail {
        // Validation performs one shape scan, decodes every first/tail/target
        // literal through its complete leading-not chain, inserts first and
        // target clauses into deterministic sets, removes each unit exactly
        // once, then compares the two remaining sets.
        let set_entries = checked_add_usize(first_premise, conclusion)?;
        let hash_operations = checked_add_usize(total, set_entries)?;
        let shape_scans = checked_mul_usize(premises.len(), 3)?;
        let work = checked_add_usize(
            literal_decode_work,
            checked_add_usize(hash_operations, shape_scans)?,
        )?;
        let hash_entry_bytes = checked_add_usize(size_of::<(TermId, bool)>(), 32)?;
        let bytes = checked_mul_usize(set_entries, hash_entry_bytes)?;
        return Ok((work, bytes));
    }

    // ENTRY COST ONLY. The bounded ambiguity search now charges each link as it
    // is explored (`checker::resolution::validate_chain_resolution_rule`), so
    // pre-charging its worst case here would double-charge the ordinary
    // unambiguous chain — and did so at two orders of magnitude, exhausting the
    // byte envelope on proofs whose steps each allocate tens of kilobytes.
    //
    // What still must be paid up front is everything that happens WITHOUT a
    // per-link charge: the two entry sets, and — on the argument-DIRECTED path,
    // which folds the chain linearly and never enters the search — one decoded
    // set per link. `branch_budget + 1` decoding passes over the step's
    // reachable-DAG literal payload (`literal_decode_work`) covers both,
    // including complete leading-not chains — the DAG payload counts every `Not`
    // node once and so bounds the total not-chain length — and the sort inside
    // each set construction (its `log2(total)` factor is far below
    // `branch_budget`).
    let branch_budget = checked_add_usize(checked_mul_usize(premises.len(), 4)?, 256)?;
    let decode_passes =
        checked_mul_usize(checked_add_usize(branch_budget, 1)?, literal_decode_work)?;
    let entry_literals = checked_mul_usize(total, 2)?;
    Ok((
        checked_add_usize(decode_passes, entry_literals)?,
        checked_mul_usize(entry_literals, size_of::<(TermId, bool)>())?,
    ))
}

fn is_argument_free_unit_tail_resolution(
    step: &ProofStep,
    derived_clauses: &[Option<Vec<TermId>>],
) -> bool {
    let ProofStep::Step {
        rule: AletheRule::Resolution | AletheRule::ThResolution,
        premises,
        args,
        ..
    } = step
    else {
        return false;
    };
    args.is_empty()
        && premises.len() >= 3
        && premises[1..]
            .iter()
            .all(|premise| prior_clause_len(derived_clauses, *premise) == Some(1))
}

fn drup_charge(
    derived_literal_count: usize,
    conclusion: usize,
) -> Result<(usize, usize), ProofCheckError> {
    let all_literals = checked_add_usize(derived_literal_count, conclusion)?;
    let iterations = checked_add_usize(all_literals, 1)?;
    Ok((
        checked_mul_usize(all_literals, iterations)?,
        checked_mul_usize(all_literals, checked_add_usize(size_of::<TermId>(), 32)?)?,
    ))
}

/// Pick the charge model for `step`. Every non-`General` class either
/// replaces the general recursive-tree estimate with a route-specific meter or
/// identifies a private allocation path charged dynamically by the checker.
fn select_semantic_charge_class(step: &ProofStep, terms: &TermStore) -> SemanticChargeClass {
    if matches!(
        step,
        ProofStep::Resolution { .. }
            | ProofStep::Step {
                rule: AletheRule::Resolution | AletheRule::ThResolution,
                ..
            }
    ) {
        return SemanticChargeClass::ResolutionRoute;
    }
    if matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::DatatypeEnumPigeonhole,
            ..
        }
    ) {
        return SemanticChargeClass::DatatypeEnumPigeonhole;
    }
    if matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArrayRowChain | TheoryLemmaKind::ArrayStorePermutation,
            ..
        }
    ) {
        return SemanticChargeClass::ArrayClauseSchema;
    }
    if farkas_meter::uses_progress_meter(step, terms) {
        return SemanticChargeClass::ProgressFarkas;
    }
    if is_euf_identity_route(step) {
        return SemanticChargeClass::EufIdentityRoute;
    }
    if matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BoolTautology,
            ..
        }
    ) {
        return SemanticChargeClass::BoundedAssignmentEval;
    }
    if matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Or | AletheRule::OrPos(_),
            ..
        }
    ) {
        return SemanticChargeClass::UnorderedClauseMatch;
    }
    // Placed LAST so every kind with its own modelled route above keeps it;
    // only the trust-kind fallthrough reaches here.
    if matches!(step, ProofStep::TheoryLemma { kind, .. } if kind.is_trust()) {
        return SemanticChargeClass::TrustKindProgressMetered;
    }
    SemanticChargeClass::General
}

/// Recognize the EUF identity/congruence family whose strict validators are
/// bounded by the step's reachable DAG (no descent into argument subterms), in
/// BOTH its Alethe-step and theory-lemma spellings. Kept as a conservative
/// allowlist: any rule NOT proven `TermId`-identity bounded stays `General` and
/// keeps the conservative tree-unfolded charge.
fn is_euf_identity_route(step: &ProofStep) -> bool {
    match step {
        ProofStep::Step {
            rule:
                AletheRule::Refl
                | AletheRule::Symm
                | AletheRule::Trans
                | AletheRule::Cong
                | AletheRule::EqTransitive
                | AletheRule::EqCongruent
                | AletheRule::EqCongruentPred,
            ..
        } => true,
        ProofStep::TheoryLemma {
            kind:
                TheoryLemmaKind::EufReflexive
                | TheoryLemmaKind::EufTransitive
                | TheoryLemmaKind::EufCongruent
                | TheoryLemmaKind::EufCongruentPred,
            ..
        } => true,
        _ => false,
    }
}

fn strict_semantic_charge(
    step: &ProofStep,
    semantic_payload: PayloadStats,
    semantic_class: SemanticChargeClass,
) -> Result<(usize, usize), ProofCheckError> {
    // `ArrayRowChain` AND `ArrayStorePermutation` meter their ACTUAL validation
    // work through the strict-check progress callback inside their validators
    // ([`crate::checker::validate_array_row_chain`] /
    // [`crate::checker::validate_array_store_permutation`]) — the same
    // (0,0)-precharge-then-debit-actual pattern `ResolutionRoute`/`Generic`
    // lemmas use — so they take NO up-front semantic precharge here. The former
    // `ArrayClauseSchema` precharge (`~8 * unfolded_work^2`) is quadratic in the
    // step's unfolded payload, hence QUARTIC in the store-chain length for the
    // store-commutativity clause shape (whose `O(P^2)` index-pair literal count
    // makes `unfolded_work` itself `Θ(P^2)`); it over-charged the common
    // genuinely-`O(L + P^2)` shape and withheld a correctly decided `storecomm`
    // UNSAT. Both validators now debit a tight `O(L + P^2)` bound per node/pair
    // and fail closed on an adversarial clause.
    if matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArrayRowChain | TheoryLemmaKind::ArrayStorePermutation,
            ..
        }
    ) {
        Ok((0, 0))
    } else if matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Hole | AletheRule::Trust,
            ..
        }
    ) {
        // A hole/trust step has NO semantic validator to reserve for: the
        // strict checker rejects it in O(1) with the typed
        // `HoleStep`/`TrustStep` refusal, and the non-strict lanes skip it.
        // Billing the General tree-unfolded estimate here charged a single
        // 1000-literal hole 285M+ work — exhausting the whole envelope and
        // masking the TYPED refusal (`ResourceLimit` instead of `HoleStep`),
        // which starves every downstream repair lane keyed on that reason.
        // The structural per-step charge in `strict_step_charge` still
        // applies, so an adversarial million-hole document remains bounded.
        Ok((0, 0))
    } else {
        semantic_validator_charge(step, semantic_payload, semantic_class)
    }
}

fn strict_step_charge(
    terms: &TermStore,
    step: &ProofStep,
    derived_clauses: &[Option<Vec<TermId>>],
    derived_literal_count: usize,
    semantic_payload: PayloadStats,
) -> Result<(usize, usize), ProofCheckError> {
    let clause_len = step_clause_len(step);
    let argument_free_unit_tail = is_argument_free_unit_tail_resolution(step, derived_clauses);
    let (mut work, mut bytes) = match step {
        ProofStep::Assume(_) => (1, size_of::<TermId>()),
        ProofStep::Resolution { clause, .. } | ProofStep::TheoryLemma { clause, .. } => (
            checked_add_usize(clause.len(), 1)?,
            checked_mul_usize(clause.len(), size_of::<TermId>())?,
        ),
        ProofStep::Step {
            clause,
            premises,
            args,
            ..
        } => {
            let base_work = checked_add_usize(clause.len(), premises.len())?;
            let base_work = checked_add_usize(checked_add_usize(base_work, args.len())?, 1)?;
            let clause_bytes = checked_mul_usize(clause.len(), size_of::<TermId>())?;
            let premise_view_bytes = checked_mul_usize(premises.len(), size_of::<&[TermId]>())?;
            (
                base_work,
                checked_add_usize(clause_bytes, premise_view_bytes)?,
            )
        }
        ProofStep::Anchor { variables, .. } => (checked_add_usize(variables.len(), 1)?, 0),
        _ => (1, 0),
    };

    let expensive = match step {
        ProofStep::Resolution {
            clause1, clause2, ..
        } => match (
            prior_clause_len(derived_clauses, *clause1),
            prior_clause_len(derived_clauses, *clause2),
        ) {
            (Some(left), Some(right)) => {
                binary_resolution_charge(left, right, clause_len, semantic_payload.unfolded_work)?
            }
            _ => (0, 0),
        },
        ProofStep::Step {
            rule: AletheRule::Resolution | AletheRule::ThResolution,
            premises,
            ..
        } if premises.len() == 2 => match (
            prior_clause_len(derived_clauses, premises[0]),
            prior_clause_len(derived_clauses, premises[1]),
        ) {
            (Some(left), Some(right)) => {
                binary_resolution_charge(left, right, clause_len, semantic_payload.unfolded_work)?
            }
            _ => (0, 0),
        },
        ProofStep::Step {
            rule: AletheRule::Resolution | AletheRule::ThResolution,
            premises,
            ..
        } => chain_resolution_charge(
            premises,
            derived_clauses,
            clause_len,
            argument_free_unit_tail,
            semantic_payload.unfolded_work,
        )?,
        ProofStep::Step {
            rule: AletheRule::Drup,
            ..
        } => drup_charge(derived_literal_count, clause_len)?,
        _ => (0, 0),
    };
    work = checked_add_usize(work, expensive.0)?;
    bytes = checked_add_usize(bytes, expensive.1)?;
    let semantic_class = select_semantic_charge_class(step, terms);
    let semantic = strict_semantic_charge(step, semantic_payload, semantic_class)?;
    work = checked_add_usize(work, semantic.0)?;
    bytes = checked_add_usize(bytes, semantic.1)?;
    Ok((work, bytes))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GenericTheoryDeferral {
    Reject,
    Collect,
}

// This is the single boundary that threads the complete proof-validation
// context into the strict pass; bundling these borrowed registries would only
// obscure their distinct provenance and lifetime contracts.
#[allow(clippy::too_many_arguments)]
fn validate_strict_steps_with_context(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    datatype_member_signatures: Option<&[DatatypeMemberSignature]>,
    problem_assertions: Option<&[TermId]>,
    generic_theory_deferral: GenericTheoryDeferral,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<StrictValidationArtifacts, ProofCheckError> {
    charge_progress(progress, 1, 0)?;
    if proof.steps.is_empty() {
        return Err(ProofCheckError::EmptyProof);
    }

    let authentication_stats = meter_authentication_payload(
        proof,
        terms,
        dt_decls,
        ctor_selectors,
        datatype_member_signatures,
        problem_assertions,
        progress,
    )?;
    let payload_stats = authentication_stats.aggregate;

    if let Some(signatures) = datatype_member_signatures {
        validate_datatype_signature_context(terms, dt_decls, ctor_selectors, signatures)?;
    }

    // Cover the proof scan that counts tagged lemmas, then debit both complete
    // memoized classifier passes before either one can execute.
    charge_progress(progress, proof.steps.len(), 0)?;
    let (bv_classifier_work, bv_classifier_bytes) =
        proof_producing_bv_classifier_charge(proof, payload_stats)?;
    charge_progress(progress, bv_classifier_work, bv_classifier_bytes)?;
    // The aggregate budget preflight performs a separate whole-proof census:
    // it classifies tagged bit-blast lemmas and counts BV/LIA lemmas. Debit
    // that second linear scan before it runs.
    charge_progress(progress, proof.steps.len(), 0)?;
    let expensive_bv_charge = crate::checker::validate_expensive_bv_budget(proof, terms)?;
    // Proof-producing BV and BV/LIA lemmas enter checkers with large private
    // limits. Debit the exact per-kind published maxima against the caller's
    // ONE aggregate envelope before entering either replay path.
    charge_progress(
        progress,
        expensive_bv_charge.work,
        expensive_bv_charge.bytes,
    )?;
    charge_progress(progress, 0, 0)?;

    if let Some(assertions) = problem_assertions {
        validate_problem_assumptions_metered(proof, terms, assertions, progress)?;
    }

    // Built ONCE, before any step is validated: construction is where the
    // whole-proof conditions (bound once, fresh against the problem, not
    // self-referential) are enforced, so a bad introduction fails the check
    // even when no lemma ever cites it.
    let (ext_diff_work, ext_diff_bytes) = ext_diff_registry_charge(proof, terms, payload_stats)?;
    charge_progress(progress, ext_diff_work, ext_diff_bytes)?;
    let ext_diff = match problem_assertions {
        Some(assertions) => Some(ExtDiffRegistry::collect(proof, terms, assertions)?),
        None => None,
    };
    charge_progress(progress, 0, 0)?;

    // Unlike ext-diff introductions, the empty-set equality closure has no
    // whole-proof validity condition of its own. Build it only when a lemma
    // actually consults it, then use the registry's metered linear BFS.
    let needs_empty_set_registry = proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::SetCardEmptyByAssertion,
                ..
            }
        )
    });
    let empty_sets = match (needs_empty_set_registry, problem_assertions) {
        (true, Some(assertions)) => Some(crate::checker::EmptySetRegistry::collect_with_progress(
            terms, assertions, progress,
        )?),
        _ => None,
    };

    let mut quality = ProofQuality::default();
    let derived_table_bytes =
        checked_mul_usize(proof.steps.len(), size_of::<Option<Vec<TermId>>>())?;
    charge_progress(progress, 1, derived_table_bytes)?;
    let mut derived_clauses: Vec<Option<Vec<TermId>>> = Vec::with_capacity(proof.steps.len());
    let mut derived_literal_count = 0_usize;
    let mut deferred_generic = Vec::new();

    if generic_theory_deferral == GenericTheoryDeferral::Collect {
        let mut deferred_count = 0_usize;
        let mut deferred_literals = 0_usize;
        for step in &proof.steps {
            if let ProofStep::TheoryLemma {
                clause,
                kind: TheoryLemmaKind::Generic,
                ..
            } = step
            {
                deferred_count = checked_add_usize(deferred_count, 1)?;
                deferred_literals = checked_add_usize(deferred_literals, clause.len())?;
            }
        }
        let entry_bytes = checked_mul_usize(deferred_count, size_of::<(ProofId, Vec<TermId>)>())?;
        let literal_bytes = checked_mul_usize(deferred_literals, size_of::<TermId>())?;
        charge_progress(
            progress,
            checked_add_usize(deferred_count, deferred_literals)?,
            checked_add_usize(entry_bytes, literal_bytes)?,
        )?;
        deferred_generic = Vec::with_capacity(deferred_count);
    }

    // A2: pure `cost()` values are memoized once per validation; every
    // payload work/byte charge stays per-step (see `TermCostMemo`). The memo
    // never outlives this validation, and the `check_bounded_finite_enum_proof`
    // route inherits it by construction — this loop is the only production
    // caller of `meter_step_term_payload`.
    let mut term_cost_memo = TermCostMemo::default();

    for (idx, step) in proof.steps.iter().enumerate() {
        let semantic_payload =
            semantic_payload::meter(step, terms, &derived_clauses, &mut term_cost_memo, progress)?;
        let (mut step_work, mut step_bytes) = strict_step_charge(
            terms,
            step,
            &derived_clauses,
            derived_literal_count,
            semantic_payload,
        )?;
        let registry_charge = datatype_registry_charge(
            step,
            semantic_payload,
            authentication_stats.datatype_registry,
            authentication_stats.selector_registry,
        )?;
        step_work = checked_add_usize(step_work, registry_charge.0)?;
        step_bytes = checked_add_usize(step_bytes, registry_charge.1)?;
        charge_progress(progress, step_work, step_bytes)?;
        classify_step(step, &mut quality);
        let collect_this_generic = generic_theory_deferral == GenericTheoryDeferral::Collect
            && matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::Generic,
                    ..
                }
            );
        validate_step_with_datatypes_and_progress(
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
            collect_this_generic.then_some(&mut deferred_generic),
            progress,
        )?;
        derived_literal_count = checked_add_usize(derived_literal_count, step_clause_len(step))?;
        // Validators such as BV replay own internal deadlines. This zero-cost
        // poll observes caller cancellation/deadline immediately on return.
        charge_progress(progress, 0, 0)?;
    }

    // Per-step Skolem validation establishes the substitution shape and live
    // witness registration. Soundness also requires a whole-fragment partial
    // bijection: one witness cannot acquire two incompatible forall sources,
    // and one source cannot be rebound to multiple witnesses. Keep this in the
    // shared strict-step path so both full refutations and premise-only
    // authentication enforce the same global provenance invariant.
    charge_progress(progress, checked_add_usize(proof.steps.len(), 1)?, 0)?;
    if proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Skolem,
                ..
            }
        )
    }) {
        // The uniqueness pass re-runs the bounded Skolem substitution check
        // with one proof-wide 100k meter after each per-step validation.
        charge_progress(progress, 100_000, 8 * 1024 * 1024)?;
    }
    quantifier::validate_sko_forall_uniqueness(proof, terms)?;

    quality.total_steps = proof.steps.len() as u32;
    charge_progress(progress, 0, 0)?;
    Ok((quality, derived_clauses, deferred_generic))
}

/// Fail-closed re-validation of every `TheoryLemmaKind::ArrayExtensionality`
/// step in `proof` against the problem's assertions.
///
/// The `--self-check` gate consults the PARTIAL (non-strict) checker, which
/// admits theory lemmas as axioms on the strength of their recorded kind. That
/// is fine for kinds whose clause is a tautology, but extensionality is not one
/// — relabelling a clause `ArrayExtensionality` would otherwise be enough to
/// ship it. This runs the provenance half of the check independently:
///
///  * every diff-witness introduction is well formed, bound ONCE, and names a
///    symbol that occurs in NO problem assertion and NO `assume` of the proof;
///  * every extensionality lemma matches the exact one-or-more-level schema and
///    every witness cites the intermediate pair it was introduced for.
///
/// Returns `Ok(())` for a proof with no extensionality content at all.
///
/// # Errors
///
/// Returns the first [`ProofCheckError`] describing why the extensionality
/// content cannot be certified; the caller must degrade the verdict.
pub fn validate_array_extensionality_provenance(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
) -> Result<(), ProofCheckError> {
    let registry = ExtDiffRegistry::collect(proof, terms, problem_assertions)?;
    for (idx, step) in proof.steps.iter().enumerate() {
        let ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArrayExtensionality,
            clause,
            ..
        } = step
        else {
            continue;
        };
        crate::checker::validate_array_extensionality_for_provenance(
            terms,
            ProofId(idx as u32),
            clause,
            Some(&registry),
        )?;
    }
    Ok(())
}

fn classify_step(step: &ProofStep, quality: &mut ProofQuality) {
    match step {
        ProofStep::Assume(_) => quality.assume_count += 1,
        ProofStep::TheoryLemma { kind, .. } => {
            quality.theory_lemma_count += 1;
            // Theory lemmas that export as `trust` in Alethe contribute
            // unverified steps — count them in trust_count too (#5657).
            if kind.is_trust() {
                quality.trust_count += 1;
                quality.trust_theory_kinds.push(*kind);
            }
        }
        ProofStep::Resolution { .. } => quality.resolution_count += 1,
        ProofStep::Step { rule, premises, .. } => match rule {
            AletheRule::Resolution => quality.resolution_count += 1,
            AletheRule::ThResolution => quality.th_resolution_count += 1,
            AletheRule::Trust => {
                quality.trust_count += 1;
                if !premises.is_empty() {
                    quality.trust_fallback_count += 1;
                }
            }
            AletheRule::Hole => quality.hole_count += 1,
            AletheRule::Drup => quality.drup_count += 1,
            _ => quality.other_rule_count += 1,
        },
        ProofStep::Anchor { .. } => quality.other_rule_count += 1,
        _ => unreachable!("unexpected ProofStep variant"),
    }
}

#[cfg(test)]
#[path = "quality_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "quality_a2_poll_tests.rs"]
mod a2_poll_tests;

#[cfg(test)]
#[path = "quality_finite_enum_meter_tests.rs"]
mod finite_enum_meter_tests;
