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

#[cfg(test)]
use crate::checker::validate_datatype_signature_context;
use crate::checker::{
    ensure_terminal_empty_clause, quantifier, validate_datatype_signature_context_with_progress,
    validate_step, validate_step_with_datatypes_and_progress, DatatypeMemberSignature,
    ExtDiffRegistry, FreshDefRegistry, ProofCheckError,
};
use crate::partial::PartialProofCheck;

type DerivedClauses = Vec<Option<Vec<TermId>>>;
type DeferredGenericClauses = Vec<(ProofId, Vec<TermId>)>;
type StrictValidationArtifacts = (ProofQuality, DerivedClauses, DeferredGenericClauses);

#[path = "quality/authentication_payload.rs"]
mod authentication_payload;
mod closed_bv_relation_charge;
mod euf_frontier_payload;
mod farkas_meter;
mod native_fp;
mod nra_sos_payload;
mod problem_assumptions;
#[path = "quality/retained.rs"]
pub(crate) mod retained;
mod semantic_payload;
pub use native_fp::{
    check_proof_strict_with_native_fp_context, NativeFpProofContext, NativeFpSnapshotQuality,
};
mod step_semantic_charge;
use authentication_payload::meter_authentication_payload;
use problem_assumptions::validate_problem_assumptions_with_progress;
use step_semantic_charge::{
    is_clause_identity_route, is_euf_identity_route, strict_semantic_charge,
};
mod term_cost_memo;
use term_cost_memo::{unfolded_work_memoized_with_progress, TermCostMemo};

#[path = "quality/and_pos_charge.rs"]
mod and_pos_charge;
#[path = "quality/quantifier_charge.rs"]
mod quantifier_charge;
#[path = "quality/semantic_charge.rs"]
mod semantic_charge;
use semantic_charge::semantic_validator_charge;
pub(crate) use semantic_charge::FOLDED_READ_UNIT_WORK;

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
    let mut unbounded = |_: usize, _: usize| true;
    check_proof_partial_with_quality_and_progress(proof, terms, &mut unbounded)
}

/// [`check_proof_partial_with_quality`] under a CALLER-OWNED resource and
/// cancellation envelope (#proof-tax, #diagnostic-envelope).
///
/// WHY THIS EXISTS. The mandatory UNSAT certification gate
/// (`check_proof_strict_with_typed_context_and_progress`) has always run under
/// the caller's envelope, so a raised interrupt, a passed solve deadline or a
/// breached memory limit stops it. The DIAGNOSTIC walk that runs beside it —
/// this one, whose output feeds `--self-check` bookkeeping and
/// `(get-info :all-statistics)` and can never make a verdict MORE accepting —
/// had no envelope at all: every path bottomed out in
/// `validate_step_with_datatypes`, which hardcodes `|_, _| true`. On a
/// triangular resolution proof (measured from deductive-checks's datatype+quantifier
/// encoding: 126,548 steps, 393,087,456 clause literals, widest clause 28,026)
/// that unmetered walk ran for 474.565 s and then 481.779 s while the caller's
/// 30 s budget and its 130 s hang watchdog were already expired — neither could
/// reach it, because nothing on this path polls anything.
///
/// The refusal is `ProofCheckError::ResourceLimit`, which every caller already
/// treats as "this proof was not checked". That is fail-closed in the only
/// direction that matters: it can withdraw a self-certification, never grant
/// one.
///
/// Semantics are otherwise IDENTICAL to [`check_proof_partial_with_quality`] —
/// same checker, same step order, same hole handling, same first-error
/// semantics — and passing an always-true meter reproduces it exactly.
pub fn check_proof_partial_with_quality_and_progress(
    proof: &Proof,
    terms: &TermStore,
    progress: &mut dyn FnMut(usize, usize) -> bool,
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

        match validate_step_with_datatypes_and_progress(
            terms,
            &mut derived_clauses,
            ProofId(idx as u32),
            step,
            false,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            progress,
        ) {
            Ok(()) => result.checked_steps += 1,
            Err(e) => return (result, None, Some(e)),
        }
    }

    quality.total_steps = proof.steps.len() as u32;
    // #completed-check-accepted: bookkeeping over steps already walked, so no
    // callback -- a stop that arrives after the last step does not undo it.
    if let Err(e) = ensure_terminal_empty_clause(&derived_clauses) {
        return (result, None, Some(e));
    }

    // FIDELITY to the legacy pair: `check_proof_with_quality` runs the
    // Skolem/forall uniqueness check before it returns, and a failure there
    // made the executor's quality slot `None` while leaving
    // `check_proof_partial`'s own verdict untouched (it never ran that check).
    // Reproduce both halves exactly.
    let quality = (result.skipped_hole_steps == 0
        && quantifier::validate_sko_forall_uniqueness(proof, terms).is_ok())
    .then_some(quality);
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
    debug_assert_eq!(deferred_generic, []);
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
    debug_assert_eq!(deferred_generic, []);
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
/// No callback follows the final step's validation: a refusal can stop the
/// walk before or between steps, never undo one that validated every step.
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
    debug_assert_eq!(deferred_generic, []);
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
    debug_assert_eq!(deferred_generic, []);
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
    fp_assignments: usize,
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
    // Live callers can supply a restored store with a valid root but a
    // dangling descendant. Authenticate every visited handle before indexing,
    // not only the roots named directly by a proof step.
    if term.index() >= terms.len() {
        return Err(ProofCheckError::MalformedProofBundle {
            reason: "reachable proof term is out of bounds".into(),
        });
    }
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
///   (it moved, memoized, into [`unfolded_work_memoized_with_progress`]).
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
) -> Result<(usize, usize), ProofCheckError> {
    let mut completed: DetHashSet<TermId> = DetHashSet::default();
    let mut active: DetHashSet<TermId> = DetHashSet::default();
    let mut stack: Vec<(TermId, bool)> = Vec::new();
    let mut discovered: Vec<TermId> = Vec::new();
    let mut children: Vec<TermId> = Vec::new();
    let mut order_variables = 0usize;
    let mut fp_variable_bits = 0u32;

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
            if matches!(terms.get(term), TermData::Var(_, _)) {
                if let Sort::FloatingPoint(eb, sb) = terms.sort(term) {
                    // The independent classifier enumerates distinct FP
                    // variables, at most 16 total bits. Wider clauses either
                    // take a width-independent schema or are refused, so the
                    // existing 65,536 ceiling remains a conservative bound.
                    fp_variable_bits = fp_variable_bits
                        .saturating_add(*eb)
                        .saturating_add(*sb)
                        .min(16);
                }
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
    Ok((order_variables, 1usize << fp_variable_bits))
}

fn ext_diff_registry_charge(
    proof: &Proof,
    terms: &TermStore,
    payload: PayloadStats,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(usize, usize), ProofCheckError> {
    charge_progress(progress, 0, 0)?;
    let mut bindings = 0_usize;
    let mut max_name_bytes = 0_usize;
    for step in &proof.steps {
        charge_progress(progress, 0, 0)?;
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
    charge_progress(progress, 0, 0)?;
    if bindings == 0 {
        return Ok((proof.steps.len(), 0));
    }

    // `ExtDiffRegistry::collect` traverses each binding's array pair with a
    // fresh visited set, then traverses the problem/assumptions once for
    // freshness. The dependency maps can be dense. Debit those worst cases
    // before entering the collector. Inner polls add cancellation, not a new
    // work/byte charge: the aggregate reservation remains unchanged.
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

/// Debit `FreshDefRegistry::collect`'s worst case before entering it.
///
/// Like `ext_diff_registry_charge`, the registry it guards is built ONCE and
/// before any step: `FreshDefRegistry::collect` is where freshness,
/// single-definiens and non-recursiveness are decided, and a malformed
/// introduction must fail the check even when no later step cites it. Unlike
/// `ext_diff` the registry is built with OR without a problem assertion set —
/// see `FreshDefRegistry::collect` for why `None` there must not fail closed.
///
/// The collector is two DAG traversals with SHARED visited sets — one over the
/// problem assertions and the proof's `assume` leaves, one over the recorded
/// definientia — plus one linear scan of the proof. `payload.work` already
/// bounds a whole-proof traversal, so two of them dominate.
fn fresh_def_registry_charge(
    proof: &Proof,
    payload: PayloadStats,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(usize, usize), ProofCheckError> {
    charge_progress(progress, 0, 0)?;
    let mut bounds = 0_usize;
    for step in &proof.steps {
        charge_progress(progress, 0, 0)?;
        // A `divmod_def` step binds TWO symbols, so it is charged twice.
        let introduced = match step {
            ProofStep::Step {
                rule: AletheRule::FreshDefBound | AletheRule::FreshDefEq,
                ..
            } => 1,
            ProofStep::Step {
                rule: AletheRule::DivModDef,
                ..
            } => 2,
            _ => 0,
        };
        bounds = checked_add_usize(bounds, introduced)?;
    }
    charge_progress(progress, 0, 0)?;
    if bounds == 0 {
        return Ok((proof.steps.len(), 0));
    }
    let mut work = checked_mul_usize(2, payload.work)?;
    work = checked_add_usize(work, proof.steps.len())?;
    let mut bytes = checked_mul_usize(2, payload.bytes)?;
    bytes = checked_add_usize(bytes, checked_mul_usize(bounds, 128)?)?;
    Ok((work, bytes))
}

fn proof_producing_bv_classifier_charge(
    proof: &Proof,
    payload: PayloadStats,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(usize, usize), ProofCheckError> {
    charge_progress(progress, 0, 0)?;
    let mut tagged_lemmas = 0_usize;
    let mut closed_lia_planners = 0_usize;
    for step in &proof.steps {
        charge_progress(progress, 0, 0)?;
        if matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::BvBitBlast | TheoryLemmaKind::BvBitBlastGate { .. },
                ..
            }
        ) {
            tagged_lemmas = checked_add_usize(tagged_lemmas, 1)?;
        }
        if matches!(step, ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BvLiaTautology, clause, farkas: None, lia: None, ..
        } if clause.len() == 1)
        {
            closed_lia_planners = checked_add_usize(closed_lia_planners, 1)?;
        }
    }

    charge_progress(progress, 0, 0)?;
    // `bv_bitblast_requires_proof_producer` makes at most two memoized passes
    // over a tagged clause: one BV-content census and one bounded-variable
    // census. Charge two complete authentication payloads per tagged lemma.
    // This deliberately happens before the classifier is called.
    let passes = checked_mul_usize(tagged_lemmas, 2)?;
    // Pay bounded, allocation-free closed-Bool BV/LIA source peeks BEFORE
    // aggregate classification. The step-only screen itself reads no terms.
    let planner = checked_mul_usize(
        closed_lia_planners,
        crate::checker::bv_bitblast::CLOSED_BV_LIA_CLASSIFIER_WORK,
    )?;
    Ok((
        checked_add_usize(checked_mul_usize(payload.work, passes)?, planner)?,
        checked_mul_usize(payload.bytes, passes)?,
    ))
}

/// Charge the literal decode of one clause — one unit per literal plus one
/// per leading `not` — and the `TermId` slots that hold it.
fn charge_decode_literals(
    terms: &TermStore,
    literals: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
    stats: &mut PayloadStats,
) -> Result<(), ProofCheckError> {
    let mut work = 0usize;
    for &literal in literals {
        let mut units = 1usize;
        let mut atom = literal;
        while let TermData::Not(inner) = terms.get(atom) {
            atom = *inner;
            units = checked_add_usize(units, 1)?;
        }
        work = checked_add_usize(work, units)?;
    }
    let bytes = checked_mul_usize(literals.len(), size_of::<TermId>())?;
    charge_progress(progress, work, bytes)?;
    stats.work = checked_add_usize(stats.work, work)?;
    stats.bytes = checked_add_usize(stats.bytes, bytes)?;
    Ok(())
}

/// The semantic payload of a resolution-family step
/// (#literal-decode-payload).
///
/// WHY. The resolution validators — `checker::resolution` (argument-free
/// binary and chain) and `checker::resolution_exact` (pivot-directed) — read
/// a literal by walking its leading-`not` chain and then treat the atom as an
/// opaque `TermId`; none of them descends into an atom (verified: every
/// `terms.get` in both modules sits inside `decode_literal` /
/// `with_outer_not`). The reachable-DAG walk [`meter_step_term_payload`]
/// performs for every other step was therefore pure overhead here, and
/// SUPER-LINEAR overhead: it re-walked the whole DAG under every literal of
/// the clause and of BOTH premises, once per step.
///
/// Measured with `--probe-strict-check` on
/// `QF_UF/QG-classification/loops6/gensys_icl102` (unbudgeted, explicit
/// proof demand): 4,221 binary resolution steps re-walked 68,056,607 payload
/// units — about 16K DAG nodes per step — and drove the BYTE limb to
/// 1,279,858,280 of 1,342,177,280 (95%), while `binary_resolution_charge`
/// was handed the TREE-unfolded figure (40,253,907) as `literal_decode_work`,
/// against its own contract, and charged four times it; the walk was refused
/// at `349994739+6414 of 350000000` with the validators' real decode work in
/// the low millions. On `QF_AX/swap/swap_t3_np_nf_ai_00008_005` the same
/// term was 228,998,552 of the 350M envelope (1,575 steps, tree-unfolded
/// 56,996,815, DAG 5,511,740) for a complete, trust-free refutation.
///
/// This computes exactly what the validators decode — over the clause, the
/// pivot or arguments, and every cited premise — charges it as it goes, and
/// reports it as BOTH `work` and `unfolded_work`, so
/// `binary_resolution_charge` / `chain_resolution_charge` receive the decode
/// figure their contract names. Fewer operations, identical validation: the
/// step's validator is untouched, and its own per-link charges still flow
/// through `progress`.
fn literal_decode_payload(
    step: &ProofStep,
    terms: &TermStore,
    derived_clauses: &[Option<Vec<TermId>>],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<PayloadStats, ProofCheckError> {
    let mut stats = PayloadStats::default();
    match step {
        ProofStep::Resolution {
            clause,
            pivot,
            clause1,
            clause2,
        } => {
            charge_decode_literals(terms, clause, progress, &mut stats)?;
            charge_decode_literals(terms, std::slice::from_ref(pivot), progress, &mut stats)?;
            for premise in [*clause1, *clause2] {
                if let Some(Some(premise_clause)) = derived_clauses.get(premise.0 as usize) {
                    charge_decode_literals(terms, premise_clause, progress, &mut stats)?;
                }
            }
        }
        ProofStep::Step {
            clause,
            premises,
            args,
            ..
        } => {
            charge_decode_literals(terms, clause, progress, &mut stats)?;
            charge_decode_literals(terms, args, progress, &mut stats)?;
            for premise in premises {
                if let Some(Some(premise_clause)) = derived_clauses.get(premise.0 as usize) {
                    charge_decode_literals(terms, premise_clause, progress, &mut stats)?;
                }
            }
        }
        _ => {}
    }
    stats.unfolded_work = stats.work;
    Ok(stats)
}

struct MeteredNanIdentity<'a, 'p> {
    terms: &'a TermStore,
    progress: &'p mut dyn FnMut(usize, usize) -> bool,
}

impl<'a> crate::checker::NanIdentityView<'a> for MeteredNanIdentity<'a, '_> {
    fn term(&mut self, id: TermId) -> Result<(&'a TermData, &'a Sort), ProofCheckError> {
        charge_progress(self.progress, 2, 0)?;
        if id.index() >= self.terms.len() {
            return Err(ProofCheckError::ResourceLimit);
        }
        Ok((self.terms.get(id), self.terms.sort(id)))
    }

    fn charge(&mut self, work: usize) -> Result<(), ProofCheckError> {
        charge_progress(self.progress, work, 0)
    }
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
    let roots = {
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
            ProofStep::TheoryLemma { clause, .. } | ProofStep::FiniteFieldLinear { clause, .. } => {
                push_term_slice(&mut roots, clause, &mut counting_progress)?;
            }
            ProofStep::NraSos {
                clause,
                certificate,
            } => {
                push_term_slice(&mut roots, clause, &mut counting_progress)?;
                for monomial in &certificate.basis {
                    push_term_slice(&mut roots, monomial, &mut counting_progress)?;
                }
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
        let (order_variables, mut fp_assignments) =
            charge_step_payload_walks(terms, &roots, &mut counting_progress)?;
        if let ProofStep::TheoryLemma {
            clause,
            kind: TheoryLemmaKind::FpClassification { .. },
            ..
        } = step
        {
            // This exact schema has a constant-size checker, independent of
            // operand width. Reuse its fallible matcher; a refused debit is
            // terminal, and every other lemma retains its assignment census.
            charge_progress(&mut counting_progress, "=".len() + "fp.isNaN".len(), 0)?;
            if !terms.is_declared_function("=")
                && !terms.is_declared_function("fp.isNaN")
                && crate::checker::is_exact_nan_identity(
                    &mut MeteredNanIdentity {
                        terms,
                        progress: &mut counting_progress,
                    },
                    clause,
                )?
            {
                fp_assignments = 1;
            }
        }
        stats.order_assignments = crate::checker::order_ite_assignment_count(order_variables);
        stats.fp_assignments = fp_assignments;
        roots
    };
    if overflow {
        Err(ProofCheckError::ResourceLimit)
    } else {
        // Memo bookkeeping consumes the same caller allowance, but it is not
        // semantic payload. Keep the latter's exact per-step bounds invariant
        // under memo warmth, and price real memo work/storage separately.
        stats.unfolded_work = unfolded_work_memoized_with_progress(memo, terms, &roots, progress)?;
        Ok(stats)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SemanticChargeClass {
    General,
    /// Unannotated BV lemmas pay the bounded evaluator here. The whole-proof
    /// census separately charges every possible proof-producing fallback its
    /// published 50M-work/768MiB maximum before any semantic validator runs.
    /// Structural BV membership is a visited-DAG walk, covered by this route's
    /// additional linear charge. Annotated gate searches remain General.
    BvBitBlastReplay,
    /// A `BvBitBlast` lemma the bounded evaluator refuses right after its
    /// classification walk (`checker::bounded_bv_evaluation_is_refused`): a
    /// variable wider than it evaluates, or more than its assignment bits.
    /// Its validator then does only linear walks, so it pays
    /// [`Self::BvBitBlastReplay`]'s structural charge without the exhaustive
    /// evaluation's `unfolded_work * 9 * 256`, which is reserved for work
    /// that never runs. Measured on external-codegen's strict-gate row 2060 (one
    /// 64-bit variable, a 134k-node tree): that reservation was 308,881,090
    /// of the 350,000,000 envelope and refused the lemma the proof-producing
    /// replay (reserved separately, see above) had already decided.
    BvBitBlastWithoutEvaluation,
    ResolutionRoute,
    DatatypeEnumPigeonhole,
    ArrayClauseSchema,
    /// `TheoryLemmaKind::ArraySelectStore { .. }` — the two read-over-write
    /// schemas, validated by `crate::checker::array_axiom::validate_array_select_store`.
    ///
    /// That validator is a CONSTANT-DEPTH shape matcher: two linear
    /// non-Bool scans, one unit-`or` flatten, and then `matches_row1_unit` /
    /// `matches_row1_conditional` / `matches_row2_conditional`, each a fixed
    /// program of `terms.get` / `terms.sort` slot reads over the top three
    /// application levels of each literal (`equality_sides`,
    /// `select_store_parts`, `is_select_of`, `matches_(not_)equality_pair`)
    /// that compares `TermId`s and never descends further (verified:
    /// crates/ay-proof/src/checker/array_axiom.rs). Its worst case is a small
    /// constant number of reads per literal — literals the base payload walk
    /// has already counted — NOT the tree-unfolded payload, and certainly not
    /// its square.
    ///
    /// The `General` `unfolded_work^2` product billed exactly that square.
    /// Measured on `QF_AX/swap/swap_t3_np_nf_ai_00008_005` with
    /// `--probe-strict-check`, unbudgeted (`AY_A2B_BUDGET_SCALE=inf`) under an
    /// explicit proof demand, on a complete, trust-free 4,378-entry
    /// propositional refutation (569 of 569 SAT variables mapped, 0
    /// untranslatable): 260 `ArraySelectStore` precharges summed
    /// **1_965_724_100** work (max 22_335_076, from a payload of 1_278 DAG
    /// nodes unfolding to 4_726) and 8 `ArrayExtensionality` precharges
    /// **713_210_912** (89_151_364 each, `9442^2`) — together 7.7x the whole
    /// 350_000_000 envelope for validators that perform a few hundred slot
    /// reads. The walk refused with `budget: work 348864266+3579666 of
    /// 350000000`; the delta is `1892^2 + 2`, one lemma's unfolded payload
    /// squared, and the correctly decided `unsat` was withheld as `unknown`.
    /// On `swap_t2_np_nf_ai_00008_008` ONE such lemma precharged
    /// **4_374_764_166**, 12.5x the envelope on its own.
    /// See [`ARRAY_ROW_SHAPE_WORK_FACTOR`].
    ArrayRowShape,
    /// `TheoryLemmaKind::ArrayExtensionality`, validated by
    /// `crate::checker::array_axiom::validate_array_extensionality`.
    ///
    /// Two routes, both bounded by the step's reachable DAG:
    ///
    ///  * the exact chain schema (`extensionality_chain_parts`): two literal
    ///    orderings, each a fixed set of slot reads plus
    ///    `select_chain_to_array_pair`, which peels the two select spines ONE
    ///    LEVEL per iteration — every level is a distinct `select` node of the
    ///    literal, so the iteration count is bounded by the DAG node count the
    ///    base payload walk already debited — then one registry lookup and
    ///    three `TermId` comparisons per peeled level;
    ///  * the folded-read fallback (`validate_folded_registry_match_with_budget`),
    ///    whose matcher is memoized and metered by a WHOLE-PROOF budget of
    ///    `FOLDED_REGISTRY_WORK_LIMIT` units; it now debits every unit it
    ///    consumes through the strict-check progress callback as well, so the
    ///    caller's envelope sees that work as it happens.
    ///
    /// The private `(100_000, 2 * bytes)` floor this class replaces priced the
    /// fallback's whole-proof budget into EVERY lemma, and the `General`
    /// product on top of it squared the unfolded spine (see
    /// [`ArrayRowShape`](Self::ArrayRowShape) for the measurement).
    /// See [`ARRAY_EXTENSIONALITY_SHAPE_WORK_FACTOR`].
    ArrayExtensionalityShape,
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
    /// The syntax-only CLAUSE-IDENTITY family — `reordering`, `weakening` and
    /// `eq_reflexive`. Each validator reads CLAUSE LITERALS as opaque
    /// `TermId`s and never descends into one:
    ///
    ///  * `reordering` ([`crate::checker::reordering::validate_reordering`]):
    ///    one premise-arity guard, `clause.to_vec()` and `premise.to_vec()`,
    ///    one `sort_unstable` each, and one `Vec` comparison;
    ///  * `weakening`
    ///    ([`crate::checker::boolean_negation::validate_weakening`]): one
    ///    premise-arity guard, one length comparison and one prefix slice
    ///    comparison;
    ///  * `eq_reflexive`
    ///    ([`crate::checker::boolean_derived::validate_eq_reflexive`]): a
    ///    unit-clause guard, one `decode_app` of the single literal, and one
    ///    `TermId` comparison of its two arguments — all `O(1)`.
    ///
    /// None of the three reads a subterm, so their worst case is a comparison
    /// sort over the step's clause plus its premise clause — every literal of
    /// which the base payload walk has already counted. The `General`
    /// `unfolded_work^2` product bills them the SQUARE of the TREE-unfolded
    /// payload instead, which on a shared `store` chain is astronomically
    /// larger than the DAG the sort actually ranges over.
    ///
    /// Measured on `smt/QF_AUFLIA/storeinv_nf_size7.smt2` with
    /// `--probe-strict-check`, over the proof the congruence-lowering pass
    /// rebuilds and then asks the MANDATORY gate to certify: the 45
    /// `reordering` and 9 `weakening` steps whose charge cleared the probe's
    /// 1_000_000 reporting floor precharge **3_685_418_580** and
    /// **594_853_732** work units respectively — together 12.2x the whole
    /// 350_000_000 envelope — for a combined DAG payload of 91_825 nodes. The
    /// check refused with `budget: work 343617891+103266260 of 350000000`, and
    /// the pass had to REVERT all 57 already-derivable lemma replacements to
    /// keep the file's `unsat` published. With this class the same file
    /// certifies, its 57 `euf_congruence_explanation` lemmas lower, and its
    /// `hole`-printing steps fall 101 -> 44.
    /// See [`CLAUSE_IDENTITY_WORK_FACTOR`].
    ClauseIdentityRoute,
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
    /// Exact unit disequality of two canonical <=64-bit BV literals. The
    /// existing Boolean evaluator has one assignment and fixed small scratch;
    /// keep its old work charge but use the bounded bytes in this module.
    ClosedBvConstantRelation,
    /// `AletheRule::Or` (premise-based clause decomposition), whose validator is
    /// [`crate::checker::validate_or_clausification`]: O(1) shape checks and
    /// then `clause_matches_unordered`, which compares `TermId`s PAIRWISE and
    /// never descends into a literal. Its worst case is quadratic in the CLAUSE
    /// LENGTH — tens — while the `General` product bills it the square of the
    /// tree-unfolded term payload, which on heavily-shared BV formulas exceeds
    /// the whole envelope for a step that performs a few hundred integer
    /// comparisons.
    UnorderedClauseMatch,
    /// `AletheRule::AndPos(i)` on a step whose two negation matchers are
    /// STRUCTURALLY UNABLE to recurse. The decision, the measurement that
    /// motivated it and the charge are all in [`and_pos_charge`]; the class is
    /// deliberately NOT a claim about the `and_pos` RULE, which reaches the same
    /// unmemoized De Morgan recursion `and_neg` does.
    AndPosShallowMatch,
    /// Exact ordered `(source, not arg0, ..)` conjunction introduction.
    /// The validator uses the identical shared guard and returns after a linear
    /// immediate-ID scan. Nonmatching De Morgan spellings keep General.
    AndNegIdentityShape,
    /// `forall_inst` and `Skolem` (`sko_forall`/`sko_ex`), whose validators
    /// debit every primitive through the strict walk's progress callback.
    /// See [`quantifier_charge`].
    QuantifierProgressMetered,
    /// `equiv_pos1`/`equiv_pos2` in the emitted identity shape, on which the
    /// validator is a fixed program. See [`quantifier_charge`].
    EquivPosIdentityShape,
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

/// Work factor for [`SemanticChargeClass::ClauseIdentityRoute`], applied to a
/// comparison-sort bound over the step's DAG payload `work` (NOT the
/// tree-unfolded payload).
///
/// Write `n` for the number of literals the widest of the three validators
/// touches — `clause.len() + premise.len()`. The base payload walk pushes the
/// clause, the args and EVERY resolvable premise clause through
/// `push_term_slice`, which debits one work unit per literal, and then debits
/// `roots.len()` again in the walk's second phase, so `payload.work >= 2n`
/// holds for every step this class can see (a premise the meter cannot resolve
/// is one `premise_clause` rejects before the validator reads a literal, so it
/// contributes to neither side).
///
/// `reordering` is the worst of the three: two `to_vec()` clones (`<= n`
/// element copies), two `sort_unstable` calls (`<= c * n * log2(n)`
/// comparisons for the standard `O(n log n)` worst case) and one `Vec`
/// comparison (`<= n`). With `n <= payload.work`, every one of those terms is
/// bounded by [`comparison_sort_bound`] of `payload.work`, which is itself
/// `>= work >= 2n`. Eight copies therefore cover two sorts at `c = 2` plus the
/// three linear passes with room to spare, and the charge stays LINEARITHMIC
/// in the step's real DAG payload — so a genuinely wide clause still grows its
/// charge and is still refused once the DAG behind it is large enough.
const CLAUSE_IDENTITY_WORK_FACTOR: usize = 8;

/// `n * (floor(log2(n)) + 2)`, saturating — an upper bound on `n + n*log2(n)`,
/// and hence on the comparison count of one `O(n log n)` comparison sort over
/// `n` elements up to the constant folded into
/// [`CLAUSE_IDENTITY_WORK_FACTOR`].
///
/// `usize::BITS - n.leading_zeros()` is `floor(log2(n)) + 1` for `n >= 1`, so
/// the multiplier is at least `log2(n) + 1` there and the product is at least
/// `n`; `n = 0` maps to `0`, which is correct — there is nothing to sort.
fn comparison_sort_bound(n: usize) -> usize {
    let bits = n.bit_width() as usize;
    n.saturating_mul(bits.saturating_add(1))
}

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

include!("quality/step_clause_len.rs");

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
    resolvent_sort: bool,
) -> Result<(usize, usize), ProofCheckError> {
    let input = checked_add_usize(left, right)?;
    let total = checked_add_usize(input, conclusion)?;

    let mut work = checked_add_usize(sort_comparison_bound(left)?, sort_comparison_bound(right)?)?;
    work = checked_add_usize(work, sort_comparison_bound(conclusion)?)?;
    // Both binary routes then MERGE the three sorted sets: `resolves_to` is
    // one linear three-pointer pass over at most `total` literals, run for at
    // most two pivot orientations on the pivot form (the argument-free form
    // additionally debits each of its trials through `progress`).
    work = checked_add_usize(work, checked_mul_usize(total, 2)?)?;
    // Only the argument-DIRECTED validator (`resolution_exact`) additionally
    // constructs and sorts the resolvent, which has at most `total` literals
    // and receives no progress callback of its own; charge that fourth sort
    // for it and for nothing else. `ProofStep::Resolution` (a pivot-annotated
    // binary step, `is_valid_binary_resolution`) and the argument-free `Step`
    // form never allocate a resolvent — `resolves_to` compares the merge
    // against the declared conclusion in place. Measured with the
    // `--probe-strict-check` charge census on
    // `QF_UF/QG-classification/loops6/gensys_icl102` after the decode figure
    // was corrected: 115,709 pivot-form steps carried an `expensive` term of
    // 197,229,756 of the 350M envelope, and the resolvent — the widest of the
    // four clauses — was the largest per-clause bound in each.
    if resolvent_sort {
        work = checked_add_usize(work, sort_comparison_bound(total)?)?;
    }
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
    // the atom's arguments. `literal_decode_work` is EXACTLY that count —
    // one unit per literal plus one per leading `not`, over the clause, the
    // pivot and both premises — computed by `literal_decode_payload`
    // (#literal-decode-payload). It is NOT the tree-unfolded payload: that
    // squared a store-chain's internal sharing and withheld correct
    // `storecomm` UNSAT results, and when it was later passed here in place
    // of the DAG figure it charged 228,998,552 of the 350M envelope for the
    // 1,575 resolution steps of `swap_t3_np_nf_ai_00008_005`. Both routes make
    // one decoding pass per clause (`clause_as_set` for the argument-free
    // form, `clause_as_unique_set` plus one pivot per link for the
    // argument-directed one); four passes cover either with room to spare.
    // Without this the exemption in `SemanticChargeClass::ResolutionRoute`
    // would leave deep negation chains unpaid.
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
    // exact literal decode count (`literal_decode_work`, from
    // `literal_decode_payload`) covers both,
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

/// Pick the charge model. Non-`General` classes use a route-specific meter or
/// identify a private allocation path charged dynamically by the checker.
fn select_semantic_charge_class(step: &ProofStep, terms: &TermStore) -> SemanticChargeClass {
    if let ProofStep::TheoryLemma {
        kind: TheoryLemmaKind::BvBitBlast,
        clause,
        ..
    } = step
    {
        return if crate::checker::bounded_bv_evaluation_is_refused(terms, clause) {
            SemanticChargeClass::BvBitBlastWithoutEvaluation
        } else {
            SemanticChargeClass::BvBitBlastReplay
        };
    }
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
    if matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArraySelectStore { .. },
            ..
        }
    ) {
        return SemanticChargeClass::ArrayRowShape;
    }
    if matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArrayExtensionality,
            ..
        }
    ) {
        return SemanticChargeClass::ArrayExtensionalityShape;
    }
    if farkas_meter::uses_progress_meter(step, terms) {
        return SemanticChargeClass::ProgressFarkas;
    }
    if is_euf_identity_route(step) {
        return SemanticChargeClass::EufIdentityRoute;
    }
    if is_clause_identity_route(step) {
        return SemanticChargeClass::ClauseIdentityRoute;
    }
    if matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::BoolTautology,
            ..
        }
    ) {
        if closed_bv_relation_charge::matches(step, terms) {
            return SemanticChargeClass::ClosedBvConstantRelation;
        }
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
    if let ProofStep::Step {
        rule: AletheRule::AndNeg,
        clause,
        premises,
        args,
    } = step
    {
        if premises.is_empty()
            && args.len() == 1
            && crate::checker::boolean_and_neg_shape::and_neg_is_emitted_identity_shape(
                terms,
                clause,
                Some(args[0]),
            )
        {
            return SemanticChargeClass::AndNegIdentityShape;
        }
    }
    if and_pos_charge::is_and_pos_shallow_match(step, terms) {
        return SemanticChargeClass::AndPosShallowMatch;
    }
    if let Some(class) = quantifier_charge::quantifier_expansion_class(step, terms) {
        return class;
    }
    // Placed LAST so every kind with its own modelled route above keeps it;
    // only the trust-kind fallthrough reaches here.
    if matches!(step, ProofStep::TheoryLemma { kind, .. } if kind.is_trust()) {
        return SemanticChargeClass::TrustKindProgressMetered;
    }
    SemanticChargeClass::General
}

/// Recognize syntax-only EUF identity/congruence routes in both Alethe-step and
/// theory-lemma spellings whose strict validators are reachable-DAG bounded,
/// without descending into argument subterms. This grants no proof authority:
/// unproven `TermId`-identity bounds stay `General` with tree-unfolded charge;
/// add routes only when their strict validator has an equivalent DAG bound.
///
/// The three components of one step's up-front strict charge, kept apart so
/// the `--probe-strict-check` charge census can say WHICH of them a walk spent
/// its envelope on. `total` is what the meter is debited.
#[derive(Clone, Copy, Debug)]
struct StrictStepChargeParts {
    /// The structural per-step term: clause/premise/argument lengths.
    base: (usize, usize),
    /// The resolution / DRUP replay term.
    expensive: (usize, usize),
    /// The semantic validator precharge (`strict_semantic_charge`).
    semantic: (usize, usize),
}

impl StrictStepChargeParts {
    fn total(&self) -> Result<(usize, usize), ProofCheckError> {
        let work = checked_add_usize(self.base.0, self.expensive.0)?;
        let work = checked_add_usize(work, self.semantic.0)?;
        let bytes = checked_add_usize(self.base.1, self.expensive.1)?;
        let bytes = checked_add_usize(bytes, self.semantic.1)?;
        Ok((work, bytes))
    }
}

/// #strict-charge-census — write-only attribution of one strict walk's
/// metered charges by step kind and component, printed to stderr under
/// `--probe-strict-check` when the census is dropped.
///
/// WHY. The envelope's refusal probe names the refusing DELTA and the running
/// total, and `probe_semantic_charge` names individual precharges above its
/// 1M floor; neither says where a walk that is refused by ACCUMULATION spent
/// its budget. Measured on `QF_UF/QG-classification/loops6/gensys_icl` under
/// `AY_A2B_BUDGET_SCALE=inf --proof`: refused at `349993586+6414 of
/// 350000000` with only four precharges above the floor, 18M of 350M — the
/// other 332M were invisible. This sums every per-step charge the strict loop
/// debits — the structural base, the resolution/DRUP `expensive` term, the
/// semantic precharge, the datatype-registry term — and the payload walk's
/// own debits, keyed by step kind, and prints the rows that matter on exit.
/// Diagnostic only: nothing reads it, and it is not constructed when the flag
/// is off.
struct StrictChargeCensus {
    rows: std::collections::BTreeMap<String, ChargeCensusRow>,
    outcome: &'static str,
}

#[derive(Default, Clone, Copy)]
struct ChargeCensusRow {
    steps: usize,
    base_work: usize,
    expensive_work: usize,
    semantic_work: usize,
    registry_work: usize,
    payload_work: usize,
    unfolded_work: usize,
    bytes: usize,
}

impl ChargeCensusRow {
    fn step_work(&self) -> usize {
        self.base_work
            .saturating_add(self.expensive_work)
            .saturating_add(self.semantic_work)
            .saturating_add(self.registry_work)
    }
}

impl StrictChargeCensus {
    fn new() -> Self {
        Self {
            rows: std::collections::BTreeMap::new(),
            outcome: "aborted (envelope refusal or typed error)",
        }
    }

    fn record(
        &mut self,
        step: &ProofStep,
        parts: &StrictStepChargeParts,
        payload: PayloadStats,
        registry: (usize, usize),
    ) {
        let key = match step {
            ProofStep::Assume(_) => "assume".to_string(),
            ProofStep::Resolution { .. } => "resolution(binary,pivot)".to_string(),
            ProofStep::TheoryLemma { kind, .. } => format!("lemma:{kind:?}"),
            ProofStep::Step { rule, .. } => format!("step:{rule:?}"),
            ProofStep::Anchor { .. } => "anchor".to_string(),
            _ => "other".to_string(),
        };
        let row = self.rows.entry(key).or_default();
        row.steps = row.steps.saturating_add(1);
        row.base_work = row.base_work.saturating_add(parts.base.0);
        row.expensive_work = row.expensive_work.saturating_add(parts.expensive.0);
        row.semantic_work = row.semantic_work.saturating_add(parts.semantic.0);
        row.registry_work = row.registry_work.saturating_add(registry.0);
        row.payload_work = row.payload_work.saturating_add(payload.work);
        row.unfolded_work = row.unfolded_work.saturating_add(payload.unfolded_work);
        row.bytes = row
            .bytes
            .saturating_add(parts.base.1)
            .saturating_add(parts.expensive.1)
            .saturating_add(parts.semantic.1)
            .saturating_add(registry.1);
    }
}

impl Drop for StrictChargeCensus {
    fn drop(&mut self) {
        if std::thread::panicking() {
            return;
        }
        let mut rows: Vec<(&String, &ChargeCensusRow)> = self.rows.iter().collect();
        rows.sort_by_key(|(_, row)| std::cmp::Reverse(row.step_work()));
        let steps = rows
            .iter()
            .fold(0usize, |acc, (_, row)| acc.saturating_add(row.steps));
        let step_charges = rows
            .iter()
            .fold(0usize, |acc, (_, row)| acc.saturating_add(row.step_work()));
        let payload_walk = rows
            .iter()
            .fold(0usize, |acc, (_, row)| acc.saturating_add(row.payload_work));
        let mut line = format!(
            "--probe-strict-check: charge census {}: steps={steps} step_charges={step_charges} \
             payload_walk={payload_walk}",
            self.outcome
        );
        for (kind, row) in rows.iter().take(12) {
            line.push_str(&format!(
                " | {kind} n={} base={} expensive={} semantic={} registry={} payload={} \
                 unfolded={} bytes={}",
                row.steps,
                row.base_work,
                row.expensive_work,
                row.semantic_work,
                row.registry_work,
                row.payload_work,
                row.unfolded_work,
                row.bytes
            ));
        }
        eprintln!("{line}");
    }
}

/// The summed form of [`strict_step_charge_parts`], kept for the metering
/// tests that pin the per-step total.
#[cfg(test)]
fn strict_step_charge(
    terms: &TermStore,
    step: &ProofStep,
    derived_clauses: &[Option<Vec<TermId>>],
    derived_literal_count: usize,
    semantic_payload: PayloadStats,
) -> Result<(usize, usize), ProofCheckError> {
    strict_step_charge_parts(
        terms,
        step,
        derived_clauses,
        derived_literal_count,
        semantic_payload,
    )?
    .total()
}

fn strict_step_charge_parts(
    terms: &TermStore,
    step: &ProofStep,
    derived_clauses: &[Option<Vec<TermId>>],
    derived_literal_count: usize,
    semantic_payload: PayloadStats,
) -> Result<StrictStepChargeParts, ProofCheckError> {
    let clause_len = step_clause_len(step);
    let argument_free_unit_tail = is_argument_free_unit_tail_resolution(step, derived_clauses);
    let (work, bytes) = match step {
        ProofStep::Assume(_) => (1, size_of::<TermId>()),
        ProofStep::Resolution { clause, .. }
        | ProofStep::TheoryLemma { clause, .. }
        | ProofStep::FiniteFieldLinear { clause, .. }
        | ProofStep::NraSos { clause, .. } => (
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
            (Some(left), Some(right)) => binary_resolution_charge(
                left,
                right,
                clause_len,
                semantic_payload.unfolded_work,
                false,
            )?,
            _ => (0, 0),
        },
        ProofStep::Step {
            rule: AletheRule::Resolution | AletheRule::ThResolution,
            premises,
            args,
            ..
        } if premises.len() == 2 => match (
            prior_clause_len(derived_clauses, premises[0]),
            prior_clause_len(derived_clauses, premises[1]),
        ) {
            // A non-empty `:args` list selects the argument-directed
            // validator, the only binary route that builds and sorts a
            // resolvent.
            (Some(left), Some(right)) => binary_resolution_charge(
                left,
                right,
                clause_len,
                semantic_payload.unfolded_work,
                !args.is_empty(),
            )?,
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
    let semantic_class = select_semantic_charge_class(step, terms);
    let semantic = strict_semantic_charge(step, semantic_payload, semantic_class)?;
    Ok(StrictStepChargeParts {
        base: (work, bytes),
        expensive,
        semantic,
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GenericTheoryDeferral {
    Reject,
    Collect,
}

/// Borrowed inputs, not proof authority. Each registry keeps its independent
/// provenance: only the strict pass authenticates these against the proof.
pub(crate) struct StrictProofContext<'a> {
    pub(crate) terms: &'a TermStore,
    pub(crate) dt_decls: Option<&'a [(String, Vec<String>)]>,
    pub(crate) ctor_selectors: Option<&'a [(String, Vec<String>)]>,
    pub(crate) datatype_member_signatures: Option<&'a [DatatypeMemberSignature]>,
    pub(crate) problem_assertions: Option<&'a [TermId]>,
}

// Preserve the legacy boundary's independent borrowed arguments; the shared
// implementation groups them without changing any public API.
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
    validate_strict_steps_with_retained(
        proof,
        StrictProofContext {
            terms,
            dt_decls,
            ctor_selectors,
            datatype_member_signatures,
            problem_assertions,
        },
        generic_theory_deferral,
        None,
        progress,
    )
    .map(|(artifacts, _)| artifacts)
}

// The optional retained path changes only how the already-prepaid ordinary BV
// steps are discharged. All other strict checks and terminal proof obligations
// remain shared with the legacy entry points.
fn validate_strict_steps_with_retained<'proof>(
    proof: &'proof Proof,
    context: StrictProofContext<'proof>,
    generic_theory_deferral: GenericTheoryDeferral,
    retained_request: Option<retained::Request<'_>>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(StrictValidationArtifacts, retained::Output), ProofCheckError> {
    validate_strict_steps_with_evidence(
        proof,
        context,
        generic_theory_deferral,
        retained_request,
        None,
        progress,
    )
}

fn validate_strict_steps_with_evidence<'proof>(
    proof: &'proof Proof,
    context: StrictProofContext<'proof>,
    generic_theory_deferral: GenericTheoryDeferral,
    retained_request: Option<retained::Request<'_>>,
    fp_steps: Option<&native_fp::ValidatedSteps<'proof>>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(StrictValidationArtifacts, retained::Output), ProofCheckError> {
    charge_progress(progress, 1, 0)?;
    if proof.steps.is_empty() {
        return Err(ProofCheckError::EmptyProof);
    }

    let authentication_stats = meter_authentication_payload(
        proof,
        context.terms,
        context.dt_decls,
        context.ctor_selectors,
        context.datatype_member_signatures,
        context.problem_assertions,
        progress,
    )?;
    let payload_stats = authentication_stats.aggregate;

    if let Some(signatures) = context.datatype_member_signatures {
        validate_datatype_signature_context_with_progress(
            context.terms,
            context.dt_decls,
            context.ctor_selectors,
            signatures,
            progress,
        )?;
    }

    let mut retained_session = prepare_strict_bv_session(
        proof,
        context.terms,
        payload_stats,
        retained_request,
        progress,
    )?;
    let registries = StrictRegistries::collect(proof, &context, payload_stats, progress)?;
    // Whole-fragment Skolem/forall provenance is independent of derived
    // clauses and re-validates its own steps. Complete this metered registry
    // before the step loop so no legacy callback follows its final step.
    quantifier::validate_sko_forall_uniqueness_with_progress(proof, context.terms, progress)?;
    let mut state = StrictStepState::new(proof, generic_theory_deferral, progress)?;
    // #strict-charge-census: constructed only under the probe flag; its Drop
    // prints on every exit path of this function, refusal included.
    let mut census = ay_core::misc_cli_flags()
        .probe_strict_check
        .then(StrictChargeCensus::new);
    {
        let mut validator = StrictStepValidator {
            context: &context,
            registries: &registries,
            retained_session: &mut retained_session,
            fp_steps,
            generic_theory_deferral,
            authentication_stats,
            state: &mut state,
            census: &mut census,
        };
        for (idx, step) in proof.steps.iter().enumerate() {
            validator.validate(ProofId(idx as u32), step, progress)?;
        }
    }

    // A completed legacy walk makes no further callback. Retained sessions
    // still own their prepaid-credit release and original final control;
    // captured evidence cannot publish past that lane's original deadline.
    let retained_output = match retained_session {
        Some(session) => session.finish(progress)?,
        None => Vec::new(),
    };
    state.quality.total_steps = proof.steps.len() as u32;
    if let Some(census) = census.as_mut() {
        census.outcome = "completed";
    }
    Ok((
        (state.quality, state.derived_clauses, state.deferred_generic),
        retained_output,
    ))
}

fn prepare_strict_bv_session<'proof, 'wire>(
    proof: &'proof Proof,
    terms: &'proof TermStore,
    payload_stats: PayloadStats,
    retained_request: Option<retained::Request<'wire>>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<
    Option<crate::checker::bv_bitblast::retained_session::RetainedSession<'proof, 'wire>>,
    ProofCheckError,
> {
    // Cover the proof scan that counts tagged lemmas, then debit both complete
    // memoized classifier passes before either one can execute.
    charge_progress(progress, proof.steps.len(), 0)?;
    let (bv_classifier_work, bv_classifier_bytes) =
        proof_producing_bv_classifier_charge(proof, payload_stats, progress)?;
    charge_progress(progress, bv_classifier_work, bv_classifier_bytes)?;
    // The aggregate budget preflight performs a separate whole-proof census:
    // it classifies tagged bit-blast lemmas and counts BV/LIA lemmas. Debit
    // that second linear scan before it runs.
    charge_progress(progress, proof.steps.len(), 0)?;
    // Proof-producing BV and BV/LIA lemmas enter checkers with large private
    // limits. Debit the exact per-kind published maxima against the caller's
    // ONE aggregate envelope before entering either replay path. A retained
    // session consumes this same census/prepayment, not a second reservation.
    let retained_session = retained::prepare(proof, terms, retained_request, progress)?;
    charge_progress(progress, 0, 0)?;
    Ok(retained_session)
}

struct StrictRegistries {
    // Preserve reverse construction-order cleanup of the original locals.
    empty_sets: Option<crate::checker::EmptySetRegistry>,
    fresh_defs: FreshDefRegistry,
    ext_diff: Option<ExtDiffRegistry>,
}

impl StrictRegistries {
    fn collect(
        proof: &Proof,
        context: &StrictProofContext<'_>,
        payload_stats: PayloadStats,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Self, ProofCheckError> {
        let terms = context.terms;
        let problem_assertions = context.problem_assertions;
        if let Some(assertions) = problem_assertions {
            validate_problem_assumptions_with_progress(proof, terms, assertions, progress)?;
        }
        // Whole-proof freshness/introduction conditions are built ONCE and
        // checked even when no later lemma cites the introduced symbol.
        charge_progress(progress, proof.steps.len(), 0)?;
        let (ext_diff_work, ext_diff_bytes) =
            ext_diff_registry_charge(proof, terms, payload_stats, progress)?;
        charge_progress(progress, ext_diff_work, ext_diff_bytes)?;
        let ext_diff = match problem_assertions {
            Some(assertions) => Some(ExtDiffRegistry::collect_with_progress(
                proof, terms, assertions, progress,
            )?),
            None => None,
        };
        charge_progress(progress, 0, 0)?;
        charge_progress(progress, proof.steps.len(), 0)?;
        let (fresh_def_work, fresh_def_bytes) =
            fresh_def_registry_charge(proof, payload_stats, progress)?;
        charge_progress(progress, fresh_def_work, fresh_def_bytes)?;
        let fresh_defs =
            FreshDefRegistry::collect_with_progress(proof, terms, problem_assertions, progress)?;
        // Empty-set closure has no introduction validity condition: construct
        // it only when used, preserving its existing metered linear BFS.
        charge_progress(progress, proof.steps.len(), 0)?;
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
            (true, Some(assertions)) => {
                Some(crate::checker::EmptySetRegistry::collect_with_progress(
                    terms, assertions, progress,
                )?)
            }
            _ => None,
        };
        Ok(Self {
            empty_sets,
            fresh_defs,
            ext_diff,
        })
    }
}

struct StrictStepState {
    // Cleanup order matches the original validation locals on refusal.
    term_cost_memo: TermCostMemo,
    deferred_generic: DeferredGenericClauses,
    derived_literal_count: usize,
    derived_clauses: DerivedClauses,
    quality: ProofQuality,
}

impl StrictStepState {
    fn new(
        proof: &Proof,
        generic_theory_deferral: GenericTheoryDeferral,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Self, ProofCheckError> {
        let quality = ProofQuality::default();
        let derived_table_bytes =
            checked_mul_usize(proof.steps.len(), size_of::<Option<Vec<TermId>>>())?;
        charge_progress(progress, 1, derived_table_bytes)?;
        let derived_clauses = Vec::with_capacity(proof.steps.len());
        let deferred_generic = allocate_deferred_generic(proof, generic_theory_deferral, progress)?;
        // Pure costs are memoized only for this validation; per-step payload
        // charges remain load-bearing and are never memoized (A2).
        let term_cost_memo = TermCostMemo::default();
        Ok(Self {
            term_cost_memo,
            deferred_generic,
            derived_literal_count: 0,
            derived_clauses,
            quality,
        })
    }
}

fn allocate_deferred_generic(
    proof: &Proof,
    deferral: GenericTheoryDeferral,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<DeferredGenericClauses, ProofCheckError> {
    if deferral == GenericTheoryDeferral::Reject {
        return Ok(Vec::new());
    }
    charge_progress(progress, proof.steps.len(), 0)?;
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
    Ok(Vec::with_capacity(deferred_count))
}

struct StrictStepValidator<'state, 'proof, 'wire> {
    fp_steps: Option<&'state native_fp::ValidatedSteps<'proof>>,
    context: &'state StrictProofContext<'proof>,
    registries: &'state StrictRegistries,
    retained_session: &'state mut Option<
        crate::checker::bv_bitblast::retained_session::RetainedSession<'proof, 'wire>,
    >,
    generic_theory_deferral: GenericTheoryDeferral,
    authentication_stats: AuthenticationPayloadStats,
    state: &'state mut StrictStepState,
    census: &'state mut Option<StrictChargeCensus>,
}

impl StrictStepValidator<'_, '_, '_> {
    fn validate(
        &mut self,
        id: ProofId,
        step: &ProofStep,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<(), ProofCheckError> {
        let terms = self.context.terms;
        let semantic_payload = semantic_payload::meter(
            step,
            terms,
            &self.state.derived_clauses,
            &mut self.state.term_cost_memo,
            progress,
        )?;
        let charge_parts = strict_step_charge_parts(
            terms,
            step,
            &self.state.derived_clauses,
            self.state.derived_literal_count,
            semantic_payload,
        )?;
        let (mut step_work, mut step_bytes) = charge_parts.total()?;
        let registry_charge = datatype_registry_charge(
            step,
            semantic_payload,
            self.authentication_stats.datatype_registry,
            self.authentication_stats.selector_registry,
        )?;
        step_work = checked_add_usize(step_work, registry_charge.0)?;
        step_bytes = checked_add_usize(step_bytes, registry_charge.1)?;
        if let Some(census) = self.census.as_mut() {
            census.record(step, &charge_parts, semantic_payload, registry_charge);
        }
        charge_progress(progress, step_work, step_bytes)?;
        classify_step(step, &mut self.state.quality);
        let collect_this_generic = self.generic_theory_deferral == GenericTheoryDeferral::Collect
            && matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::Generic,
                    ..
                }
            );
        let retained_clause = match self.retained_session.as_mut() {
            Some(session) => session.validate_step(id, progress)?,
            None => None,
        };
        let fp_clause = match self.fp_steps {
            Some(steps) => steps.clause(id, step, terms, progress)?,
            None => None,
        };
        if let Some(clause) = retained_clause.or(fp_clause) {
            // Either session binds the exact immutable proof/store step.
            // Independent complete-source replay precedes semantic memo use.
            // Its ordinary derived-clause copy was priced above for this step.
            self.state.derived_clauses.push(Some(clause.to_vec()));
        } else {
            validate_step_with_datatypes_and_progress(
                terms,
                &mut self.state.derived_clauses,
                id,
                step,
                true,
                self.context.dt_decls,
                self.context.ctor_selectors,
                self.context.datatype_member_signatures,
                self.registries.ext_diff.as_ref(),
                self.registries.empty_sets.as_ref(),
                Some(&self.registries.fresh_defs),
                collect_this_generic.then_some(&mut self.state.deferred_generic),
                progress,
            )?;
        }
        self.state.derived_literal_count =
            checked_add_usize(self.state.derived_literal_count, step_clause_len(step))?;
        // The next step's payload meter and admission charge are the
        // between-step stop points. A poll here could only discard a final
        // step that already validated (#completed-check-accepted).
        Ok(())
    }
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
        // Native verification authenticates this payload. Its separate Alethe
        // rendering remains an honest hole and is a publication wire gap.
        ProofStep::NraSos { .. } | ProofStep::FiniteFieldLinear { .. } => {
            quality.theory_lemma_count += 1
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

#[cfg(test)]
#[path = "quality/registry_cancellation_tests.rs"]
mod registry_cancellation_tests;

#[cfg(test)]
#[path = "quality/bv_classification_cancellation_tests.rs"]
mod bv_classification_cancellation_tests;

#[cfg(test)]
#[path = "quality/fp_classification_meter_tests.rs"]
mod fp_classification_meter_tests;
