// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof quality metrics and strict checking.
//!
//! Provides [`ProofQuality`] metrics counting each step type, plus
//! [`check_proof_with_quality`] and [`check_proof_strict`] for diagnosing
//! proof completeness and rejecting unverified fallbacks.

use std::mem::size_of;

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{
    AletheRule, Constant, DatatypeConstructor, DatatypeField, LiaAnnotation, Proof, ProofId,
    ProofStep, Sort, Symbol, TermData, TermId, TermStore, TheoryLemmaKind,
};

use crate::checker::{
    ensure_terminal_empty_clause, quantifier, validate_step, validate_step_with_datatypes,
    ExtDiffRegistry, ProofCheckError,
};
use crate::partial::PartialProofCheck;

type DerivedClauses = Vec<Option<Vec<TermId>>>;
type DeferredGenericClauses = Vec<(ProofId, Vec<TermId>)>;
type StrictValidationArtifacts = (ProofQuality, DerivedClauses, DeferredGenericClauses);

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
    /// Note: this metric does not imply full semantic verification of every
    /// proof step. `theory_lemma` and generic rule steps are still accepted as
    /// axiomatic in the checker.
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
/// Limitation: `Generic` theory lemma kind and generic Alethe rules still
/// lack semantic validation and are rejected in strict mode.
pub fn check_proof_strict(
    proof: &Proof,
    terms: &TermStore,
) -> Result<ProofQuality, ProofCheckError> {
    check_proof_strict_with_datatypes(proof, terms, None)
}

/// As [`check_proof_strict`], but with the datatype constructor registry so
/// strict mode can semantically validate `TheoryLemmaKind::DatatypeDistinct`
/// lemmas instead of failing closed.
///
/// `dt_decls` is the list of `(datatype_name, [constructor_name, ..])`
/// declarations from the executor. Runtime datatype terms carry
/// `Sort::Uninterpreted`, so the checker cannot recover constructor membership
/// from the `TermStore` alone — the registry is supplied explicitly. Passing
/// `None` is equivalent to [`check_proof_strict`].
pub fn check_proof_strict_with_datatypes(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
) -> Result<ProofQuality, ProofCheckError> {
    check_proof_strict_with_datatypes_and_selectors(proof, terms, dt_decls, None)
}

/// As [`check_proof_strict_with_datatypes`], but additionally threading the
/// constructor→selector registry so strict mode can semantically validate
/// `TheoryLemmaKind::DatatypeSelectorProject` lemmas (`fst (mk x y) = x`)
/// instead of failing closed.
///
/// `ctor_selectors` is the list of `(constructor_name, [selector_name in field
/// order])` declarations from the executor. As with `dt_decls`, runtime
/// datatype terms carry `Sort::Uninterpreted`, so the field-position registry is
/// supplied explicitly. Passing `None` is equivalent to
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
/// rules are rejected, supported theory lemmas are checked semantically,
/// datatype and selector declarations are honored, proof-producing BV budgets
/// are enforced, and every `assume` must belong to `problem_assertions` (or a
/// nested conjunct of one).
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
/// Each `Generic` theory lemma is retained by exact [`ProofId`] and clause, but
/// is inaccessible through the strict-clause accessor on the returned type.
/// The caller must independently establish every deferred clause before using
/// it as a premise in a composed certificate.
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

/// Account the complete dynamic proof/context payload and every reachable
/// term-DAG edge before semantic validation starts. This replaces scalar
/// `terms.len() * constant` guesses with data-dependent charges and provides
/// frequent caller-owned cancellation/deadline polls while walking the input.
fn meter_authentication_payload(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    problem_assertions: Option<&[TermId]>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<AuthenticationPayloadStats, ProofCheckError> {
    let mut stats = PayloadStats::default();
    let mut overflow = false;
    let registry = {
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
        meter_authentication_payload_inner(
            proof,
            terms,
            dt_decls,
            ctor_selectors,
            problem_assertions,
            &mut counting_progress,
        )?
    };
    if overflow {
        Err(ProofCheckError::ResourceLimit)
    } else {
        Ok(AuthenticationPayloadStats {
            aggregate: stats,
            datatype_registry: registry.datatype,
            selector_registry: registry.selectors,
        })
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct PayloadStats {
    work: usize,
    bytes: usize,
    unfolded_work: usize,
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

fn meter_authentication_payload_inner(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
    problem_assertions: Option<&[TermId]>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<RegistryContextStats, ProofCheckError> {
    charge_progress(
        progress,
        proof.steps.len(),
        checked_mul_usize(proof.steps.capacity(), size_of::<ProofStep>())?,
    )?;
    let datatype = match dt_decls {
        Some(declarations) => charge_name_lists(declarations, progress)?,
        None => RegistryPayloadStats::default(),
    };
    let selectors = match ctor_selectors {
        Some(selectors) => charge_name_lists(selectors, progress)?,
        None => RegistryPayloadStats::default(),
    };

    let mut pending = Vec::new();
    if let Some(assertions) = problem_assertions {
        push_term_slice(&mut pending, assertions, progress)?;
    }

    for step in &proof.steps {
        charge_progress(progress, 1, 0)?;
        match step {
            ProofStep::Assume(term) => push_term(&mut pending, *term, progress)?,
            ProofStep::Resolution { clause, pivot, .. } => {
                charge_progress(
                    progress,
                    1,
                    checked_mul_usize(clause.capacity(), size_of::<TermId>())?,
                )?;
                push_term_slice(&mut pending, clause, progress)?;
                push_term(&mut pending, *pivot, progress)?;
            }
            ProofStep::TheoryLemma {
                theory,
                clause,
                farkas,
                lia,
                ..
            } => {
                let clause_bytes = checked_mul_usize(clause.capacity(), size_of::<TermId>())?;
                charge_progress(
                    progress,
                    checked_add_usize(theory.len(), 1)?,
                    checked_add_usize(theory.capacity(), clause_bytes)?,
                )?;
                push_term_slice(&mut pending, clause, progress)?;
                if let Some(annotation) = farkas {
                    charge_progress(
                        progress,
                        annotation.coefficients.len(),
                        checked_mul_usize(
                            annotation.coefficients.capacity(),
                            size_of::<num_rational::Rational64>(),
                        )?,
                    )?;
                }
                if let Some(LiaAnnotation::CuttingPlane(annotation)) = lia {
                    charge_progress(
                        progress,
                        annotation.farkas.coefficients.len(),
                        checked_mul_usize(
                            annotation.farkas.coefficients.capacity(),
                            size_of::<num_rational::Rational64>(),
                        )?,
                    )?;
                }
            }
            ProofStep::Step {
                rule,
                clause,
                premises,
                args,
            } => {
                let clause_bytes = checked_mul_usize(clause.capacity(), size_of::<TermId>())?;
                let premise_bytes = checked_mul_usize(premises.capacity(), size_of::<ProofId>())?;
                let arg_bytes = checked_mul_usize(args.capacity(), size_of::<TermId>())?;
                let mut bytes = checked_add_usize(clause_bytes, premise_bytes)?;
                bytes = checked_add_usize(bytes, arg_bytes)?;
                if let AletheRule::Custom(name) = rule {
                    bytes = checked_add_usize(bytes, name.capacity())?;
                }
                let rule_name_work = match rule {
                    AletheRule::Custom(name) => checked_add_usize(name.len(), 1)?,
                    _ => 1,
                };
                charge_progress(progress, rule_name_work, bytes)?;
                push_term_slice(&mut pending, clause, progress)?;
                push_term_slice(&mut pending, args, progress)?;
            }
            ProofStep::Anchor { variables, .. } => {
                charge_progress(
                    progress,
                    variables.len(),
                    checked_mul_usize(variables.capacity(), size_of::<(String, Sort)>())?,
                )?;
                for (name, sort) in variables {
                    charge_progress(progress, checked_add_usize(name.len(), 1)?, name.capacity())?;
                    meter_sort(sort, progress)?;
                }
            }
            _ => charge_progress(progress, 1, 0)?,
        }
    }

    meter_reachable_terms(terms, pending, progress)?;
    Ok(RegistryContextStats {
        datatype,
        selectors,
    })
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

fn meter_sort(
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
                push_term_slice(&mut pending, args, progress)?;
            }
            TermData::Let(bindings, body) => {
                charge_progress(
                    progress,
                    bindings.len(),
                    checked_mul_usize(bindings.capacity(), size_of::<(String, TermId)>())?,
                )?;
                for (name, value) in bindings {
                    charge_progress(progress, checked_add_usize(name.len(), 1)?, name.capacity())?;
                    push_term(&mut pending, *value, progress)?;
                }
                push_term(&mut pending, *body, progress)?;
            }
            TermData::Not(inner) => push_term(&mut pending, *inner, progress)?,
            TermData::Ite(condition, then_branch, else_branch) => {
                push_term(&mut pending, *condition, progress)?;
                push_term(&mut pending, *then_branch, progress)?;
                push_term(&mut pending, *else_branch, progress)?;
            }
            TermData::Forall(variables, body, triggers)
            | TermData::Exists(variables, body, triggers) => {
                let variable_bytes =
                    checked_mul_usize(variables.capacity(), size_of::<(String, Sort)>())?;
                let trigger_bytes =
                    checked_mul_usize(triggers.capacity(), size_of::<Vec<TermId>>())?;
                charge_progress(
                    progress,
                    variables.len(),
                    checked_add_usize(variable_bytes, trigger_bytes)?,
                )?;
                for (name, sort) in variables {
                    charge_progress(progress, checked_add_usize(name.len(), 1)?, name.capacity())?;
                    meter_sort(sort, progress)?;
                }
                push_term(&mut pending, *body, progress)?;
                for trigger in triggers {
                    charge_progress(
                        progress,
                        1,
                        checked_mul_usize(trigger.capacity(), size_of::<TermId>())?,
                    )?;
                    push_term_slice(&mut pending, trigger, progress)?;
                }
            }
            _ => charge_progress(progress, 1, 0)?,
        }
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

/// Exact tree-unfolding upper bound for recursive validators over a hash-consed
/// term DAG. A memoized postorder computes `cost(t) = 1 + sum(cost(child))`;
/// the arithmetic is checked, so an exponentially shared DAG that cannot fit
/// the caller's finite counter is refused before any unmetered recursion.
fn unfolded_term_work(
    terms: &TermStore,
    roots: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<usize, ProofCheckError> {
    let mut costs: DetHashMap<TermId, usize> = DetHashMap::default();
    let mut active = DetHashSet::default();
    let mut stack: Vec<(TermId, bool)> = Vec::new();

    for &root in roots {
        if costs.contains_key(&root) {
            continue;
        }
        charge_progress(progress, 1, size_of::<(TermId, bool)>())?;
        stack.push((root, false));
        while let Some((term, expanded)) = stack.pop() {
            charge_progress(progress, 1, 0)?;
            if costs.contains_key(&term) {
                continue;
            }
            if expanded {
                active.remove(&term);
                let mut children = Vec::new();
                append_term_children(terms, term, &mut children, progress)?;
                let mut cost = 1_usize;
                for child in children {
                    let child_cost = costs
                        .get(&child)
                        .copied()
                        .ok_or(ProofCheckError::ResourceLimit)?;
                    cost = checked_add_usize(cost, child_cost)?;
                }
                charge_progress(
                    progress,
                    1,
                    checked_add_usize(size_of::<(TermId, usize)>(), 32)?,
                )?;
                costs.insert(term, cost);
                continue;
            }

            charge_progress(progress, 1, checked_add_usize(size_of::<TermId>(), 32)?)?;
            if !active.insert(term) {
                return Err(ProofCheckError::ResourceLimit);
            }
            charge_progress(progress, 1, size_of::<(TermId, bool)>())?;
            stack.push((term, true));
            let mut children = Vec::new();
            append_term_children(terms, term, &mut children, progress)?;
            for child in children.into_iter().rev() {
                if active.contains(&child) {
                    return Err(ProofCheckError::ResourceLimit);
                }
                if !costs.contains_key(&child) {
                    charge_progress(progress, 1, size_of::<(TermId, bool)>())?;
                    stack.push((child, false));
                }
            }
        }
    }

    let mut total = 0_usize;
    for root in roots {
        total = checked_add_usize(
            total,
            costs
                .get(root)
                .copied()
                .ok_or(ProofCheckError::ResourceLimit)?,
        )?;
    }
    Ok(total)
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
        let unfolded_work = unfolded_term_work(terms, &roots, &mut counting_progress)?;
        meter_reachable_terms(terms, roots, &mut counting_progress)?;
        unfolded_work
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
    ArgumentFreeUnitTail,
    DatatypeEnumPigeonhole,
}

fn semantic_validator_charge(
    step: &ProofStep,
    payload: PayloadStats,
    class: SemanticChargeClass,
) -> Result<(usize, usize), ProofCheckError> {
    match class {
        SemanticChargeClass::ArgumentFreeUnitTail => {
            // `chain_resolution_charge` accounts the exact deterministic-set
            // route, including leading-not decoding and both live hash sets.
            // Do not also apply the generic recursive-product estimate: this
            // validator never enters the ambiguity search for an all-unit
            // tail.
            return Ok((0, 0));
        }
        SemanticChargeClass::DatatypeEnumPigeonhole => {
            // The enum validator performs a constant number of hash probes per
            // literal/member. Member sorts are checked only on first insertion;
            // declaration scans and set scratch are charged separately by
            // `datatype_registry_charge`.
            let linear = payload.work.max(payload.unfolded_work);
            return Ok((checked_mul_usize(linear, 8)?, payload.bytes));
        }
        SemanticChargeClass::General => {}
    }

    // Unordered component matching and several exact schema validators have a
    // product worst case over their recursive term-tree walks, even when the
    // authored clause/`:args` vectors are tiny. `unfolded_work` counts shared
    // sub-DAGs once per recursive occurrence, so it also covers exponential
    // re-walks that a unique-node census misses.
    let named_recursive_work = checked_mul_usize(payload.work, payload.unfolded_work)?;
    let recursive_pair_work = checked_mul_usize(payload.unfolded_work, payload.unfolded_work)?;
    let base_work = named_recursive_work.max(recursive_pair_work);
    let mut work = base_work;
    let mut bytes = payload.bytes;

    let (private_work, private_bytes) = match step {
        ProofStep::Step {
            rule: AletheRule::Skolem,
            ..
        } => (100_000, 8 * 1024 * 1024),
        ProofStep::Step {
            rule: AletheRule::Evaluate,
            ..
        } => (100_000, 1024 * 1024),
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::StringGroundEval,
            ..
        } => {
            // Ground string values are decoded from UTF-8 to four-byte chars
            // and cloned through the value memo. The three evaluator maps can
            // retain one hash-table entry per unit of their shared 4M budget;
            // 96 bytes covers the largest loop-memo key, value, bucket slack,
            // and control bytes. Its separate aggregate `Vec<char>` allocation
            // cap is shared with the evaluator, so the precharge and internal
            // fail-closed check cannot drift.
            let decoded_and_cloned = checked_mul_usize(payload.bytes, 16)?;
            let table_overhead = checked_mul_usize(crate::checker::STRING_EVAL_WORK_LIMIT, 96)?;
            let char_allocation = checked_mul_usize(
                crate::checker::STRING_CHAR_ALLOCATION_LIMIT,
                size_of::<char>(),
            )?;
            let numeric_allocation =
                checked_add_usize(crate::checker::STRING_NUMERIC_BIT_ALLOCATION_LIMIT, 7)? / 8;
            let private_work = checked_add_usize(
                checked_add_usize(
                    crate::checker::STRING_EVAL_WORK_LIMIT,
                    crate::checker::STRING_CHAR_ALLOCATION_LIMIT,
                )?,
                crate::checker::STRING_NUMERIC_WORK_LIMIT,
            )?;
            (
                private_work,
                checked_add_usize(
                    checked_add_usize(
                        checked_add_usize(table_overhead, char_allocation)?,
                        numeric_allocation,
                    )?,
                    decoded_and_cloned,
                )?,
            )
        }
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::RegexIntersectEmpty,
            ..
        } => (10_600_000, 256 * 1024 * 1024),
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::NraIntervalUnsat | TheoryLemmaKind::NraUnivariateUnsat,
            ..
        } => (8_300_000, 128 * 1024 * 1024),
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::FpForwardError,
            ..
        } => (1_000_000, 16 * 1024 * 1024),
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::FpGroundEval,
            ..
        } => {
            // The exact IEEE-754 evaluator enumerates at most
            // `2^MAX_ENUMERATION_BITS` assignments and spends one unit per
            // evaluated node, capped by its own work budget; its rationals are
            // bounded by the same constant, so the byte charge scales with the
            // clause payload at the same factor as the enumeration.
            (
                crate::checker::FP_GROUND_WORK_LIMIT,
                checked_mul_usize(payload.bytes, 1 << 16)?,
            )
        }
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::FpClassification { .. },
            ..
        } => (
            checked_mul_usize(base_work, 1 << 16)?,
            checked_mul_usize(payload.bytes, 1 << 16)?,
        ),
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::OrderIteTautology,
            ..
        } => (
            checked_mul_usize(base_work, 46_656)?,
            checked_mul_usize(payload.bytes, 46_656)?,
        ),
        ProofStep::TheoryLemma {
            kind:
                TheoryLemmaKind::BoolTautology
                | TheoryLemmaKind::BvBitBlast
                | TheoryLemmaKind::BvBitBlastGate { .. },
            ..
        } => (
            checked_mul_usize(base_work, 1 << 8)?,
            checked_mul_usize(payload.bytes, 1 << 8)?,
        ),
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArrayDefaultConst | TheoryLemmaKind::ArrayExtensionality,
            ..
        } => (100_000, checked_mul_usize(payload.bytes, 2)?),
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::SetCardMemberCount,
            ..
        } => (
            checked_mul_usize(payload.work, payload.unfolded_work)?,
            checked_mul_usize(payload.bytes, 512)?,
        ),
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArrayRowChain | TheoryLemmaKind::ArrayStorePermutation,
            ..
        } => {
            let square = checked_mul_usize(payload.unfolded_work, payload.unfolded_work)?;
            let cube = checked_mul_usize(square, payload.unfolded_work)?;
            let named_cube = checked_mul_usize(square, payload.work)?;
            (
                cube.max(named_cube),
                checked_mul_usize(payload.bytes, square)?,
            )
        }
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::LraFarkas | TheoryLemmaKind::LiaGeneric,
            ..
        } => {
            let square = checked_mul_usize(payload.unfolded_work, payload.unfolded_work)?;
            let cube = checked_mul_usize(square, payload.unfolded_work)?;
            let coefficient_work = checked_mul_usize(square, payload.work)?;
            (
                cube.max(coefficient_work),
                checked_mul_usize(payload.bytes, square)?,
            )
        }
        _ => (0, 0),
    };
    work = work.max(private_work);
    bytes = bytes.max(private_bytes);
    Ok((work, bytes))
}

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
                | TheoryLemmaKind::DatatypeTesterEval,
            ..
        }
    ) {
        return Ok((0, 0));
    }

    // All three declaration-backed validators can rescan a registry for each
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
) -> Result<(usize, usize), ProofCheckError> {
    let input = checked_add_usize(left, right)?;
    let total = checked_add_usize(input, conclusion)?;
    let pairs = checked_mul_usize(left, right)?;

    let mut work = checked_add_usize(sort_comparison_bound(left)?, sort_comparison_bound(right)?)?;
    work = checked_add_usize(work, sort_comparison_bound(conclusion)?)?;
    work = checked_add_usize(
        work,
        checked_mul_usize(pairs, checked_add_usize(total, 1)?)?,
    )?;

    let decoded_bytes = checked_mul_usize(total, size_of::<(TermId, bool)>())?;
    let semantic_bytes = checked_mul_usize(
        checked_mul_usize(pairs, total)?,
        checked_add_usize(size_of::<TermId>(), 32)?,
    )?;
    Ok((work, checked_add_usize(decoded_bytes, semantic_bytes)?))
}

fn chain_resolution_charge(
    premises: &[ProofId],
    derived_clauses: &[Option<Vec<TermId>>],
    conclusion: usize,
    argument_free_unit_tail: bool,
    unfolded_literal_work: usize,
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
            unfolded_literal_work,
            checked_add_usize(hash_operations, shape_scans)?,
        )?;
        let hash_entry_bytes = checked_add_usize(size_of::<(TermId, bool)>(), 32)?;
        let bytes = checked_mul_usize(set_entries, hash_entry_bytes)?;
        return Ok((work, bytes));
    }

    let branch_budget = checked_add_usize(checked_mul_usize(premises.len(), 4)?, 256)?;
    let pair_checks = checked_mul_usize(checked_mul_usize(branch_budget, total)?, max_premise)?;
    let candidates_per_branch = max_premise.min(8);
    let candidate_literals = checked_mul_usize(
        checked_mul_usize(branch_budget, candidates_per_branch)?,
        total,
    )?;
    let candidate_work = checked_mul_usize(
        candidate_literals,
        checked_add_usize(
            if total <= 1 {
                1
            } else {
                usize::BITS as usize - (total - 1).leading_zeros() as usize
            },
            1,
        )?,
    )?;
    Ok((
        checked_add_usize(pair_checks, candidate_work)?,
        checked_mul_usize(candidate_literals, size_of::<TermId>())?,
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

fn strict_step_charge(
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
            (Some(left), Some(right)) => binary_resolution_charge(left, right, clause_len)?,
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
            (Some(left), Some(right)) => binary_resolution_charge(left, right, clause_len)?,
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
    let semantic_class = if argument_free_unit_tail {
        SemanticChargeClass::ArgumentFreeUnitTail
    } else if matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::DatatypeEnumPigeonhole,
            ..
        }
    ) {
        SemanticChargeClass::DatatypeEnumPigeonhole
    } else {
        SemanticChargeClass::General
    };
    let semantic = semantic_validator_charge(step, semantic_payload, semantic_class)?;
    work = checked_add_usize(work, semantic.0)?;
    bytes = checked_add_usize(bytes, semantic.1)?;
    Ok((work, bytes))
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum GenericTheoryDeferral {
    Reject,
    Collect,
}

fn validate_strict_steps_with_context(
    proof: &Proof,
    terms: &TermStore,
    dt_decls: Option<&[(String, Vec<String>)]>,
    ctor_selectors: Option<&[(String, Vec<String>)]>,
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
        problem_assertions,
        progress,
    )?;
    let payload_stats = authentication_stats.aggregate;

    // Cover the proof scan that counts tagged lemmas, then debit both complete
    // memoized classifier passes before either one can execute.
    charge_progress(progress, proof.steps.len(), 0)?;
    let (bv_classifier_work, bv_classifier_bytes) =
        proof_producing_bv_classifier_charge(proof, payload_stats)?;
    charge_progress(progress, bv_classifier_work, bv_classifier_bytes)?;
    let bv_charge = crate::checker::validate_proof_producing_bv_budget(proof, terms)?;
    // A proof-producing BV lemma enters a checker with its own large private
    // replay limits. Debit those published maxima against the caller's ONE
    // aggregate envelope before entering it; otherwise each lemma silently
    // acquires a fresh 50M-work/128MiB allowance.
    charge_progress(progress, bv_charge.work, bv_charge.bytes)?;
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

    for (idx, step) in proof.steps.iter().enumerate() {
        let semantic_payload = match step {
            ProofStep::Resolution { .. }
            | ProofStep::TheoryLemma { .. }
            | ProofStep::Step { .. } => {
                meter_step_term_payload(step, terms, &derived_clauses, progress)?
            }
            _ => PayloadStats::default(),
        };
        let (mut step_work, mut step_bytes) = strict_step_charge(
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
        validate_step_with_datatypes(
            terms,
            &mut derived_clauses,
            ProofId(idx as u32),
            step,
            true,
            dt_decls,
            ctor_selectors,
            ext_diff.as_ref(),
            empty_sets.as_ref(),
            collect_this_generic.then_some(&mut deferred_generic),
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
#[path = "quality_finite_enum_meter_tests.rs"]
mod finite_enum_meter_tests;
