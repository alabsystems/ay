// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof quality metrics and strict checking.
//!
//! Provides [`ProofQuality`] metrics counting each step type, plus
//! [`check_proof_with_quality`] and [`check_proof_strict`] for diagnosing
//! proof completeness and rejecting unverified fallbacks.

use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermId, TermStore, TheoryLemmaKind};

use crate::checker::{
    ensure_terminal_empty_clause, quantifier, validate_problem_assumptions, validate_step,
    validate_step_with_datatypes, ExtDiffRegistry, ProofCheckError,
};
use crate::partial::PartialProofCheck;

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
    if proof.steps.is_empty() {
        return Err(ProofCheckError::EmptyProof);
    }

    if let Some(assertions) = problem_assertions {
        validate_problem_assumptions(proof, terms, assertions)?;
    }

    // Built ONCE, before any step is validated: construction is where the
    // whole-proof conditions (bound once, fresh against the problem, not
    // self-referential) are enforced, so a bad introduction fails the check
    // even when no lemma ever cites it.
    let ext_diff = match problem_assertions {
        Some(assertions) => Some(ExtDiffRegistry::collect(proof, terms, assertions)?),
        None => None,
    };

    let mut quality = ProofQuality::default();
    let mut derived_clauses: Vec<Option<Vec<TermId>>> = Vec::with_capacity(proof.steps.len());

    for (idx, step) in proof.steps.iter().enumerate() {
        classify_step(step, &mut quality);
        validate_step_with_datatypes(
            terms,
            &mut derived_clauses,
            ProofId(idx as u32),
            step,
            true,
            dt_decls,
            ctor_selectors,
            ext_diff.as_ref(),
            None,
        )?;
    }

    quality.total_steps = proof.steps.len() as u32;
    ensure_terminal_empty_clause(&derived_clauses)?;
    Ok(quality)
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
