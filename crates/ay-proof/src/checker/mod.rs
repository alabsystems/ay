// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Proof structure validation for premise linkage, resolution, DRUP, and terminal empty-clause derivation.
mod ite_premise;
pub use ite_premise::assumed_is_authored_bool_ite_consequence;
mod array_axiom;
pub(crate) use array_axiom::{
    array_row_chain_printer_terms, array_select_store_printer_terms,
    array_store_permutation_printer_terms, ArrayRowChainPrinterTerms, ArraySelectStorePrinterTerms,
    RowChainEnd, RowChainPath,
};
pub use array_axiom::{
    ite_eval::recognize_array_row_chain_ite_eval, recognize_array_extensionality,
    recognize_array_extensionality_chain, recognize_array_select_store,
    recognize_array_theory_lemma, recognize_array_theory_lemma_with_typed_context,
    recognize_folded_array_extensionality, ExtDiffRegistry,
};
mod array_finite;
pub use array_finite::{
    recognize_array_finite_extensionality,
    recognize_array_finite_extensionality_with_typed_context,
    recognize_array_finite_select_expansion,
    recognize_array_finite_select_expansion_with_typed_context,
};
mod boolean;
pub(crate) mod boolean_and_pos_shape;
mod boolean_derived;
mod boolean_negation;
mod bv_bitblast;
mod bv_lia_query;
mod closed_bv_evaluate;
pub use bv_bitblast::{
    authenticate_atom_leaf_bool_bv_unsat_query, authenticate_bool_bv_unsat_query,
    authenticate_uf_leaf_bool_bv_unsat_query, bv_bitblast_requires_proof_producer,
    recognize_bool_tautology, recognize_bv_bitblast, recognize_bv_ground_evaluate,
    AuthenticatedBoolBvUnsatQuery, BoolBvUnsatAuthenticationError,
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
mod datatype_ground;
pub(crate) use datatype_axiom::validate_datatype_signature_context;
pub use datatype_axiom::{
    recognize_datatype_acyclic_direct, recognize_datatype_constructor_reconstruct,
    recognize_datatype_distinct, recognize_datatype_exhaustive,
    recognize_datatype_selector_project, recognize_datatype_tester_eval,
    recognize_datatype_tester_eval_with_selectors, recognize_datatype_tester_exclusive,
    recognize_datatype_value_eq_congruence, DatatypeMemberSignature,
};
pub use datatype_ground::recognize_datatype_ground_conflict;
mod euf;
pub use euf::{
    recognize_euf_congruent, recognize_euf_congruent_pred, recognize_euf_reflexive,
    recognize_euf_transitive,
};
mod euf_congruence_explanation;
pub use euf_congruence_explanation::recognize_euf_congruence_explanation;
mod euf_polarity_congruence;
pub use euf_polarity_congruence::recognize_euf_polarity_congruence;
mod euf_step_rules;
mod fresh_def;
mod fresh_def_dispatch;
pub use fresh_def::FreshDefRegistry;
mod ite_axiom;
pub use ite_axiom::recognize_ite_same;
mod ground_subst;
mod ite_branch;
pub use ground_subst::{ground_substitution_image_matches, recognize_ground_equality_substitution};
mod nia_fourier_motzkin;
pub use ite_branch::{recognize_array_guarded_row_expansion, recognize_ite_branch_projection};
mod nia_linear_ideal;
pub use nia_linear_ideal::recognize_arith_clause_tautology;
mod nra_interval;
mod nra_poly;
mod nra_univariate;
pub use nra_interval::recognize_nra_interval_unsat;
pub use nra_univariate::recognize_nra_univariate_unsat;
mod order_ite;
pub(crate) use order_ite::assignment_count as order_ite_assignment_count;
pub use order_ite::recognize_order_ite_tautology;
mod poly_simp;
pub use poly_simp::recognize_arith_poly_simp;
mod regex_empty;
mod reordering;
pub use regex_empty::recognize_regex_intersect_empty;
mod regex_length;
pub use regex_length::{recognize_regex_length_lower_bound, regex_min_length};
mod rounding_mode;
mod seq_extensional_companion;
pub use seq_extensional_companion::recognize as recognize_seq_extensional_companion_contradiction;
mod seq_ground;
pub use seq_ground::recognize_seq_ground_eval;
#[path = "set_axiom.rs"]
mod set_axiom;
#[path = "set_card_chain.rs"]
mod set_card_chain;
#[path = "subset_axiom.rs"]
mod subset_axiom;
pub use rounding_mode::recognize_rounding_mode_domain;
pub(crate) use set_axiom::EmptySetRegistry;
pub use set_card_chain::recognize_set_card_chain_recurrence;
pub use string_ground::clause_mentions_string_or_regex;
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
pub use fp_ground::clause_mentions_floating_point;
pub use fp_ground::recognize_fp_ground_eval;
pub(crate) use fp_ground::FP_GROUND_WORK_LIMIT;
mod fp_to_bv;
mod ground_evaluate;
pub use ground_evaluate::recognize_ground_evaluate;
pub(crate) use ground_evaluate::validate_ground_evaluate as validate_ground_evaluate_for_printer;
mod lia;
pub use lia::recognize_arith_eq_implies_bound;
pub use lia::recognize_arith_eq_triangle;
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
use euf_congruence_explanation::validate_euf_congruence_explanation;
use euf_polarity_congruence::validate_euf_polarity_congruence;
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
mod error;
pub use error::ProofCheckError;

/// Validate proof structure: premise linkage, resolution, DRUP, and terminal empty clause.
/// Theory lemmas and trust-style rules are treated as axioms in this mode.
pub fn check_proof(proof: &Proof, terms: &TermStore) -> Result<(), ProofCheckError> {
    let mut unbounded = |_: usize, _: usize| true;
    check_proof_with_progress(proof, terms, &mut unbounded)
}

/// [`check_proof`] under a CALLER-OWNED resource and cancellation envelope
/// (#diagnostic-envelope).
///
/// The executor uses [`check_proof`] as a whole-proof REVERT GATE around proof
/// surgery ("if the rebuilt proof does not check, put the original back"). That
/// gate had no envelope: it bottoms out in `validate_step_with_datatypes`, whose
/// meter is hardcoded to `|_, _| true`, so neither an interrupt, nor an expired
/// solve deadline, nor a memory limit could stop it. MEASURED on deductive-checks's
/// `datatype_ne_refutation` obligation, a 126,548-step / 393,087,456-literal
/// triangular resolution proof held this gate for minutes at a time with every
/// stop signal already raised.
///
/// A refusal is `ProofCheckError::ResourceLimit`, i.e. an `Err` — and an `Err`
/// is exactly what every revert gate already reverts on. Fail-closed: the
/// surgery is discarded and the original proof stands.
pub fn check_proof_with_progress(
    proof: &Proof,
    terms: &TermStore,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
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
        validate_step_with_datatypes_and_progress(
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
    // Fresh-symbol definitions are built even without a problem assertion set:
    // the load-bearing freshness test is against the proof's own `assume`
    // leaves (see `FreshDefRegistry::collect`), and failing closed here would
    // turn a rescuable `trust` rejection into an unrescuable hard one on the
    // one caller that passes `None`.
    let fresh_defs = FreshDefRegistry::collect(proof, terms, problem_assertions)?;

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
            Some(&fresh_defs),
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
    // Boolean-ITE closure members (#ite-expansion-authority): an assume of a
    // branch implication `(=> c t)` / `(=> (not c) e)` of one of these is an
    // ENTAILED premise — the executor's `rewrite_assertion_bool_ites` pass
    // asserts exactly those forms for a top-level Bool ITE. Recognition is
    // the shared structural matcher in `ite_premise`; it re-derives the
    // entailment from the SUPPLIED problem terms, so nothing producer-side
    // is trusted.
    let mut authored_bool_ites: Vec<(TermId, TermId, TermId)> = Vec::new();
    let mut expanded = ay_core::kani_compat::DetHashSet::default();
    let mut stack = problem_assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !expanded.insert(term) {
            continue;
        }
        match terms.get(term) {
            ay_core::term::TermData::Ite(cond, then_term, else_term) => {
                authored_bool_ites.push((*cond, *then_term, *else_term));
            }
            ay_core::term::TermData::App(ay_core::Symbol::Named(name), args) if name == "and" => {
                for &arg in args {
                    allowed.insert(arg);
                    stack.push(arg);
                }
            }
            _ => {}
        }
    }
    for (index, step) in proof.steps.iter().enumerate() {
        if let ProofStep::Assume(term) = step {
            if !allowed.contains(term)
                && !assumed_is_authored_bool_ite_consequence(terms, *term, &authored_bool_ites)
            {
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
/// Validate one fresh-definition step (`fresh_def_bound` or `fresh_def_eq`)
/// and return the clause it derives.
///
/// A fresh-definition step is a DEFINITION, not an inference: it asserts one
/// bound of `d = lin`, or the equality `d = lin` outright, for a symbol `d` the
/// problem never mentions. Its clause is NOT a tautology, so unlike every
/// theory-lemma kind it cannot be certified from the clause alone; what makes
/// it sound is whole-proof provenance (`d` fresh, ONE definiens ACROSS BOTH
/// RULES, no introduced symbol inside any definiens, matching sorts), enforced
/// once in [`FreshDefRegistry::collect`]. Without that registry there is
/// nothing to check against, so strict mode rejects; non-strict mode admits the
/// clause exactly as it admits `trust`.
///
/// Non-strict mode never reaches this function: its caller returns the clause
/// exactly as it does for `trust`.
///
/// # Errors
///
/// Returns [`ProofCheckError::InvalidTheoryLemma`] when there is no registry,
/// when the rule is not a fresh-definition rule, or when the registry declines
/// this step.
fn validate_fresh_definition_step(
    terms: &TermStore,
    rule: &AletheRule,
    step_id: ProofId,
    clause: &[TermId],
    premises: &[ProofId],
    args: &[TermId],
    fresh_defs: Option<&FreshDefRegistry>,
) -> Result<Vec<TermId>, ProofCheckError> {
    let registry = fresh_defs.ok_or_else(|| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "a fresh definition needs the whole-proof provenance registry this checker \
                 entry point does not build"
            .to_string(),
    })?;
    match rule {
        AletheRule::FreshDefBound => {
            registry.validate_bound(terms, step_id, clause, premises, args)
        }
        AletheRule::FreshDefEq => registry.validate_eq(terms, step_id, clause, premises, args),
        other => Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: format!("`{}` is not a fresh-definition rule", other.name()),
        }),
    }
    .map(|atom| vec![atom])
}

pub(crate) use fresh_def_dispatch::validate_fresh_definition_for_printer;

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

include!("step_validation.rs");
include!("theory_lemma_dispatch.rs");
include!("theory_lemma_dispatch_extended.rs");
#[cfg(test)]
#[path = "fresh_def_tests.rs"]
mod fresh_def_tests;
#[cfg(test)]
#[path = "tests.rs"]
mod tests;
// DRIFT-PROOF native-operator lint; see the module docs for the bug class.
#[cfg(test)]
#[path = "name_authority_tests.rs"]
mod name_authority_tests;

#[cfg(test)]
#[path = "bv_expensive_budget_tests.rs"]
mod expensive_bv_budget_tests;

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
    // Problem-derived empty-set registry. `None` keeps `SetCardEmptyByAssertion`
    // fail-closed, exactly as a `None` `ext_diff` does for extensionality.
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
                    | TheoryLemmaKind::EufCongruenceExplanation
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
        let mut validation = TheoryLemmaValidation {
            terms,
            step_id,
            clause,
            farkas,
            lia_ann,
            dt_decls,
            ctor_selectors,
            datatype_member_signatures,
            ext_diff,
            empty_sets,
            progress,
        };
        let handled = validate_theory_core(&mut validation, kind)?
            || validate_theory_numeric_and_fp(&mut validation, kind)?
            || validate_theory_sets(&mut validation, kind)?
            || validate_theory_arrays_and_strings(&mut validation, kind)?
            || validate_theory_ground_and_words(&mut validation, kind)?
            || validate_theory_datatype_primary(&mut validation, kind)?
            || validate_theory_nra_and_tester(&mut validation, kind)?
            || validate_theory_datatype_remaining(&mut validation, kind)?;
        if !handled {
            validate_theory_fallback(&mut validation, kind, trust_collector)?;
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
        // Clause permutation. Sound because an Alethe clause IS a disjunction
        // and `or` is commutative; see `reordering` for the argument and for
        // why the premise-arity guard is the soundness-critical half.
        AletheRule::Reordering if strict => {
            reordering::validate_reordering(terms, step_id, clause, &premise_clauses)?;
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
                // `evaluate` also has deliberately separate closed-BV
                // fragments: the legacy <=64-bit concat evaluator and the
                // bounded exact wide evaluator. All validators are
                // independent and fail closed; admission by any exact
                // semantics is enough.
                bv_bitblast::validate_bv_ground_evaluate(
                    terms,
                    step_id,
                    clause,
                    premises.len(),
                    args,
                )
                .or_else(|_| {
                    closed_bv_evaluate::validate_closed_bv_evaluate(
                        terms,
                        step_id,
                        clause,
                        premises.len(),
                        args,
                        progress,
                    )
                })?;
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
