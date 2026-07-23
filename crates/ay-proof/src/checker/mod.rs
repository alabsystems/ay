// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof structure validation for premise linkage, resolution, DRUP, and terminal empty-clause derivation.
mod array_axiom;
pub(crate) use array_axiom::{array_select_store_printer_terms, ArraySelectStorePrinterTerms};
pub use array_axiom::{
    recognize_array_extensionality, recognize_array_extensionality_chain,
    recognize_array_select_store, recognize_array_theory_lemma,
    recognize_folded_array_extensionality, ExtDiffRegistry,
};
mod boolean;
mod boolean_derived;
mod boolean_negation;
mod bv_bitblast;
pub use bv_bitblast::{
    recognize_bool_tautology, recognize_bv_bitblast, recognize_bv_ground_evaluate,
};
mod clausification;
mod datatype_axiom;
pub use datatype_axiom::{recognize_datatype_distinct, recognize_datatype_selector_project};
mod euf;
mod euf_step_rules;
mod ite_axiom;
pub use ite_axiom::recognize_ite_same;
mod regex_empty;
pub use regex_empty::recognize_regex_intersect_empty;
mod rounding_mode;
pub use rounding_mode::recognize_rounding_mode_domain;
pub use string_ground::recognize_string_ground_eval;
mod fp_bounded;
pub use fp_bounded::{
    recognize_fp_classification, recognize_fp_classification_op, recognize_fp_rounding_mode_domain,
};
mod fp_to_bv;
mod lia;
mod lra_farkas;
pub(crate) mod quantifier;
mod resolution;
mod string_axiom;
mod string_ground;
mod string_length_identity;
pub use string_length_identity::recognize_string_length_lemma;

use ay_core::{
    AletheRule, FarkasAnnotation, LiaAnnotation, Proof, ProofId, ProofStep, TermId, TermStore,
    TheoryLemmaKind,
};
use thiserror::Error;

use euf::{validate_euf_congruent, validate_euf_congruent_pred, validate_euf_transitive};
use euf_step_rules::{validate_cong, validate_refl, validate_symm, validate_trans};
use resolution::{is_valid_binary_resolution, is_valid_rup_step, validate_binary_resolution_rule};

/// Validation failure returned by [`check_proof`].
#[derive(Debug, Error, PartialEq, Eq)]
#[non_exhaustive]
pub enum ProofCheckError {
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
    /// The checker only supports binary resolution for this rule.
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
/// Datatype constructor and selector declarations allow their corresponding
/// theory lemmas to be validated at the strict boundary. `problem_assertions`
/// allows [`ExtDiffRegistry`] to authenticate every
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
    if proof.steps.is_empty() {
        return Err(ProofCheckError::EmptyProof);
    }

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
            ext_diff.as_ref(),
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
#[allow(clippy::too_many_arguments)]
pub(crate) fn validate_step_with_datatypes(
    terms: &TermStore,
    derived_clauses: &mut Vec<Option<Vec<TermId>>>,
    step_id: ProofId,
    step: &ProofStep,
    strict: bool,
    dt_decls: Option<datatype_axiom::DatatypeDecls<'_>>,
    ctor_selectors: Option<datatype_axiom::SelectorDecls<'_>>,
    // Whole-proof extensionality diff-witness provenance, built once by the
    // caller from the proof's `array_ext_diff_intro` steps and the PROBLEM's
    // assertions. `None` (no problem assertion set available) keeps
    // `TheoryLemmaKind::ArrayExtensionality` fail-closed.
    ext_diff: Option<&ExtDiffRegistry>,
    // Deferred-trust recovery (see [`validate_step`]): when `Some`, a strict
    // `Trust` step is collected for independent discharge instead of rejected.
    mut trust_collector: Option<&mut Vec<(ProofId, Vec<TermId>)>>,
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
            ext_diff,
            trust_collector.as_deref_mut(),
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
        } => {
            if strict && matches!(rule, AletheRule::Trust) {
                match trust_collector {
                    // DEFERRED-TRUST mode: record the trust clause for an
                    // independent semantic discharge and fall through so the
                    // clause is admitted into the derived-clause table (as the
                    // non-strict checker does), keeping resolution/DRUP linkage
                    // intact. This is NOT an accept: the caller MUST re-discharge
                    // every collected clause as a genuine theory tautology.
                    Some(collector) => collector.push((step_id, clause.to_vec())),
                    // Plain strict mode: trust steps are unverified → reject.
                    None => return Err(ProofCheckError::TrustStep { step: step_id }),
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
            )?;
        }
        ProofStep::Anchor { .. } => derived_clauses.push(None),
        _ => unreachable!("unexpected ProofStep variant"),
    }

    Ok(())
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
    ext_diff: Option<&ExtDiffRegistry>,
    // When `Some` AND a strict trust-kind (`Generic`) theory lemma is encountered,
    // the lemma is DEFERRED (its clause collected for independent re-discharge)
    // instead of rejected — the theory-lemma analogue of the `Step{rule:Trust}`
    // deferral. The caller MUST re-discharge every collected clause.
    trust_collector: Option<&mut Vec<(ProofId, Vec<TermId>)>>,
) -> Result<(), ProofCheckError> {
    if strict {
        match kind {
            TheoryLemmaKind::EufTransitive => {
                validate_euf_transitive(terms, step_id, clause)?;
            }
            TheoryLemmaKind::EufCongruent => {
                validate_euf_congruent(terms, step_id, clause)?;
            }
            TheoryLemmaKind::EufCongruentPred => {
                validate_euf_congruent_pred(terms, step_id, clause)?;
            }
            TheoryLemmaKind::LraFarkas => {
                lra_farkas::validate_lra_farkas(terms, step_id, clause, farkas)?;
            }
            TheoryLemmaKind::LiaGeneric => {
                lia::validate_lia_generic(terms, step_id, clause, farkas, lia_ann)?;
            }
            // BV bit-blast lemmas: bounded semantic validation (#8820).
            //
            // The previous checker accepted any non-empty clause, which let a
            // forged proof label arbitrary Boolean literals as a bit-blast
            // lemma. `validate_bv_bitblast` enforces:
            //  - every literal is Boolean-sorted;
            //  - the clause mentions at least one bitvector sub-term;
            //  - for `BvBitBlastGate`, the clause references the declared
            //    operator (`bvand`, `bvadd`, etc.).
            //
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
            // If-then-else with identical branches: `(= (ite c x x) x)` — a
            // syntactic axiom valid for any condition and any sort of x.
            TheoryLemmaKind::IteSame => {
                ite_axiom::validate_ite_same(terms, step_id, clause)?;
            }
            TheoryLemmaKind::FpClassification { .. } => {
                fp_bounded::validate_fp_classification(terms, step_id, clause)?;
            }
            TheoryLemmaKind::FpRoundingModeDomain => {
                fp_bounded::validate_fp_rounding_mode_domain(terms, step_id, clause)?;
            }
            TheoryLemmaKind::RoundingModeDomain => {
                rounding_mode::validate_rounding_mode_domain(terms, step_id, clause)?;
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
                array_axiom::validate_array_store_permutation(terms, step_id, clause)?;
            }
            TheoryLemmaKind::ArrayRowChain => {
                array_axiom::validate_array_row_chain(terms, step_id, clause)?;
            }
            // Skolemized extensionality: NOT a tautology, so shape alone can
            // never license it. Accepted only against the whole-proof
            // `array_ext_diff_intro` provenance registry; `None` (the caller
            // had no problem assertion set to check freshness against) fails
            // closed exactly as this kind always did.
            TheoryLemmaKind::ArrayExtensionality => {
                array_axiom::validate_array_extensionality(terms, step_id, clause, ext_diff)?;
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
            // Datatype constructor distinctness (#8419 / trust_count→0).
            //
            // `(not (= C1(..) C2(..)))` for two distinct constructors of the
            // same datatype is a tautology of datatype theory. The checker
            // cannot recover constructor membership from `TermStore` alone
            // (runtime datatype terms carry `Sort::Uninterpreted`), so the
            // executor supplies the `declare-datatype` registry. Without it
            // this kind fails closed rather than assuming distinctness by shape.
            TheoryLemmaKind::DatatypeDistinct => match dt_decls {
                Some(decls) => {
                    datatype_axiom::validate_datatype_distinct(terms, step_id, clause, decls)?;
                }
                None => {
                    return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                        step: step_id,
                        kind,
                    });
                }
            },
            // Datatype selector projection (#trust-count→0).
            //
            // `(= (sel_i (C a_0 .. a_n)) a_i)` — reading field `i` of a
            // constructor application yields argument `i` — is a tautology of
            // datatype theory exactly when `sel_i` is `C`'s registered field-`i`
            // selector. The carrier sort is `Sort::Uninterpreted`, so the checker
            // is given the constructor→selector registry; without it this kind
            // fails closed rather than assuming the projection by shape.
            TheoryLemmaKind::DatatypeSelectorProject => match ctor_selectors {
                Some(selectors) => {
                    datatype_axiom::validate_datatype_selector_project(
                        terms, step_id, clause, selectors,
                    )?;
                }
                None => {
                    return Err(ProofCheckError::UnsupportedTheoryLemmaKind {
                        step: step_id,
                        kind,
                    });
                }
            },
            other => {
                // A trust-kind (`Generic`) theory lemma has no dedicated strict
                // validator (e.g. an integer-arithmetic lemma over an `ite` whose
                // proof is not Farkas-pure, so `validate_lia_generic` never sees
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
) -> Result<(), ProofCheckError> {
    let premise_clauses: Vec<&[TermId]> = premises
        .iter()
        .map(|premise| premise_clause(derived_clauses, step_id, *premise))
        .collect::<Result<_, _>>()?;

    match rule {
        AletheRule::Resolution | AletheRule::ThResolution => validate_binary_resolution_rule(
            terms,
            step_id,
            rule,
            clause,
            &premise_clauses,
            args.first().copied(),
        )?,
        AletheRule::Drup => {
            if !is_valid_rup_step(terms, clause, derived_clauses) {
                return Err(ProofCheckError::InvalidDrup { step: step_id });
            }
        }
        AletheRule::Hole => return Err(ProofCheckError::HoleStep { step: step_id }),
        AletheRule::Trust => {}
        AletheRule::AndPos(i) if strict => {
            boolean::validate_and_pos(terms, step_id, clause, *i, args.first().copied())?;
        }
        AletheRule::AndNeg if strict => {
            boolean::validate_and_neg(terms, step_id, clause, args.first().copied())?;
        }
        AletheRule::OrPos(_) if strict => {
            boolean::validate_or_pos(terms, step_id, clause)?;
        }
        // Bool-const units from Tseitin encoding of `true`/`false`: clause is
        // `[true_const]` / `[(not false_const)]` — 0-var tautologies. The same
        // exhaustive bounded-assignment evaluator used for BoolTautology accepts
        // a clause ONLY if true under every assignment (every literal Bool-sorted),
        // so a forged non-tautological unit is rejected. Strict + fail-closed; lets
        // Tseitin-registered Bool-const aux vars carry a checkable rule instead of
        // dropping to a Trust fallback (#verification-route).
        AletheRule::True if strict => {
            bv_bitblast::validate_bool_tautology(terms, step_id, clause)?;
        }
        AletheRule::False if strict => {
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
        AletheRule::EqTransitive if strict => {
            validate_euf_transitive(terms, step_id, clause)?;
        }
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
            bv_bitblast::validate_bv_ground_evaluate(terms, step_id, clause, premises.len(), args)?;
        }
        AletheRule::LaDisequality if strict => {
            lia::validate_la_disequality(terms, step_id, clause, premises.len(), args)?;
        }
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
