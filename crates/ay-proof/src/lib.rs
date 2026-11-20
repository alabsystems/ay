// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
#![forbid(unsafe_code)]
//! AY Proof - Proof production and export
//!
//! Generate and export proofs in Alethe format.
//!
//! ## Alethe Format
//!
//! The Alethe format is the standard proof format for SMT solvers,
//! supported by carcara and SMTCoq. It uses SMT-LIB syntax with
//! additional proof commands.
//!
//! ## A proof document contains PROOF COMMANDS ONLY
//!
//! The checker reads the problem file separately, and — MEASURED against
//! carcara 1.1.0 — its Alethe proof grammar accepts **no** declaration
//! command at any position: `declare-fun` and `declare-const`, at line 0 or
//! mid-file, all abort with `parser error: unexpected token`. A single
//! declaration line therefore makes the whole document uncheckable, which is
//! strictly worse than emitting nothing.
//!
//! Symbols the proof needs but the problem does not declare (theory Skolems,
//! extensionality witnesses, datatype field splits) must be RESUGARED into
//! terms — Alethe's `choice` binder — or DEFINED with `define-fun` as the term
//! they denote. Where neither is possible the problem-scoped exporter declines
//! ([`AlethePrintError::UndeclarableProofSymbols`]).
//!
//! ## Example
//!
//! ```text
//! ; problem file (read separately by the checker)
//! ;   (declare-const a Int)
//! ;   (declare-const b Int)
//!
//! ; proof document — commands only, no declarations
//! (assume h1 (= a b))
//! (assume h2 (not (= a a)))
//! (step t1 (cl (= a a)) :rule refl)
//! (step t2 (cl) :rule resolution :premises (h2 t1))
//! ```
#![warn(missing_docs)]
#![warn(clippy::all)]

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{quote_symbol, TermId, TermStore};
pub use ay_core::{AletheRule, BvGateType, Proof, ProofId, ProofStep, TheoryLemmaKind};
pub use bv_offset_bridge::derive_bv_offset_normalization;
use std::fmt::Write;

mod alethe_document_scan;
mod alethe_parser;
mod alethe_printer;
mod application_heads;
mod array_row_axiom;
mod array_store_overwrite;
mod authored_surfaces;
mod bundle;
pub mod bv_blast_export;
pub mod bv_blast_lean;
pub mod bv_blast_solver;
pub mod bv_cnf_refutation;
mod bv_offset_bridge;
mod checker;
mod congruence_derivation;
mod congruence_forest;
mod definition_bridge;
mod exact_division_sweeps;
mod la_generic_signs;
mod non_adjacent_form;
mod nra_sos_query;
mod partial;
mod quality;
pub mod resolution_dag_memo;
mod sat_sweep;
mod scope;
mod terminal_trust;
mod variables;
mod wire_rule;

pub use alethe_document_scan::AletheDocumentScan;
pub use alethe_parser::{
    check_alethe_document, check_alethe_document_in_dialect, checkable_rule_names, AletheDefect,
    AletheDocumentChecker, AletheDocumentReport, AletheSelfCheckWriter, Pos as AlethePos,
    ProblemScope,
};
pub use alethe_printer::dialect::{
    capture_alethe_dialect_report, with_alethe_dialect, AletheDialect, AletheDialectReport,
    CleanOnlySpelling,
};
pub use alethe_printer::refused_surface_hole::with_refused_surface_steps_declined_to_hole;
pub use alethe_printer::{
    arith_equality_chain_lowering_supported, carcara_declaration_gap, carcara_proof_surface,
    carcara_proof_surface_is_supported, certified_let_assume_bridge_is_supported,
    checked_array_read_lowering_supported, checked_bv_bitblast_lowering_supported,
    checked_bv_bitblast_lowering_supported_asking,
    checked_bv_bitblast_lowering_supported_within_solve, checked_euf_transitive_lowering_supported,
    checked_ground_substitution_lowering_supported,
    checked_guarded_row_expansion_lowering_supported,
    checked_ite_branch_projection_lowering_supported, checked_shadowed_stores_lowering_supported,
    checked_urem_bound_lowering_supported, dt_project_lowering_supported,
    effective_wire_term_overrides_for_proof, lia_lattice_lowering_supported,
    mul_overflow_division_lowering_supported, negation_shell_assume_surface_pairs,
    nra_sos_lowering_supported, recognize_mul_overflow_division, split_alethe_application_bounded,
    theory_lemma_bv_arithmetic_lowering_supported_within_solve, trans_step_surface_is_supported,
    AlethePrintError, AletheSurfaceParseError, BvSupportDeclines, CarcaraSurface, CompleteBlastAsk,
};
pub use array_row_axiom::{mint_row1_axiom, plan_row1_axiom_instances};
pub use array_store_overwrite::{mint_store_overwrite_axiom, plan_store_overwrite_instances};
pub use authored_surfaces::{
    effective_wire_term_overrides_for_authored_proof,
    effective_wire_term_overrides_for_authored_proof_with_progress,
    export_alethe_with_authored_surfaces, export_alethe_with_authored_surfaces_with_progress,
    folded_authored_assume_bridge_is_supported,
    folded_authored_assume_bridge_is_supported_with_progress,
    nullary_definition_assume_bridge_is_supported, term_overrides_outside_confined_let_assumes,
    try_export_alethe_with_authored_surfaces, try_export_alethe_with_authored_surfaces_until,
    try_export_alethe_with_authored_surfaces_with_progress,
    try_export_alethe_with_authored_surfaces_within_solve, AletheAuthoredSurfaces, AskingSolve,
};
pub use bundle::{
    capture_strict_retained_bundle_with_resource_control, re_check_bundle_strict,
    re_check_bundle_strict_with_cancellation, re_check_bundle_strict_with_resource_control,
    re_check_retained_bundle_strict_with_resource_control,
    read_retained_proof_bundle_with_resource_control,
    read_retained_proof_bundle_with_resource_control_and_diagnostics, render_term_canonical,
    BundleReCheck, RetainedProofBundle, RetainedProofCapture, RetainedProofTransportLimits,
    RetainedReadDiagnostics, RetainedReadErrorClass, RetainedReadFailure, RetainedReadRefusal,
    RetainedReadStage, RetainedReadTerminal, SerializableProofBundle, PROOF_BUNDLE_SCHEMA,
    RETAINED_PROOF_BUNDLE_SCHEMA,
};
pub use bv_blast_export::{
    export_bv_blast_proof, BitLemma, BitLemmaKind, BvBlastExportError, BvBlastProof,
    BvBlastValidateError, BvBlastValidateLimits, BvOp, Clause, ClauseProvenance, Lit, OperandRef,
    Refutation, ResRule, ResolutionStep, SliceObligation, VarRole, VarTable,
    FORMAT_VERSION as BV_BLAST_FORMAT_VERSION, SLICE_WIDTH,
};
pub use bv_blast_lean::render_bv_blast_proof_lean;
pub use bv_blast_solver::{
    export_bv_blast_proof_expr, export_bv_blast_proof_expr_bounded, export_bv_blast_proof_solved,
    BvExpr, BvExprExportError, BvExprProofBudget, BvExprProofBudgetError, BvSolvedExportError,
    SolvedObligation,
};
pub use bv_cnf_refutation::surface_bv_cnf_refutation;
pub use checker::assumed_is_authored_bool_ite_consequence;
pub use checker::clause_mentions_floating_point;
pub use checker::clause_mentions_string_or_regex;
pub use checker::fp_ground_format_supported;
pub use checker::recognize_arith_clause_tautology;
pub use checker::recognize_arith_eq_implies_bound;
pub use checker::recognize_arith_eq_triangle;
pub use checker::recognize_arith_poly_simp;
pub use checker::recognize_array_guarded_row_expansion;
pub use checker::recognize_datatype_acyclic_direct;
pub use checker::recognize_euf_congruent;
pub use checker::recognize_euf_congruent_pred;
pub use checker::recognize_euf_reflexive;
pub use checker::recognize_euf_transitive;
pub use checker::recognize_ground_evaluate;
pub use checker::recognize_ite_branch_projection;
pub use checker::recognize_ite_same;
pub use checker::recognize_native_bv_affine_identity;
pub use checker::recognize_nra_interval_unsat;
pub use checker::recognize_nra_univariate_unsat;
pub use checker::recognize_order_ite_tautology;
pub use checker::recognize_regex_intersect_empty;
pub use checker::recognize_regex_length_lower_bound;
pub use checker::recognize_rounding_mode_domain;
pub use checker::recognize_seq_extensional_companion_contradiction;
pub use checker::recognize_string_concat_cancellation;
pub use checker::recognize_string_containment_identity;
pub use checker::recognize_string_ground_eval;
pub use checker::recognize_string_ground_factor_conflict;
pub use checker::recognize_string_length_lemma;
pub use checker::regex_min_length;
pub use checker::FreshDefRegistry;
pub use checker::{
    authenticate_atom_leaf_bool_bv_unsat_query, authenticate_bool_bv_unsat_query,
    authenticate_uf_leaf_bool_bv_unsat_query, bv_bitblast_requires_proof_producer,
    recognize_bool_tautology, recognize_bv_bitblast,
    recognize_bv_bitblast_speculative_with_progress, recognize_bv_bitblast_with_progress,
    recognize_bv_ground_evaluate, AuthenticatedBoolBvUnsatQuery, BoolBvUnsatAuthenticationError,
    MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF, MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA,
    MAX_PROOF_PRODUCING_BV_LEMMAS_PER_PROOF, MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA,
};
pub use checker::{
    authenticate_bv_lia_unsat_query, AuthenticatedBvLiaUnsatQuery, BvLiaUnsatAuthenticationError,
    MAX_BV_LIA_QUERY_ROOTS, MAX_BV_LIA_TAUTOLOGY_BYTES_PER_LEMMA,
    MAX_BV_LIA_TAUTOLOGY_WORK_PER_LEMMA,
};
pub use checker::{
    check_proof, check_proof_collecting_trust, check_proof_collecting_trust_with_context,
    check_proof_collecting_trust_with_typed_context, check_proof_with_progress,
    DatatypeMemberSignature, ProofCheckError,
};
pub use checker::{
    ground_substitution_image_matches, recognize_array_extensionality,
    recognize_array_extensionality_chain, recognize_array_finite_extensionality,
    recognize_array_finite_extensionality_with_typed_context,
    recognize_array_finite_select_expansion,
    recognize_array_finite_select_expansion_with_typed_context, recognize_array_row_chain_ite_eval,
    recognize_array_select_store, recognize_array_theory_lemma,
    recognize_array_theory_lemma_with_typed_context, recognize_folded_array_extensionality,
    recognize_ground_equality_substitution, ExtDiffRegistry,
};
pub use checker::{
    recognize_bv_offset_spines_with_progress, recognize_bv_reconstruct_with_progress,
};
pub use checker::{
    recognize_datatype_constructor_reconstruct, recognize_datatype_distinct,
    recognize_datatype_exhaustive, recognize_datatype_ground_conflict,
    recognize_datatype_selector_project, recognize_datatype_tester_eval,
    recognize_datatype_tester_eval_with_selectors, recognize_datatype_tester_exclusive,
    recognize_datatype_value_eq_congruence,
};
pub use checker::{recognize_euf_congruence_explanation, recognize_euf_polarity_congruence};
pub use checker::{recognize_fp_classification, recognize_fp_classification_op};
pub use checker::{
    recognize_fp_forward_error, recognize_fp_ground_eval, recognize_fp_ground_eval_with_progress,
    recognize_fp_ground_eval_without_enumeration_with_progress, recognize_fp_rounding_mode_domain,
};
pub use checker::{recognize_seq_ground_eval, recognize_seq_ground_eval_with_progress};
pub use checker::{recognize_set_card_chain_recurrence, recognize_subset_theory_lemma};
pub use checker::{MAX_EXPENSIVE_BV_BYTES_PER_LEMMA, MAX_EXPENSIVE_BV_WORK_PER_LEMMA};
pub use congruence_derivation::{
    close_congruence_derivation, congruence_derivation_renders_within,
    plan_euf_congruence_derivation, CongruenceDerivation, DerivationRender,
    DERIVATION_RENDER_WORK_BUDGET,
};
pub use definition_bridge::{plan_definitional_bridge, DefinitionBridge, MAX_BRIDGE_CANDIDATES};
pub use exact_division_sweeps::{
    without_exact_division, ExactDivisionSweepMemo, ExactDivisionSweepScope,
};
pub use la_generic_signs::*;
pub use nra_sos_query::{
    check_nra_sos_query_with_progress, CheckedNraSosQuery, NraSosQueryCheckError,
};
pub use partial::{check_proof_partial, check_proof_partial_with_progress, PartialProofCheck};
pub use quality::{
    authenticate_premise_clauses_strict_with_context,
    authenticate_premise_clauses_strict_with_context_and_progress,
    authenticate_premise_clauses_strict_with_typed_context,
    authenticate_premise_clauses_strict_with_typed_context_and_progress,
    authenticate_premise_clauses_with_deferred_generic_theory_and_progress,
    authenticate_premise_clauses_with_deferred_generic_theory_and_typed_context_and_progress,
    check_proof_partial_with_quality, check_proof_partial_with_quality_and_progress,
    check_proof_strict, check_proof_strict_with_context,
    check_proof_strict_with_context_and_progress, check_proof_strict_with_datatypes,
    check_proof_strict_with_datatypes_and_selectors, check_proof_strict_with_native_fp_context,
    check_proof_strict_with_typed_context, check_proof_strict_with_typed_context_and_progress,
    check_proof_with_quality, validate_array_extensionality_provenance,
    AuthenticatedPremiseClauses, NativeFpProofContext, NativeFpSnapshotQuality,
    PremiseClausesWithDeferredGeneric, ProofQuality,
};
pub use scope::problem_scope_symbol_names;
pub use terminal_trust::{
    terminal_trust_report, terminal_trust_report_with_provenance, TerminalTrustReport,
};
pub use wire_rule::{
    arith_eq_implies_bound_lowering_supported, arith_eq_triangle_lowering_supported,
    arith_order_split_lowering, arith_poly_simp_lowering_supported,
    bv_eq_simplify_step_lowering_supported, bv_offset_spines_step_lowering_supported,
    bv_reconstruct_step_lowering_supported, evaluate_step_lowering_supported,
    exact_clause_surface_preserved, int_bounds_tautology_lowering_supported,
    la_generic_farkas_lowering_supported, lia_divisibility_lowering_supported, promoted_wire_rule,
    theory_lemma_bv_arithmetic_lowering_supported,
    theory_lemma_bv_arithmetic_lowering_supported_asking,
    theory_lemma_poly_simp_lowering_supported, ArithPolySimpPromotionBudget,
    MAX_ARITH_POLY_SIMP_PROMOTIONS_PER_PROOF,
};

use alethe_printer::AlethePrinter;
use variables::{
    collect_auxiliary_proof_declarations, collect_proof_variables, free_var_names,
    SymbolSortConflict,
};

impl From<SymbolSortConflict> for AlethePrintError {
    fn from(conflict: SymbolSortConflict) -> Self {
        Self::AmbiguousSymbolSort {
            name: conflict.name,
            first: conflict.first,
            second: conflict.second,
        }
    }
}

/// Render a single term with the exact Alethe surface syntax used by
/// [`export_alethe`] (same symbol quoting, constant spelling, and operator
/// canonicalization).
///
/// Callers that assemble Alethe text fragments AROUND an exported proof
/// (e.g. the arrays→LIA rescue's `choice`-skolem term overrides, which must
/// splice printer-identical subterms into a hand-built binder) need the
/// printer's rendering, not a debug `Display`.
#[must_use]
pub fn format_term_alethe(terms: &TermStore, term: TermId) -> String {
    AlethePrinter::new(terms).format_term(term)
}

/// Render one term with the same source-syntax override table used by Alethe
/// proof export.
///
/// Certificate producers that synthesize a larger surface term around an
/// existing proof argument must use this function so substituted arguments
/// have exactly the spelling the proof printer will emit.
#[must_use]
pub fn format_term_alethe_with_overrides(
    terms: &TermStore,
    term: TermId,
    overrides: &ay_core::kani_compat::DetHashMap<TermId, String>,
) -> String {
    AlethePrinter::new_with_overrides(terms, Some(overrides)).format_term(term)
}

/// [`format_term_alethe_with_overrides`] (or [`format_term_alethe`] when
/// `overrides` is `None`), produced only when the rendering is at most
/// `max_bytes` long and `keep_going` (polled at term boundaries) never
/// answers `false`.
///
/// Byte-exact: the printer streams assembled renderings, so
/// a `not`/`ite`/`let`/quantifier is written straight into the output instead
/// of being assembled and cached, and the work it charges is exactly the
/// bytes it writes. `Some(text)` is therefore returned exactly when the
/// unbounded renderers' text is at most `max_bytes` long (and it is that
/// text), and the rendering stops at the first term boundary past the cap:
/// memory and time grow with `max_bytes`, not with the term's TREE size (a
/// `let`-shared DAG of a few thousand nodes can spell 1e14 bytes,
/// DR-PROOF-RENDER-BUDGET-20261118).
#[must_use]
pub fn format_term_alethe_bounded(
    terms: &TermStore,
    term: TermId,
    overrides: Option<&ay_core::kani_compat::DetHashMap<TermId, String>>,
    max_bytes: u64,
    keep_going: &mut dyn FnMut() -> bool,
) -> Option<String> {
    // A renderability check (`PrinterPurpose`): a single term's rendering
    // reaches none of the gates that purpose changes, so the text is the
    // unbounded renderers' byte for byte; the purpose only keeps every
    // bounded render the producers run under one flag.
    let printer = AlethePrinter::new_with_overrides_and_budget(terms, overrides, Some(max_bytes))
        .with_assembled_rendering(alethe_printer::AssembledRendering::Streamed)
        .as_renderability_check()
        .with_emission_progress(keep_going);
    let text = printer.format_term(term);
    (!printer.work_budget_exhausted()).then_some(text)
}

/// Export a proof to Alethe format.
///
/// Converts a AY proof to the Alethe format, which can be verified
/// by carcara or other Alethe-compatible checkers.
///
/// ## Fail-loud behavior (#8821)
///
/// When a proof step cannot be rendered as a verifiable rule (e.g., an
/// `la_generic` / `lia_generic` theory lemma missing its Farkas annotation),
/// this function does **not** silently emit `:rule trust`. Instead it
/// returns a clearly-marked document containing `(error "UNVERIFIABLE
/// PROOF: ...")` headers describing the failure and logs a loud warning
/// to `stderr`. Callers that need to reject such proofs programmatically
/// should use [`try_export_alethe`] which returns a typed error.
///
/// # Arguments
///
/// * `proof` - The proof to export
/// * `terms` - The term store containing all terms referenced in the proof
///
/// # Returns
///
/// A string containing the Alethe proof commands, or an unverifiable-proof
/// error document if any step refused to render.
#[must_use]
pub fn export_alethe(proof: &Proof, terms: &TermStore) -> String {
    match try_export_alethe(proof, terms) {
        Ok(output) => output,
        Err(e) => render_unverifiable(&e, "export_alethe"),
    }
}

/// Fallible variant of [`export_alethe`] (#8821).
///
/// Returns `Err(AlethePrintError)` when any step cannot be rendered as a
/// verifiable Alethe rule — including `LraFarkas` / `LiaGeneric` theory lemmas
/// missing their `FarkasAnnotation` and array-extensionality certificates whose
/// internal witness provenance has no stock Alethe/Carcara translation.
///
/// Use this variant when the caller must refuse to write an unverifiable
/// proof to disk. The infallible [`export_alethe`] wraps this function and
/// converts the error into a loudly-marked document for backwards
/// compatibility.
///
/// ## Not the checker-facing artifact
///
/// This entry point has no notion of a problem file, so it declares EVERY
/// symbol the proof mentions and its output is consequently a standalone
/// dump, not something carcara can read (see the module docs: an Alethe proof
/// document admits no declaration command). The artifact AY writes to
/// `<input>.alethe`, and everything the external-checker measurements are
/// taken over, comes from
/// [`try_export_alethe_with_problem_scope_overrides_and_budget_to`], which
/// emits proof commands only and declines when a symbol can be neither
/// resugared nor defined.
///
/// # Errors
///
/// Returns an [`AlethePrintError`] when a step cannot be rendered as a
/// verifiable rule.
pub fn try_export_alethe(proof: &Proof, terms: &TermStore) -> Result<String, AlethePrintError> {
    let mut output = String::new();
    let printer = AlethePrinter::new(terms);
    printer.prepare_proof(proof)?;

    // Collect all variables referenced in proof terms and emit declarations.
    // Carcara requires all symbols to be declared before use.
    let vars = collect_proof_variables(proof, terms)?;
    for (name, sort) in &vars {
        if printer.is_skolem_witness_name(name) {
            continue;
        }
        let _ = writeln!(
            output,
            "(declare-fun {} () {})",
            quote_symbol(name),
            alethe_printer::format_sort_alethe(sort)
        );
    }

    for (idx, step) in proof.steps.iter().enumerate() {
        let step_id = ProofId(idx as u32);
        output.push_str(&printer.format_step(step, step_id)?);
        output.push('\n');
        printer.finish_exported_step(step_id);
    }

    Ok(output)
}

/// Export a proof to Alethe format against the original problem's declaration
/// scope: the emitted document contains PROOF COMMANDS ONLY.
///
/// The checker reads the problem file separately, so the proof must not
/// re-declare its symbols — and must not declare anything at all: carcara
/// 1.1.0's Alethe proof grammar has no declaration command, and one
/// `(declare-fun ...)` line anywhere aborts the parse before any rule is
/// checked. This variant used to open the document with exactly such a
/// preamble for every symbol free in the proof but absent from
/// `problem_assertions`. It now emits a `define-fun` for each symbol whose
/// defining term AY recorded (Skolem constants — see
/// [`ay_core::SkolemChoice`]) and DECLINES for the rest
/// ([`AlethePrintError::UndeclarableProofSymbols`]).
///
/// The `define-fun` preamble is deterministic (mint order, so a body may name
/// an earlier definition).
///
/// Fail-loud behavior matches [`export_alethe`] (#8821).
#[must_use]
pub fn export_alethe_with_problem_scope(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
) -> String {
    export_alethe_with_problem_scope_and_overrides(proof, terms, problem_assertions, None)
}

/// Export a proof to Alethe format with proof-only auxiliary declarations and
/// optional term-level rendering overrides.
///
/// Fail-loud behavior matches [`export_alethe`] (#8821).
#[must_use]
pub fn export_alethe_with_problem_scope_and_overrides(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
) -> String {
    match try_export_alethe_with_problem_scope_and_overrides(
        proof,
        terms,
        problem_assertions,
        term_overrides,
    ) {
        Ok(output) => output,
        Err(e) => render_unverifiable(&e, "export_alethe_with_problem_scope_and_overrides"),
    }
}

/// Fallible variant of [`export_alethe_with_problem_scope_and_overrides`] (#8821).
///
/// # Errors
///
/// Returns an [`AlethePrintError`] when a step cannot be rendered as a
/// verifiable rule.
pub fn try_export_alethe_with_problem_scope_and_overrides(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
) -> Result<String, AlethePrintError> {
    try_export_alethe_with_problem_scope_overrides_and_budget(
        proof,
        terms,
        problem_assertions,
        term_overrides,
        None,
    )
}

/// Budgeted variant of [`try_export_alethe_with_problem_scope_and_overrides`]
/// (#A2b).
///
/// `work_budget` caps the printer's rendering work (abstract units, roughly
/// bytes touched). Pass `Some(..)` only for the synthesized-default
/// certificate, or for an explicitly requested finite-enum certificate whose
/// exact proof, source assumptions, query epoch, and resource envelope were
/// independently checked and sealed by the caller. The by-default
/// `<input>.alethe` must never trade a fast UNSAT verdict for minutes of proof
/// materialization (QF_ALIA pp-family: 2s solves whose emission ground 300s+
/// without completing). Other explicit `--proof` / `--strict-proofs` /
/// `--self-check` / `(get-proof)` exports must pass `None`.
///
/// # Errors
///
/// Returns [`AlethePrintError::EmissionBudgetExhausted`] when the budget
/// runs out, or any other [`AlethePrintError`] a step refuses to render
/// with.
pub fn try_export_alethe_with_problem_scope_overrides_and_budget(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    work_budget: Option<u64>,
) -> Result<String, AlethePrintError> {
    try_export_alethe_with_authored_assume_shells(
        proof,
        terms,
        problem_assertions,
        term_overrides,
        None,
        work_budget,
    )
}

/// [`try_export_alethe_with_problem_scope_overrides_and_budget`] plus the
/// authored `not`-shell spellings for `assume` leaves; see
/// [`try_export_alethe_with_authored_surfaces_to`].
///
/// # Errors
///
/// As [`try_export_alethe_with_problem_scope_overrides_and_budget`], plus
/// [`AlethePrintError::InvalidSurfaceStep`] when a promised authored spelling
/// is not derivable from the printed term.
pub fn try_export_alethe_with_authored_assume_shells(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    negation_shell_assumes: Option<&HashMap<TermId, String>>,
    work_budget: Option<u64>,
) -> Result<String, AlethePrintError> {
    try_export_alethe_with_authored_surfaces(
        proof,
        terms,
        problem_assertions,
        term_overrides,
        AletheAuthoredSurfaces::shells(negation_shell_assumes),
        work_budget,
    )
}

/// Error type for the streaming Alethe export ([`AletheStreamError::Io`] can
/// only occur with a fallible sink; the in-memory `String` wrappers never
/// produce it).
#[derive(Debug)]
pub enum AletheStreamError {
    /// A proof step refused to render as a verifiable Alethe rule (#8821) or
    /// the emission work budget ran out (#A2b).
    Print(AlethePrintError),
    /// The sink failed (disk full, closed pipe, read-only target, ...).
    Io(std::io::Error),
}

impl std::fmt::Display for AletheStreamError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Print(e) => e.fmt(f),
            Self::Io(e) => write!(f, "I/O error while writing Alethe proof: {e}"),
        }
    }
}

impl std::error::Error for AletheStreamError {}

/// Maximum symbol names quoted in an
/// [`AlethePrintError::UndeclarableProofSymbols`] message. Wide preambles
/// (hundreds of datatype field-split symbols) would otherwise render a
/// multi-kilobyte one-line warning.
const UNDECLARABLE_SYMBOLS_IN_MESSAGE: usize = 8;

/// Whether every symbol in the emitted `define-fun` preamble resolves.
///
/// The preamble is the only text this exporter writes that is not a proof
/// command, and it is the only place a symbol can be INTRODUCED. Parsing it
/// back with [`AletheDocumentChecker`] turns the guard from a claim about
/// terms into a check of the bytes: an
/// [`AletheDefect::UndefinedSymbol`](alethe_parser::AletheDefect::UndefinedSymbol)
/// here is exactly carcara's `identifier '<x>' is not defined`.
///
/// Defects surface eagerly from `push_str`, so `finish()` — which would demand
/// an empty clause the preamble alone cannot derive — is never called.
///
/// The scope is built from the problem's free variables PLUS its application
/// heads. The heads matter: `problem_scope_symbol_names` walks only `Var`
/// nodes, so a scope without them would fail to resolve `P` in a body like
/// `(choice ((x Int)) (P x))` and reject a correct definition. Sorts are left
/// open (`ProblemScope::from_symbols`), because AY does not retain the
/// problem's `declare-sort` names in-process and sorts are not a known defect
/// source.
fn skolem_definition_preamble_resolves(
    definitions: &[String],
    terms: &TermStore,
    problem_assertions: &[TermId],
) -> bool {
    let mut symbols = free_var_names(terms, problem_assertions.iter().copied());
    symbols.extend(variables::application_symbol_names(
        terms,
        problem_assertions.iter().copied(),
    ));
    let mut checker = AletheDocumentChecker::new(ProblemScope::from_symbols(symbols));
    for definition in definitions {
        if checker.push_str(definition).is_err() || checker.push_str("\n").is_err() {
            return false;
        }
    }
    true
}

/// Build the fail-closed error naming the symbols that made the document
/// unrenderable.
fn undeclarable_proof_symbols_error(names: &[String]) -> AlethePrintError {
    let mut shown = names
        .iter()
        .take(UNDECLARABLE_SYMBOLS_IN_MESSAGE)
        .cloned()
        .collect::<Vec<_>>()
        .join(", ");
    if names.len() > UNDECLARABLE_SYMBOLS_IN_MESSAGE {
        let _ = write!(
            shown,
            ", ... +{} more",
            names.len() - UNDECLARABLE_SYMBOLS_IN_MESSAGE
        );
    }
    AlethePrintError::UndeclarableProofSymbols {
        count: names.len(),
        names: shown,
    }
}

/// Streaming variant of
/// [`try_export_alethe_with_problem_scope_overrides_and_budget`]: renders the
/// proof step-by-step directly into `out` instead of materializing the whole
/// certificate as one in-memory `String`.
///
/// This is the peak-RSS fix for large default-mode certificates
/// (#rss-vs-z3 campaign): a multi-hundred-MB Alethe document built via
/// `String::push_str` transiently holds ~1.5x its final size during buffer
/// growth. Streaming through a `BufWriter` bounds the exporter's own memory
/// to one rendered step. The byte stream is IDENTICAL to the `String`
/// variant's output — the wrapper above delegates here.
///
/// # Errors
///
/// Returns [`AletheStreamError::Print`] exactly where the `String` variant
/// errors, and [`AletheStreamError::Io`] when the sink fails. On error the
/// sink may have received a partial prefix; callers writing to a file should
/// write to a temporary path and rename on success.
pub fn try_export_alethe_with_problem_scope_overrides_and_budget_to<W: std::io::Write>(
    out: &mut W,
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    work_budget: Option<u64>,
) -> Result<(), AletheStreamError> {
    try_export_alethe_with_authored_surfaces_to(
        out,
        proof,
        terms,
        problem_assertions,
        term_overrides,
        AletheAuthoredSurfaces::default(),
        work_budget,
    )
}

/// [`try_export_alethe_with_problem_scope_overrides_and_budget_to`] plus the
/// authored surfaces ([`AletheAuthoredSurfaces`]): the `not`-shell spellings
/// for `assume` leaves (#assume-boundary) and the nullary `define-fun`
/// premises.
///
/// `negation_shell_assumes` maps an assumed term to the EXACT text the problem
/// file asserts for it, in the one case AY's term store cannot represent:
/// `TermStore::mk_not` eliminates a double negation at construction, so
/// `(assert (not (not phi)))` leaves only `phi` behind and the `assume` printed
/// for it is AY's own rewriting rather than a premise of the query. The printer
/// puts the authored text at the leaf and derives the canonical unit with stock
/// `not_not` steps; it fails closed if the authored text is not exactly that
/// shape over the term's own printed rendering.
///
/// # Errors
///
/// As [`try_export_alethe_with_problem_scope_overrides_and_budget_to`], plus
/// [`AlethePrintError::InvalidSurfaceStep`] when a promised authored spelling
/// is not derivable from the printed term.
pub fn try_export_alethe_with_authored_surfaces_to<W: std::io::Write>(
    out: &mut W,
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    surfaces: AletheAuthoredSurfaces<'_>,
    work_budget: Option<u64>,
) -> Result<(), AletheStreamError> {
    try_export_alethe_with_authored_surfaces_to_with_progress(
        out,
        proof,
        terms,
        problem_assertions,
        term_overrides,
        surfaces,
        work_budget,
        &mut || true,
    )
}

/// Caller-controlled streaming export. The same irreversible observation is
/// used before preparation, between steps, and before reporting success.
/// On error the sink may contain a prefix; publish a temporary file only on
/// success. The callback grants no proof authority and introduces no deadline.
///
/// # Errors
/// As [`try_export_alethe_with_authored_surfaces_to`], plus caller refusal.
#[expect(
    clippy::too_many_arguments,
    reason = "the public streaming boundary keeps proof, context, authored surfaces, budget, and owner explicit"
)]
pub fn try_export_alethe_with_authored_surfaces_to_with_progress<W: std::io::Write>(
    out: &mut W,
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    surfaces: AletheAuthoredSurfaces<'_>,
    work_budget: Option<u64>,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<(), AletheStreamError> {
    // A budget-exhausted export is refused at the next step, so nothing
    // assembled past exhaustion is read (DR-PROOF-RENDER-BUDGET-20261118).
    let printer = AlethePrinter::new_with_overrides_and_budget(terms, term_overrides, work_budget)
        .with_assembled_rendering(alethe_printer::AssembledRendering::CachedWithinBudget)
        .with_emission_progress(keep_going)
        .with_authored_surfaces(surfaces);
    export_alethe_with_printer_to(out, proof, terms, problem_assertions, &printer)
}

/// Stream through the configured printer, retaining its original progress owner.
pub(crate) fn export_alethe_with_printer_to<W: std::io::Write>(
    out: &mut W,
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    printer: &AlethePrinter<'_>,
) -> Result<(), AletheStreamError> {
    printer
        .check_emission_progress(0)
        .map_err(AletheStreamError::Print)?;
    validate_reachable_assumes_in_problem_scope(proof, problem_assertions)
        .map_err(AletheStreamError::Print)?;
    printer
        .prepare_proof(proof)
        .map_err(AletheStreamError::Print)?;

    let definitions = prepare_alethe_definitions(printer, proof, terms, problem_assertions)?;
    // The same obligation for APPLICATION heads and SORT names, which the
    // definitions walk never sees (`application_heads.rs`): judged on the
    // shipped bytes of each definition and step.
    let foreign_symbols =
        application_heads::unresolvable_proof_symbols(proof, terms, problem_assertions);
    for definition in &definitions {
        application_heads::decline_if_shipped(definition, &foreign_symbols)
            .map_err(AletheStreamError::Print)?;
    }
    printer
        .check_emission_progress(0)
        .map_err(AletheStreamError::Print)?;
    for definition in definitions {
        writeln!(out, "{definition}").map_err(AletheStreamError::Io)?;
    }
    for (idx, step) in proof.steps.iter().enumerate() {
        let step_id = ProofId(idx as u32);
        printer
            .check_emission_progress(step_id.0)
            .map_err(AletheStreamError::Print)?;
        let rendered = printer
            .format_step(step, step_id)
            .map_err(AletheStreamError::Print)?;
        printer
            .check_emission_progress(step_id.0.saturating_add(1))
            .map_err(AletheStreamError::Print)?;
        application_heads::decline_if_shipped(&rendered, &foreign_symbols)
            .map_err(AletheStreamError::Print)?;
        out.write_all(rendered.as_bytes())
            .map_err(AletheStreamError::Io)?;
        out.write_all(b"\n").map_err(AletheStreamError::Io)?;
        printer.finish_exported_step(step_id);
    }
    printer
        .check_emission_progress(u32::try_from(proof.steps.len()).unwrap_or(u32::MAX))
        .map_err(AletheStreamError::Print)
}

fn prepare_alethe_definitions(
    printer: &AlethePrinter<'_>,
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
) -> Result<Vec<String>, AletheStreamError> {
    // An Alethe PROOF document has no declaration command (see
    // `AlethePrintError::UndeclarableProofSymbols` for the carcara
    // measurement). Every symbol free in the proof but absent from the problem
    // must therefore be either RESUGARED away, DEFINED as the term it denotes,
    // or the export must DECLINE. Nothing is declared, ever.
    let auxiliary_declarations =
        collect_auxiliary_proof_declarations(proof, terms, problem_assertions)
            .map_err(|conflict| AletheStreamError::Print(conflict.into()))?;
    // A witness already resugared to an inline `choice` is not a free symbol of
    // the printed document at all, so it needs nothing in the preamble.
    let pending: Vec<String> = auxiliary_declarations
        .into_iter()
        .map(|(name, _sort)| name)
        .filter(|name| !printer.is_skolem_witness_name(name))
        .collect();
    // Skolem CONSTANTS are DEFINED as the Hilbert `choice` term they denote, in
    // mint order so a later definition may name an earlier one.
    let wanted: HashSet<String> = pending.iter().cloned().collect();
    let problem_symbols = free_var_names(terms, problem_assertions.iter().copied());
    let (definitions, defined) = printer.skolem_choice_definitions(&wanted, &problem_symbols);
    // (D) Post-emission invariant, checked on the TEXT rather than trusted.
    //
    // Everything above reasons about TERMS. The bytes that actually ship are
    // rendered through surface overrides, so a body can name a symbol the
    // term-level guard never saw. Re-read the preamble with AY's own Alethe
    // parser — the same one that reproduces carcara's document-layer
    // acceptance — and drop the whole preamble if any symbol in it fails to
    // resolve. Those witnesses then land in `undeclarable` below and the
    // export declines.
    //
    // Cost is O(preamble), not O(document): skipped outright when there is no
    // definition to check, which is the overwhelming majority of proofs. That
    // is why this can run unconditionally while the whole-document round-trip
    // (`--proof-self-check`) stays opt-in — the latter re-parses certificates
    // that reach hundreds of MB.
    //
    // Known limitation — the full invariant is "every free
    // symbol of the emitted document is bound — problem-declared, define-fun
    // bound, or locally bound". This checks the preamble, which is the only
    // place a symbol is INTRODUCED, but not the steps. One gap survives: the
    // `is_skolem_witness_name` filter above suppresses a witness from `pending`
    // on the PRINTER'S CLAIM to have resugared it to an inline `choice`. That
    // claim is unverified here, and a surface-override string that textually
    // mentions the raw witness name would leak it into a step, where it is
    // neither defined nor declined. Closing it needs the whole-document check,
    // which is exactly `AletheDocumentChecker` via `AletheSelfCheckWriter` —
    // already wired at `crates/ay/src/run.rs` behind `--proof-self-check` and
    // default-OFF because its false-reject rate over the corpus is measured,
    // not proved. Making it default-ON is a separate, measured decision.
    let (definitions, defined) = if definitions.is_empty()
        || skolem_definition_preamble_resolves(&definitions, terms, problem_assertions)
    {
        (definitions, defined)
    } else {
        (Vec::new(), HashSet::default())
    };
    // DECLINE BEFORE WRITING A BYTE. The sink is a file the caller publishes on
    // success; a partial prefix followed by an error is exactly the unparseable
    // artifact this whole path exists to prevent.
    let undeclarable: Vec<String> = pending
        .into_iter()
        .filter(|name| !defined.contains(name))
        .collect();
    if !undeclarable.is_empty() {
        return Err(AletheStreamError::Print(undeclarable_proof_symbols_error(
            &undeclarable,
        )));
    }
    Ok(definitions)
}

include!("reachable_assume_validation.rs");
/// Render an [`AlethePrintError`] as a loudly-marked document and warn on `stderr`.
///
/// The output is intentionally NOT a valid Alethe proof. Every downstream
/// checker will refuse it: the `(error ...)` S-expression is not a legal
/// proof command. This guarantees that a printer failure cannot be mistaken
/// for a successful UNSAT certificate (#8821).
fn render_unverifiable(err: &AlethePrintError, context: &str) -> String {
    // Loud stderr log — the caller almost certainly redirects proof output
    // to a file, so the stderr warning is the only visible signal.
    eprintln!(
        "ay-proof: UNVERIFIABLE PROOF from {context}: {err} (see #8821; no :rule trust \
         fallback will be written)"
    );
    format!(
        "; UNVERIFIABLE PROOF — ay refused to emit :rule trust fallback (#8821)\n\
         ; context: {context}\n\
         (error \"UNVERIFIABLE PROOF: {err}\")\n"
    )
}

#[cfg(test)]
#[path = "lib_tests.rs"]
mod tests;
