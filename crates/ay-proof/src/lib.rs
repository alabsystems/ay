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
use std::fmt::Write;

mod alethe_parser;
mod alethe_printer;
mod bundle;
pub mod bv_blast_export;
pub mod bv_blast_lean;
pub mod bv_blast_solver;
pub mod bv_cnf_refutation;
mod checker;
mod la_generic_signs;
mod partial;
mod quality;
mod terminal_trust;
mod variables;

pub use alethe_parser::{
    check_alethe_document, checkable_rule_names, AletheDefect, AletheDocumentChecker,
    AletheDocumentReport, AletheSelfCheckWriter, Pos as AlethePos, ProblemScope,
};
pub use alethe_printer::{
    split_alethe_application_bounded, AlethePrintError, AletheSurfaceParseError,
};
pub use bundle::{
    re_check_bundle_strict, render_term_canonical, BundleReCheck, SerializableProofBundle,
    PROOF_BUNDLE_SCHEMA,
};
pub use bv_blast_export::{
    export_bv_blast_proof, BitLemma, BitLemmaKind, BvBlastExportError, BvBlastProof,
    BvBlastValidateError, BvBlastValidateLimits, BvOp, Clause, ClauseProvenance, Lit, OperandRef,
    Refutation, ResRule, ResolutionStep, SliceObligation, VarRole, VarTable,
    FORMAT_VERSION as BV_BLAST_FORMAT_VERSION, SLICE_WIDTH,
};
pub use bv_blast_lean::render_bv_blast_proof_lean;
pub use bv_blast_solver::{
    export_bv_blast_proof_expr, export_bv_blast_proof_solved, BvExpr, BvExprExportError,
    BvSolvedExportError, SolvedObligation,
};
pub use bv_cnf_refutation::surface_bv_cnf_refutation;
pub use checker::recognize_ground_evaluate;
pub use checker::recognize_ite_same;
pub use checker::recognize_nra_interval_unsat;
pub use checker::recognize_nra_univariate_unsat;
pub use checker::recognize_order_ite_tautology;
pub use checker::recognize_regex_intersect_empty;
pub use checker::recognize_rounding_mode_domain;
pub use checker::recognize_string_ground_eval;
pub use checker::recognize_string_length_lemma;
pub use checker::{
    authenticate_bool_bv_unsat_query, bv_bitblast_requires_proof_producer,
    recognize_bool_tautology, recognize_bv_bitblast, recognize_bv_ground_evaluate,
    AuthenticatedBoolBvUnsatQuery, BoolBvUnsatAuthenticationError,
    MAX_PROOF_PRODUCING_BV_LEMMAS_PER_PROOF,
};
pub use checker::{
    authenticate_bv_lia_unsat_query, AuthenticatedBvLiaUnsatQuery, BvLiaUnsatAuthenticationError,
};
pub use checker::{
    check_proof, check_proof_collecting_trust, check_proof_collecting_trust_with_context,
    ProofCheckError,
};
pub use checker::{
    recognize_array_extensionality, recognize_array_extensionality_chain,
    recognize_array_select_store, recognize_array_theory_lemma,
    recognize_folded_array_extensionality, ExtDiffRegistry,
};
pub use checker::{
    recognize_datatype_distinct, recognize_datatype_selector_project,
    recognize_datatype_tester_eval, recognize_datatype_tester_eval_with_selectors,
};
pub use checker::{recognize_fp_classification, recognize_fp_classification_op};
pub use checker::{
    recognize_fp_forward_error, recognize_fp_ground_eval, recognize_fp_rounding_mode_domain,
};
pub use la_generic_signs::*;
pub use partial::{check_proof_partial, PartialProofCheck};
pub use quality::{
    authenticate_premise_clauses_strict_with_context,
    authenticate_premise_clauses_strict_with_context_and_progress,
    authenticate_premise_clauses_with_deferred_generic_theory_and_progress,
    check_proof_partial_with_quality, check_proof_strict, check_proof_strict_with_context,
    check_proof_strict_with_context_and_progress, check_proof_strict_with_datatypes,
    check_proof_strict_with_datatypes_and_selectors, check_proof_with_quality,
    validate_array_extensionality_provenance, AuthenticatedPremiseClauses,
    PremiseClausesWithDeferredGeneric, ProofQuality,
};
pub use terminal_trust::{
    terminal_trust_report, terminal_trust_report_with_provenance, TerminalTrustReport,
};

use alethe_printer::AlethePrinter;
use variables::{
    collect_auxiliary_proof_declarations, collect_proof_variables, free_var_names,
    SymbolSortConflict,
};

/// The problem-declared symbol names the Alethe exporter treats as already in
/// scope.
///
/// The round-trip self-check needs a [`ProblemScope`]; when the problem text
/// is not available on disk (stdin mode) this is the in-process substitute.
/// Sorts are not recoverable this way, so the resulting scope tolerates
/// unknown sort names — see [`ProblemScope::from_symbols`].
#[must_use]
pub fn problem_scope_symbol_names(terms: &TermStore, problem_assertions: &[TermId]) -> Vec<String> {
    variables::problem_scope_symbol_names(terms, problem_assertions)
}

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
        let _ = writeln!(output, "(declare-fun {} () {})", quote_symbol(name), sort);
    }

    for (idx, step) in proof.steps.iter().enumerate() {
        let step_id = ProofId(idx as u32);
        output.push_str(&printer.format_step(step, step_id)?);
        output.push('\n');
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
    let mut output = Vec::new();
    match try_export_alethe_with_problem_scope_overrides_and_budget_to(
        &mut output,
        proof,
        terms,
        problem_assertions,
        term_overrides,
        work_budget,
    ) {
        Ok(()) => Ok(String::from_utf8(output).expect("Alethe printer emits UTF-8")),
        Err(AletheStreamError::Print(e)) => Err(e),
        // Writing into a Vec<u8> is infallible.
        Err(AletheStreamError::Io(e)) => unreachable!("Vec<u8> sink cannot fail: {e}"),
    }
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
    validate_reachable_assumes_in_problem_scope(proof, problem_assertions)
        .map_err(AletheStreamError::Print)?;
    let printer = AlethePrinter::new_with_overrides_and_budget(terms, term_overrides, work_budget);
    printer
        .prepare_proof(proof)
        .map_err(AletheStreamError::Print)?;

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
    // (`AY_PROOF_SELF_CHECK`) stays opt-in — the latter re-parses certificates
    // that reach hundreds of MB.
    //
    // TODO(#alethe-free-symbol-invariant): the FULL invariant is "every free
    // symbol of the emitted document is bound — problem-declared, define-fun
    // bound, or locally bound". This checks the preamble, which is the only
    // place a symbol is INTRODUCED, but not the steps. One gap survives: the
    // `is_skolem_witness_name` filter above suppresses a witness from `pending`
    // on the PRINTER'S CLAIM to have resugared it to an inline `choice`. That
    // claim is unverified here, and a surface-override string that textually
    // mentions the raw witness name would leak it into a step, where it is
    // neither defined nor declined. Closing it needs the whole-document check,
    // which is exactly `AletheDocumentChecker` via `AletheSelfCheckWriter` —
    // already wired at `crates/ay/src/run.rs` behind `AY_PROOF_SELF_CHECK` and
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
    for definition in definitions {
        writeln!(out, "{definition}").map_err(AletheStreamError::Io)?;
    }

    for (idx, step) in proof.steps.iter().enumerate() {
        let step_id = ProofId(idx as u32);
        let rendered = printer
            .format_step(step, step_id)
            .map_err(AletheStreamError::Print)?;
        out.write_all(rendered.as_bytes())
            .map_err(AletheStreamError::Io)?;
        out.write_all(b"\n").map_err(AletheStreamError::Io)?;
        // #A2b: bounded-overhead emission for the synthesized-default
        // certificate — never delays or changes the verdict, which was
        // printed before emission began.
        if printer.work_budget_exhausted() {
            return Err(AletheStreamError::Print(
                printer.work_budget_error(step_id.0.saturating_add(1)),
            ));
        }
    }

    Ok(())
}

/// Reject any authored leaf in the dependency cone of an empty clause unless
/// it is an actual problem-scope assertion. This is the production authority
/// boundary: an internally well-formed proof is still invalid if preprocessing
/// quietly introduced a stronger `Assume`.
pub fn validate_reachable_assumes_in_problem_scope(
    proof: &Proof,
    problem_assertions: &[TermId],
) -> Result<(), AlethePrintError> {
    let problem_assertions: HashSet<TermId> = problem_assertions.iter().copied().collect();
    let mut reachable = vec![false; proof.steps.len()];
    let mut stack = Vec::new();
    for (index, step) in proof.steps.iter().enumerate() {
        let derives_empty = match step {
            ProofStep::Step { clause, .. }
            | ProofStep::Resolution { clause, .. }
            | ProofStep::TheoryLemma { clause, .. } => clause.is_empty(),
            ProofStep::Assume(_) | ProofStep::Anchor { .. } => false,
            _ => false,
        };
        if derives_empty {
            reachable[index] = true;
            stack.push(index);
        }
    }
    while let Some(index) = stack.pop() {
        let mut push = |premise: ProofId| {
            let premise = premise.0 as usize;
            if premise < reachable.len() && !reachable[premise] {
                reachable[premise] = true;
                stack.push(premise);
            }
        };
        match &proof.steps[index] {
            ProofStep::Step { premises, .. } => {
                for &premise in premises {
                    push(premise);
                }
            }
            ProofStep::Resolution {
                clause1, clause2, ..
            } => {
                push(*clause1);
                push(*clause2);
            }
            _ => {}
        }
    }
    for (index, step) in proof.steps.iter().enumerate() {
        if !reachable[index] {
            continue;
        }
        if let ProofStep::Assume(term) = step {
            if !problem_assertions.contains(term) {
                return Err(AlethePrintError::NonProblemAssume {
                    id: ProofId(index as u32),
                    term: *term,
                });
            }
        }
    }
    Ok(())
}

/// Render an [`AlethePrintError`] as a loudly-marked Alethe document and
/// log a warning to `stderr`.
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
