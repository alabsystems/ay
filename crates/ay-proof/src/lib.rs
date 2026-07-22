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
//! ## Example
//!
//! ```text
//! ; Declarations from problem
//! (declare-const a Int)
//! (declare-const b Int)
//!
//! ; Proof commands
//! (assume h1 (= a b))
//! (assume h2 (not (= a a)))
//! (step t1 (cl (= a a)) :rule refl)
//! (step t2 (cl) :rule resolution :premises (h2 t1))
//! ```
#![warn(missing_docs)]
#![warn(clippy::all)]

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{quote_symbol, TermId, TermStore};
pub use ay_core::{AletheRule, BvGateType, Proof, ProofId, ProofStep, TheoryLemmaKind};
use std::fmt::Write;

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

pub use alethe_printer::AlethePrintError;
pub use bundle::{
    re_check_bundle_strict, render_term_canonical, BundleReCheck, SerializableProofBundle,
    PROOF_BUNDLE_SCHEMA,
};
pub use bv_blast_export::{
    export_bv_blast_proof, BitLemma, BitLemmaKind, BvBlastExportError, BvBlastProof,
    BvBlastValidateError, BvOp, Clause, ClauseProvenance, Lit, OperandRef, Refutation, ResRule,
    ResolutionStep, SliceObligation, VarRole, VarTable, FORMAT_VERSION as BV_BLAST_FORMAT_VERSION,
    SLICE_WIDTH,
};
pub use bv_blast_lean::render_bv_blast_proof_lean;
pub use bv_blast_solver::{
    export_bv_blast_proof_expr, export_bv_blast_proof_solved, BvExpr, BvExprExportError,
    BvSolvedExportError, SolvedObligation,
};
pub use bv_cnf_refutation::surface_bv_cnf_refutation;
pub use checker::recognize_ite_same;
pub use checker::recognize_regex_intersect_empty;
pub use checker::recognize_string_ground_eval;
pub use checker::{check_proof, check_proof_collecting_trust, ProofCheckError};
pub use checker::{
    recognize_array_extensionality, recognize_array_select_store, recognize_array_theory_lemma,
    ExtDiffRegistry,
};
pub use checker::{recognize_bool_tautology, recognize_bv_bitblast};
pub use checker::{recognize_datatype_distinct, recognize_datatype_selector_project};
pub use checker::{recognize_fp_classification, recognize_fp_classification_op};
pub use partial::{check_proof_partial, PartialProofCheck};
pub use quality::{
    check_proof_partial_with_quality, check_proof_strict, check_proof_strict_with_context,
    check_proof_strict_with_datatypes, check_proof_strict_with_datatypes_and_selectors,
    check_proof_with_quality, validate_array_extensionality_provenance, ProofQuality,
};
pub use terminal_trust::{
    terminal_trust_report, terminal_trust_report_with_provenance, TerminalTrustReport,
};

use alethe_printer::AlethePrinter;
use variables::{collect_auxiliary_proof_declarations, collect_proof_variables};

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
/// verifiable Alethe rule — currently this fires only for `LraFarkas` /
/// `LiaGeneric` theory lemmas missing their `FarkasAnnotation`.
///
/// Use this variant when the caller must refuse to write an unverifiable
/// proof to disk. The infallible [`export_alethe`] wraps this function and
/// converts the error into a loudly-marked document for backwards
/// compatibility.
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
    let vars = collect_proof_variables(proof, terms);
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

/// Export a proof to Alethe format with proof-only auxiliary declarations.
///
/// This variant emits `(declare-fun ...)` lines for auxiliary symbols that are:
/// 1. Referenced by proof steps, and
/// 2. Not part of the original problem assertion scope.
///
/// The declaration preamble is deterministic (sorted by symbol name).
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
/// bytes touched). Pass `Some(..)` ONLY for the synthesized-default
/// certificate: the by-default `<input>.alethe` must never trade a fast
/// UNSAT verdict for minutes of proof materialization (QF_ALIA pp-family:
/// 2s solves whose emission ground 300s+ without completing). Explicit
/// `--proof` / `--strict-proofs` / `--self-check` / `(get-proof)` exports
/// must pass `None`.
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

    for (name, sort) in collect_auxiliary_proof_declarations(proof, terms, problem_assertions) {
        if printer.is_skolem_witness_name(&name) {
            continue;
        }
        writeln!(out, "(declare-fun {} () {sort})", quote_symbol(&name))
            .map_err(AletheStreamError::Io)?;
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
