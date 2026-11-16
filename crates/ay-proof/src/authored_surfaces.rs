// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The authored-surface channels of an Alethe export.
//!
//! The term overrides give the printer the problem's spelling of a TERM. Two
//! facts about the problem are not terms, and each has its own channel here:
//!
//! * `negation_shell_assumes` — the authored text of an assertion whose `not`
//!   shells elaboration ate (#assume-boundary); see
//!   [`super::try_export_alethe_with_authored_surfaces_to`];
//! * `nullary_definitions` — the problem's nullary `define-fun`s. AY expands
//!   such a macro at every use, so its strict checker validates the EXPANDED
//!   clause, while an instance spelled from an authored quantifier body still
//!   names the macro. Pinned carcara, run without `--apply-function-defs`,
//!   reads `(define-fun a () S body)` as a declaration of `a` plus the problem
//!   premise `(= a body)`, which is exactly the bridge between the two. The
//!   closed-atom lowering (`alethe_printer/closed_guard.rs`) `assume`s that
//!   premise only inside a derivation it completes.

use super::{
    export_alethe_with_printer_to, render_unverifiable, AlethePrintError, AletheStreamError,
    HashMap, Proof, TermId, TermStore,
};
use crate::alethe_printer::{AlethePrinter, CompleteBlastAsk};

/// Authored spellings the Alethe printer consults beyond the term overrides.
#[derive(Clone, Copy, Debug, Default)]
pub struct AletheAuthoredSurfaces<'a> {
    /// Exact problem text for assumed terms whose authored `not` shells
    /// elaboration ate.
    pub negation_shell_assumes: Option<&'a HashMap<TermId, String>>,
    /// Printed symbol to printed body of every nullary `define-fun` the
    /// printer may read through as the premise `(= symbol body)`.
    pub nullary_definitions: Option<&'a HashMap<String, String>>,
}

impl<'a> AletheAuthoredSurfaces<'a> {
    /// The `not`-shell channel alone.
    #[must_use]
    pub fn shells(negation_shell_assumes: Option<&'a HashMap<TermId, String>>) -> Self {
        Self {
            negation_shell_assumes,
            nullary_definitions: None,
        }
    }
}

impl<'a> AlethePrinter<'a> {
    /// Attach every authored-surface channel.
    #[must_use]
    pub(crate) fn with_authored_surfaces(self, surfaces: AletheAuthoredSurfaces<'a>) -> Self {
        self.with_negation_shell_assumes(surfaces.negation_shell_assumes)
            .with_nullary_definitions(surfaces.nullary_definitions)
    }
}

/// Whether the Alethe printer confines the authored spelling `surface` of
/// the canonical `term` to its own `assume` by reading `definitions` (printed
/// nullary `define-fun` symbol to printed body) as the problem premises
/// `(= symbol body)`, where the ordinary equivalence bridge alone cannot.
///
/// This runs the planner's own bounds and equivalence attempts, so a
/// producer that restores such a spelling only when this holds never hands
/// the printer a spelling it would leave document-wide. See
/// `alethe_printer/authored_assume/nullary_definition.rs`.
#[must_use]
pub fn nullary_definition_assume_bridge_is_supported(
    terms: &TermStore,
    term: TermId,
    surface: &str,
    definitions: &HashMap<String, String>,
) -> bool {
    const PREFLIGHT_WORK_BUDGET: u64 = 4 * 1024 * 1024;
    AlethePrinter::new_with_overrides_and_budget(terms, None, Some(PREFLIGHT_WORK_BUDGET))
        .with_nullary_definitions(Some(definitions))
        .nullary_definition_assume_bridge_supported(term, surface)
}

/// Whether the Alethe printer confines the authored spelling `surface` of a
/// canonical `term` whose top-level connective elaboration FOLDED away
/// (`(or (< x 3) false)`, `(= p true)`, `(and (> x 3) (= x x))` over
/// `(< x 3)` / `p` / `(< 3 x)`), deriving the canonical unit from the authored
/// `assume` with checked steps and no `hole`.
///
/// This runs the printer's own admissions, in its order: the authored-assume
/// equivalence engine (whose Boolean-fold leaf mirrors carcara's
/// simplification rules), then the folded-conjunction projection. It judges
/// the one spelling alone: the fold also declines beside another override
/// that re-spells a term inside or around `term`
/// (`alethe_printer/authored_assume/boolean_fold/document_spelling.rs`),
/// which only the finished override table shows, so a producer re-judges
/// what it restored against that table with
/// [`effective_wire_term_overrides_for_authored_proof`] (a confined term
/// leaves the wire channel). See `alethe_printer/authored_assume/
/// boolean_fold.rs` and `alethe_printer/folded_assume.rs`.
#[must_use]
pub fn folded_authored_assume_bridge_is_supported(
    terms: &TermStore,
    term: TermId,
    surface: &str,
) -> bool {
    folded_authored_assume_bridge_is_supported_with_progress(terms, term, surface, &mut || true)
}

/// Caller-controlled form of [`folded_authored_assume_bridge_is_supported`].
/// Refusal is sticky for this attempt and never licenses a new proof schema.
#[must_use]
pub fn folded_authored_assume_bridge_is_supported_with_progress(
    terms: &TermStore,
    term: TermId,
    surface: &str,
    keep_going: &mut dyn FnMut() -> bool,
) -> bool {
    const PREFLIGHT_WORK_BUDGET: u64 = 4 * 1024 * 1024;
    let printer =
        AlethePrinter::new_with_overrides_and_budget(terms, None, Some(PREFLIGHT_WORK_BUDGET))
            .with_emission_progress(keep_going);
    printer.check_emission_progress(0).is_ok()
        && printer.folded_authored_assume_bridge_supported(term, surface)
        && printer.check_emission_progress(0).is_ok()
}

/// [`crate::effective_wire_term_overrides_for_proof`] under the authored
/// surfaces the export hands the printer.
///
/// The authored-assume planner reads the definition table: it confines an
/// authored spelling that names a nullary `define-fun` by `assume`ing the
/// premise `(= name body)` (`alethe_printer/authored_assume/
/// nullary_definition.rs`). A wire screen that plans without that table keeps
/// such a spelling in its channel as if it rode the whole document, and judges
/// every theory lowering over text the exporter never prints. MEASURED with
/// every other part of the definition bridge in place and only the terminal
/// wire-gap screen planning without the table: `(define-fun lo () Bool (< x
/// 3))` with `(assert lo)` or `(assert (not (not lo)))`, and `(assert (>= x
/// 5))`, took the NRA-SOS bundle route and were published `trust_free=yes`
/// with a single-premise `resolution` pinned carcara 1.1.0 refused
/// ("expected at least 2 premises, got 1"); planned as the exporter plans,
/// the same queries publish a `la_generic` refutation carcara checks `valid`.
///
/// # Errors
///
/// As [`crate::effective_wire_term_overrides_for_proof`].
pub fn effective_wire_term_overrides_for_authored_proof(
    proof: &Proof,
    terms: &TermStore,
    term_overrides: Option<&HashMap<TermId, String>>,
    surfaces: AletheAuthoredSurfaces<'_>,
) -> Result<Option<HashMap<TermId, String>>, AlethePrintError> {
    effective_wire_term_overrides_for_authored_proof_with_progress(
        proof,
        terms,
        term_overrides,
        surfaces,
        None,
        &mut || true,
    )
}

/// Plan the same wire view under one caller observation and optional work cap.
/// Refusal returns an error, never a successfully planned empty override map.
///
/// # Errors
/// As [`effective_wire_term_overrides_for_authored_proof`], plus caller refusal.
pub fn effective_wire_term_overrides_for_authored_proof_with_progress(
    proof: &Proof,
    terms: &TermStore,
    term_overrides: Option<&HashMap<TermId, String>>,
    surfaces: AletheAuthoredSurfaces<'_>,
    work_budget: Option<u64>,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<Option<HashMap<TermId, String>>, AlethePrintError> {
    let printer = AlethePrinter::new_with_overrides_and_budget(terms, term_overrides, work_budget)
        .with_emission_progress(keep_going)
        .with_authored_surfaces(surfaces);
    printer.check_emission_progress(0)?;
    printer.planned_wire_term_overrides(proof)
}

/// `term_overrides` as every step OTHER than a confined `let` assume prints
/// it: without each authored `let` spelling the exporter confines to its own
/// `assume` (`alethe_printer/let_assume_confinement.rs`), planned exactly as
/// the exporter plans under `surfaces`.
///
/// For a producer that predicts how a FRAGMENT of steps prints by running the
/// printer's bare step formatter, which plans nothing and so reads every
/// producer spelling as document-wide. A confined term prints as the
/// rendering of its own structure under every OTHER entry, which is exactly
/// what this table renders. MEASURED on `benchmarks/smt/QF_AUFLIA/
/// storeinv_nf_size2.smt2` (array equality authored as a two-binding `let`):
/// with the raw table every congruence-explanation fragment over that
/// equality printed `(not (let ..))`, the fragment render check refused it,
/// and three `EufCongruenceExplanation` lemmas stayed `hole`.
///
/// # Errors
///
/// As [`crate::effective_wire_term_overrides_for_proof`].
pub fn term_overrides_outside_confined_let_assumes(
    proof: &Proof,
    terms: &TermStore,
    term_overrides: Option<&HashMap<TermId, String>>,
    surfaces: AletheAuthoredSurfaces<'_>,
) -> Result<Option<HashMap<TermId, String>>, AlethePrintError> {
    AlethePrinter::new_with_overrides(terms, term_overrides)
        .with_authored_surfaces(surfaces)
        .overrides_outside_confined_let_assumes(proof)
}

/// The in-memory [`try_export_alethe_with_authored_surfaces_to`].
///
/// # Errors
///
/// As [`super::try_export_alethe_with_problem_scope_overrides_and_budget`],
/// plus [`AlethePrintError::InvalidSurfaceStep`] when a promised authored
/// spelling is not derivable from the printed term.
pub fn try_export_alethe_with_authored_surfaces(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    surfaces: AletheAuthoredSurfaces<'_>,
    work_budget: Option<u64>,
) -> Result<String, AlethePrintError> {
    try_export_alethe_with_authored_surfaces_with_progress(
        proof,
        terms,
        problem_assertions,
        term_overrides,
        surfaces,
        work_budget,
        &mut || true,
    )
}

/// Caller-controlled in-memory authored-surface export. The old entry point
/// delegates here with an always-accepting observer.
///
/// # Errors
/// As [`try_export_alethe_with_authored_surfaces`], plus caller refusal.
pub fn try_export_alethe_with_authored_surfaces_with_progress(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    surfaces: AletheAuthoredSurfaces<'_>,
    work_budget: Option<u64>,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<String, AlethePrintError> {
    rendered(|output| {
        crate::try_export_alethe_with_authored_surfaces_to_with_progress(
            output,
            proof,
            terms,
            problem_assertions,
            term_overrides,
            surfaces,
            work_budget,
            keep_going,
        )
    })
}

/// [`try_export_alethe_with_authored_surfaces`] for a render asked from
/// inside a solve: the complete bit-blast is asked until `stop` fires
/// ([`CompleteBlastAsk::AskedUntil`]). Such a render only chooses between
/// documents or screens one; a stopped lemma prints as the honest `hole` it
/// would print unasked, which the caller reads as not clean.
///
/// # Errors
///
/// As [`try_export_alethe_with_authored_surfaces`].
pub fn try_export_alethe_with_authored_surfaces_until(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    surfaces: AletheAuthoredSurfaces<'_>,
    work_budget: Option<u64>,
    stop: &dyn Fn() -> bool,
) -> Result<String, AlethePrintError> {
    let printer = AlethePrinter::new_with_overrides_and_budget(terms, term_overrides, work_budget)
        .with_authored_surfaces(surfaces)
        .asking_complete_blast(CompleteBlastAsk::AskedUntil(stop));
    rendered(|output| {
        export_alethe_with_printer_to(output, proof, terms, problem_assertions, &printer)
    })
}

/// The solve a render is asked from inside
/// ([`try_export_alethe_with_authored_surfaces_within_solve`]).
#[derive(Clone, Copy)]
pub struct AskingSolve<'s> {
    /// The solve's stop: the complete bit-blast is asked until it fires
    /// ([`CompleteBlastAsk::AskedUntil`]).
    pub stop: &'s dyn Fn() -> bool,
    /// The solve's record of its screen's declines
    /// ([`crate::BvSupportDeclines`]).
    pub declines: &'s crate::BvSupportDeclines,
}

/// [`try_export_alethe_with_authored_surfaces_until`] for a render of
/// `solve`, which also reads that solve's record of its screen's declines: a
/// bit-vector lemma the screen declined unstopped, spelled as this render
/// spells it, is not lowered again and keeps the `hole` its declined
/// lowerings leave.
///
/// # Errors
///
/// As [`try_export_alethe_with_authored_surfaces`].
pub fn try_export_alethe_with_authored_surfaces_within_solve(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    surfaces: AletheAuthoredSurfaces<'_>,
    work_budget: Option<u64>,
    solve: AskingSolve<'_>,
) -> Result<String, AlethePrintError> {
    let printer = AlethePrinter::new_with_overrides_and_budget(terms, term_overrides, work_budget)
        .with_authored_surfaces(surfaces)
        .asking_complete_blast(CompleteBlastAsk::AskedUntil(solve.stop))
        .reading_support_declines(solve.declines);
    rendered(|output| {
        export_alethe_with_printer_to(output, proof, terms, problem_assertions, &printer)
    })
}

/// The document `export` writes into memory.
fn rendered(
    export: impl FnOnce(&mut Vec<u8>) -> Result<(), AletheStreamError>,
) -> Result<String, AlethePrintError> {
    let mut output = Vec::new();
    match export(&mut output) {
        Ok(()) => Ok(String::from_utf8(output).expect("Alethe printer emits UTF-8")),
        Err(AletheStreamError::Print(e)) => Err(e),
        // Writing into a Vec<u8> is infallible.
        Err(AletheStreamError::Io(e)) => unreachable!("Vec<u8> sink cannot fail: {e}"),
    }
}

/// Unbudgeted [`try_export_alethe_with_authored_surfaces`] whose refusal
/// renders exactly as [`super::export_alethe_with_problem_scope_and_overrides`]
/// renders one.
#[must_use]
pub fn export_alethe_with_authored_surfaces(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    surfaces: AletheAuthoredSurfaces<'_>,
) -> String {
    export_alethe_with_authored_surfaces_with_progress(
        proof,
        terms,
        problem_assertions,
        term_overrides,
        surfaces,
        &mut || true,
    )
}

/// The same marked refusal document under a retained caller observation.
#[must_use]
pub fn export_alethe_with_authored_surfaces_with_progress(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    term_overrides: Option<&HashMap<TermId, String>>,
    surfaces: AletheAuthoredSurfaces<'_>,
    keep_going: &mut dyn FnMut() -> bool,
) -> String {
    try_export_alethe_with_authored_surfaces_with_progress(
        proof,
        terms,
        problem_assertions,
        term_overrides,
        surfaces,
        None,
        keep_going,
    )
    .unwrap_or_else(|e| render_unverifiable(&e, "export_alethe_with_problem_scope_and_overrides"))
}
