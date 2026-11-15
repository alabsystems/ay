// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The authored surfaces an Alethe export hands the printer.
//!
//! Two problem facts are not terms, so the override table cannot carry them:
//! the authored `not`-shell spellings of the parent module, and the problem's
//! nullary `define-fun`s. The frontend expands such a macro at every use, so
//! no stored term names it and AY's strict checker validates the EXPANDED
//! clause; an instance spelled from an authored quantifier body still prints
//! `(select a k)` where AY checked `(select (store ..) k)`. Pinned carcara,
//! run without `--apply-function-defs`, reads `(define-fun a () S body)` as a
//! declaration of `a` plus the premise `(= a body)`, which is the exact bridge
//! between the two. The printer `assume`s an entry only inside a derivation it
//! completes (`ay-proof` `alethe_printer/closed_guard.rs`).

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{quote_symbol, Proof, TermId};

use super::super::proof_surface_syntax::format_frontend_term;
use super::super::Executor;

/// Most definitions handed over; a partial table only loses lowerings.
const MAX_DEFINITIONS: usize = 1024;
/// Longest single printed body.
const MAX_DEFINITION_BYTES: usize = 64 * 1024;
/// Largest table.
const MAX_TOTAL_BYTES: usize = 1024 * 1024;

/// The owned tables one export borrows as [`ay_proof::AletheAuthoredSurfaces`].
pub(in crate::executor) struct AuthoredExportSurfaces {
    negation_shells: HashMap<TermId, String>,
    nullary_definitions: HashMap<String, String>,
}

impl AuthoredExportSurfaces {
    /// Every non-empty channel.
    pub(in crate::executor) fn channels(&self) -> ay_proof::AletheAuthoredSurfaces<'_> {
        ay_proof::AletheAuthoredSurfaces {
            negation_shell_assumes: (!self.negation_shells.is_empty())
                .then_some(&self.negation_shells),
            nullary_definitions: (!self.nullary_definitions.is_empty())
                .then_some(&self.nullary_definitions),
        }
    }
}

impl Executor {
    /// The authored surfaces of the current problem, for one export.
    pub(in crate::executor) fn authored_export_surfaces(&self) -> AuthoredExportSurfaces {
        AuthoredExportSurfaces {
            negation_shells: self.authored_negation_shell_spellings().bridgeable,
            nullary_definitions: self.nullary_definition_premises(),
        }
    }

    /// The `(get-proof)` document for `proof` over `scope`.
    ///
    /// `(get-proof)` is a second exit for the SAME document, so the authored
    /// surfaces that the file-backed export restores must reach it too —
    /// otherwise the same query hands two consumers two different first lines,
    /// one of them a formula the problem does not assert (#assume-boundary).
    /// Without a `not`-shell spelling a refusal renders as the unverifiable
    /// marker document; with one, as the authored-spelling error.
    pub(in crate::executor) fn get_proof_alethe_with_authored_surfaces(
        &self,
        proof: &Proof,
        scope: &[TermId],
    ) -> String {
        let overrides = self.proof_export_term_overrides();
        let surfaces = self.authored_export_surfaces();
        let terms = &self.ctx.terms;
        if surfaces.negation_shells.is_empty() {
            return ay_proof::export_alethe_with_authored_surfaces(
                proof,
                terms,
                scope,
                overrides.as_ref(),
                surfaces.channels(),
            );
        }
        ay_proof::try_export_alethe_with_authored_surfaces(
            proof,
            terms,
            scope,
            overrides.as_ref(),
            surfaces.channels(),
            None,
        )
        .unwrap_or_else(|_| {
            "(error \"an authored assumption spelling has no checkable derivation\")".to_string()
        })
    }

    /// The override channel downstream wire rules see for `proof`, planned as
    /// the exporter plans it. The authored-assume planner confines a spelling
    /// that names a nullary `define-fun` through its definition premise, so it
    /// must read the table [`Self::authored_export_surfaces`] hands the
    /// printer; the `not`-shell channel is emission-only and plans nothing.
    /// See `ay_proof::effective_wire_term_overrides_for_authored_proof`.
    pub(in crate::executor) fn effective_wire_term_overrides_for_export(
        &self,
        proof: &Proof,
        raw: Option<&HashMap<TermId, String>>,
    ) -> Result<Option<HashMap<TermId, String>>, ay_proof::AlethePrintError> {
        let definitions = self.nullary_definition_premises();
        ay_proof::effective_wire_term_overrides_for_authored_proof(
            proof,
            &self.ctx.terms,
            raw,
            ay_proof::AletheAuthoredSurfaces {
                negation_shell_assumes: None,
                nullary_definitions: (!definitions.is_empty()).then_some(&definitions),
            },
        )
    }

    /// The producer table as every step other than a confined `let` assume
    /// prints it in the export of `proof`, planned under the same definition
    /// table, for producers that render a step FRAGMENT with the printer's
    /// bare formatter (see `ay_proof::term_overrides_outside_confined_let_assumes`).
    ///
    /// `None` means "render with `raw`": the table spells nothing with `let`,
    /// so no entry can be confined, or the planner declines, so the fragment
    /// keeps the conservative document-wide reading.
    pub(in crate::executor) fn let_confined_overrides_for_export(
        &self,
        proof: &Proof,
        raw: Option<&HashMap<TermId, String>>,
    ) -> Option<HashMap<TermId, String>> {
        if !raw?.values().any(|surface| surface.starts_with("(let")) {
            return None;
        }
        let definitions = self.nullary_definition_premises();
        ay_proof::term_overrides_outside_confined_let_assumes(
            proof,
            &self.ctx.terms,
            raw,
            ay_proof::AletheAuthoredSurfaces {
                negation_shell_assumes: None,
                nullary_definitions: (!definitions.is_empty()).then_some(&definitions),
            },
        )
        .ok()
        .flatten()
    }

    /// Printed symbol to printed body for every nullary `define-fun` the
    /// frontend authenticates for proof use (`source_nullary_definition_for_proof`:
    /// not recursive, not internal, not an adopted declared-function macro).
    pub(in crate::executor) fn nullary_definition_premises(&self) -> HashMap<String, String> {
        let mut premises = HashMap::default();
        let mut total = 0usize;
        for (name, _) in self.ctx.symbols_iter() {
            if premises.len() >= MAX_DEFINITIONS {
                break;
            }
            let Some(body) = self.ctx.source_nullary_definition_for_proof(name) else {
                continue;
            };
            let body = format_frontend_term(body);
            // A body the surface renderer cannot spell would be an `assume` no
            // problem premise matches; and carcara matches a premise THROUGH a
            // `let` without eliminating it (see the parent module), so a body
            // carrying one is left unreadable rather than guessed at.
            if body.len() > MAX_DEFINITION_BYTES
                || body.contains("<unsupported")
                || body.contains("(let ")
            {
                continue;
            }
            total = total.saturating_add(body.len() + name.len());
            if total > MAX_TOTAL_BYTES {
                break;
            }
            premises.insert(quote_symbol(name), body);
        }
        premises
    }
}
