// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The presentation gate of the nested-CEGQI expansion certificate
//! (`nested_publish.rs`): the installed proof's authored `assume` spellings,
//! and, under a demanded certificate, the document it must render.
//!
//! The contract is RESTORE OR REVERT. The restoration's document is kept only
//! when it is complete and the input's own: it renders, carries no `hole` or
//! `trust` step, assumes only assertions as written (with no foreign
//! terminal `assume` on the internal path either), and states no integer
//! numeral the realify lane leaves in a `Real` binder body. Anything else
//! puts the proof-publication state back, so the certificate prints the
//! document it printed before the restoration existed and is judged exactly
//! as before: no shape moves from published to declined, and no document
//! changes unless it becomes authored and complete.

use super::super::proof_surface_syntax::holds_numeral_beyond_realify;
use super::super::qsat_route::ProofStateSnapshot;
use super::super::Executor;
use crate::normalize_premise_surface;

impl Executor {
    /// Present the installed expansion certificate, then say why it cannot
    /// back an `unsat` whose certificate the caller demanded, or `None` when
    /// it can (`nested_publish.rs` module docs).
    ///
    /// The certificate replaces `last_proof` through the strict installation
    /// boundary AFTER the ordinary assembly's
    /// `restore_reachable_authored_assume_surface_overrides` ran for a
    /// different proof, so it owes that restoration (the pass's contract), as
    /// the implied-universal lane pays it
    /// (`implied_ground_inst_presentation.rs`). Without it the root `assume`
    /// printed AY's freshened binder: `(forall ((q_0 Bool)) q_0)` for an
    /// authored `(forall ((q Bool)) q)` (Trust's `forall-bool`), which an
    /// external checker, matching premises without alpha-equivalence,
    /// refuses at the first `assume`.
    pub(super) fn qlra_presentation_refusal(&mut self) -> Option<&'static str> {
        if self.qlra_authored_presentation_restored() {
            return None;
        }
        self.qlra_demanded_document_refusal()
    }

    /// Restore the authored `assume` spellings of the installed certificate;
    /// `true` when the restored document is kept (module docs).
    ///
    /// A revert restores the [`ProofStateSnapshot`] taken before the pass:
    /// the installed proof, its override table, the suppression flag, its
    /// quality and check results, the decline mechanism, the replay ledger
    /// and the unknown reason. Two effects of the pass are outside it and
    /// stay, as in the implied-universal lane: terms
    /// `elaborate_surface_subterm` interned (the store is append-only, and
    /// nothing that ships references them), and the finite-enum proof state
    /// a suppression clears, which is why a proof carrying that state is
    /// never handed to the pass at all.
    ///
    /// MEASURED reverts: `(forall ((q Bool)) (and q q))` (likewise
    /// `(= q true)`, `(not (not q))`, `(< q q)` over `Real`) has the instance
    /// `false` under a body that prints otherwise, so the restored document
    /// demotes its `forall_inst` to a `hole`; a certificate that already had
    /// a `hole` keeps it under the restoration; and
    /// `(forall ((x Real)) (= (+ x 1) x))` would assume `(+ x 1)`, which
    /// pinned carcara's proof parser refuses as `Int` against `Real`.
    ///
    /// Skipped, as in the implied lane, when no document is produced by
    /// request: the shed posture, no proof production, or no retained
    /// authored text (the retention-off rule of the restoration pass).
    fn qlra_authored_presentation_restored(&mut self) -> bool {
        if !self.checked_certificate_demanded()
            && (self.competition_shedding_active()
                || !self.is_producing_proofs()
                || !self.ctx.retains_parsed_assertions())
        {
            return false;
        }
        if self.last_finite_enum_pigeonhole.is_some()
            || self.last_checked_finite_enum_pigeonhole.is_some()
        {
            return false;
        }
        let Some(proof) = self.last_proof.clone() else {
            return false;
        };
        let before = ProofStateSnapshot::take(self);
        self.restore_reachable_authored_assume_surface_overrides(&proof);
        if self.qlra_installed_document_is_authored_and_complete() {
            return true;
        }
        before.restore(self);
        false
    }

    /// Whether the installed proof's problem-scoped document renders with no
    /// unproved step, assumes only the input as written, and states no
    /// numeral the realify lane leaves unrealified (module docs).
    fn qlra_installed_document_is_authored_and_complete(&self) -> bool {
        if self.last_unsat_proof_reconstruction_suppressed {
            return false;
        }
        let mut scan = ay_proof::AletheDocumentScan::default();
        if !matches!(
            self.try_export_installed_proof_alethe_to(&mut scan),
            Some(Ok(()))
        ) {
            return false;
        }
        if scan.unproved > 0 || scan.overflowed {
            return false;
        }
        let Some(authored) = self.authored_premise_surfaces() else {
            return false;
        };
        if scan
            .premise_assumes
            .iter()
            .any(|assume| !authored.contains(&normalize_premise_surface(assume)))
            || self.unsat_proof_terminal_foreign_assume()
        {
            return false;
        }
        !self.premise_holds_numeral_beyond_realify(&scan.premise_assumes)
    }

    /// Whether a premise `assume` states an integer numeral inside a binder
    /// or `match` while `Real` arithmetic is in play
    /// (`holds_numeral_beyond_realify`). `Real` is in play when the logic
    /// names real arithmetic or a declared symbol's signature mentions
    /// `Real`; a premise that does not re-parse counts as holding one.
    fn premise_holds_numeral_beyond_realify(&self, premise_assumes: &[String]) -> bool {
        let real_logic = self
            .ctx
            .logic()
            .is_some_and(|logic| logic.contains("RA") || logic.contains("RDL") || logic == "ALL");
        let real_in_play = real_logic
            || self.ctx.symbol_iter().any(|(name, info)| {
                !self.ctx.is_internal_symbol(name)
                    && std::iter::once(&info.sort)
                        .chain(&info.arg_sorts)
                        .any(core_sort_mentions_real)
            });
        premise_assumes.iter().any(|assume| {
            ay_frontend::sexp::parse_sexp(assume)
                .ok()
                .and_then(|sexp| ay_frontend::Term::from_sexp(&sexp).ok())
                .is_none_or(|term| holds_numeral_beyond_realify(&term, real_in_play))
        })
    }

    /// Why the installed expansion certificate cannot back an `unsat` whose
    /// certificate the caller demanded, or `None` when it can
    /// (`nested_publish.rs` module docs):
    /// the problem-scoped Alethe document must render.
    fn qlra_demanded_document_refusal(&self) -> Option<&'static str> {
        if !self.checked_certificate_demanded() {
            return None;
        }
        match self.try_export_installed_proof_alethe_to(&mut std::io::sink()) {
            None => Some("expansion-unrendered"),
            Some(Err(error)) => {
                tracing::debug!(target: "ay::qlra", %error, "expansion cert: render refused");
                Some("expansion-render-refused")
            }
            Some(Ok(())) => None,
        }
    }
}

fn core_sort_mentions_real(sort: &ay_core::Sort) -> bool {
    match sort {
        ay_core::Sort::Real => true,
        ay_core::Sort::Array(array) => {
            core_sort_mentions_real(&array.index_sort)
                || core_sort_mentions_real(&array.element_sort)
        }
        ay_core::Sort::Seq(element) => core_sort_mentions_real(element),
        _ => false,
    }
}
