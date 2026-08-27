// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed handling for `eq_transitive` surface forms.

use ay_core::{AletheRule, Proof, ProofStep, TermData, TermId, TheoryLemmaKind};

use super::super::Executor;

impl Executor {
    /// Demote `eq_transitive` when an override cannot print its hypothesis.
    ///
    /// A boolean wrapper can re-spell canonical `(not (= a b))` as
    /// `(= (= a b) false)`, which Carcara rejects for `eq_transitive`. The
    /// internal certificate remains valid, but its wire rendering does not.
    /// Demoting to an honest `hole` makes mandatory certification decline the
    /// artifact instead of publishing an invalid document. `Generic` is not a
    /// substitute: the same clause can validate as a linear-arithmetic identity.
    ///
    /// This runs only on a real proof demand and after all promotion passes and
    /// surface rewriting. A `(distinct a b)` override remains admissible because
    /// the printer's resugaring bridge reconstructs a spec-valid derivation.
    pub(super) fn demote_unrenderable_eq_transitive_lemmas(&self, proof: &mut Proof) {
        if !(self.produce_proofs_enabled() || self.strict_proofs_enabled()) {
            return;
        }
        let Some(overrides) = self.last_proof_term_overrides.as_ref() else {
            return;
        };
        for step in &mut proof.steps {
            let ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::EufTransitive,
                clause,
                ..
            } = step
            else {
                continue;
            };
            if Self::eq_transitive_clause_is_unrenderable(&self.ctx.terms, overrides, clause) {
                *step = ProofStep::Step {
                    rule: AletheRule::Hole,
                    clause: clause.clone(),
                    premises: Vec::new(),
                    args: Vec::new(),
                };
            }
        }
    }

    /// Whether an installed surface override makes a `(not (= ..))` hypothesis
    /// of this clause unprintable as `eq_transitive`.
    ///
    /// Shared so the demotion above and the producers that MINT an
    /// `EufTransitive` leaf decide it identically. A producer that promotes a
    /// clause this predicate rejects would only be handing the demotion a
    /// `hole` — trading a rescuable `trust` rejection for a hard one — so the
    /// producers consult it and decline instead.
    pub(in crate::executor) fn eq_transitive_clause_is_unrenderable(
        terms: &ay_core::TermStore,
        overrides: &ay_core::kani_compat::DetHashMap<TermId, String>,
        clause: &[TermId],
    ) -> bool {
        clause.iter().any(|&literal| {
            matches!(terms.get(literal), TermData::Not(_))
                && overrides.get(&literal).is_some_and(|surface| {
                    let surface = surface.trim_start();
                    !surface.starts_with("(not ") && !surface.starts_with("(distinct ")
                })
        })
    }
}
