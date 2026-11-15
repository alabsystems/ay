// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Canonical-spelling re-render of an already checked refutation.
//!
//! Authored source syntax is a PRESENTATION channel over the proof: it
//! re-spells canonical `TermId`s so an exported `assume` reads the way the
//! query authored it. The Alethe printer is fail-closed about a spelling it
//! cannot replay, which is right — but that refusal is a refusal of the
//! SPELLING, not of the derivation the strict checker accepted. A consumer
//! boundary that owns the PAIRED problem transport can therefore re-render
//! both halves canonically instead of withdrawing a checked refutation; see
//! `Solver::export_last_unsat_artifact`, the only caller.

use ay_core::TermId;
use ay_proof::AlethePrintError;

use super::{Executor, DEFAULT_ALETHE_EMISSION_WORK_BUDGET};

impl Executor {
    /// Render the last proof for the problem scope with the AUTHORED
    /// SOURCE-SYNTAX overrides withheld — the exact canonical spelling
    /// [`Self::check_proof_strict_with_datatypes`] validated.
    ///
    /// A source-syntax override is a PRESENTATION channel: it re-spells one
    /// canonical `TermId` so an exported `assume` reads the way the query
    /// authored it. It is not proof authority — `resolve_reachable_authored_sources`
    /// already authenticated every reachable root before any spelling was
    /// chosen, and withholding a spelling "restores nothing and removes
    /// nothing: the root keeps the canonical spelling the strict checker
    /// validated".
    ///
    /// The printer is nevertheless fail-closed about a spelling it cannot
    /// replay, and rightly so: an authored grouping that no `and_pos` /
    /// `cong` / `comp_simplify` chain bridges to the canonical term must not
    /// be disclosed. But that refusal is a refusal of the SPELLING, and a
    /// consumer boundary that owns the paired problem transport can re-render
    /// the same checked refutation canonically instead of withdrawing it. See
    /// `Solver::export_last_unsat_artifact`, the only caller: it pairs this
    /// with [`Self::try_export_last_proof_alethe_problem_smt2_canonical`], so
    /// the disclosed document and the disclosed problem agree byte-for-byte on
    /// every spelling. Text-file consumers of `(get-proof)` keep the loud
    /// refusal, because their problem file is not AY's to re-render.
    ///
    /// The canonical document is not trusted for being a retry: it goes
    /// through the same fail-closed printer, so an override-independent
    /// refusal (a missing Farkas certificate, an unrepresentable Skolem step,
    /// a non-problem `assume`) is raised here exactly as it was there.
    ///
    /// A caller must not read the identity of that error as the discriminator,
    /// though, because the other way to refuse is to DECLINE: the `None` arms
    /// below return no result at all rather than re-raising, and a sealed
    /// finite-enum proof — which has no canonical fallback spelling — takes
    /// that route today. `Some(Ok(_))` is the only outcome that means rescued;
    /// `None` and `Some(Err(_))` both mean it was not.
    ///
    /// Nor does succeeding here confer any verdict. This rescues a SPELLING,
    /// so it may only ever publish a refutation the strict verdict already
    /// accepts; the caller withdraws the artifact again when the verdict comes
    /// back `Rejected`, because before this rescue existed every print refusal
    /// returned `None` and a rejected artifact was never on the record. Nor
    /// does it restore the authored spelling: what the caller then discloses is
    /// this canonical text, paired with the canonical problem transport.
    ///
    /// `None` on the same terms as
    /// [`Self::try_export_last_proof_alethe_for_problem_scope`], plus for a
    /// finite-enum sidecar proof, whose surface overrides are its sealed
    /// authority rather than a presentation preference.
    #[must_use]
    pub fn try_export_last_proof_alethe_for_problem_scope_canonical(
        &self,
    ) -> Option<Result<String, AlethePrintError>> {
        self.in_alethe_dialect(|| self.export_canonical_in_dialect())
    }

    fn export_canonical_in_dialect(&self) -> Option<Result<String, AlethePrintError>> {
        if self.last_unsat_proof_reconstruction_suppressed
            || self.last_proof_has_finite_enum_sidecar()
        {
            return None;
        }
        let proof = self.last_proof_with_authenticated_alethe_surface()?;
        let emission_budget = self
            .proof_reconstruction_step_budget
            .map(|_| DEFAULT_ALETHE_EMISSION_WORK_BUDGET);
        let scope = self.proof_export_scope_assertions_for(proof)?;
        let overrides = self.canonical_export_term_overrides();
        Some(ay_proof::try_export_alethe_with_authored_assume_shells(
            proof,
            &self.ctx.terms,
            &scope,
            overrides.as_ref(),
            None,
            emission_budget,
        ))
    }

    /// Exact SMT-LIB problem bytes paired with
    /// [`Self::try_export_last_proof_alethe_for_problem_scope_canonical`].
    ///
    /// Rendered from the same scope and the same withheld-override table, so a
    /// consumer that checks the canonical document against these bytes sees
    /// one spelling throughout.
    #[must_use]
    pub fn try_export_last_proof_alethe_problem_smt2_canonical(&self) -> Option<String> {
        if self.last_unsat_proof_reconstruction_suppressed
            || self.last_proof_has_finite_enum_sidecar()
        {
            return None;
        }
        let proof = self.last_proof_with_authenticated_alethe_surface()?;
        let scope = self.proof_export_scope_assertions_for(proof)?;
        let overrides = self.canonical_export_term_overrides();
        self.alethe_problem_smt2_for(&scope, overrides.as_ref())
    }

    /// The same export override table with the AUTHORED SOURCE-SYNTAX channel
    /// (`last_proof_term_overrides`) withheld.
    ///
    /// Datatype field spellings stay: they are not a presentation preference
    /// but the only spelling under which a selector application is a legal
    /// external symbol, so dropping them would change what the document means,
    /// not merely how it reads.
    pub(in crate::executor) fn canonical_export_term_overrides(
        &self,
    ) -> Option<ay_core::kani_compat::DetHashMap<TermId, String>> {
        let fields = self.ctx.dt_field_surface_overrides();
        (!fields.is_empty()).then_some(fields)
    }
}
