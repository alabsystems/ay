// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sealed SAT-emission chokepoints (#sat-chokepoint).
//!
//! Historically a public `Sat` could be minted at three independent verdict
//! paths — plain `check_sat` (`check_sat_guarded`), `check_sat_assuming`, and
//! `optimize` (`finalize_optimization`) — but the INDEPENDENT, fail-closed
//! model-check gate ([`Executor::apply_independent_model_gate`]) ran at ONLY the
//! first of them. A wrong model could therefore bypass the soundness kernel
//! entirely through check-sat-assuming or optimize.
//!
//! [`Executor::emit_sat_verdict`] closes that hole structurally for ordinary
//! solver proposals: it runs the full gate sequence
//!
//! ```text
//!   strict gate  ->  quantified gate  ->  independent gate
//!                ->  authoritative-failclosed gate  ->  non-string-seq gate
//!                ->  formula-neutral output completion
//!                ->  validation-evidence postcondition  ->  certificate mint
//! ```
//!
//! in order, then mints an unforgeable [`SatCertificate`]. Every ordinary public
//! verdict path routes its proposed `Sat` through here; the inner theory loops
//! keep returning bare `SolveResult::Sat` (a PROPOSED verdict, always re-gated).
//! The only second minting lane is [`Executor::emit_checked_projection_sat`],
//! which consumes sealed semantic, declaration/source, and caller-authored-query
//! evidence for one restricted quantified model. The certificate is required to
//! construct a public `Sat`
//! [`VerifiedSolveResult`](crate::api::types::VerifiedSolveResult), so the
//! compiler forbids either lane from surfacing `Sat` without complete evidence.

use std::cell::Cell;
use std::sync::atomic::Ordering;
use std::time::Instant;

use ay_core::TermId;

use crate::executor::exact_exists_bounds::CheckedExactExistsSat;
use crate::executor::quantified_sat::CheckedProjectionSatEvidence;
use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult, UnknownReason};

use super::completion::CheckedProjectionOutputCompletion;

/// Unforgeable witness that a `Sat` verdict passed one complete checked
/// emission lane.
///
/// Both the field and its enum type are private to this module, so a
/// `SatCertificate` can only ever be constructed by one of the complete
/// emission chokepoints below: the ordinary model-validation funnel, the
/// constructive quantified-projection proof lane, or the exact-exists theorem
/// lane. A public `Sat`
/// [`VerifiedSolveResult`](crate::api::types::VerifiedSolveResult) requires one,
/// which makes it a compile-time impossibility to surface a `Sat` at a consumer
/// boundary without routing through the chokepoint.
#[derive(Debug)]
pub(crate) struct SatCertificate(SatCertificateKind);

/// Linear proof that the ordinary model-validation funnel, rather than a
/// model-free theorem/projection lane, minted a SAT certificate.
///
/// Same-`Context` internal model transport consumes this narrower token before
/// it can move any model state out of a disposable executor.  The private field
/// prevents sibling modules from manufacturing the proof directly.
#[derive(Debug)]
pub(in crate::executor) struct ValidatedModelCertificate(());

#[derive(Debug)]
enum SatCertificateKind {
    /// The final witness passed the ordinary strict/independent gate funnel.
    ValidatedModel,
    /// The final witness is the exact total projection model established by
    /// independently checked semantic, declaration, and public-query evidence.
    CheckedProjection,
    /// The exact authored existential is a theorem for every valuation of its
    /// free integer constants, and the emitted model is the completed canonical
    /// default interpretation bound to that same immutable query snapshot.
    CheckedExactExists(Box<CheckedExactExistsSat>),
}

impl SatCertificate {
    /// Consume no authority; only confirm that this opaque token was minted by
    /// one of the module-private complete emission lanes.
    pub(crate) fn confirms_sat_emission(&self) -> bool {
        // Keep this exhaustive instead of using `matches!`: adding a future
        // certificate kind must make this admission point fail to compile
        // until that kind is deliberately classified as complete.
        match &self.0 {
            SatCertificateKind::ValidatedModel
            | SatCertificateKind::CheckedProjection
            | SatCertificateKind::CheckedExactExists(_) => true,
        }
    }

    /// Consume this SAT certificate only when it came from the ordinary
    /// validated-model funnel.
    ///
    /// Keep this match exhaustive: adding another SAT theorem lane must not
    /// silently make that lane eligible to transport a raw solver model.
    pub(in crate::executor) fn into_validated_model(self) -> Option<ValidatedModelCertificate> {
        match self.0 {
            SatCertificateKind::ValidatedModel => Some(ValidatedModelCertificate(())),
            SatCertificateKind::CheckedProjection | SatCertificateKind::CheckedExactExists(_) => {
                None
            }
        }
    }

    /// Recheck any snapshot-bearing certificate immediately before its
    /// one-shot consumption. Existing strict-model and projection tokens are
    /// minted at their terminal gates; the new exact-exists token deliberately
    /// retains its authored permit and immutable term snapshot.
    pub(crate) fn is_current_for(&self, executor: &Executor) -> bool {
        match &self.0 {
            SatCertificateKind::ValidatedModel | SatCertificateKind::CheckedProjection => true,
            SatCertificateKind::CheckedExactExists(evidence) => evidence.is_current(executor),
        }
    }
}

impl Executor {
    /// Record one SAT-gate timing span in milliseconds (float stats print with
    /// two decimals, so seconds-resolution would round sub-10ms gates to 0).
    fn record_gate_span_ms(&mut self, stat_name: &str, started_at: Instant) {
        self.last_statistics
            .set_float(stat_name, started_at.elapsed().as_secs_f64() * 1e3);
    }

    /// Emit SAT from the exact unit-difference existential theorem.
    ///
    /// The sealed evidence proves the sole authored formula true for every
    /// valuation of its free Int constants. Consequently the canonical
    /// completed default model is a genuine witness; no quantified evaluator
    /// or Cooper candidate is trusted. Evidence is rechecked both before and
    /// after model construction, and the private token is minted last.
    pub(in crate::executor) fn emit_checked_exact_exists_sat(
        &mut self,
        evidence: CheckedExactExistsSat,
    ) -> Result<SolveResult> {
        self.last_sat_certificate = None;
        self.last_model_validated = false;
        self.last_model = None;
        self.last_proof = None;
        self.clear_finite_enum_proof_state();

        if !evidence.is_current(self) {
            return Ok(self.reject_checked_exact_exists_sat(
                "exact-exists SAT evidence was stale before model construction",
            ));
        }
        if self.should_abort_theory_loop() {
            self.last_result = Some(SolveResult::Unknown);
            return Ok(SolveResult::Unknown);
        }

        let model = self.completed_default_model();
        if !evidence.is_current(self) {
            return Ok(self.reject_checked_exact_exists_sat(
                "exact-exists SAT evidence became stale during model construction",
            ));
        }
        if self.should_abort_theory_loop() {
            self.last_result = Some(SolveResult::Unknown);
            return Ok(SolveResult::Unknown);
        }

        self.last_model = Some(model);
        self.last_unknown_reason = None;
        self.last_model_validated = true;
        self.last_statistics
            .set_int("model_validation.checked_exact_exists_certificate", 1);
        self.last_result = Some(SolveResult::Sat);
        self.last_sat_certificate = Some(SatCertificate(SatCertificateKind::CheckedExactExists(
            Box::new(evidence),
        )));
        Ok(SolveResult::Sat)
    }

    fn reject_checked_exact_exists_sat(&mut self, detail: &str) -> SolveResult {
        self.last_sat_certificate = None;
        self.last_model_validated = false;
        self.last_model = None;
        self.last_statistics
            .set_int("model_validation.checked_exact_exists_rejected", 1);
        self.downgrade_sat_after_gate(detail);
        self.last_result = Some(SolveResult::Unknown);
        tracing::warn!(detail, "checked exact-exists SAT emission failed closed");
        SolveResult::Unknown
    }

    /// Canonically reject an internal SAT that reaches a publication boundary
    /// without its linear certificate.
    ///
    /// Both text and native consumers use this transition. Clearing only the
    /// wrapper/model bit would leave stale objective/proof state behind, while
    /// retaining a decision trace would claim the raw SAT that AY refused to
    /// publish. The canonical Unknown transition therefore revokes every query
    /// artefact, detaches incompatible trace writers, and records one consistent
    /// internal-error diagnostic before either surface returns `unknown`.
    pub(crate) fn reject_unadmitted_sat_publication(&mut self, detail: &str) {
        self.replace_last_result_with_unknown(UnknownReason::InternalError);
        self.last_statistics
            .set_string("unknown.reason", UnknownReason::InternalError.to_string());
        self.last_statistics
            .set_string("unknown.phase", "sat-publication-admission");
        self.last_statistics.set_string("unknown.detail", detail);
        tracing::warn!(detail, "SAT publication failed closed");
    }

    /// Consume the appropriate private one-shot certificate before a
    /// text-command result may publish a definite verdict.
    ///
    /// The native API consumes the same token while constructing
    /// `VerifiedSolveResult`. The command executor returns SMT-LIB text rather
    /// than that wrapper, so it must perform the equivalent admission here;
    /// formatting a bare internal `SolveResult::Sat` is never sufficient.
    pub(in crate::executor) fn admit_command_solve_result(
        &mut self,
        result: SolveResult,
    ) -> SolveResult {
        // The command-wide absolute deadline/interrupt remains installed here.
        // Let a late external stop revoke either capability before this method
        // consumes it; otherwise text SAT could escape a stop that fired after
        // model certification, and text UNSAT could race its proof funnel.
        let result = self.decline_definite_publication_on_external_stop(result);
        // M0(a): refresh the strict-check attribution stats so the published
        // values include the mint-time strict re-check that certification ran
        // after proof-quality stats were populated. Counting only.
        self.publish_strict_check_counters();
        self.last_command_unsat_admission = None;
        if result.is_unsat() {
            self.last_sat_certificate = None;
            if let Some(certificate) = self.take_unsat_certificate() {
                self.last_command_unsat_admission = Some(certificate.command_admission());
                return result;
            }
            return self.reject_uncertified_verdict_for_publication(
                "text-command UNSAT publication lacked an exact-query certification capability"
                    .to_string(),
            );
        }
        if result != SolveResult::Sat {
            self.last_sat_certificate = None;
            let _ = self.take_unsat_certificate();
            return result;
        }

        let _ = self.take_unsat_certificate();
        let admitted = self
            .take_sat_certificate()
            .is_some_and(|certificate| certificate.confirms_sat_emission());
        if admitted {
            return SolveResult::Sat;
        }

        self.reject_unadmitted_sat_publication(
            "text-command SAT publication lacked a sealed emission certificate",
        );
        SolveResult::Unknown
    }

    /// Emit SAT from one exact constructive quantified projection proof.
    ///
    /// This is deliberately separate from [`Self::emit_sat_verdict`]: the
    /// ordinary evaluator cannot evaluate universal quantifiers, whereas the
    /// sealed projection checker proves the complete quantified assertion after
    /// beta-reducing total UF projections. The final symbolic model, source
    /// declarations, and authored query are rechecked after every output-visible
    /// completion step and immediately before the private certificate is minted.
    pub(in crate::executor) fn emit_checked_projection_sat(
        &mut self,
        evidence: CheckedProjectionSatEvidence,
    ) -> Result<SolveResult> {
        // Revoke first, mint last. No predecessor token can survive a failed
        // installation, completion conflict, stop request, or stale epoch.
        self.last_sat_certificate = None;
        self.last_model_validated = false;

        let started_at = Instant::now();
        if !evidence.is_current(self) {
            return Ok(self.reject_checked_projection_sat(
                "checked projection SAT evidence was stale at the emission boundary",
            ));
        }
        if self.should_abort_theory_loop() {
            return Ok(self.stop_checked_projection_sat());
        }

        if let Err(error) = self.install_authorized_projection_model(&evidence) {
            return Ok(self.reject_checked_projection_sat(&format!(
                "checked projection model installation failed closed: {error}"
            )));
        }

        // Keep `last_result` revoked throughout completion. The checked pass
        // operates on its explicit model and evidence, so it does not need a
        // provisional SAT marker. SAT becomes observable only after every
        // post-completion check succeeds and the private certificate is ready.
        // Use only the bounded projection-specific pass: the ordinary
        // completion pipeline performs repairs outside this proof's fragment.
        // The accepted implication is parametric in free constants, while
        // functions absent from every checked root may take the canonical empty
        // table.
        let interrupt = self.solve_interrupt.clone();
        let deadline = self.solve_deadline.clone();
        let memory_limit = self.memory_limit;
        let external_stop_observed = Cell::new(false);
        let mut memory_poll_countdown = 0u8;
        let mut should_stop = || {
            let stopped = interrupt
                .as_ref()
                .is_some_and(|flag| flag.load(Ordering::Relaxed))
                || deadline.expired()
                || if memory_poll_countdown == 0 {
                    memory_poll_countdown = 63;
                    crate::memory::memory_exceeded(memory_limit)
                        || ay_sys::process_memory_exceeded()
                } else {
                    memory_poll_countdown -= 1;
                    false
                };
            if stopped {
                external_stop_observed.set(true);
            }
            stopped
        };
        match self
            .complete_checked_projection_model_for_output(evidence.semantics(), &mut should_stop)
        {
            CheckedProjectionOutputCompletion::Completed => {}
            CheckedProjectionOutputCompletion::Stopped if external_stop_observed.get() => {
                return Ok(self.stop_checked_projection_sat());
            }
            CheckedProjectionOutputCompletion::Stopped => {
                return Ok(self.reject_checked_projection_sat(
                    "checked projection output completion exceeded its deterministic work limit",
                ));
            }
            CheckedProjectionOutputCompletion::Conflict => {
                return Ok(self.reject_checked_projection_sat(
                    "checked projection output completion conflicted with the frozen evidence",
                ));
            }
        }

        let installed_matches = self
            .last_model
            .as_ref()
            .is_some_and(|model| model.projection_ufs.matches_checked(evidence.semantics()));
        if !installed_matches {
            return Ok(self.reject_checked_projection_sat(
                "output completion changed the checked projection model",
            ));
        }
        if !evidence.is_current(self) {
            return Ok(self.reject_checked_projection_sat(
                "checked projection SAT evidence became stale before certificate minting",
            ));
        }
        if self.should_abort_theory_loop() {
            return Ok(self.stop_checked_projection_sat());
        }

        self.last_unknown_reason = None;
        self.last_model_validated = true;
        self.last_statistics
            .set_int("model_validation.checked_projection_certificate", 1);
        self.record_gate_span_ms("phase.sat_gate.checked_projection.ms", started_at);
        self.last_result = Some(SolveResult::Sat);
        self.last_sat_certificate = Some(SatCertificate(SatCertificateKind::CheckedProjection));
        Ok(SolveResult::Sat)
    }

    /// Clear every provisional SAT artefact after an external stop.
    ///
    /// Checked output completion temporarily installs `last_result = Sat` so
    /// the existing model machinery can operate. An interrupt, deadline, or
    /// memory stop must retire that marker together with the incomplete model;
    /// otherwise later API consumers can mistake the stopped solve for a
    /// completed SAT result and synthesize a default model.
    fn stop_checked_projection_sat(&mut self) -> SolveResult {
        self.last_model = None;
        self.last_model_validated = false;
        self.last_sat_certificate = None;
        self.last_result = Some(SolveResult::Unknown);
        SolveResult::Unknown
    }

    /// Fail-closed cleanup shared by every constructive-certificate rejection.
    fn reject_checked_projection_sat(&mut self, detail: &str) -> SolveResult {
        self.last_sat_certificate = None;
        self.last_model_validated = false;
        self.last_statistics
            .set_int("model_validation.checked_projection_rejected", 1);
        self.downgrade_sat_after_gate(detail);
        self.last_result = Some(SolveResult::Unknown);
        tracing::warn!(detail, "checked projection SAT emission failed closed");
        SolveResult::Unknown
    }

    /// The single emission path for an ordinary solver-proposed `Sat`.
    ///
    /// For a non-`Sat` `proposed` verdict this is a no-op passthrough (and clears
    /// any stale certificate). For a proposed `Sat` it runs, IN ORDER:
    ///
    /// 0. for the vacuous empty formula, construct and complete the final
    ///    output-visible model, then record explicit vacuous validation evidence;
    /// 1. unconstrained-constant output completion over `roots` (so the gates
    ///    check exactly the values the printers will read);
    /// 2. the STRICT model gate — the full model validation
    ///    ([`finalize_sat_model_validation`](Executor::finalize_sat_model_validation))
    ///    when the model was not already validated in-loop, otherwise the
    ///    strict definitive-false gate
    ///    ([`apply_strict_model_gate`](Executor::apply_strict_model_gate)). If
    ///    that gate repairs the model, full validation is rerun so evidence
    ///    always describes the final emitted witness;
    /// 3. the quantified-assertion certificate gate, which can independently
    ///    discharge quantified leaf conjuncts and fails closed otherwise;
    /// 4. the INDEPENDENT, fail-closed model-check gate
    ///    ([`apply_independent_model_gate`](Executor::apply_independent_model_gate));
    /// 5. the AUTHORITATIVE-FAILCLOSED gate
    ///    ([`apply_authoritative_failclosed_gate`](Executor::apply_authoritative_failclosed_gate)),
    ///    retained as a theory-specific defense in depth after the universal
    ///    `CannotConfirm -> Unknown` boundary.
    /// 6. ordinary-model formula-neutral arity>0 output completion after the
    ///    gates. Quantified theorem producers instead complete exact-root-
    ///    absent declarations before sealing; their funnel path is read-only;
    /// 7. a release-mode validation-evidence postcondition: a non-trivial
    ///    `Sat` may not escape unless model validation completed. Deferred
    ///    inner solves never reach this public emission funnel; their scope
    ///    restores `skip_model_eval` before the outer verdict is emitted.
    ///
    /// It mints a [`SatCertificate`] into `last_sat_certificate` iff the funnel
    /// emits `Sat`, and clears it otherwise. `roots` are the extra constraint
    /// roots for unconstrained-output completion: `&[]` for plain check-sat,
    /// the assumptions for check-sat-assuming.
    pub(in crate::executor) fn emit_sat_verdict(
        &mut self,
        proposed: SolveResult,
        roots: &[TermId],
    ) -> Result<SolveResult> {
        // Revoke first, mint last. In particular, a `?` error from any
        // validation gate must not leave the preceding solve's token live.
        self.last_sat_certificate = None;
        // Assumptions are first-class validation obligations, not merely model-
        // completion roots. Install one scoped combined assertion set so EVERY
        // completion pass and gate below checks the exact public formula
        // `assertions ∧ roots`. Restoring outside the closure guarantees both the
        // success and `?` error paths leave the persistent assertion stack intact.
        // No assumption validator may mutate the model after this function mints
        // its certificate.
        let scoped_validation_state = if roots.is_empty() {
            None
        } else {
            let mut combined = self.ctx.assertions.clone();
            combined.extend_from_slice(roots);
            Some((
                std::mem::replace(&mut self.ctx.assertions, combined),
                self.qfax_refinement_clause.clone(),
                self.last_rejected_array_assertion,
            ))
        };

        let emitted = (|| -> Result<SolveResult> {
            if proposed != SolveResult::Sat {
                self.last_sat_certificate = None;
                return Ok(proposed);
            }

            // Certificate models are affine. Move the one already-completed
            // checked witness into `last_model`; never clone or semantically
            // mutate it in this funnel. Finite/constant packages receive their
            // replacement-sensitive identity immediately on the local object,
            // before it becomes visible to the read-only gate stack.
            let publication_roots = self.ctx.assertions.clone();
            let model_free_mbqi_theorem_lane =
                self.has_current_model_free_mbqi_sat_authority(&publication_roots);
            if model_free_mbqi_theorem_lane {
                // The exact structural checker proves every authored root for
                // every interpretation. Discard any unrelated candidate left
                // by an inner solve and construct one deterministic witness
                // for output. This is deliberately Model::empty rather than a
                // pre-completed clone: the ordinary formula-neutral constant
                // and function completion below must remain the sole path that
                // determines printer-visible defaults.
                self.last_model = Some(super::Model::empty());
                self.last_model_validated = true;
                self.last_statistics
                    .set_int("model_validation.exact_closed_sentence_certificate", 1);
                super::eval_memo_clear();
            }
            // Routing bits are not authority. Retire a stale affine table lane
            // before selecting the publication model so it cannot mask a
            // different exact-current DT/MBQI/BV/CEGQI theorem. If no checked
            // authority remains, preserve the historical fail-closed outcome.
            let finite_table_transport_current = self.finite_table_cert_grant_active
                && self
                    .finite_table_cert_witness_state
                    .as_ref()
                    .is_some_and(|state| state.is_pending_current_for(self, &publication_roots));
            let const_interp_transport_current = self.const_interp_cert_grant_active
                && self
                    .const_interp_cert_witness_state
                    .as_ref()
                    .is_some_and(|state| state.is_pending_current_for(self, &publication_roots));
            let stale_table_routing = (self.finite_table_cert_grant_active
                && !finite_table_transport_current)
                || (self.const_interp_cert_grant_active && !const_interp_transport_current);
            if self.finite_table_cert_grant_active && !finite_table_transport_current {
                self.finite_table_cert_grant_active = false;
                self.finite_table_cert_witness_state = None;
            }
            if self.const_interp_cert_grant_active && !const_interp_transport_current {
                self.const_interp_cert_grant_active = false;
                self.const_interp_cert_witness_state = None;
            }
            let other_current_quantified_authority = model_free_mbqi_theorem_lane
                || self.has_current_model_bound_quantified_sat_authority(&publication_roots)
                || (self.bv_quantifier_full_domain_proof
                    && self
                        .bv_quantifier_full_domain_query_grant
                        .as_ref()
                        .is_some_and(|grant| grant.is_current_for(self, &publication_roots)))
                || self
                    .cegqi_uf_recompletion_grant
                    .as_ref()
                    .is_some_and(|grant| grant.is_current_for(self, &publication_roots));
            if stale_table_routing
                && !finite_table_transport_current
                && !const_interp_transport_current
                && !other_current_quantified_authority
            {
                self.downgrade_sat_after_gate(
                    "quantified table SAT routing was stale and no current theorem remained",
                );
                return Ok(SolveResult::Unknown);
            }
            let mut finite_certificate_lane = false;
            let mut const_interp_certificate_lane = false;
            if finite_table_transport_current {
                let Some(state) = self.finite_table_cert_witness_state.take() else {
                    self.downgrade_sat_after_gate(
                        "finite/default-table SAT authority lost its exact checked witness",
                    );
                    return Ok(SolveResult::Unknown);
                };
                let Some((staging, mut model)) = state.into_staging(self, &publication_roots)
                else {
                    self.downgrade_sat_after_gate(
                        "finite/default-table SAT authority was stale at publication",
                    );
                    return Ok(SolveResult::Unknown);
                };
                let model_epoch = model.seal_quantified_grant_model();
                let Some(installed) =
                    staging.into_installed(self, &publication_roots, &model, model_epoch)
                else {
                    self.downgrade_sat_after_gate(
                        "finite/default-table SAT authority could not seal its exact model",
                    );
                    return Ok(SolveResult::Unknown);
                };
                self.last_model = Some(model);
                self.finite_table_cert_witness_state = Some(installed);
                finite_certificate_lane = true;
                self.revoke_cegqi_uf_recompletion_authority();
                self.revoke_dt_sat_authority();
                self.revoke_mbqi_sat_authority();
                super::eval_memo_clear();
                // The finite/default certificate is the later authority when
                // both narrow certificates accepted.
                self.const_interp_cert_witness_state = None;
                self.const_interp_cert_grant_active = false;
            } else if const_interp_transport_current {
                let Some(state) = self.const_interp_cert_witness_state.take() else {
                    self.downgrade_sat_after_gate(
                        "constant-interpretation SAT authority lost its exact checked witness",
                    );
                    return Ok(SolveResult::Unknown);
                };
                let Some((staging, mut model)) = state.into_staging(self, &publication_roots)
                else {
                    self.downgrade_sat_after_gate(
                        "constant-interpretation SAT authority was stale at publication",
                    );
                    return Ok(SolveResult::Unknown);
                };
                let model_epoch = model.seal_quantified_grant_model();
                let Some(installed) =
                    staging.into_installed(self, &publication_roots, &model, model_epoch)
                else {
                    self.downgrade_sat_after_gate(
                        "constant-interpretation SAT authority could not seal its exact model",
                    );
                    return Ok(SolveResult::Unknown);
                };
                self.last_model = Some(model);
                self.const_interp_cert_witness_state = Some(installed);
                const_interp_certificate_lane = true;
                self.cegqi_uf_recompletion_grant = None;
                self.revoke_dt_sat_authority();
                self.revoke_mbqi_sat_authority();
                super::eval_memo_clear();
            }
            // DT/MBQI and CEGQI producers likewise arrive with a sealed exact
            // model. Merely classify their still-live authority. The exact
            // closed-sentence theorem above is model-free, so its canonical
            // witness follows ordinary formula-neutral completion rather than
            // this immutable theorem-model lane.
            let model_bound_certificate_lane = !finite_certificate_lane
                && !const_interp_certificate_lane
                && self.has_current_model_bound_quantified_sat_authority(&publication_roots);
            let cegqi_uf_certificate_lane = !model_bound_certificate_lane
                && self
                    .cegqi_uf_recompletion_grant
                    .as_ref()
                    .is_some_and(|grant| grant.is_current_for(self, &publication_roots));
            let certificate_model_lane = finite_certificate_lane
                || const_interp_certificate_lane
                || model_bound_certificate_lane
                || cegqi_uf_certificate_lane;

            // Vacuous SAT (no assertions and no assumption roots): the empty
            // conjunction is `true`, so model validation has no obligations.
            // Still finalize the exact printer-visible witness BEFORE recording
            // evidence: an empty solve may have no model object yet, and declared
            // unconstrained constants/functions must receive their canonical
            // interpretations. Once that formula-neutral completion is done,
            // `last_model_validated=true` is explicit VACUOUS evidence for the
            // final witness. This makes the private certificate and public
            // consumer boundary agree: empty SAT is definite, not UNDEF.
            if self.ctx.assertions.is_empty() && roots.is_empty() && !certificate_model_lane {
                self.last_result = Some(SolveResult::Sat);
                if self.last_model.is_none() {
                    self.last_model = Some(super::Model::empty());
                }
                self.complete_unconstrained_constants_for_output(roots);
                if !self.complete_unconstrained_functions_for_output(roots) {
                    self.downgrade_sat_after_gate(
                        "the symbolic projection model conflicts with a live declaration signature",
                    );
                    self.last_result = Some(SolveResult::Unknown);
                    return Ok(SolveResult::Unknown);
                }
                self.last_model_validated = true;
                self.last_sat_certificate =
                    Some(SatCertificate(SatCertificateKind::ValidatedModel));
                return Ok(SolveResult::Sat);
            }

            // Model validation expects a SAT marker in last_result.
            self.last_result = Some(SolveResult::Sat);
            // Timing is observational only. It spans the model completion and
            // three validation gates, never the verdict or error policy.
            let funnel_started_at = Instant::now();
            // Default declared-but-unconstrained constants IN the model before any
            // gate runs, so the strict/independent gates check exactly the values
            // the printers will read. Fill-only (#no-fabricated-model-values).
            let span = Instant::now();
            if !certificate_model_lane {
                self.complete_unconstrained_constants_for_output(roots);
                self.materialize_symbolic_array_defaults();
            }
            self.record_gate_span_ms("phase.sat_gate.completion.ms", span);

            // (1) STRICT gate. When the model was not already validated in-loop, run
            // the full validation pipeline; otherwise the global strict
            // definitive-false gate still MUST run (in-loop theory SAT-fallback can
            // accept a model an oracle then proves concretely false).
            let span = Instant::now();
            let gated = if certificate_model_lane {
                self.apply_strict_gate_to_affine_certificate_model()
            } else if !self.last_model_validated {
                self.finalize_sat_model_validation()?
            } else {
                let strict = self.apply_strict_model_gate(SolveResult::Sat);
                // The strict array retry can repair an already-validated model.
                // That invalidates evidence for the pre-repair witness; the strict
                // gate clears last_model_validated before mutation. Re-run the full
                // pipeline now so the certificate is bound to the FINAL model, not
                // a stale predecessor. A strict rejection already returned Unknown
                // and needs no further work.
                if strict == SolveResult::Sat && !self.last_model_validated {
                    self.finalize_sat_model_validation()?
                } else {
                    strict
                }
            };
            self.record_gate_span_ms("phase.sat_gate.strict.ms", span);

            if certificate_model_lane && gated != SolveResult::Sat {
                self.finite_table_cert_witness_state = None;
                self.const_interp_cert_witness_state = None;
                self.finite_table_cert_grant_active = false;
                self.const_interp_cert_grant_active = false;
                self.revoke_dt_sat_authority();
                self.revoke_mbqi_sat_authority();
                self.cegqi_uf_recompletion_grant = None;
            }

            // (2) QUANTIFIED-ASSERTION certificate gate. It runs before the
            // compositional evaluator and outside its caches because its nested
            // solves build models of other formulas. On success it records an
            // exact certificate marker; the independent pass then skips only
            // those quantified leaf conjuncts and still checks every ground
            // sibling. Deferred or indeterminate checks fail closed here.
            let span = Instant::now();
            let gated = self.apply_quantified_model_failclosed_gate(gated);
            self.record_gate_span_ms("phase.sat_gate.quantified.ms", span);

            // The independent and authoritative passes are read-only over the
            // now-final witness unless they reject it. Share only solver-side
            // leaf-evaluation and view caches across those two passes; their
            // independent compositional evaluator remains separate.
            let _gate_eval_memo = super::EvalMemoSession::new();
            let _gate_view_caches = super::independent_gate::GateViewCacheSession::new();
            // (3) INDEPENDENT, fail-closed model-check gate (soundness kernel):
            // every Sat whose model is either refuted or cannot be independently
            // confirmed is downgraded to Unknown.
            let span = Instant::now();
            let gated = self.apply_independent_model_gate(gated);
            self.record_gate_span_ms("phase.sat_gate.independent.ms", span);
            // (4) AUTHORITATIVE-FAILCLOSED defense in depth. The universal gate
            // above already rejects CannotConfirm; this preserves the narrower
            // ground-theory classifier and its regression diagnostics.
            let span = Instant::now();
            let gated = self.apply_authoritative_failclosed_gate(gated);
            self.record_gate_span_ms("phase.sat_gate.authoritative.ms", span);
            // (4b) NON-STRING-SEQUENCE FAIL-CLOSED gate: AY's symbolic non-string
            // sequence theory ((Seq Int)/(Seq Bool)/(Seq (_ BitVec n))/(Seq Real))
            // is systemically unsound on the sat side — many `seq.*` ops return a
            // wrong `sat` whose model cannot be produced/validated. Over a `Sat`
            // the independent gate could not confirm, an assertion referencing a
            // non-string-seq term the evaluator cannot pin to `true` fails CLOSED
            // to Unknown. Strings (`Sort::String`) never contain a `Sort::Seq(_)`
            // subterm, so this leaves them (and every non-sequence theory)
            // untouched. Runs while the gate caches are still live.
            let span = Instant::now();
            let mut gated = self.apply_nonstring_seq_failclosed_gate(gated);
            self.record_gate_span_ms("phase.sat_gate.nonstring_seq.ms", span);
            drop(_gate_view_caches);
            drop(_gate_eval_memo);
            self.record_gate_span_ms("phase.sat_gate.total.ms", funnel_started_at);
            if certificate_model_lane && gated == SolveResult::Sat {
                // Producer evidence was revoked before the read-only public
                // gate stack. Record validation only now, after the untouched
                // theorem model passed strict, quantified, independent, and
                // authoritative checks as the exact final witness.
                self.last_model_validated = true;
            }
            // (5) Complete only arity>0 functions absent from every assertion and
            // assumption. This must run after the gates (creating an otherwise-
            // absent EUF model earlier would change their evidence classification)
            // but before the certificate is minted, so the certified model is the
            // final model printers observe. Formula-neutral by construction.
            if gated == SolveResult::Sat
                && !certificate_model_lane
                && !self.complete_unconstrained_functions_for_output(roots)
            {
                self.downgrade_sat_after_gate(
                    "the symbolic projection model conflicts with a live declaration signature",
                );
                gated = SolveResult::Unknown;
            }

            // The model-free theorem is what justified replacing an arbitrary
            // predecessor candidate with the canonical witness. Recheck its
            // immutable query/source/root identity after output completion and
            // immediately before the validation postcondition can mint SAT.
            if gated == SolveResult::Sat
                && model_free_mbqi_theorem_lane
                && !self.has_current_model_free_mbqi_sat_authority(&publication_roots)
            {
                self.downgrade_sat_after_gate(
                    "exact closed-sentence SAT authority became stale during publication",
                );
                gated = SolveResult::Unknown;
            }
            // (6) RELEASE-MODE POSTCONDITION. The debug assertion at the public
            // check-sat boundary is useful diagnosis, but it cannot be the soundness
            // policy: optimized builds compile it out. Defense in depth at the only
            // SAT minting site guarantees that a future early return or stale defer
            // flag can only lose completeness (`Sat -> Unknown`), never publish an
            // unvalidated SAT witness. `skip_model_eval` is deliberately NOT
            // evidence here: scoped inner solves restore it before this funnel, and
            // legacy BV+LIA fallback paths can also set it after model validation
            // failed. Treating the flag as evidence would certify exactly those
            // known-unvalidated public results.
            let mut gated = self.apply_sat_validation_postcondition(gated, roots);

            // Recheck the original immutable authority immediately before
            // minting. Any model replacement/mutation, root slot reuse,
            // declaration redeclaration, value rollback, or pin staleness
            // drops currentness; this funnel never manufactures a replacement
            // epoch.
            if gated == SolveResult::Sat && certificate_model_lane {
                let current = self.last_model.as_ref().is_some_and(|model| {
                    if finite_certificate_lane {
                        self.finite_table_cert_witness_state
                            .as_ref()
                            .is_some_and(|state| {
                                state.is_installed_current_for(self, &publication_roots, model)
                            })
                    } else if const_interp_certificate_lane {
                        self.const_interp_cert_witness_state
                            .as_ref()
                            .is_some_and(|state| {
                                state.is_installed_current_for(self, &publication_roots, model)
                            })
                    } else if model_bound_certificate_lane {
                        self.has_current_model_bound_quantified_sat_authority(&publication_roots)
                    } else if cegqi_uf_certificate_lane {
                        self.cegqi_uf_recompletion_grant
                            .as_ref()
                            .is_some_and(|grant| grant.is_current_for(self, &publication_roots))
                    } else {
                        false
                    }
                });
                if !current {
                    self.downgrade_sat_after_gate(
                        "quantified SAT certificate no longer names the final emitted model",
                    );
                    self.finite_table_cert_witness_state = None;
                    self.const_interp_cert_witness_state = None;
                    self.finite_table_cert_grant_active = false;
                    self.const_interp_cert_grant_active = false;
                    self.revoke_dt_sat_authority();
                    self.revoke_mbqi_sat_authority();
                    self.cegqi_uf_recompletion_grant = None;
                    gated = SolveResult::Unknown;
                }
            }

            if gated == SolveResult::Sat {
                self.last_sat_certificate =
                    Some(SatCertificate(SatCertificateKind::ValidatedModel));
            } else {
                self.last_sat_certificate = None;
            }
            self.last_result = Some(gated.clone());
            Ok(gated)
        })();

        // One cleanup boundary for every fail-closed exit, including errors and
        // early affine-model failures. No routing bit or typed query grant from
        // a rejected candidate may survive to a later publication attempt.
        if !matches!(&emitted, Ok(result) if *result == SolveResult::Sat) {
            self.last_sat_certificate = None;
            self.last_model_validated = false;
            if emitted.is_err() {
                self.last_model = None;
            }
            self.clear_quantified_sat_authority();
        }

        if let Some((assertions, qfax_refinement, rejected_array_assertion)) =
            scoped_validation_state
        {
            self.ctx.assertions = assertions;
            // A strict/gate rejection of a temporary array assumption may derive
            // a retry clause and rejected-target marker. Neither is valid in the
            // persistent base assertion scope, so restore them with the assertion
            // stack on both Sat and fail-closed exits.
            self.qfax_refinement_clause = qfax_refinement;
            self.last_rejected_array_assertion = rejected_array_assertion;
        }
        emitted
    }

    /// Apply the strict oracle without exposing an affine theorem model to any
    /// repair-capable pipeline.
    ///
    /// A certificate model that needs repair fails closed. Its producer
    /// validation bit is revoked here and is restored only after the untouched
    /// model passes the complete public gate stack.
    fn apply_strict_gate_to_affine_certificate_model(&mut self) -> SolveResult {
        if !matches!(self.last_result, Some(SolveResult::Sat))
            || !self.last_model_validated
            || self.last_model.is_none()
        {
            self.downgrade_sat_after_gate(
                "quantified SAT certificate reached publication without a validated exact model",
            );
            self.last_model_validated = false;
            return SolveResult::Unknown;
        }

        self.last_model_validated = false;
        if !self.exact_certificate_model_passes_strict_read_only() {
            self.downgrade_sat_after_gate(
                "quantified SAT certificate model required a post-theorem semantic repair",
            );
            self.last_model_validated = false;
            return SolveResult::Unknown;
        }
        SolveResult::Sat
    }

    fn apply_sat_validation_postcondition(
        &mut self,
        result: SolveResult,
        roots: &[TermId],
    ) -> SolveResult {
        let has_obligations = !self.ctx.assertions.is_empty() || !roots.is_empty();
        let has_validated_model = self.last_model_validated && self.last_model.is_some();
        if result != SolveResult::Sat || !has_obligations || has_validated_model {
            return result;
        }

        self.last_statistics.model_validation_failures += 1;
        self.last_statistics
            .set_int("model_validation.sat_emission_postcondition", 1);
        self.last_model = None;
        self.last_model_validated = false;
        self.last_unknown_reason = Some(UnknownReason::Incomplete);
        self.last_result = Some(SolveResult::Unknown);
        self.record_model_validation_unknown_diagnostic(
            "SAT emission rejected: non-trivial result lacks completed model-validation evidence",
        );
        tracing::warn!(
            assertions = self.ctx.assertions.len(),
            assumption_roots = roots.len(),
            "SAT emission postcondition failed; degrading unvalidated SAT to Unknown"
        );
        SolveResult::Unknown
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor::model::EvalValue;
    use ay_core::Sort;
    use num_bigint::BigInt;

    #[test]
    fn sat_emission_postcondition_rejects_nontrivial_unvalidated_sat() {
        let mut exec = Executor::new();
        let assertion = exec.ctx.terms.true_term();
        exec.ctx.assertions.push(assertion);

        let result = exec.apply_sat_validation_postcondition(SolveResult::Sat, &[]);

        assert_eq!(result, SolveResult::Unknown);
        assert_eq!(exec.last_result, Some(SolveResult::Unknown));
        assert_eq!(
            exec.last_statistics
                .get_int("model_validation.sat_emission_postcondition"),
            Some(1)
        );
    }

    #[test]
    fn sat_emission_postcondition_rejects_model_less_validated_marker() {
        let mut exec = Executor::new();
        let assertion = exec.ctx.terms.true_term();
        exec.ctx.assertions.push(assertion);
        exec.last_model_validated = true;
        assert!(exec.last_model.is_none());

        let result = exec.apply_sat_validation_postcondition(SolveResult::Sat, &[]);

        assert_eq!(result, SolveResult::Unknown);
        assert!(!exec.last_model_validated);
        assert!(exec.last_model.is_none());
        assert_eq!(exec.last_result, Some(SolveResult::Unknown));
    }

    #[test]
    fn sat_emission_postcondition_rejects_skip_flag_leaked_from_plain_theory_path() {
        let mut exec = Executor::new();
        let assertion = exec.ctx.terms.true_term();
        exec.ctx.assertions.push(assertion);
        exec.skip_model_eval = true;

        let result = exec.apply_sat_validation_postcondition(SolveResult::Sat, &[]);

        assert_eq!(result, SolveResult::Unknown);
        assert_eq!(
            exec.last_statistics
                .get_int("model_validation.sat_emission_postcondition"),
            Some(1)
        );
    }

    #[test]
    fn sat_funnel_cannot_mint_certificate_from_skip_flag_alone() {
        let mut exec = Executor::new();
        let assertion = exec.ctx.terms.true_term();
        exec.ctx.assertions.push(assertion);
        exec.last_model = Some(crate::executor::model::Model::empty());
        exec.skip_model_eval = true;

        let result = exec
            .emit_sat_verdict(SolveResult::Sat, &[])
            .expect("release-mode SAT funnel should fail closed without an executor error");

        assert_eq!(result, SolveResult::Unknown);
        assert!(!exec.last_model_validated);
        assert!(exec.last_sat_certificate.is_none());
        assert_eq!(
            exec.last_statistics
                .get_int("model_validation.sat_emission_postcondition"),
            Some(1)
        );
    }

    #[test]
    fn model_transport_downcast_rejects_model_free_sat_lanes() {
        assert!(SatCertificate(SatCertificateKind::ValidatedModel)
            .into_validated_model()
            .is_some());
        assert!(SatCertificate(SatCertificateKind::CheckedProjection)
            .into_validated_model()
            .is_none());
    }

    #[test]
    fn finite_table_marker_without_parked_model_fails_closed() {
        let mut exec = Executor::new();
        let body = exec.ctx.terms.true_term();
        let forall = exec
            .ctx
            .terms
            .mk_forall(vec![("x".to_string(), Sort::Int)], body);
        exec.ctx.assertions.push(forall);
        exec.last_model = Some(crate::executor::model::Model::empty());
        exec.last_model_validated = true;
        exec.finite_table_cert_grant_active = true;
        assert!(exec.finite_table_cert_witness_state.is_none());

        let result = exec
            .emit_sat_verdict(SolveResult::Sat, &[])
            .expect("a lost certificate package must downgrade, not error");

        assert_eq!(result, SolveResult::Unknown);
        assert!(exec.last_sat_certificate.is_none());
    }

    #[test]
    fn legacy_quantified_markers_cannot_authorize_an_extra_false_assumption() {
        for marker in ["dt", "mbqi", "bv-full-domain"] {
            let mut exec = Executor::new();
            let body = exec.ctx.terms.false_term();
            let false_forall = exec
                .ctx
                .terms
                .mk_forall(vec![("x".to_string(), Sort::Int)], body);
            exec.last_model = Some(crate::executor::model::Model::empty());
            exec.last_result = Some(SolveResult::Sat);
            exec.last_model_validated = true;
            match marker {
                "dt" => exec.dt_cert_grant_active = true,
                "mbqi" => exec.mbqi_sat_cert_grant_active = true,
                "bv-full-domain" => exec.bv_quantifier_full_domain_proof = true,
                _ => unreachable!(),
            }

            let result = exec
                .emit_sat_verdict(SolveResult::Sat, &[false_forall])
                .expect("a forged routing marker must fail closed without an executor error");

            assert_eq!(
                result,
                SolveResult::Unknown,
                "legacy {marker} bit alone must not cover a different root window"
            );
            assert!(exec.last_sat_certificate.is_none(), "{marker}");
        }
    }

    #[test]
    fn finite_table_package_is_query_and_exact_root_scoped() {
        let mut exec = Executor::new();
        let body = exec.ctx.terms.true_term();
        let forall = exec
            .ctx
            .terms
            .mk_forall(vec![("x".to_string(), Sort::Int)], body);
        exec.ctx.assertions.push(forall);
        let package = crate::executor::mbqi::FiniteTableWitnessState::for_test(
            &exec,
            &exec.ctx.assertions,
            crate::executor::model::Model::empty(),
            Default::default(),
        )
        .expect("live finite-table package");
        assert!(package.is_pending_current_for(&exec, &exec.ctx.assertions));

        let saved_epoch = exec.query_authority_epoch.clone();
        exec.advance_query_authority_epoch();
        assert!(
            !package.is_pending_current_for(&exec, &exec.ctx.assertions),
            "a textually identical later query must not reuse finite-table authority"
        );
        exec.query_authority_epoch = saved_epoch;
        assert!(package.is_pending_current_for(&exec, &exec.ctx.assertions));

        let extra_root = exec.ctx.terms.true_term();
        exec.ctx.assertions.push(extra_root);
        assert!(
            !package.is_pending_current_for(&exec, &exec.ctx.assertions),
            "even a redundant added root is a different checked obligation window"
        );
    }

    #[test]
    fn finite_table_pending_scope_rejects_root_slot_reuse_but_accepts_append_only_growth() {
        let mut exec = Executor::new();
        let checkpoint = exec.ctx.terms.rollback_checkpoint();
        let body = exec.ctx.terms.true_term();
        let root = exec
            .ctx
            .terms
            .mk_forall(vec![("x".to_string(), Sort::Int)], body);
        exec.ctx.assertions.push(root);
        let package = crate::executor::mbqi::FiniteTableWitnessState::for_test(
            &exec,
            &[root],
            crate::executor::model::Model::empty(),
            Default::default(),
        )
        .expect("live finite-table package");

        let _suffix = exec
            .ctx
            .terms
            .mk_fresh_var("finite-package-suffix", Sort::Bool);
        assert!(package.is_pending_current_for(&exec, &[root]));

        exec.ctx.assertions.clear();
        exec.ctx.terms.rollback_to(checkpoint);
        let replacement_body = exec.ctx.terms.false_term();
        let replacement = exec.ctx.terms.mk_forall(
            vec![("replacement".to_string(), Sort::Int)],
            replacement_body,
        );
        assert_eq!(replacement, root, "rollback should reuse the numeric slot");
        exec.ctx.assertions.push(replacement);
        assert!(
            !package.is_pending_current_for(&exec, &[replacement]),
            "numeric root equality cannot retarget a package across arena generations"
        );
    }

    #[test]
    fn finite_table_pending_marker_cannot_authorize_quantified_gate() {
        let mut exec = Executor::new();
        let body = exec.ctx.terms.false_term();
        let root = exec
            .ctx
            .terms
            .mk_forall(vec![("x".to_string(), Sort::Int)], body);
        exec.ctx.assertions.push(root);
        exec.finite_table_cert_witness_state = Some(
            crate::executor::mbqi::FiniteTableWitnessState::for_test(
                &exec,
                &[root],
                crate::executor::model::Model::empty(),
                Default::default(),
            )
            .expect("live pending package"),
        );
        exec.finite_table_cert_grant_active = true;
        exec.last_model = Some(crate::executor::model::Model::empty());

        assert_eq!(
            exec.apply_quantified_model_failclosed_gate(SolveResult::Sat),
            SolveResult::Unknown,
            "Pending is transport state, not quantified SAT authority"
        );
    }

    #[test]
    fn stale_table_routing_cannot_mask_current_model_bound_authority() {
        let mut exec = Executor::new();
        let body = exec.ctx.terms.true_term();
        let root = exec
            .ctx
            .terms
            .mk_forall(vec![("x".to_string(), Sort::Int)], body);
        exec.ctx.assertions.push(root);
        exec.last_model = Some(crate::executor::model::Model::empty());
        let evidence = crate::executor::mbqi::CheckedDtSatAuthority::for_test(&mut exec, &[root])
            .expect("test model can be sealed for the exact root");
        assert!(exec.install_dt_sat_authority(evidence));
        exec.last_model_validated = true;

        // Simulate stale routing residue from narrower attempts. The raw bits
        // have no affine witnesses and must be retired rather than winning a
        // table publication branch over the exact-current DT theorem.
        exec.finite_table_cert_grant_active = true;
        exec.finite_table_cert_witness_state = None;
        exec.const_interp_cert_grant_active = true;
        exec.const_interp_cert_witness_state = None;

        let result = exec
            .emit_sat_verdict(SolveResult::Sat, &[])
            .expect("SAT emission does not error");

        assert_eq!(result, SolveResult::Sat);
        assert!(!exec.finite_table_cert_grant_active);
        assert!(exec.finite_table_cert_witness_state.is_none());
        assert!(!exec.const_interp_cert_grant_active);
        assert!(exec.const_interp_cert_witness_state.is_none());
        assert!(exec.dt_cert_grant_active);
        assert!(exec
            .dt_cert_query_grant
            .as_ref()
            .is_some_and(|grant| grant.is_current_for(&exec, &[root])));
    }

    #[test]
    fn finite_table_ground_projection_is_owned_by_parked_model() {
        let mut exec = Executor::new();
        let predicate = exec.ctx.terms.mk_var("p", Sort::Bool);
        let mut pins = ay_core::kani_compat::DetHashMap::default();
        pins.insert(predicate, EvalValue::Bool(true));
        let package = crate::executor::mbqi::FiniteTableWitnessState::for_test(
            &exec,
            &[],
            crate::executor::model::Model::empty(),
            pins,
        )
        .expect("live finite-table pin package");

        let (_staging, published) = package
            .into_staging(&exec, &[])
            .expect("current package moves its exact model once");
        assert_eq!(
            exec.evaluate_term(&published, predicate),
            EvalValue::Bool(true)
        );
        assert_ne!(
            exec.evaluate_term(&crate::executor::model::Model::empty(), predicate),
            EvalValue::Bool(true),
            "the parked model's pin must not become executor-global evaluator state"
        );
    }

    #[test]
    fn sat_emission_postcondition_rejects_unvalidated_assumption_only_sat() {
        let mut exec = Executor::new();
        let assumption = exec.ctx.terms.true_term();
        // The assumption-based BV+LIA fallback can leak this flag after its BV
        // model failed validation and the AUFLIA cross-check returned Unknown.
        // A SAT-level skeleton check is not model-validation evidence.
        exec.skip_model_eval = true;

        let result = exec.apply_sat_validation_postcondition(SolveResult::Sat, &[assumption]);

        assert_eq!(result, SolveResult::Unknown);
        assert_eq!(exec.last_result, Some(SolveResult::Unknown));
    }

    #[test]
    fn sat_emission_postcondition_accepts_completed_validation_evidence() {
        let mut exec = Executor::new();
        let assertion = exec.ctx.terms.true_term();
        exec.ctx.assertions.push(assertion);
        exec.last_model = Some(crate::executor::model::Model::empty());
        exec.last_model_validated = true;

        let result = exec.apply_sat_validation_postcondition(SolveResult::Sat, &[]);

        assert_eq!(result, SolveResult::Sat);
    }

    #[test]
    fn lifecycle_invalidation_revokes_prior_sat_certificate() {
        let mut exec = Executor::new();
        let result = exec
            .emit_sat_verdict(SolveResult::Sat, &[])
            .expect("trivial SAT emission");
        assert_eq!(result, SolveResult::Sat);
        assert!(exec.last_sat_certificate.is_some());
        exec.dt_cert_grant_active = true;
        exec.finite_table_cert_grant_active = true;
        exec.const_interp_cert_grant_active = true;
        exec.mbqi_sat_cert_grant_active = true;
        exec.bv_quantifier_full_domain_proof = true;
        let finite_package = crate::executor::mbqi::FiniteTableWitnessState::for_test(
            &exec,
            &exec.ctx.assertions,
            crate::executor::model::Model::empty(),
            Default::default(),
        )
        .expect("live finite-table package");
        exec.finite_table_cert_witness_state = Some(finite_package);

        exec.invalidate_last_check_result();

        assert!(exec.last_sat_certificate.is_none());
        assert!(exec.last_result.is_none());
        assert!(exec.last_model.is_none());
        assert!(!exec.dt_cert_grant_active);
        assert!(exec.dt_cert_query_grant.is_none());
        assert!(!exec.finite_table_cert_grant_active);
        assert!(!exec.const_interp_cert_grant_active);
        assert!(!exec.mbqi_sat_cert_grant_active);
        assert!(exec.mbqi_sat_cert_query_grant.is_none());
        assert!(!exec.bv_quantifier_full_domain_proof);
        assert!(exec.bv_quantifier_full_domain_query_grant.is_none());
        assert!(exec.finite_table_cert_witness_state.is_none());
        assert!(exec.const_interp_cert_witness_state.is_none());
    }

    #[test]
    fn stopped_checked_projection_clears_provisional_sat_state() {
        let mut exec = Executor::new();
        exec.last_result = Some(SolveResult::Sat);
        exec.last_model = Some(crate::executor::model::Model::empty());
        exec.last_model_validated = true;
        exec.last_sat_certificate = Some(SatCertificate(SatCertificateKind::CheckedProjection));

        let result = exec.stop_checked_projection_sat();

        assert_eq!(result, SolveResult::Unknown);
        assert_eq!(exec.last_result, Some(SolveResult::Unknown));
        assert!(!exec.last_result_is_sat());
        assert!(exec.last_result_is_unknown());
        assert!(exec.last_model.is_none());
        assert!(!exec.last_model_validated);
        assert!(exec.last_sat_certificate.is_none());
    }

    #[test]
    fn text_command_publication_consumes_certificate_and_rejects_bare_sat() {
        let mut admitted = Executor::new();
        let proposed = admitted
            .emit_sat_verdict(SolveResult::Sat, &[])
            .expect("trivial SAT emission");
        assert_eq!(
            admitted.admit_command_solve_result(proposed),
            SolveResult::Sat
        );
        assert!(
            admitted.last_sat_certificate.is_none(),
            "the command boundary must consume, not copy, its authority"
        );

        let mut bare = Executor::new();
        bare.last_model_validated = true;
        assert_eq!(
            bare.admit_command_solve_result(SolveResult::Sat),
            SolveResult::Unknown,
            "a validation boolean cannot substitute for the private token"
        );
        assert!(!bare.last_model_validated);
        assert!(bare.last_model.is_none());
        assert!(bare.last_result_is_unknown());
        assert_eq!(bare.unknown_reason(), Some(UnknownReason::InternalError));
        assert_eq!(
            bare.statistics().get_string("unknown.phase"),
            Some("sat-publication-admission")
        );
    }

    #[test]
    fn control_lifetime_late_interrupt_revokes_sat_before_text_command_admission() {
        let mut exec = Executor::new();
        let proposed = exec
            .emit_sat_verdict(SolveResult::Sat, &[])
            .expect("trivial SAT emission");
        assert_eq!(proposed, SolveResult::Sat);
        assert!(exec.last_sat_certificate.is_some());

        exec.set_solve_controls(
            Some(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
                true,
            ))),
            None,
        );
        let admitted = exec.admit_command_solve_result(proposed);

        assert_eq!(admitted, SolveResult::Unknown);
        assert_eq!(exec.unknown_reason(), Some(UnknownReason::Interrupted));
        assert_eq!(
            exec.unknown_origin(),
            Some(crate::UnknownOrigin::InterruptFlag)
        );
        assert!(exec.last_sat_certificate.is_none());
        assert!(exec.last_unsat_certificate.is_none());
        assert!(exec.last_model.is_none());
    }

    #[test]
    fn control_lifetime_late_memory_stop_revokes_sat_before_text_command_admission() {
        let mut exec = Executor::new();
        let proposed = exec
            .emit_sat_verdict(SolveResult::Sat, &[])
            .expect("trivial SAT emission");
        assert_eq!(proposed, SolveResult::Sat);
        assert!(exec.last_sat_certificate.is_some());

        exec.set_memory_limit(Some(0));
        let admitted = exec.admit_command_solve_result(proposed);

        assert_eq!(admitted, SolveResult::Unknown);
        assert_eq!(exec.unknown_reason(), Some(UnknownReason::MemoryLimit));
        assert_eq!(
            exec.unknown_origin(),
            Some(crate::UnknownOrigin::MemoryBudget)
        );
        assert!(exec.last_sat_certificate.is_none());
        assert!(exec.last_unsat_certificate.is_none());
        assert!(exec.last_model.is_none());
    }

    #[test]
    fn text_command_rejects_stale_exact_exists_sat_certificate() {
        let mut exec = Executor::new();
        let commands = ay_frontend::parse(
            "(set-logic LIA) (declare-const y Int) \
             (assert (exists ((x Int)) (and (> x y) (< x (+ y 2)))))",
        )
        .expect("valid exact-exists SAT setup");
        for command in &commands {
            exec.execute(command).expect("setup command executes");
        }

        let permit = exec
            .detached_authored_plain_hard_permit_for_test()
            .expect("plain hard query permit");
        let crate::executor::exact_exists_bounds::ExactExistsDecision::Sat(evidence) =
            exec.try_authorize_exact_exists_decision(permit)
        else {
            panic!("gap-two interval must produce exact SAT evidence");
        };
        let proposed = exec
            .emit_checked_exact_exists_sat(evidence)
            .expect("exact SAT emission");
        assert_eq!(proposed, SolveResult::Sat);

        // Any append changes the immutable term-store snapshot carried inside
        // the token, even when the authored assertion vector is unchanged.
        let _later = exec.ctx.terms.mk_var("later", Sort::Int);
        assert_eq!(
            exec.admit_command_solve_result(proposed),
            SolveResult::Unknown,
            "the text boundary must recheck snapshot-bearing SAT authority"
        );
        assert!(exec.last_sat_certificate.is_none());
        assert!(!exec.last_model_validated);
    }

    #[test]
    fn assumption_root_refutes_prevalidated_witness_before_certificate_mint() {
        let mut exec = Executor::new();
        let x = exec.ctx.terms.mk_var("x", Sort::Int);
        let zero = exec.ctx.terms.mk_int(BigInt::from(0));
        let one = exec.ctx.terms.mk_int(BigInt::from(1));
        let base = exec.ctx.terms.mk_eq(x, zero);
        let assumption = exec.ctx.terms.mk_eq(x, one);
        exec.ctx.assertions.push(base);

        let mut model = crate::executor::model::Model::empty();
        let mut values = ay_core::kani_compat::DetHashMap::<TermId, BigInt>::default();
        values.insert(x, BigInt::from(0));
        model.lia_model = Some(ay_lia::LiaModel { values });
        exec.last_model = Some(model);
        exec.last_result = Some(SolveResult::Sat);
        exec.last_model_validated = true;

        let result = exec
            .emit_sat_verdict(SolveResult::Sat, &[assumption])
            .expect("combined assertion+assumption validation must fail closed cleanly");

        assert_eq!(result, SolveResult::Unknown);
        assert!(exec.last_sat_certificate.is_none());
        assert_eq!(exec.ctx.assertions, vec![base], "scope must restore");
    }

    #[test]
    fn check_sat_assuming_certificate_is_for_final_combined_witness() {
        let commands = ay_frontend::parse(
            "(set-logic QF_LRA)\n\
             (declare-const x Real)\n\
             (declare-const y Real)\n\
             (declare-const z Real)\n\
             (assert (>= x 0.0))(assert (<= x 1.0))\n\
             (assert (>= y 0.0))(assert (<= y 1.0))\n\
             (assert (= (+ (* 1.0 x) (* 1.0 y) (* -1.0 z)) 1.0))\n\
             (check-sat-assuming ((>= z 1.0)))\n\
             (get-value (x y z))",
        )
        .expect("regression script must parse");
        let mut exec = Executor::new();
        let outputs = exec
            .execute_all(&commands)
            .expect("combined check-sat-assuming script must execute");

        assert_eq!(outputs.first().map(String::as_str), Some("sat"));
        assert_eq!(
            outputs.get(1).map(String::as_str),
            Some("((x 1.0) (y 1.0) (z 1.0))"),
            "the certified witness must be the assumption-pinned final Real model"
        );
        assert!(exec.last_model_validated);
        assert!(
            exec.last_sat_certificate.is_none(),
            "the text-command boundary consumes the one-shot certificate"
        );
        assert_eq!(
            exec.ctx.assertions.len(),
            5,
            "temporary assumption must not leak into the persistent assertion stack"
        );
    }
}
