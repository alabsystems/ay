// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The SINGLE SAT-emission chokepoint (#sat-chokepoint).
//!
//! Historically a public `Sat` could be minted at three independent verdict
//! paths — plain `check_sat` (`check_sat_guarded`), `check_sat_assuming`, and
//! `optimize` (`finalize_optimization`) — but the INDEPENDENT, fail-closed
//! model-check gate ([`Executor::apply_independent_model_gate`]) ran at ONLY the
//! first of them. A wrong model could therefore bypass the soundness kernel
//! entirely through check-sat-assuming or optimize.
//!
//! [`Executor::emit_sat_verdict`] closes that hole structurally: it is the ONLY
//! function that turns a *proposed* `Sat` into an *emitted* `Sat`, and it runs
//! the full gate sequence
//!
//! ```text
//!   strict gate  ->  quantified gate  ->  independent gate
//!                ->  authoritative-failclosed gate  ->  non-string-seq gate
//!                ->  formula-neutral output completion
//!                ->  validation-evidence postcondition  ->  certificate mint
//! ```
//!
//! in order, then mints an unforgeable [`SatCertificate`]. Every public verdict
//! path routes its proposed `Sat` through here; the inner theory loops keep
//! returning bare `SolveResult::Sat` (a PROPOSED verdict, always re-gated), so
//! no 40-site rewrite is needed. The certificate is required to construct a
//! public `Sat` [`VerifiedSolveResult`](crate::api::types::VerifiedSolveResult),
//! so the compiler forbids returning `Sat` at the public boundary without having
//! gone through this funnel.

use std::time::Instant;

use ay_core::TermId;

use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult};

/// Unforgeable witness that a `Sat` verdict passed the full
/// [`Executor::emit_sat_verdict`] funnel (strict, quantified, independent,
/// authoritative-failclosed, and non-string-sequence gates).
///
/// The single-element tuple field is PRIVATE to this module, so a
/// `SatCertificate` can only ever be constructed inside `emit_sat_verdict`
/// (below). A public `Sat`
/// [`VerifiedSolveResult`](crate::api::types::VerifiedSolveResult) requires one,
/// which makes it a compile-time impossibility to surface a `Sat` at a consumer
/// boundary without routing through the chokepoint.
#[derive(Debug)]
pub(crate) struct SatCertificate(());

impl Executor {
    /// Record one SAT-gate timing span in milliseconds (float stats print with
    /// two decimals, so seconds-resolution would round sub-10ms gates to 0).
    fn record_gate_span_ms(&mut self, stat_name: &str, started_at: Instant) {
        self.last_statistics
            .set_float(stat_name, started_at.elapsed().as_secs_f64() * 1e3);
    }

    /// The SINGLE place a proposed `Sat` becomes an emitted `Sat`.
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
    /// 6. formula-neutral arity>0 output completion, after the gates so it
    ///    cannot manufacture EUF validation evidence and before minting so the
    ///    certificate refers to the final printer-visible model;
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

            // A finite-table certificate can run residual validity probes
            // after constructing its outer witness. Those nested solves are
            // allowed to overwrite `last_model`; install the parked certified
            // witness only here, at the final public Sat funnel after every
            // result-mapping probe has finished.
            if self.finite_table_cert_grant_active {
                if let Some((model, pins)) = self.finite_table_cert_pending_witness.take() {
                    self.last_model = Some(model);
                    self.mbqi_sat_cert_pins = pins;
                    super::eval_memo_clear();
                }
            }

            // Vacuous SAT (no assertions and no assumption roots): the empty
            // conjunction is `true`, so model validation has no obligations.
            // Still finalize the exact printer-visible witness BEFORE recording
            // evidence: an empty solve may have no model object yet, and declared
            // unconstrained constants/functions must receive their canonical
            // interpretations. Once that formula-neutral completion is done,
            // `last_model_validated=true` is explicit VACUOUS evidence for the
            // final witness. This makes the private certificate and public
            // consumer boundary agree: empty SAT is definite, not UNDEF.
            if self.ctx.assertions.is_empty() && roots.is_empty() {
                self.last_result = Some(SolveResult::Sat);
                if self.last_model.is_none() {
                    self.last_model = Some(super::Model::empty());
                }
                self.complete_unconstrained_constants_for_output(roots);
                self.complete_unconstrained_functions_for_output(roots);
                self.last_model_validated = true;
                self.last_sat_certificate = Some(SatCertificate(()));
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
            self.complete_unconstrained_constants_for_output(roots);
            self.materialize_symbolic_array_defaults();
            self.record_gate_span_ms("phase.sat_gate.completion.ms", span);

            // (1) STRICT gate. When the model was not already validated in-loop, run
            // the full validation pipeline; otherwise the global strict
            // definitive-false gate still MUST run (in-loop theory SAT-fallback can
            // accept a model an oracle then proves concretely false).
            let span = Instant::now();
            let gated = if !self.last_model_validated {
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
            let gated = self.apply_nonstring_seq_failclosed_gate(gated);
            self.record_gate_span_ms("phase.sat_gate.nonstring_seq.ms", span);
            drop(_gate_view_caches);
            drop(_gate_eval_memo);
            self.record_gate_span_ms("phase.sat_gate.total.ms", funnel_started_at);
            // (5) Complete only arity>0 functions absent from every assertion and
            // assumption. This must run after the gates (creating an otherwise-
            // absent EUF model earlier would change their evidence classification)
            // but before the certificate is minted, so the certified model is the
            // final model printers observe. Formula-neutral by construction.
            if gated == SolveResult::Sat {
                self.complete_unconstrained_functions_for_output(roots);
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
            let gated = self.apply_sat_validation_postcondition(gated, roots);

            if gated == SolveResult::Sat {
                self.last_sat_certificate = Some(SatCertificate(()));
            } else {
                self.last_sat_certificate = None;
            }
            self.last_result = Some(gated.clone());
            Ok(gated)
        })();

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

    fn apply_sat_validation_postcondition(
        &mut self,
        result: SolveResult,
        roots: &[TermId],
    ) -> SolveResult {
        let has_obligations = !self.ctx.assertions.is_empty() || !roots.is_empty();
        if result != SolveResult::Sat || !has_obligations || self.last_model_validated {
            return result;
        }

        self.last_statistics.model_validation_failures += 1;
        self.last_statistics
            .set_int("model_validation.sat_emission_postcondition", 1);
        self.last_model = None;
        self.last_unknown_reason = Some(crate::executor_types::UnknownReason::Incomplete);
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

        exec.invalidate_last_check_result();

        assert!(exec.last_sat_certificate.is_none());
        assert!(exec.last_result.is_none());
        assert!(exec.last_model.is_none());
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
        assert!(exec.last_sat_certificate.is_some());
        assert_eq!(
            exec.ctx.assertions.len(),
            5,
            "temporary assumption must not leak into the persistent assertion stack"
        );
    }
}
