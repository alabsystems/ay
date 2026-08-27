// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Internal proof-check bookkeeping and self-certification diagnostics.

use super::*;

impl Executor {
    /// One post-verdict diagnostic pass over a freshly built UNSAT proof:
    /// the `--self-check` bookkeeping walk AND the `ProofQuality` measurement
    /// walk, fused into a single metered, cancellable traversal.
    ///
    /// #diagnostic-envelope — this replaces `run_internal_proof_check` followed
    /// by `validate_and_measure_proof` at the one site that ran both back to
    /// back (`finalize_unsat_proof`). Two independent defects were sitting there:
    ///
    ///  1. DOUBLE WALK. Both entered `ay_proof` through the identical
    ///     `validate_step(.., strict = false, ..)` call, so every step was
    ///     semantically checked twice. `ay_proof::check_proof_partial_with_quality`
    ///     was written for exactly this (#proof-tax) and had never been wired to
    ///     a caller.
    ///  2. NO ENVELOPE. Neither walk was metered or cancellable, while the
    ///     MANDATORY certification gate beside them
    ///     (`check_strict_unsat_presentation` -> `check_with_executor_progress`)
    ///     has always been both. A caller's interrupt, solve deadline and memory
    ///     limit therefore governed the gate that decides the verdict but not the
    ///     diagnostics that cannot — which is backwards, and is why a
    ///     393-million-literal triangular resolution proof could hold a solve
    ///     open for ~16 minutes per attempt with every stop signal already raised.
    ///
    /// Strict mode is deliberately UNTOUCHED: it keeps its two existing strict
    /// walks (already metered) so no strict-mode statistic moves.
    #[cfg(feature = "proof-checker")]
    pub(in crate::executor) fn run_internal_proof_check_and_measure(&mut self, proof: &Proof) {
        if self.strict_proofs_enabled() {
            self.run_internal_proof_check(proof);
            let quality = self.validate_and_measure_proof(proof);
            if let Some(ref quality) = quality {
                self.populate_proof_quality_stats(quality);
            }
            self.last_proof_quality = quality;
            return;
        }

        let MeteredPartialCheck {
            summary,
            quality,
            error,
            ..
        } = check_partial_with_executor_progress(self, proof, WantQuality::Yes);
        self.proof_check_result = Some(summary.clone());
        if let Some(error) = error {
            let shape = Self::proof_shape_summary(proof);
            let checked = shape.checked_steps;
            let skipped = shape.skipped_hole_steps;
            let total = shape.total_steps;
            self.record_proof_check_stats(1, shape);
            tracing::error!(
                error = %error,
                checked_steps = checked,
                skipped_hole_steps = skipped,
                total_steps = total,
                "internal proof checker rejected UNSAT proof"
            );
        } else {
            self.record_proof_check_stats(0, summary);
        }

        if let Some(ref quality) = quality {
            tracing::debug!(
                %quality,
                complete = quality.is_complete(),
                "UNSAT proof quality"
            );
            if !quality.is_complete() {
                tracing::warn!(
                    trust = quality.trust_count,
                    hole = quality.hole_count,
                    total = quality.total_steps,
                    "UNSAT proof has unverified fallback steps"
                );
            }
            self.populate_proof_quality_stats(quality);
        }
        self.last_proof_quality = quality;
    }

    #[cfg(feature = "proof-checker")]
    pub(in crate::executor) fn run_internal_proof_check(&mut self, proof: &Proof) {
        // Strict mode (#4420): when enabled, reject trust and hole steps.
        // This gates on the SMT-LIB option `(set-option :check-proofs-strict true)`.
        if self.strict_proofs_enabled() {
            match self.check_proof_strict_with_datatypes(proof) {
                Ok(_quality) => {
                    let shape = Self::proof_shape_summary(proof);
                    self.proof_check_result = Some(PartialProofCheck {
                        checked_steps: shape.total_steps,
                        skipped_hole_steps: 0,
                        total_steps: shape.total_steps,
                    });
                    self.record_proof_check_stats(0, Self::proof_shape_summary(proof));
                }
                Err(error) => {
                    let shape = Self::proof_shape_summary(proof);
                    let checked = shape.checked_steps;
                    let skipped = shape.skipped_hole_steps;
                    let total = shape.total_steps;
                    self.proof_check_result = Some(shape.clone());
                    self.record_proof_check_stats(1, shape);
                    tracing::error!(
                        error = %error,
                        checked_steps = checked,
                        skipped_hole_steps = skipped,
                        total_steps = total,
                        "strict proof checker rejected UNSAT proof"
                    );
                }
            }
            return;
        }

        // #diagnostic-envelope: the proof-surgery callers reach this on
        // candidate proofs that can be as large as the published one, so the
        // walk runs under the caller's solve controls here too. Quality is not
        // measured on this path (it never was); a refusal is recorded as a
        // check failure, which is the fail-closed direction.
        let MeteredPartialCheck { summary, error, .. } =
            check_partial_with_executor_progress(self, proof, WantQuality::No);
        self.proof_check_result = Some(summary.clone());
        if let Some(error) = error {
            let shape = Self::proof_shape_summary(proof);
            let checked = shape.checked_steps;
            let skipped = shape.skipped_hole_steps;
            let total = shape.total_steps;
            self.record_proof_check_stats(1, shape);

            tracing::error!(
                error = %error,
                checked_steps = checked,
                skipped_hole_steps = skipped,
                total_steps = total,
                "internal proof checker rejected UNSAT proof"
            );
        } else {
            self.record_proof_check_stats(0, summary);
        }
    }

    #[cfg(feature = "proof-checker")]
    fn proof_shape_summary(proof: &Proof) -> PartialProofCheck {
        let total_steps = proof.steps.len() as u32;
        let skipped_hole_steps = proof
            .steps
            .iter()
            .filter(|step| {
                matches!(
                    step,
                    ProofStep::Step {
                        rule: AletheRule::Hole,
                        ..
                    }
                )
            })
            .count() as u32;

        PartialProofCheck {
            checked_steps: total_steps.saturating_sub(skipped_hole_steps),
            skipped_hole_steps,
            total_steps,
        }
    }

    #[cfg(feature = "proof-checker")]
    fn record_proof_check_stats(&mut self, failures: u64, summary: PartialProofCheck) {
        // Record whether the internal checker accepted the refutation with no
        // errors. `--self-check` consults this (plus hole-freeness) before it
        // will emit `unsat` rather than a sound `unknown`.
        self.proof_check_ok = failures == 0;
        self.last_statistics
            .set_int(PROOF_CHECKER_FAILURES_KEY, failures);
        self.last_statistics.set_int(
            PROOF_CHECKER_SKIPPED_HOLE_STEPS_KEY,
            u64::from(summary.skipped_hole_steps),
        );
        self.last_statistics.set_int(
            PROOF_CHECKER_CHECKED_STEPS_KEY,
            u64::from(summary.checked_steps),
        );
        self.last_statistics.set_int(
            PROOF_CHECKER_TOTAL_STEPS_KEY,
            u64::from(summary.total_steps),
        );
    }
}
