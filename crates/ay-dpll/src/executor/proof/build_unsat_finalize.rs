// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Final checking, measurement, and publication for reconstructed UNSAT proofs.

use ay_core::Proof;
#[cfg(not(feature = "proof-checker"))]
use ay_proof::{check_proof_partial, PartialProofCheck};

use super::super::Executor;

impl Executor {
    pub(super) fn finalize_unsat_proof(&mut self, mut proof: Proof) {
        // Proof validation (#4393): validates all non-Hole steps via partial
        // checker. Replaces the old check_proof + Hole-skip pattern that skipped
        // entire proofs when ANY Hole step was present.
        // #diagnostic-envelope: ONE metered, cancellable walk that serves both
        // the self-check bookkeeping and the ProofQuality measurement. See
        // `Executor::run_internal_proof_check_and_measure`.
        #[cfg(feature = "proof-checker")]
        self.run_internal_proof_check_and_measure(&proof);
        #[cfg(not(feature = "proof-checker"))]
        {
            if self.strict_proofs_enabled() {
                // Strict mode without proof-checker feature: use the strict
                // checker with datatype-distinctness validation (#8419).
                match self.check_proof_strict_with_datatypes(&proof) {
                    Ok(_quality) => {
                        let total = proof.steps.len() as u32;
                        self.proof_check_result = Some(PartialProofCheck {
                            checked_steps: total,
                            skipped_hole_steps: 0,
                            total_steps: total,
                        });
                    }
                    Err(e) => {
                        let total = proof.steps.len() as u32;
                        self.proof_check_result = Some(PartialProofCheck {
                            checked_steps: total,
                            skipped_hole_steps: 0,
                            total_steps: total,
                        });
                        tracing::error!(
                            error = %e,
                            total_steps = total,
                            "strict proof checker rejected UNSAT proof"
                        );
                    }
                }
            } else {
                let (partial, error) = check_proof_partial(&proof, &self.ctx.terms);
                self.proof_check_result = Some(partial.clone());
                if let Some(ref e) = error {
                    tracing::error!(
                        error = %e,
                        result = %partial,
                        "internal proof checker rejected UNSAT proof"
                    );
                }
            }
        }

        // Proof quality metrics (#4176, #4420). Under `proof-checker` (the
        // default) this was measured by the fused walk above; without the
        // feature the legacy separate measurement stands.
        #[cfg(not(feature = "proof-checker"))]
        {
            let quality = self.validate_and_measure_proof(&proof);
            if let Some(ref q) = quality {
                self.populate_proof_quality_stats(q);
            }
            self.last_proof_quality = quality;
        }

        // Postcondition contracts (#4642): proof built successfully.
        debug_assert!(
            !proof.steps.is_empty(),
            "BUG: build_unsat_proof produced an empty proof"
        );
        debug_assert!(
            Self::proof_derives_empty_clause(&proof),
            "BUG: build_unsat_proof produced a proof that does not derive the empty clause"
        );
        #[cfg(feature = "proof-checker")]
        debug_assert!(
            self.proof_check_result.is_some(),
            "BUG: build_unsat_proof did not run internal proof checker"
        );

        self.promote_final_collection_axioms(&mut proof);
        self.last_proof = Some(proof);
    }
}
