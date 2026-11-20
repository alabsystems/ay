// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Final checking, measurement, and publication for reconstructed UNSAT proofs.

use ay_core::Proof;

use super::super::Executor;

impl Executor {
    pub(super) fn finalize_unsat_proof(&mut self, mut proof: Proof) {
        // Proof validation (#4393): validates all non-Hole steps via partial
        // checker. Replaces the old check_proof + Hole-skip pattern that skipped
        // entire proofs when ANY Hole step was present.
        // #diagnostic-envelope: ONE metered, cancellable walk that serves both
        // the self-check bookkeeping and the ProofQuality measurement. See
        // `Executor::run_internal_proof_check_and_measure`.
        self.run_internal_proof_check_and_measure(&proof);

        // Postcondition contracts (#4642): proof built successfully.
        debug_assert!(
            !proof.steps.is_empty(),
            "BUG: build_unsat_proof produced an empty proof"
        );
        debug_assert!(
            Self::proof_derives_empty_clause(&proof),
            "BUG: build_unsat_proof produced a proof that does not derive the empty clause"
        );
        debug_assert!(
            self.proof_check_result.is_some(),
            "BUG: build_unsat_proof did not run internal proof checker"
        );

        self.promote_final_collection_axioms(&mut proof);
        self.last_proof = Some(proof);
    }
}
