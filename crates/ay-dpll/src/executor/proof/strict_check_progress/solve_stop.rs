// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The strict checker's two plain entry points, reached under this solve's
//! stop signals.
//!
//! Proof repair asks `ay_proof::check_proof_strict` and
//! `ay_proof::recognize_bv_bitblast` whether a candidate holds, many times per
//! solve. Both ran with an unconditional `|_, _| true` progress, so neither
//! the solve deadline nor an interrupt reached the checker's poll — including
//! the proof-producing BV fallback, whose counted exhaustion takes seconds.
//! These are the same checker, the same (empty) context and the same verdicts;
//! the one difference is that an asserted interrupt, solve deadline or memory
//! limit now ends the check as a failure (`ResourceLimit`, or "not
//! recognized"), which every caller already reads as "do not adopt". No work
//! budget is added: the metered envelope stays with the gates that had it.

use ay_core::{Proof, TermId};
use ay_proof::{ProofCheckError, ProofQuality};

use super::poll::strided_memory_poll;
use crate::executor::Executor;

impl Executor {
    /// `ay_proof::check_proof_strict(proof, &self.ctx.terms)`, stopped by this
    /// solve's interrupt, deadline or memory limit.
    pub(in crate::executor) fn check_proof_strict_until_stopped(
        &self,
        proof: &Proof,
    ) -> Result<ProofQuality, ProofCheckError> {
        let should_stop = self.make_strict_check_stop();
        let stopped = strided_memory_poll(&should_stop, self.memory_limit());
        ay_proof::check_proof_strict_with_context_and_progress(
            proof,
            &self.ctx.terms,
            None,
            None,
            None,
            &mut |_, _| !stopped.poll(),
        )
    }

    /// `ay_proof::recognize_bv_bitblast(&self.ctx.terms, clause)`, stopped by
    /// this solve's interrupt, deadline or memory limit (a stop reads as "not
    /// recognized").
    ///
    /// Every caller is a capability probe inside proof assembly: "yes" lets
    /// it install a candidate lemma (always re-validated by the full strict
    /// checker before anything publishes); "no" declines that one repair.
    /// In the synthesized-default best-effort posture (a reconstruction step
    /// budget is set and no proof artifact is required) the probe therefore
    /// runs under the reduced speculative counted envelope
    /// (`ay_proof::recognize_bv_bitblast_speculative_with_progress`): a
    /// doomed whole-problem candidate otherwise pays the full strict
    /// exhaustion (measured 35.6 s on QF_BV Mulh_u32.0005) for a certificate
    /// the corroboration fallback replaces anyway. Explicit proof requests
    /// and mandatory collection keep the strict envelope, so what can be
    /// certified there is unchanged.
    pub(in crate::executor) fn recognize_bv_bitblast_until_stopped(
        &self,
        clause: &[TermId],
    ) -> bool {
        let should_stop = self.make_strict_check_stop();
        let stopped = strided_memory_poll(&should_stop, self.memory_limit());
        if self.proof_reconstruction_step_budget.is_some() && !self.proof_artifact_required {
            ay_proof::recognize_bv_bitblast_speculative_with_progress(
                &self.ctx.terms,
                clause,
                &mut |_, _| !stopped.poll(),
            )
        } else {
            ay_proof::recognize_bv_bitblast_with_progress(&self.ctx.terms, clause, &mut |_, _| {
                !stopped.poll()
            })
        }
    }
}
