// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The presentation gate of the implied-universal lane
//! (#iff-split-implied-authority).
//!
//! The lane installs its certificate from the artifact firewall
//! (`translated_unsat_proof_or_downgrade`), AFTER the ordinary assembly's
//! presentation passes ran for a different proof. Nothing re-spelled the
//! installed proof's `assume`s, so the exported document printed whatever the
//! earlier override table held — on the w1_51 files 13, 49, 92 and 121 AY's
//! own normalised assertion (`(< (- 2) X)` for `(> X (- 2))`, `v_5` for `v`,
//! `(+ e 0)` folded), which pinned carcara 1.1.0 refuses at the first
//! `assume` ("could not match term to any of the original problem
//! premises"). The verdict was still admitted as `strict-proof`, the one
//! class in the corpus that combined that label with `foreign_assumes=yes`.
//!
//! So, as the QSAT route's evidence gate does (`qsat_route/evidence.rs`), the
//! lane publishes only with the document a consumer receives:
//!
//! 1. the installed proof gets the presentation every installer that replaces
//!    `last_proof` owes it (`restore_reachable_authored_assume_surface_overrides`:
//!    each reachable authored root, the universal under an authored `(= A F)`
//!    with its body, and every `forall_inst` instance re-spelled from the
//!    problem text);
//! 2. that document must render, and every premise `assume` in it must be an
//!    assertion of the input as written;
//! 3. under `--self-check` or strict rigor (`--strict-proofs`,
//!    `:check-proofs-strict`) it must also carry no unproved step, so a
//!    `--self-check` `unsat` from this lane is never published beside
//!    `ay_self_checkable=no`.
//!
//! A refusal restores every byte of proof state the attempt changed, and the
//! firewall answers `unknown` exactly as before the lane existed. That is the
//! outcome today for an authored `(=> A F)`: the restoration pass gives no
//! spelling to a root whose authored head differs from its canonical one
//! (`or`), so its certificate would assume `(or F' (not A))`. A session
//! that produces no document by request (the shed posture, or no retained
//! authored text and no artifact owed) keeps the internal strict admission.
//! Nothing here grants authority; it only declines.

use super::*;
use crate::normalize_premise_surface;

impl Executor {
    /// Why the certificate the lane just installed cannot back a published
    /// `unsat`, or `None` when it can. See the module documentation.
    pub(super) fn implied_lane_presentation_refusal(&mut self) -> Option<&'static str> {
        let demanded = self.checked_certificate_demanded();
        // No document is produced by request: the shed posture, a session
        // producing no proof at all (a library caller that never asked for
        // one), or one that retains no authored text and owes no artifact
        // (the retention-off rule
        // `restore_reachable_authored_assume_surface_overrides` applies). The
        // internal strict admission stands, as for every lane. MEASURED: a
        // gate that demanded a document here withheld the plain-`Executor`
        // verdict of `unsat_verus_zero_divisor_after_int_const_subst_twin`.
        if !demanded
            && (self.competition_shedding_active()
                || !self.is_producing_proofs()
                || !self.ctx.retains_parsed_assertions())
        {
            return None;
        }
        // `--self-check` and strict rigor publish `unsat` only on a document
        // with no unproved step; a bare `--proof FILE` takes the document as
        // it renders, holes disclosed.
        let hole_free_demanded = self.self_check() || !self.accepts_discharged_trust_grant();
        let proof = self.last_proof.clone()?;
        self.restore_reachable_authored_assume_surface_overrides(&proof);
        let mut scan = ay_proof::AletheDocumentScan::default();
        match self.try_export_installed_proof_alethe_to(&mut scan) {
            None => return Some("has no document"),
            Some(Err(error)) => {
                tracing::debug!(
                    target: "ay::cert::implied_forall_inst",
                    %error,
                    "presentation: render refused"
                );
                return Some("does not render");
            }
            Some(Ok(())) => {}
        }
        if scan.overflowed {
            return Some("has premises that could not be judged");
        }
        let Some(authored) = self.authored_premise_surfaces() else {
            return Some("has premises that could not be judged");
        };
        if scan
            .premise_assumes
            .iter()
            .any(|assume| !authored.contains(&normalize_premise_surface(assume)))
            || self.unsat_proof_terminal_foreign_assume()
        {
            return Some("assumes a premise the input does not state");
        }
        if hole_free_demanded && scan.unproved > 0 {
            return Some("carries an unproved step a demanded certificate refuses");
        }
        None
    }
}
