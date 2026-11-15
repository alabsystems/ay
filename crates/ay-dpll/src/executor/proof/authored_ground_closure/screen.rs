// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The wire screen: judge the document the exporter will PUBLISH.
//!
//! The lane commits inside the replacement cascade, but the published bytes
//! are decided later, by the two presentation passes that close
//! `build_unsat_assembly`: `rehome_elaborated_conjunction_assumes` swaps an
//! assumed elaborated conjunction for its raw authored spelling, and
//! `restore_reachable_authored_assume_surface_overrides` re-spells every
//! reachable authored `assume` (and each `forall_inst` under an authored
//! universal) from the problem text. A screen that exported the committed
//! state alone judged spellings that never ship. Measured on
//! `(assert (forall ((i (_ BitVec 8))) (=> (bvsge i #x30) (= (select data i) #x07))))`
//! with a constant-array pin at `#x30`: the elaborated body is
//! `(or (not (bvsle #x30 i)) ..)`, the screen saw a clean document, the
//! restore pass re-spelled the instance as the authored `(=> (bvsge ..) ..)`,
//! and the clausifying `or` step shipped as `hole` (`unknown` became a
//! `holey` `unsat`). A record query written as a nested `and`, or with a
//! `(not (distinct ..))` conjunct, was refused at export instead (`and_pos
//! indexed conjunct is absent from its effective source`).
//!
//! [`Executor::presents_wire_clean`] therefore runs both passes on a CLONE
//! of the committed proof, exports what they leave, and restores every
//! executor field they write (the override table, both premise ledgers, the
//! suppression latch and the decline census). A pass that suppresses the
//! reconstruction is a refusal too: the real pass would drop the Alethe
//! surface. Suppression also clears the finite-enum sidecar, which cannot be
//! cloned, so a query holding one is declined outright (completeness only).
//! What the screen still does not re-run: the derivation passes between the
//! cascade and the presentation (`derive_*`, `demote_*`), which rewrite only
//! leaves the exporter could not spell, and a candidate that reached this
//! screen spells every leaf.

use super::*;

impl Executor {
    /// Whether the document the exporter will publish for the committed
    /// `proof` has no `hole` or `trust` step and renders at all; see the
    /// module documentation. Leaves every executor field it touches as it
    /// found it. The unrewritten authored replay screens its candidate here
    /// too: it also installs a proof after the assembly's presentation passes
    /// ran.
    pub(in crate::executor::proof) fn presents_wire_clean(&mut self, proof: &Proof) -> bool {
        // Both sidecar fields are `None` from here on: the passes can only
        // clear them, so there is nothing of theirs to restore.
        if self.last_finite_enum_pigeonhole.is_some()
            || self.last_checked_finite_enum_pigeonhole.is_some()
        {
            return false;
        }
        let saved_overrides = self.last_proof_term_overrides.clone();
        let saved_rebuild = self.last_proof_rebuild_originals.clone();
        let saved_raw = self.last_proof_raw_original_assertions.clone();
        let saved_suppressed = self.last_unsat_proof_reconstruction_suppressed;
        let saved_decline = self.last_proof_decline;
        let mut presented = proof.clone();
        self.rehome_elaborated_conjunction_assumes(&mut presented);
        self.restore_reachable_authored_assume_surface_overrides(&presented);
        let kept_surface = saved_suppressed || !self.last_unsat_proof_reconstruction_suppressed;
        let clean = kept_surface && self.renders_wire_clean(&presented);
        self.last_proof_term_overrides = saved_overrides;
        self.last_proof_rebuild_originals = saved_rebuild;
        self.last_proof_raw_original_assertions = saved_raw;
        self.last_unsat_proof_reconstruction_suppressed = saved_suppressed;
        self.last_proof_decline = saved_decline;
        clean
    }

    /// Whether the `(get-proof)` exporter renders `proof` with no `hole` or
    /// `trust` step under the executor's CURRENT state: the same scope,
    /// override table, authored surfaces and emission budget, so the screen
    /// judges the artifact's own bytes. The conservative
    /// `proof_has_known_wire_gap` cannot stand in for it here: it reads a
    /// read-over-write lemma by its kind's non-Carcara rule name and does not
    /// see the printer's last-resort closed-guard lowering, so it flags
    /// documents the exporter spells with checked rules only. Asked from
    /// inside the solve, the render's complete bit-blast polls the solve's
    /// stop, and a lemma the decision's screen already declined is not
    /// lowered again; a stopped render is not clean.
    fn renders_wire_clean(&self, proof: &Proof) -> bool {
        let Some(scope) = self.proof_export_scope_assertions_for(proof) else {
            return false;
        };
        let overrides = self.proof_export_term_overrides();
        let surfaces = self.authored_export_surfaces();
        let stop = self.make_proof_assembly_should_stop();
        let solve = ay_proof::AskingSolve {
            stop: &stop,
            declines: self.wire_gap_screen_declines(),
        };
        self.in_alethe_dialect(|| {
            ay_proof::try_export_alethe_with_authored_surfaces_within_solve(
                proof,
                &self.ctx.terms,
                &scope,
                overrides.as_ref(),
                surfaces.channels(),
                Some(DEFAULT_ALETHE_EMISSION_WORK_BUDGET),
                solve,
            )
        })
        .is_ok_and(|document| !document.contains(":rule hole") && !document.contains(":rule trust"))
    }
}
