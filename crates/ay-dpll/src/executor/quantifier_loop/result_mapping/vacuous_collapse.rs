// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authority policy and diagnostics for vacuous quantified collapses.

use ay_core::TermId;

use super::Executor;

impl Executor {
    pub(super) fn note_cegqi_inner_unsat_artifact_clear(&self) {
        if ay_core::misc_cli_flags().debug_cert && self.last_checked_sat_refutation.is_some() {
            eprintln!(
                "CERT/sidecar cleared by clear_cegqi_inner_unsat_artifacts exec={:p}",
                std::ptr::from_ref(self)
            );
        }
    }

    /// Whether a certified vacuous collapse still needs the conservative
    /// incomplete-translation marker.
    ///
    /// A collapse to literal `true` contributes no premise: no proof can cite
    /// it, no refutation depends on it, and dropping it changes no model. It is
    /// therefore exempt independently of the staged broad narrowing, which
    /// also exempts real premises such as `(> b 0)` and still owes the strict
    /// proof gate. This narrow exemption cannot grant SAT because a `true`
    /// conjunct constrains no model (#sat-grants-are-staged).
    ///
    /// This matters for deductive-checks's degenerate seq-equality axiom
    /// `(forall ((idx (_ BitVec 64))) true)`: retaining the marker demanded a
    /// strict proof, downgraded the valid BV refutation to quantifier-unknown,
    /// and prevented deferred-trust discharge of a theorem AY had proved.
    pub(super) fn vacuous_collapse_requires_translation_marker(&self, simplified: TermId) -> bool {
        simplified != self.ctx.terms.true_term()
            && !crate::quant_unit_authority::vacuous_marker_narrowing_enabled()
    }
}
