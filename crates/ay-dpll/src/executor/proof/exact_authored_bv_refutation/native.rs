// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Early proof construction over frozen native roots, without authored SMT syntax.

use super::*;

mod grammar;

#[cfg(test)]
mod tests;

impl Executor {
    /// Re-prove native roots after named-core solving restores their public
    /// scope. A nested proof can be internally checked yet have no presentation
    /// over the outer authored roots, or retain an incomplete Trust step without
    /// setting the presentation-suppressed bit. Never publish it by relabelling
    /// assumptions. Offer the same exact-root producer instead.
    pub(in crate::executor) fn refresh_authenticated_native_bv_refutation_after_named_core_redirect(
        &mut self,
    ) {
        if self.skips_trust_elimination_repairs() {
            return;
        }
        let Some(proof) = self.last_proof.take() else {
            return;
        };
        if !self.last_unsat_proof_reconstruction_suppressed
            && self
                .check_proof_strict_with_datatypes(&proof)
                .is_ok_and(|quality| quality.is_complete())
            && self.candidate_authored_surface_is_available(&proof)
        {
            self.last_proof = Some(proof);
            return;
        }
        // Park the withheld proof without copying its potentially large DAG.
        // This scratch document is never published: the producer must build
        // and strictly validate a complete refutation of the original roots.
        let mut candidate = Proof::new();
        let replaced = self.try_authenticated_native_bv_refutation(&mut candidate);
        if replaced && self.candidate_authored_surface_is_available(&candidate) {
            if let Ok(quality) = self.check_proof_strict_with_datatypes(&candidate) {
                if quality.is_complete() {
                    self.commit_authenticated_plain_refutation(candidate, quality);
                    return;
                }
            }
        }
        self.last_proof = Some(proof);
    }

    /// Offer the native query once before unrelated authored repairs. This is
    /// only scheduling: the existing exact theorem producer and strict checker
    /// must still independently prove every step under the original controls.
    pub(in crate::executor::proof) fn try_authenticated_native_bv_refutation(
        &mut self,
        proof: &mut Proof,
    ) -> bool {
        let control = control::Continuation::capture(self);
        let _scope = control.enter();
        let candidate = if self.native_bv_source_kind(&|| control.stopped())
            == Some(NativeAssertionSurfaces::Native)
        {
            self.authenticated_native_bv_candidate(proof, &control)
                .filter(|(scope, _)| {
                    NativeBvRefutationScope::capture(self)
                        .is_some_and(|current| current.matches(scope))
                        && self.native_bv_source_kind(&|| control.stopped())
                            == Some(NativeAssertionSurfaces::Native)
                })
        } else {
            None
        };
        let stopped = control.stopped();
        if let Some(reason) = control.reason() {
            self.note_certification_stop(reason);
        }
        if stopped {
            return false;
        }
        let Some((_, candidate)) = candidate else {
            return false;
        };
        // Appended proof terms preserve all root entry identities. The
        // bookend above reauthenticates the entire same public scope. Neither
        // generated nor raw re-interned premises are admitted here.
        *proof = candidate;
        true
    }

    /// Metadata only: the epoch getter below remains the sole premise source.
    pub(super) fn native_bv_source_kind(
        &self,
        stop: &dyn Fn() -> bool,
    ) -> Option<NativeAssertionSurfaces> {
        // Source routing can encounter a genuine row beyond the native cap.
        // Debit every visit before it runs, using the SAME query envelope.
        let kind = self.ctx.native_assertion_surfaces_for(
            self.proof_original_problem_assertions_slice(),
            64,
            &mut |work| !stop() && self.proof_source_work.spend_canonical_scan_work(work),
        )?;
        (!stop()).then_some(kind)
    }

    fn authenticated_native_bv_candidate(
        &mut self,
        incumbent: &Proof,
        control: &control::Continuation,
    ) -> Option<(NativeBvRefutationScope, Proof)> {
        if control.stopped() {
            return None;
        }
        let scope = NativeBvRefutationScope::capture(self)?;
        if self
            .evaluation_attempt()
            .native_bv_refutation_attempted(&scope)
            || !grammar::accepts(self, scope.roots(), &|| control.stopped())
            || (!self.last_unsat_proof_reconstruction_suppressed
                && self
                    .check_proof_strict_with_datatypes(incumbent)
                    .is_ok_and(|quality| quality.is_complete()))
            || control.stopped()
            || !self
                .evaluation_attempt()
                .begin_native_bv_refutation(scope.clone())
        {
            return None;
        }
        crate::executor::unsat_cert::probe_cert_reject(|| {
            format!(
                "native authored BV: producer offer roots={}",
                scope.roots().len()
            )
        });
        let candidate =
            self.exact_bv_candidate_with_control(scope.roots(), |_, _| true, control)?;
        // The shared producer validates all reachable Assume leaves against
        // these exact roots, requires strict COMPLETE and derives empty. The
        // final mandatory publication and presentation gates remain unchanged.
        Some((scope, candidate))
    }
}
