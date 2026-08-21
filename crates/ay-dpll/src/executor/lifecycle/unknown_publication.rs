// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Canonical fail-closed publication of `Unknown` results.

impl Executor {
    /// Close every decision-trace writer retained by an incremental SAT lane.
    ///
    /// Persistent solvers keep their buffered writer across `check-sat` calls.
    /// A CLI-level fail-closed result must detach those file descriptors before
    /// removing the now-non-authoritative trace; reopening or truncating the
    /// path while an old writer remains live can corrupt or re-expose it.
    fn detach_persistent_decision_trace_writers(&mut self) {
        if let Some(state) = self.incr_bv_state.as_mut() {
            if let Some(sat) = state.persistent_sat.as_mut() {
                sat.disable_decision_trace();
            }
        }
        if let Some(state) = self.incr_theory_state.as_mut() {
            if let Some(sat) = state.persistent_sat.as_mut() {
                sat.disable_decision_trace();
            }
            if let Some(sat) = state.lia_persistent_sat.as_mut() {
                sat.disable_decision_trace();
            }
        }
        if ay_core::trace_config().decision_trace_path.is_some() {
            // Once a public/raw mismatch occurs, a later partial trace cannot
            // replay the full session honestly. Leave tracing disabled for the
            // rest of this process instead of silently starting a forged stream.
            ay_sat::suppress_decision_trace_after_public_mismatch();
        }
    }

    /// Publish `Unknown` from an authoritative production origin and revoke
    /// every artifact belonging to an older or partially completed decision.
    ///
    /// CLI preflight rejection and panic containment can decide to fail closed
    /// without receiving a normal `Unknown` from the solver. This canonical
    /// transition prevents subsequent model/proof/core queries from observing
    /// a stale result. Decision tracing is also detached and permanently
    /// suppressed when configured, because replay would reproduce the solver's
    /// raw result rather than the external boundary's synthesized result.
    pub(crate) fn publish_unknown_from_origin(&mut self, origin: UnknownOrigin) {
        self.detach_persistent_decision_trace_writers();
        self.invalidate_last_check_result();
        self.last_result = Some(SolveResult::Unknown);
        self.last_unknown_reason = Some(origin.reason());
        self.last_unknown_origin = Some(origin);
    }

    /// Compatibility entrypoint for existing external fail-closed callers.
    ///
    /// The reason is immediately converted to its unique registered origin;
    /// callers cannot create a mismatched reason/origin pair.
    pub fn replace_last_result_with_unknown(&mut self, reason: UnknownReason) {
        self.publish_unknown_from_origin(reason.origin());
    }

    /// Classify a provisional internal Unknown through the typed origin
    /// registry. The public solve boundary subsequently calls
    /// [`Self::finalize_unknown_publication`] to revoke artifacts and publish
    /// the result. Production origin sites use this instead of independently
    /// pairing a reason with a code string.
    pub(crate) fn record_unknown_from_origin(&mut self, origin: UnknownOrigin) {
        self.last_unknown_reason = Some(origin.reason());
        self.last_unknown_origin = Some(origin);
    }

    /// Inject an exact registered production origin for the authenticated
    /// conformance executable's negative/coverage campaign.
    ///
    /// This is not a solver option and ordinary solving never calls it. The
    /// hidden probe reports the injection honestly and pairs it with the
    /// audited production chokepoint from [`UnknownOrigin::production_chokepoint`].
    #[doc(hidden)]
    pub fn conformance_inject_unknown_origin(&mut self, origin: UnknownOrigin) {
        self.record_unknown_from_origin(origin);
        let _ = self.finalize_unknown_publication(SolveResult::Unknown);
    }

    /// Publish and fully revoke an external stop observed at a result boundary.
    ///
    /// This is shared by definite-token admission and the interruptible
    /// transaction's error path. An executor error does not authorize any
    /// verdict, but a concurrently fired caller stop still owns the public
    /// Unknown classification and must be recorded before local controls are
    /// restored.
    pub(crate) fn finalize_external_stop_for_publication(&mut self) -> Option<SolveResult> {
        if !self.should_abort_theory_loop() {
            return None;
        }
        if !self.is_producing_proofs() {
            self.proof_tracker.disable();
        }
        Some(self.finalize_unknown_publication(SolveResult::Unknown))
    }

    /// Revoke a provisional definite verdict when a live external solve
    /// control has fired before its publication capability is consumed.
    ///
    /// SAT and UNSAT use different certification funnels, but their final
    /// native/text consumers share this last admission rule. Keeping it on the
    /// executor preserves the typed interrupt/deadline/memory origin and routes
    /// every rejection through the canonical artifact-revoking Unknown state.
    pub(crate) fn decline_definite_publication_on_external_stop(
        &mut self,
        proposed: SolveResult,
    ) -> SolveResult {
        if proposed.is_unknown() {
            return proposed;
        }
        self.finalize_external_stop_for_publication()
            .unwrap_or(proposed)
    }

    /// Apply the mandatory public Unknown boundary to a provisional result.
    ///
    /// This is intentionally idempotent. Every public solve route calls it
    /// after the internal lane chooses a result, so direct internal writes to
    /// `last_unknown_reason` cannot bypass result-artifact revocation.
    pub(crate) fn finalize_unknown_publication(&mut self, proposed: SolveResult) -> SolveResult {
        if proposed.is_unknown() {
            let reason = self.last_unknown_reason.unwrap_or(UnknownReason::Unknown);
            self.publish_unknown_from_origin(reason.origin());
            SolveResult::Unknown
        } else {
            self.last_unknown_origin = None;
            proposed
        }
    }
}
