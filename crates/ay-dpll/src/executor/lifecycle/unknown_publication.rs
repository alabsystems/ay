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

    /// Publish `Unknown` for a decision query that ended in `error`, under
    /// the error's own reason ([`ExecutorError::unknown_reason`]).
    ///
    /// A refusal ([`ExecutorError::UnsupportedLogic`]: no combined decision
    /// procedure for the problem's theory mix) never searched, so its
    /// diagnostic is the refusal itself: phase `theory-combination`, and the
    /// error's text, which names the declared logic, as the detail. Without
    /// it the diagnostic fell back to `theory-search` / "solver returned
    /// Unknown", as if a search had run. Any other executor error publishes
    /// `InternalError` with the default diagnostic. The native API's recorder
    /// (`api/solving/check.rs::record_executor_failure_unknown`) and the CLI
    /// both publish an errored decision query through here, so one refusal
    /// reads the same on either surface.
    pub fn replace_last_result_with_executor_error(&mut self, error: &ExecutorError) {
        self.replace_last_result_with_unknown(error.unknown_reason());
        if matches!(error, ExecutorError::UnsupportedLogic(_)) {
            self.record_refusal_diagnostic(error);
        }
    }

    /// The phase of a refusal's diagnostic.
    const REFUSAL_PHASE: &'static str = "theory-combination";

    /// The statistics an `unknown`'s diagnostic is read from.
    const UNKNOWN_DIAGNOSTIC_KEYS: [&'static str; 4] = [
        "unknown.reason",
        "unknown.phase",
        "unknown.cost_center",
        "unknown.detail",
    ];

    /// A refusal's diagnostic: phase `theory-combination`, and the refusal's
    /// text, which names the declared logic, as the detail.
    fn record_refusal_diagnostic(&mut self, refusal: &ExecutorError) {
        self.last_statistics
            .set_string("unknown.phase", Self::REFUSAL_PHASE);
        self.last_statistics
            .set_string("unknown.detail", refusal.to_string());
    }

    /// Take the router's refusal diagnostic out of the statistics while the
    /// partition rescue searches the components of the refused mix; `None`
    /// when the last diagnostic is not the refusal.
    ///
    /// The refusal describes an `unknown` no lane searched. A firing rescue
    /// searches, so the refusal describes its solve only when the rescue ends
    /// by restoring the refusal's own `unknown`
    /// ([`Self::restore_refusal_diagnostic`]). A definite verdict needs none,
    /// and a component's deadline or budget stop publishes its own.
    pub(in crate::executor) fn hold_refusal_diagnostic(
        &mut self,
    ) -> Option<[Option<crate::executor_types::StatValue>; 4]> {
        if self.last_statistics.get_string("unknown.phase") != Some(Self::REFUSAL_PHASE) {
            return None;
        }
        Some(Self::UNKNOWN_DIAGNOSTIC_KEYS.map(|key| self.last_statistics.extra.remove(key)))
    }

    /// Put a held refusal diagnostic back exactly as it was held, over
    /// whatever the rescue's components recorded.
    pub(in crate::executor) fn restore_refusal_diagnostic(
        &mut self,
        held: Option<[Option<crate::executor_types::StatValue>; 4]>,
    ) {
        let Some(values) = held else {
            return;
        };
        for (key, value) in Self::UNKNOWN_DIAGNOSTIC_KEYS.into_iter().zip(values) {
            match value {
                Some(value) => {
                    self.last_statistics.extra.insert(key.to_string(), value);
                }
                None => {
                    self.last_statistics.extra.remove(key);
                }
            }
        }
    }

    /// The `LogicCategory::Other` arm of `check-sat` and `check-sat-assuming`:
    /// no combined decision procedure for this theory mix. Since 550b6b40e the
    /// arm answers the standard `unknown` (`Incomplete`) instead of an
    /// `UnsupportedLogic` error, which also lets the symbol-disjoint partition
    /// rescue decide a mix whose components each have a lane. The refusal
    /// stays the diagnostic of an `unknown` nothing else decides: without it
    /// the diagnostic fell back to the active phase and "solver returned
    /// Unknown", as if a search had run.
    pub(in crate::executor) fn refuse_theory_mix_without_a_lane(&mut self) -> SolveResult {
        self.last_unknown_reason = Some(UnknownReason::Incomplete);
        let refusal = ExecutorError::UnsupportedLogic(
            self.ctx.logic().unwrap_or("<unspecified>").to_string(),
        );
        self.record_refusal_diagnostic(&refusal);
        SolveResult::Unknown
    }

    /// Classify a provisional internal Unknown through the typed origin
    /// registry. The public solve boundary subsequently calls
    /// [`Self::finalize_unknown_publication`] to revoke artifacts and publish
    /// the result. Production origin sites use this instead of independently
    /// pairing a reason with a code string.
    pub(crate) fn record_unknown_from_origin(&mut self, origin: UnknownOrigin) {
        // DIAGNOSTIC ONLY, and the sibling of the `CERT/unknown-record` line in
        // `check_sat.rs`: the typed origin is the stable evidence code, so this
        // says WHICH chokepoint stopped, in order, where the statistics block
        // keeps only the last. No verdict path reads it.
        if ay_core::misc_cli_flags().debug_cert {
            ay_core::safe_eprintln!("CERT/unknown-origin {}", origin.code());
        }
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
