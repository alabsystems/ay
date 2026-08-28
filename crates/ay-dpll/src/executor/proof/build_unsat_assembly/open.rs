// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Admission and short-circuit gates for a fresh UNSAT proof build.

use super::*;

impl Executor {
    /// Retires the stale checked-SAT sidecar and applies every short-circuit guard
    /// that can settle this query before any proof is assembled.
    ///
    /// Assumes it runs exactly once at the head of `build_unsat_proof`, before the
    /// clause trace is consumed. Returns [`AssemblyGate::Stop`] at each point the
    /// original code returned early — the caller must then return without seeding a
    /// proof, because this method has already published the query's proof state.
    pub(super) fn open_unsat_proof_assembly(&mut self) -> AssemblyGate {
        // A checked SAT sidecar authorizes one immutable trace/mapping/query bundle.
        // Retire any prior candidate before inspecting it, including on suppressed exits.
        //
        // ...but ONLY when there IS a current bundle to inspect
        // (#checked-sat-sidecar-second-call). This method is NOT idempotent: it `take()`s
        // `last_clause_trace`, `last_var_to_term`, and `last_negations`, so a second call on the same
        // query arrives with the trace already consumed. Retiring
        // unconditionally then destroyed the sidecar the FIRST call had
        // correctly minted and could not re-mint it, and the certification
        // funnel fell through to the Alethe presentation, which on the DT
        // lanes is a `Generic` trust stub that strict mode rejects. Measured on
        // QF_DT `vlsat3_b83`: "no SAT clause trace is available" printed TWICE,
        // and a correct `unsat` published as `unknown`.
        //
        // Keeping it is not weaker. The sidecar carries its own authority and
        // is checked at USE by `is_current_for` against the query epoch, the
        // frontend source stamp, the ordered roots and the ordered assumption
        // slice, so a sidecar that no longer denotes this query is rejected
        // there regardless of what happens here.
        if self.last_clause_trace.is_some() {
            self.last_checked_sat_refutation = None;
        }
        if self.last_unsat_proof_reconstruction_suppressed {
            self.clear_finite_enum_proof_state();
            return AssemblyGate::Stop;
        }
        // `build_unsat_proof` consumes its generic SAT trace, so callers may
        // invoke it twice for one query. Preserve an already checked bounded
        // proof only when the sealed capability still authenticates the exact
        // stored canonical proof.
        if self.current_checked_finite_enum_proof().is_some() {
            return AssemblyGate::Stop;
        }
        self.last_checked_finite_enum_pigeonhole = None;
        // The sealed path is an exception only to the existing oversized-
        // source poison. Bounded queries retain the ordinary reconstruction
        // path (including its broader accepted finite-enum source shapes).
        if let Some(mechanism) = self.proof_source_decline() {
            if self.last_finite_enum_pigeonhole.is_some()
                && self.try_install_bounded_finite_enum_pigeonhole_proof()
            {
                return AssemblyGate::Stop;
            }
            // SURFACE THE SILENT DECLINE. Both exits below stop the funnel
            // before it ever runs, so `--probe-cert-reject` printed NEITHER a
            // mint nor a decline and the run was indistinguishable from one
            // that never had a refutation to certify. Measured on a stratified
            // 987-file corpus census: 62 of 517 UNSATs (12.0%) end here,
            // silently -- the third-largest certification outcome after
            // minted and declined, and the only one with no diagnostic at all.
            // The mechanism was already computed and stored in
            // `last_proof_decline`; it simply had no stdout surface.
            crate::executor::unsat_cert::probe_cert_reject(|| {
                format!("assembly gate STOPPED before certification: {mechanism:?}")
            });
            self.install_uncertifiable_proof_poison(mechanism);
            return AssemblyGate::Stop;
        }
        if self.last_clause_trace.is_some() {
            self.refresh_checked_sat_refutation();
        } else {
            // The other silent exit: no clause trace, so the checked-refutation
            // builder is never even consulted.
            crate::executor::unsat_cert::probe_cert_reject(|| {
                "assembly gate PROCEEDED without certification: no SAT clause trace \
                 is recorded, so the checked-refutation builder never runs"
                    .to_string()
            });
        }
        AssemblyGate::Proceed
    }
}
