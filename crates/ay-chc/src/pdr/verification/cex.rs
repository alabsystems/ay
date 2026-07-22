// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counterexample verification for PDR solver.
//!
//! Contains methods for verifying that counterexamples are forward-reachable
//! from initial states, detecting spurious counterexamples.

use super::*;

impl PdrSolver {
    /// Verify that a counterexample is forward-reachable from initial states.
    ///
    /// REQUIRES: `self.problem` is the CHC problem the counterexample was generated for.
    /// ENSURES: If this returns `true`, `cex` is forward-reachable from init and is a sound
    ///   witness of unsafety. If it returns `false`, the counterexample is spurious or
    ///   verification could not be completed (conservatively treated as failure).
    ///
    /// This catches spurious counterexamples where backward exploration finds
    /// states that satisfy transition constraints but are not reachable from init.
    ///
    /// Returns `Valid` if verified, `Spurious` if proven spurious, `Unknown` if inconclusive.
    pub fn verify_counterexample(&mut self, cex: &Counterexample) -> CexVerificationResult {
        // Precondition: witness entries reference valid clause indices (#4757).
        if cfg!(debug_assertions) {
            if let Some(witness) = &cex.witness {
                let num_clauses = self.problem.clauses().len();
                for (i, entry) in witness.entries.iter().enumerate() {
                    if let Some(clause_idx) = entry.incoming_clause {
                        debug_assert!(
                            clause_idx < num_clauses,
                            "BUG: Witness entry {i} references clause {clause_idx} but problem has only {num_clauses} clauses",
                        );
                    }
                    let num_entries = witness.entries.len();
                    for &premise_idx in &entry.premises {
                        debug_assert!(
                            premise_idx < num_entries,
                            "BUG: Witness entry {i} has premise {premise_idx} but witness has only {num_entries} entries",
                        );
                    }
                }
            }
        }

        // Ground-derivation fast path. A `GroundDerivation` that validates
        // against THIS solver's clause list is a complete, decided proof that
        // `false` is derivable: every clause constraint evaluates to true and
        // every body-predicate argument tuple matches its premise's head, all
        // under totally concrete assignments. That is strictly stronger than
        // what the SMT arms below establish ("satisfiable with the instances
        // pinned"), and unlike them it cannot come back Unknown on a theory the
        // executor does not decide.
        //
        // No trust is transferred by the derivation merely being attached: it
        // is re-validated here against `self.problem`, so a transform-space or
        // stale derivation simply fails and falls through to the existing path.
        if let Some(derivation) = &cex.ground_derivation {
            match crate::ground_derivation::validate_ground_derivation(&self.problem, derivation) {
                Ok(()) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: counterexample carries a ground-validated derivation over these \
                             clauses ({} steps); accepting without SMT replay",
                            derivation.len()
                        );
                    }
                    return CexVerificationResult::Valid;
                }
                Err(err) => {
                    crate::ground_derivation::log_ground_translation_detail(format_args!(
                        "attached derivation does not validate against this problem: {err}"
                    ));
                }
            }
        }

        let Some(witness) = &cex.witness else {
            return self.verify_counterexample_without_witness(cex);
        };

        if witness.entries.is_empty() {
            return self.verify_counterexample_without_witness(cex);
        }

        let mut saw_unknown = false;
        if let Some(result) = self.verify_counterexample_witness_entries(witness, &mut saw_unknown)
        {
            return self.upgrade_unknown_via_replay(result, cex);
        }

        if let Some(result) = self.verify_counterexample_query_clause(witness, &mut saw_unknown) {
            return self.upgrade_unknown_via_replay(result, cex);
        }

        // Return Unknown if any SMT check was inconclusive, otherwise Valid
        if saw_unknown {
            self.upgrade_unknown_via_replay(CexVerificationResult::Unknown, cex)
        } else {
            CexVerificationResult::Valid
        }
    }

    /// Attempt the bounded-BMC replay when witness verification was
    /// INCONCLUSIVE (inc-9). Valid and Spurious results pass through
    /// untouched — the replay only ever upgrades Unknown, and only via its
    /// own complete verified derivation of false on this solver's clauses
    /// (the witness content is irrelevant to that certificate). Typical
    /// trigger: back-translated witnesses whose transform-space metadata no
    /// longer evaluates against the original clauses.
    fn upgrade_unknown_via_replay(
        &mut self,
        result: CexVerificationResult,
        cex: &Counterexample,
    ) -> CexVerificationResult {
        match result {
            CexVerificationResult::Unknown => self.replay_unencodable_counterexample(cex),
            other => other,
        }
    }

    /// Panic-safe wrapper around [`verify_counterexample`].
    ///
    /// If verification panics, the panic is caught and returned as an
    pub(in crate::pdr) fn verify_counterexample_without_witness(
        &mut self,
        cex: &Counterexample,
    ) -> CexVerificationResult {
        let Some((_pred, state_vars, init, transition, query)) = self.transition_system_encoding()
        else {
            // No transition-system encoding (any multi-predicate problem, and
            // single-predicate shapes the encoder rejects). "Cannot encode"
            // is NOT evidence of spuriousness — returning Spurious here
            // misclassified every witness-free multipred counterexample and
            // suppressed genuine refutations (inc-9 gate g2). Attempt a
            // bounded BMC replay against this solver's clauses instead: a
            // complete verified replay upgrades to Valid; every other outcome
            // is Unknown (fail closed). Never Spurious from this branch.
            return self.replay_unencodable_counterexample(cex);
        };

        let depth = cex.steps.len().saturating_sub(1);
        let reachability = Self::encode_transition_system_reachability(
            &state_vars,
            &init,
            &transition,
            &query,
            depth,
        );

        self.smt.reset();
        let timeout = VERIFY_INITIAL_TIMEOUT;
        let mut result = self.smt.check_sat_with_timeout(&reachability, timeout);
        if matches!(result, SmtResult::Unknown)
            && !Self::contains_mod_or_div(&reachability)
            && !reachability.contains_array_ops()
        {
            // Same policy as verify_model: retry hard-but-linear queries once.
            self.smt.reset();
            result = self
                .smt
                .check_sat_with_timeout(&reachability, VERIFY_RETRY_TIMEOUT);
        }

        match result {
            SmtResult::Sat(_) => array_sat_cross_check_result(
                &mut self.smt,
                &reachability,
                self.config.verbose,
                "witness-free reachability",
            )
            .unwrap_or(CexVerificationResult::Valid),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                CexVerificationResult::Spurious
            }
            SmtResult::Unknown => CexVerificationResult::Unknown,
        }
    }

    /// Bounded-BMC replay for counterexamples that could not be verified
    /// directly (inc-9; gates g1/g2): problems without a transition-system
    /// encoding, and witness replays that came back inconclusive.
    ///
    /// The engine counterexample is never trusted: only its depth (steps /
    /// witness length) seeds the replay bound.
    /// `BmcSolver::replay_confirm_unsafe_on_problem` accepts ONLY a complete
    /// verified derivation of false on `self.problem`'s clauses —
    /// reachability of false at bounded depth is itself the certificate, so
    /// no engine trace is needed.
    ///
    /// Fail-closed: budget exhaustion, unsupported shapes, missing witness,
    /// or replay-verification failure all return Unknown. A failed replay
    /// depth is memoized per solver instance so refinement loops (CEGAR-style
    /// callers) cannot repeatedly burn the replay budget on the same depth.
    fn replay_unencodable_counterexample(&mut self, cex: &Counterexample) -> CexVerificationResult {
        const REPLAY_BUDGET: std::time::Duration = std::time::Duration::from_secs(10);
        if self.config.disable_cex_replay {
            return CexVerificationResult::Unknown;
        }
        // Engines may understate the original-clause depth (preprocessing can
        // lengthen derivations); add slack — overshoot only costs budget,
        // which is capped below, and the BMC level encoding covers all
        // derivations ≤ its level.
        let witness_len = cex
            .witness
            .as_ref()
            .map_or(0, |witness| witness.entries.len());
        let depth_hint = cex.steps.len().max(witness_len).saturating_add(2);
        if self
            .failed_replay_depth
            .is_some_and(|failed| depth_hint <= failed)
        {
            return CexVerificationResult::Unknown;
        }
        let budget = self.cap_timeout(REPLAY_BUDGET);
        if budget < std::time::Duration::from_millis(250) {
            return CexVerificationResult::Unknown;
        }
        match crate::bmc::BmcSolver::replay_confirm_unsafe_on_problem(
            &self.problem,
            depth_hint,
            budget,
            self.config.cancellation_token.clone(),
            self.config.verbose,
        ) {
            Some(_verified) => {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: witness-free counterexample CONFIRMED by bounded BMC replay \
                         (depth hint {depth_hint})"
                    );
                }
                CexVerificationResult::Valid
            }
            None => {
                self.failed_replay_depth = Some(
                    self.failed_replay_depth
                        .map_or(depth_hint, |failed| failed.max(depth_hint)),
                );
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: witness-free counterexample replay inconclusive \
                         (depth hint {depth_hint}); returning Unknown"
                    );
                }
                CexVerificationResult::Unknown
            }
        }
    }

    /// Panic-safe variant of [`verify_counterexample`](Self::verify_counterexample).
    ///
    /// Catches ay-internal panics and returns them as `ChcError::Internal`.
    /// Non-ay panics propagate normally via `resume_unwind`.
    pub fn try_verify_counterexample(
        &mut self,
        cex: &Counterexample,
    ) -> crate::ChcResult<CexVerificationResult> {
        ay_core::catch_ay_panics(
            std::panic::AssertUnwindSafe(|| Ok(self.verify_counterexample(cex))),
            |reason| Err(crate::ChcError::Internal(reason)),
        )
    }
}
