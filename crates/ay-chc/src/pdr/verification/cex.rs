// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counterexample verification for PDR solver.
//!
//! Contains methods for verifying that counterexamples are forward-reachable
//! from initial states, detecting spurious counterexamples.

use super::*;

mod compact;

/// A counterexample verdict and what it was decided on.
enum CexDecision {
    /// Decided on the counterexample that was handed in.
    Checked(CexVerificationResult),
    /// `Valid`, decided on a ground derivation the handed-in counterexample
    /// did not carry (or whose trace its steps do not state), which this
    /// counterexample carries instead: the input with the derivation its
    /// witness names, the unrolling model's or the bounded-BMC replay's own
    /// counterexample, or the input restated as its derivation's trace.
    Substituted(Counterexample),
}

impl CexDecision {
    fn verdict(&self) -> CexVerificationResult {
        match self {
            Self::Checked(verdict) => *verdict,
            Self::Substituted(_) => CexVerificationResult::Valid,
        }
    }
}

impl PdrSolver {
    /// Verify that a counterexample is forward-reachable from initial states.
    ///
    /// REQUIRES: `self.problem` is the CHC problem the counterexample was generated for.
    /// ENSURES: `Valid` only on a ground derivation of `false` that validates
    ///   against `self.problem` (concrete values for every clause instance), so
    ///   the PROBLEM is unsafe. `Spurious` when a check refutes `cex`, `Unknown`
    ///   otherwise: no ground evidence means no `Valid` (fail closed).
    ///
    /// The derivation is the one `cex` carries, the one its witness names, or
    /// one found by searching this problem's clauses at `cex`'s depth; in the
    /// last two cases it certifies the PROBLEM unsafe, not `cex`'s steps, and a
    /// caller that publishes the counterexample uses `confirm_counterexample`.
    pub fn verify_counterexample(&mut self, cex: &Counterexample) -> CexVerificationResult {
        self.decide_counterexample(cex).verdict()
    }

    /// [`Self::verify_counterexample`] for a caller that PUBLISHES the
    /// counterexample. `Ok` holds the counterexample the `Valid` verdict rests
    /// on; `Err` holds the verdict otherwise (`Spurious` or `Unknown`, never
    /// `Valid`).
    ///
    /// The bounded-BMC replay (inc-9) decides `Valid` from its own verified
    /// derivation of `false` on this solver's clauses and never checks the
    /// content of `cex`, typically a back-translation whose inlined final step
    /// was not re-inserted (a trace one transition short of the query). `Ok`
    /// then holds the replay's counterexample, a complete init-to-bad trace on
    /// these clauses carrying its witness and ground derivation. Likewise the
    /// ground-derivation fast path decides on `cex`'s derivation, not its
    /// steps: when the steps claim another trace (the same back-translation,
    /// with its derivation translated in full), `Ok` holds `cex` restated as
    /// the derivation's trace. What is published is what passed.
    pub(crate) fn confirm_counterexample(
        &mut self,
        cex: Counterexample,
    ) -> Result<Counterexample, CexVerificationResult> {
        match self.decide_counterexample(&cex) {
            CexDecision::Checked(CexVerificationResult::Valid) => Ok(cex),
            CexDecision::Checked(verdict) => Err(verdict),
            CexDecision::Substituted(substituted) => Ok(substituted),
        }
    }

    fn decide_counterexample(&mut self, cex: &Counterexample) -> CexDecision {
        let memory = self.validation_memory();
        let _memory_scope = memory.install();
        if !memory.open() || self.smt.exact_term_memory_exceeded() {
            return CexDecision::Checked(CexVerificationResult::Unknown);
        }
        // INV-S2 (#horn-smt-session §7.2): the Unsafe verifier never routes to
        // a `HornSmt` session (`ground_evidence_by_search` is only reached
        // from here).
        let _verification_pin = crate::smt::lane::ScopedVerificationMode::install();
        if cex.compact_evidence().is_some() {
            return self.decide_compact_counterexample(cex);
        }
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

        // Acceptance is ground evaluation on THESE clauses, nothing else: a
        // `Valid` verdict always rests on a `GroundDerivation` that
        // `validate_ground_derivation` re-evaluates here against
        // `self.problem` (every clause constraint true, every premise tuple
        // equal to its premise's head, all under totally concrete values).
        // Engine summaries, witness states and SMT "satisfiable with the
        // instances pinned" checks never accept: a PDR must summary that
        // dropped a `(mod y 3)` head argument once produced a fake
        // counterexample that the witness-entry and root-state checks passed.
        //
        // 1. A carried derivation (never trusted for being attached).
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
                    // Publish what was verified: the derivation's trace, not
                    // steps that claim another one.
                    return match cex.restated_by_derivation(&self.problem, derivation) {
                        Some(restated) => CexDecision::Substituted(restated),
                        None => CexDecision::Checked(CexVerificationResult::Valid),
                    };
                }
                Err(err) => {
                    crate::ground_derivation::log_ground_translation_detail(format_args!(
                        "attached derivation does not validate against this problem: {err}"
                    ));
                }
            }
        }

        // 2. The derivation the witness names: per derived fact the clause that
        //    fired and that clause's values; then the same with the values the
        //    witness leaves open filled by bounded per-clause solves.
        if let Some(derivation) = self.witness_named_derivation(cex) {
            return self.accept_derivation(cex, derivation, "its derivation witness");
        }

        // 3. The witness checks may REFUTE a counterexample (PDR refines on a
        //    spurious one) but never accept it.
        if let Some(witness) = cex.witness.as_ref().filter(|w| !w.entries.is_empty()) {
            let mut saw_unknown = false;
            let verdict = self
                .verify_counterexample_witness_entries(witness, &mut saw_unknown)
                .or_else(|| self.verify_counterexample_query_clause(witness, &mut saw_unknown));
            if verdict == Some(CexVerificationResult::Spurious) {
                return CexDecision::Checked(CexVerificationResult::Spurious);
            }
            return self.ground_evidence_by_search(cex, false);
        }
        self.ground_evidence_by_search(cex, true)
    }

    /// The derivation `cex`'s witness names (as is, else completed), when it
    /// validates against `self.problem`.
    fn witness_named_derivation(
        &self,
        cex: &Counterexample,
    ) -> Option<crate::ground_derivation::GroundDerivation> {
        let validates = |derivation: &crate::ground_derivation::GroundDerivation| {
            match crate::ground_derivation::validate_ground_derivation(&self.problem, derivation) {
                Ok(()) => true,
                Err(err) => {
                    crate::ground_derivation::log_ground_translation_detail(format_args!(
                        "witness-named derivation rejected on these clauses: {err}"
                    ));
                    false
                }
            }
        };
        if let Some(derivation) = cex.witness_ground_derivation(&self.problem) {
            if validates(&derivation) {
                return Some(derivation);
            }
        } else {
            return None;
        }
        let token = self
            .config
            .effective_cancellation_token()
            .unwrap_or_default();
        let _budget = crate::ground_derivation::witness::ScopedWitnessChainBudget::new_bounded(
            Some(crate::ground_derivation::linear_trace::trace_witness_deadline()),
            token,
        );
        cex.witness_ground_derivation_completed(&self.problem)
            .filter(|derivation| validates(derivation))
    }

    /// `Valid` on `derivation`, validated against `self.problem`: publish `cex`
    /// carrying it, restated as the derivation's trace when its steps claim
    /// another one.
    fn accept_derivation(
        &self,
        cex: &Counterexample,
        derivation: crate::ground_derivation::GroundDerivation,
        source: &str,
    ) -> CexDecision {
        tracing::debug!(
            "PDR: counterexample ground-validated from {source} ({} steps)",
            derivation.len()
        );
        let carried = Counterexample {
            steps: cex.steps.clone(),
            witness: cex.witness.clone(),
            compact_derivation: None,
            ground_derivation: Some(derivation),
        };
        let restated = carried
            .ground_derivation
            .as_ref()
            .and_then(|derivation| carried.restated_by_derivation(&self.problem, derivation));
        CexDecision::Substituted(restated.unwrap_or(carried))
    }

    /// Search this problem's clauses for ground evidence of `false` at the
    /// counterexample's depth: the single-predicate unrolling, whose model is
    /// read back as a ground derivation, then the bounded-BMC replay. The
    /// engine's counterexample contributes only its depth.
    ///
    /// An unreachable unrolling refutes a WITNESS-LESS counterexample (its
    /// depth is all it claims); a witness names its own path, which the
    /// replay searches for from its depth with slack.
    fn ground_evidence_by_search(
        &mut self,
        cex: &Counterexample,
        witness_less: bool,
    ) -> CexDecision {
        let Some((pred, state_vars, init, transition, query)) = self.transition_system_encoding()
        else {
            // No transition-system encoding (multi-predicate problems and
            // shapes the encoder rejects) is NOT evidence of spuriousness.
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
        let mut result = self
            .smt
            .check_sat_with_timeout(&reachability, VERIFY_INITIAL_TIMEOUT);
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
            SmtResult::Sat(model) => {
                match self.unrolling_counterexample(pred, &state_vars, &model, depth) {
                    Some(grounded) => {
                        tracing::debug!(
                            "PDR: depth-{depth} unrolling model ground-validated on these clauses"
                        );
                        CexDecision::Substituted(grounded)
                    }
                    None => self.replay_unencodable_counterexample(cex),
                }
            }
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
                if witness_less =>
            {
                CexDecision::Checked(CexVerificationResult::Spurious)
            }
            SmtResult::Unknown if witness_less => {
                CexDecision::Checked(CexVerificationResult::Unknown)
            }
            _ => self.replay_unencodable_counterexample(cex),
        }
    }

    /// The counterexample a SAT model of the depth-`depth` unrolling
    /// (`encode_transition_system_reachability`) describes, ground-validated
    /// on `self.problem`; `None` when its trace does not ground-validate.
    fn unrolling_counterexample(
        &self,
        pred: PredicateId,
        state_vars: &[ChcVar],
        model: &FxHashMap<String, SmtValue>,
        depth: usize,
    ) -> Option<Counterexample> {
        use crate::ground_derivation::linear_trace::{
            counterexample_from_linear_trace, trace_witness_deadline, ts_locals_with_suffix,
            LinearTrace, TraceEdgeHint,
        };
        let edge = |suffix: &str| TraceEdgeHint {
            clause_locals: ts_locals_with_suffix(model, suffix),
            ..TraceEdgeHint::default()
        };
        let mut edges = Vec::with_capacity(depth + 2);
        edges.push(edge("__init"));
        edges.extend((0..depth).map(|step| edge(&format!("__trans{step}"))));
        edges.push(edge("__query"));
        let states = (0..=depth)
            .map(|step| {
                state_vars
                    .iter()
                    .map(|var| {
                        model
                            .get(
                                &crate::transition_system::TransitionSystem::version_var(var, step)
                                    .name,
                            )
                            .cloned()
                    })
                    .collect()
            })
            .collect();
        let trace = LinearTrace {
            predicate: pred,
            states,
            edges,
        };
        let token = self
            .config
            .effective_cancellation_token()
            .unwrap_or_default();
        counterexample_from_linear_trace(
            &self.problem,
            &trace,
            Some(trace_witness_deadline()),
            &token,
        )
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
    fn replay_unencodable_counterexample(&mut self, cex: &Counterexample) -> CexDecision {
        const REPLAY_BUDGET: std::time::Duration = std::time::Duration::from_secs(10);
        const INCONCLUSIVE: CexDecision = CexDecision::Checked(CexVerificationResult::Unknown);
        if self.config.disable_cex_replay {
            return INCONCLUSIVE;
        }
        // Acceptance needs a derivation that validates on `self.problem`; a
        // problem the validator's whole-source preflight refuses admits none,
        // so the replay could only spend its budget (fail closed: Unknown).
        let problem = &self.problem;
        if !*self.ground_validation_admitted.get_or_insert_with(|| {
            crate::ground_derivation::problem_admits_native_ground_validation(problem)
        }) {
            return INCONCLUSIVE;
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
            return INCONCLUSIVE;
        }
        let budget = self.cap_timeout(REPLAY_BUDGET);
        if budget < std::time::Duration::from_millis(250) {
            return INCONCLUSIVE;
        }
        match crate::bmc::BmcSolver::replay_confirm_unsafe_on_problem(
            &self.problem,
            depth_hint,
            budget,
            self.config.effective_cancellation_token(),
            self.config.verbose,
        ) {
            // The verdict rests on the replay's own counterexample, and only
            // on the ground derivation it carries, re-validated here.
            Some(verified)
                if verified
                    .ground_derivation
                    .as_ref()
                    .is_some_and(|derivation| {
                        crate::ground_derivation::validate_ground_derivation(
                            &self.problem,
                            derivation,
                        )
                        .is_ok()
                    }) =>
            {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: counterexample CONFIRMED by bounded BMC replay with a ground \
                         derivation (depth hint {depth_hint})"
                    );
                }
                CexDecision::Substituted(verified)
            }
            Some(_) => INCONCLUSIVE,
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
                INCONCLUSIVE
            }
        }
    }

    /// Panic-safe [`Self::confirm_counterexample`].
    pub(crate) fn try_confirm_counterexample(
        &mut self,
        cex: Counterexample,
    ) -> crate::ChcResult<Result<Counterexample, CexVerificationResult>> {
        ay_core::catch_ay_panics(
            std::panic::AssertUnwindSafe(|| Ok(self.confirm_counterexample(cex))),
            |reason| Err(crate::ChcError::Internal(reason)),
        )
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

#[cfg(test)]
#[path = "cex_confirmation_tests.rs"]
mod confirmation_tests;

#[cfg(test)]
#[path = "cex_ground_only_tests.rs"]
mod ground_only_tests;
