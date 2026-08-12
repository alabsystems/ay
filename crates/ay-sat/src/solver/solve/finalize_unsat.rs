// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! UNSAT declaration and proof finalization.
//!
//! Centralizes UNSAT proof output: empty clause emission, LRAT chain
//! verification, and the `declare_unsat` / `declare_unsat_assume` API
//! methods.

use super::super::*;
use crate::fmla_runtime_ledger::{
    validate_external_checker_verdict_artifact_file, ExternalProofCheckerVerdictArtifactRef,
    FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
    FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV,
    FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_SCHEMA,
};
use crate::kani_compat::det_hash_set_new;
use crate::proof_certificate::ProofCertificate;
use crate::solver::backward_proof::{BackwardProofFailure, BackwardProofResult};
use crate::solver_log::solver_log;
use serde_json::Value;
use sha2::{Digest, Sha256};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(in crate::solver) enum UnsatProofFinalizationError {
    ProofIo,
    LratAuthorityFailClosed,
    LratChainFailures(u64),
    InvalidLratChain(&'static str),
    MissingEmptyClause,
}

impl UnsatProofFinalizationError {
    fn detail(&self) -> String {
        match self {
            Self::ProofIo => "UNSAT proof finalization failed: proof I/O error".to_string(),
            Self::LratAuthorityFailClosed => {
                "UNSAT proof finalization failed: LRAT authority fail-closed".to_string()
            }
            Self::LratChainFailures(count) => {
                format!("UNSAT proof finalization failed: LRAT checker reported {count} failures")
            }
            Self::InvalidLratChain(reason) => {
                format!("UNSAT proof finalization failed: invalid LRAT chain ({reason})")
            }
            Self::MissingEmptyClause => {
                "UNSAT proof finalization failed: empty clause was not written".to_string()
            }
        }
    }
}

impl Solver {
    /// Finalize UNSAT proof by writing the empty clause
    ///
    /// This method centralizes UNSAT proof finalization. All UNSAT return sites
    /// MUST call this method before returning `SatResult::Unsat(_)`.
    ///
    /// # DRAT/LRAT format
    ///
    /// The empty clause (`0`) marks the final derivation of contradiction in
    /// DRAT/LRAT proofs. External proof checkers (e.g., drat-trim) require
    /// this to validate the proof is complete.
    ///
    /// # Debug verification
    ///
    /// Declare the formula unsatisfiable: emit the TLA+ trace step,
    /// finalize the DRAT/LRAT proof, and return `SatResult::Unsat(_)`.
    ///
    /// This is the UNSAT counterpart to [`declare_sat_from_current_assignment`].
    #[inline]
    pub(in crate::solver) fn declare_unsat(&mut self) -> SatResult {
        // Oversized-clause poison: a clause exceeding the arena's 16-bit length
        // field was stored truncated (a sound STRENGTHENING — see
        // `ClauseArena::add`). A truncated CNF clause has FEWER disjuncts, so the
        // formula the solver actually searched is stronger than the user's: any
        // UNSAT it derives may be spurious (the original could be SAT). Downgrade
        // to Unknown. (SAT is unaffected: a model of the strengthened formula
        // also satisfies the weaker original, and is re-verified against the full
        // original clauses in `finalize_sat`.)
        if self.arena.has_oversized_clause() {
            return self.declare_unknown_with_reason(SatUnknownReason::ClauseTooLarge);
        }
        // #8754: FINALIZE_SAT_FAIL poison — if we saw an invalid SAT model
        // earlier in this solve call, any UNSAT we now derive is suspect.
        // The learned clauses / reconstruction stack / clause-DB state that
        // led to the finalize failure may also be driving this UNSAT. Return
        // Unknown instead of a potentially unsound UNSAT.
        if self.cold.finalize_sat_fail_count > 0 {
            tracing::warn!(
                finalize_sat_fail_count = self.cold.finalize_sat_fail_count,
                "declare_unsat: downgrading to Unknown because a prior SAT \
                 model failed finalization (FINALIZE_SAT_FAIL poison)"
            );
            eprintln!(
                "FINALIZE_SAT_FAIL_POISON: downgrading UNSAT to Unknown \
                 (finalize_sat_fail_count={}). See earlier FINALIZE_SAT_FAIL \
                 line for the failing clause.",
                self.cold.finalize_sat_fail_count,
            );
            return self.declare_unknown_with_reason(SatUnknownReason::InvalidSatModel);
        }
        // #oversized: if any clause was stored truncated (oversized-clause
        // splitting disabled via AY_SPLIT_OVERSIZED_CLAUSES=0), the clause-DB
        // is a strengthening of the input. UNSAT on a strengthened formula does
        // not imply UNSAT of the original, so downgrade to Unknown. SAT remains
        // sound (a model of the strengthened formula models the original too).
        if self.cold.oversized_clause_poison {
            tracing::warn!(
                "declare_unsat: downgrading to Unknown because an oversized \
                 clause was stored truncated (oversized-clause splitting disabled)"
            );
            return self.declare_unknown_with_reason(SatUnknownReason::Unspecified);
        }
        if self.cold.trace_ext_conflict {
            eprintln!(
                "[DECLARE_UNSAT] conflicts={} decisions={} dl={} has_empty_clause={} trail_len={}",
                self.num_conflicts,
                self.num_decisions,
                self.decision_level,
                self.has_empty_clause,
                self.trail.len()
            );
            // Print the trail
            for (i, &lit) in self.trail.iter().enumerate() {
                let var = lit.variable();
                let level = self.var_data[var.index()].level;
                eprintln!(
                    "[DECLARE_UNSAT]   trail[{}]: var={} pos={} level={}",
                    i,
                    var.index(),
                    lit.is_positive(),
                    level
                );
            }
        }
        self.maybe_append_authorized_fmla_learned_lrat_materialization();

        // Run backward LRAT reconstruction BEFORE finalize_unsat_proof so we
        // can capture the result for the proof certificate.
        let backward_result = self.run_backward_proof_reconstruction();
        if self.cold.backward_proof_failure.is_some()
            || (self.cold.backward_proof_limits.is_some() && !self.cold.empty_clause_in_proof)
        {
            return self.declare_unknown_with_reason(SatUnknownReason::ProofFinalizationFailure);
        }
        if let Err(error) = self.finalize_unsat_proof() {
            return self.declare_proof_finalization_unknown(error);
        }
        self.tla_trace_step(CdclTraceState::Unsat, Some(CdclTraceAction::DeclareUnsat));

        let proof_steps = self
            .proof_manager
            .as_ref()
            .map_or(0, ProofManager::added_count);
        solver_log!(
            self,
            "UNSAT: {} conflicts, {} decisions, {} proof steps",
            self.num_conflicts,
            self.num_decisions,
            proof_steps
        );
        tracing::info!(
            num_conflicts = self.num_conflicts,
            num_decisions = self.num_decisions,
            proof_steps,
            "solve: unsat"
        );
        self.emit_diagnostic_unsat_summary();

        // Build proof certificate from backward reconstruction result.
        let mut certificate = match backward_result {
            Some(backward) => {
                ProofCertificate::from_backward_result(backward.steps, backward.complete)
            }
            None => ProofCertificate::empty(),
        };

        // Finalize streaming UNSAT core: mark level-0 antecedents that
        // conflict analysis never sees (#8250). Then attach to certificate.
        if self.cold.retain_unsat_certificate {
            self.finalize_streaming_core();
            if let Some(core) = self.extract_streaming_core() {
                certificate.set_streaming_core(core);
            }
        }

        SatResult::Unsat(certificate)
    }

    /// Run backward LRAT proof reconstruction (#8105, primary path).
    ///
    /// This is the PRIMARY LRAT proof path. After the solver determines UNSAT,
    /// this method walks the clause dependency graph backward from the empty
    /// clause and produces proof steps for only the reachable learned clauses.
    ///
    /// With forward chain collection removed from the conflict analysis hot
    /// path (#8105), this backward reconstruction is the sole source of LRAT
    /// hint information. The forward path emits no additions during solving
    /// (IDs are reserved but not written), and this method writes the actual
    /// LRAT addition lines with proper hints.
    fn run_backward_proof_reconstruction(&mut self) -> Option<BackwardProofResult> {
        if !self.cold.lrat_enabled || !self.cold.unsat_certificate_enabled {
            return None;
        }
        if let Some(limits) = self.cold.backward_proof_limits.clone() {
            // An input-time contradiction can already be a complete,
            // authenticated proof. If no deferred learned ID exists, there is
            // nothing to reconstruct; avoid even allocating the visited map so
            // a zero backward-memory allowance still accepts that proof.
            let existing_terminal_needs_no_backfill = self.cold.empty_clause_in_proof
                && self.proof_manager.as_ref().is_some_and(|manager| {
                    !manager.has_io_error()
                        && manager.has_file_visible_terminal_empty()
                        && !manager.has_backward_reserved_ids()
                });
            if existing_terminal_needs_no_backfill {
                return None;
            }

            let mut backward = match self.reconstruct_lrat_backward_bounded(&limits) {
                Ok(backward) => backward,
                Err(failure) => {
                    self.cold.backward_proof_failure = Some(failure);
                    return None;
                }
            };
            tracing::info!(
                steps = backward.steps.len().saturating_add(1),
                complete = backward.complete,
                "bounded backward LRAT proof reconstruction (primary path)"
            );
            debug_assert!(
                !self.cold.retain_unsat_certificate,
                "bounded reconstruction is configured as emit-only"
            );

            // Input-time contradictions (an original empty clause or
            // complementary original units) may already have emitted and
            // authenticated a terminal empty addition. The arena walk has no
            // learned step to append in that case, so preserve the existing
            // terminal instead of replacing it with an empty hint chain.
            let existing_terminal_is_authoritative = backward.steps.is_empty()
                && self.cold.empty_clause_in_proof
                && self.proof_manager.as_ref().is_some_and(|manager| {
                    !manager.has_io_error() && manager.has_file_visible_terminal_empty()
                });
            if existing_terminal_is_authoritative {
                if let Some(ref mut manager) = self.proof_manager {
                    if let Err(error) = manager.finish_bounded_backward_emission(limits.deadline) {
                        self.cold.empty_clause_in_proof = false;
                        self.cold.empty_clause_lrat_id = None;
                        if error.kind() == std::io::ErrorKind::TimedOut {
                            self.cold.backward_proof_failure = Some(BackwardProofFailure::Deadline);
                        }
                    }
                }
                return None;
            }

            // Any earlier empty addition stops being terminal once the
            // reserved learned steps below are appended. Clear its solver
            // marker before emission so an I/O or deadline failure cannot
            // license an incomplete UNSAT proof.
            self.cold.empty_clause_in_proof = false;
            self.cold.empty_clause_lrat_id = None;

            let mut emission_failure = None;
            if let Some(ref mut manager) = self.proof_manager {
                for step in backward.steps.drain(..) {
                    if let Err(error) = manager.emit_bounded_backward_rup_step(
                        step.clause_id,
                        &step.literals,
                        &step.hints,
                        limits.deadline,
                    ) {
                        emission_failure = Some(error.kind());
                        break;
                    }
                }
                // Unreachable reservations are dead data only after every
                // reachable step was emitted coherently. On failure retain
                // them so structural finalization also fails closed.
                if emission_failure.is_none() {
                    if let Err(error) = manager.finish_bounded_backward_emission(limits.deadline) {
                        emission_failure = Some(error.kind());
                    }
                }
            }
            if let Some(kind) = emission_failure {
                if kind == std::io::ErrorKind::TimedOut {
                    self.cold.backward_proof_failure = Some(BackwardProofFailure::Deadline);
                }
                // Writer/storage failures are latched by the bounded proof
                // buffer's shared typed handle. Other structural failures are
                // retained by ProofManager; the cleared terminal marker makes
                // the bounded solve downgrade to Unknown in either case.
                return None;
            }

            // Consume the already-bounded final hint chain through the direct
            // positive-RUP funnel. This avoids the generic hint filtering and
            // allocation path and establishes terminal flags only after the
            // writer's added-count has advanced.
            if let Err(error) = self.mark_empty_clause_with_bounded_prevalidated_hints(
                &backward.empty_hints,
                limits.deadline,
            ) {
                if error.kind() == std::io::ErrorKind::TimedOut {
                    self.cold.backward_proof_failure = Some(BackwardProofFailure::Deadline);
                }
                return None;
            }
            return None;
        }

        let backward = self.reconstruct_lrat_backward();
        tracing::info!(
            steps = backward.steps.len(),
            complete = backward.complete,
            "backward LRAT proof reconstruction (primary path)"
        );

        // Write backward-reconstructed steps to the proof file.
        // Steps are in emission order (reverse topological: deepest deps first).
        // The last step is the empty clause, which we skip here -- finalize_unsat_proof
        // writes the empty clause separately via mark_empty_clause_with_hints.
        if let Some(ref mut manager) = self.proof_manager {
            for step in &backward.steps {
                // Skip the empty clause step (clause_id == 0, empty literals).
                // The finalize_unsat_proof path handles empty clause emission.
                if step.literals.is_empty() {
                    continue;
                }
                let _ = manager.emit_backward_step(step.clause_id, &step.literals, &step.hints);
            }
            // Backward emission is complete — the reserved IDs set is now dead
            // data. Clear it to release memory (#8603).
            manager.clear_backward_reserved_ids();
        }
        Some(backward)
    }

    /// In debug builds, this method verifies that at least one clause was added
    /// to the proof (the empty clause itself). This catches bugs where UNSAT is
    /// returned without proper proof derivation. For full external verification,
    /// use `Solver::with_proof()` and verify with drat-trim.
    pub(in crate::solver) fn finalize_unsat_proof(
        &mut self,
    ) -> Result<(), UnsatProofFinalizationError> {
        // Backward proof reconstruction is now run in declare_unsat() before
        // this method, so the backward result can be captured for the proof
        // certificate (#8104).

        // Keep ClauseTrace's UNSAT marker consistent with UNSAT returns even when
        // the solver exits at decision level 0 without explicitly learning/adding
        // an empty clause. This is required for SMT-level proof reconstruction.
        if let Some(ref mut trace) = self.cold.clause_trace {
            trace.mark_empty();
        }

        if self.proof_manager.is_some() || self.cold.forward_checker.is_some() {
            let mut prior_visible_empty_lrat_id = None;
            if let Some(ref mut manager) = self.proof_manager {
                // A successfully emitted empty clause is already the terminal
                // addition for this solve. Preserve that record so the
                // always-on LRAT structural check below can authenticate it.
                // If a later incremental proof addition followed an earlier
                // still-valid empty clause, re-emit an empty clause below so
                // this solve also ends at a checker-visible contradiction. In
                // LRAT mode the earlier empty clause itself is the strongest
                // possible one-step hint when it remains live.
                let terminal_empty =
                    self.cold.empty_clause_in_proof && manager.has_file_visible_terminal_empty();
                if !terminal_empty {
                    if self.cold.empty_clause_in_proof && manager.is_lrat() {
                        prior_visible_empty_lrat_id = self
                            .cold
                            .empty_clause_lrat_id
                            .filter(|&id| manager.lrat_id_visible_in_file(id));
                    }
                    manager.clear_last_add();
                    self.cold.empty_clause_in_proof = false;
                }
            }
            // Write empty clause to indicate final derivation of contradiction,
            // unless mark_empty_clause already wrote it (#4123).
            if !self.cold.empty_clause_in_proof {
                // In LRAT mode, build hints for the empty clause from
                // level-0 trail state (#7108). Without hints, external LRAT
                // checkers reject the empty clause derivation.
                #[allow(unused_mut)] // mut needed in debug builds for assumption hint prepend
                let mut hints = if self.cold.lrat_enabled {
                    if let Some(empty_id) = prior_visible_empty_lrat_id {
                        vec![empty_id]
                    } else {
                        self.ensure_level0_unit_proof_ids();
                        self.build_finalize_empty_clause_hints()
                    }
                } else {
                    Vec::new()
                };
                #[cfg(debug_assertions)]
                for &axiom_id in &self.cold.scope_selector_axiom_ids {
                    if axiom_id != 0 && !hints.contains(&axiom_id) {
                        hints.push(axiom_id);
                    }
                }
                self.mark_empty_clause_with_hints(&hints);
            }
        }
        if let Some(ref mut manager) = self.proof_manager {
            if let Err(error) = manager.flush() {
                tracing::error!(
                    error = %error,
                    "UNSAT proof finalization failed while flushing proof output"
                );
                return Err(UnsatProofFinalizationError::ProofIo);
            }
            if manager.has_lrat_authority_fail_closed()
                && (!self.cold.ambient_artifacts_enabled
                    || !Self::fmla_learned_lrat_main_proof_authority_replay_admits())
            {
                return Err(UnsatProofFinalizationError::LratAuthorityFailClosed);
            }

            // Detect silently truncated proofs caused by I/O errors during solve.
            // Without this check, a disk-full or broken-pipe produces a corrupted
            // proof that drat-trim rejects with no diagnosis path back to the solver.
            // The I/O error state is tracked internally (CaDiCaL-style) — call sites
            // use `let _ =` to avoid aborting mid-solve, but the error is captured.
            if manager.has_io_error() {
                tracing::error!(
                    "UNSAT proof finalization failed because the proof manager latched an I/O or structural error"
                );
                return Err(UnsatProofFinalizationError::ProofIo);
            }

            // Verify proof has at least the empty clause.
            // For trivial UNSAT (e.g., x AND NOT x), the empty clause alone is valid.
            // For non-trivial UNSAT, learned clauses + empty clause form the proof.
            // Full external verification (drat-trim) is done in integration tests.
            // Always-on: checking a counter is O(1) and catching a missing empty clause
            // prevents producing a structurally invalid proof.
            // Note: added_count() only counts successful writes, so this also catches
            // cases where the empty clause write itself failed.
            // Check LRAT chain verifier for accumulated failures (#4172).
            // In debug builds, individual failures fire debug_assert! at each
            // emit_add call. This post-solve check is defense-in-depth: if any
            // failure was somehow swallowed, catch it here.
            let lrat_fail_count = manager.lrat_failures();
            if lrat_fail_count > 0 {
                tracing::error!(
                    failures = lrat_fail_count,
                    "LRAT chain verifier detected failures during solve"
                );
                return Err(UnsatProofFinalizationError::LratChainFailures(
                    lrat_fail_count,
                ));
            }

            // Post-UNSAT derivation chain integrity check (#5005).
            // Walks backward from the empty clause through all LRAT hint
            // references, verifying they form a valid chain terminating at
            // original (axiom) clauses. Always-on in both debug and release.
            if let Err(reason) = manager.try_verify_unsat_chain() {
                tracing::error!(
                    reason,
                    "UNSAT proof finalization failed LRAT chain validation"
                );
                return Err(UnsatProofFinalizationError::InvalidLratChain(reason));
            }

            let added = manager.added_count();
            tracing::debug!(
                proof_steps = added,
                empty_clause_written = self.cold.empty_clause_in_proof,
                lrat_mode = manager.is_lrat(),
                "proof: finalization complete"
            );

            if !manager.lrat_blocked_by_theory_lemmas() && added < 1 {
                tracing::error!(
                    proof_steps = added,
                    "UNSAT proof finalization failed because the empty clause was not written"
                );
                return Err(UnsatProofFinalizationError::MissingEmptyClause);
            }

            // Always-on structural chain integrity check (#5005).
            // Verifies LRAT ID tracking is consistent after proof finalization.
            if let Err(reason) = manager.try_verify_unsat_chain() {
                tracing::error!(
                    reason,
                    "UNSAT proof finalization failed final LRAT chain validation"
                );
                return Err(UnsatProofFinalizationError::InvalidLratChain(reason));
            }
        }
        Ok(())
    }

    fn declare_proof_finalization_unknown(
        &mut self,
        error: UnsatProofFinalizationError,
    ) -> SatResult {
        let detail = error.detail();
        tracing::error!(
            detail = detail.as_str(),
            "declare_unsat: downgrading UNSAT to Unknown after proof finalization failure"
        );
        self.cold.last_unknown_detail = Some(detail);
        self.declare_unknown_with_reason(SatUnknownReason::ProofFinalizationFailure)
    }

    fn declare_assume_proof_finalization_unknown(
        &mut self,
        error: UnsatProofFinalizationError,
    ) -> AssumeResult {
        let detail = error.detail();
        tracing::error!(
            detail = detail.as_str(),
            "declare_unsat_assume: downgrading UNSAT to Unknown after proof finalization failure"
        );
        self.cold.last_unknown_detail = Some(detail);
        self.declare_assume_unknown_with_reason(SatUnknownReason::ProofFinalizationFailure)
    }

    /// Build LRAT hints for the empty clause when `finalize_unsat_proof`
    /// reaches the fallback path (no prior `mark_empty_clause_with_hints`).
    ///
    /// Strategy: find a clause in the arena that is falsified under the current
    /// level-0 assignment and use `collect_resolution_chain` to build the full
    /// derivation chain. If no falsified clause is found (shouldn't happen for
    /// a genuine UNSAT), fall back to collecting all level-0 unit proof IDs.
    pub(in crate::solver) fn build_finalize_empty_clause_hints(&mut self) -> Vec<u64> {
        use crate::watched::ClauseRef;

        // Strategy 1: find a falsified clause and build resolution chain.
        // live_indices (husk adjudication): a garbage-kept husk (e.g.
        // congruence forward subsumption, clause_ids zeroed) seeding this
        // chain corrupts the certificate — its deletion was already emitted.
        let mut falsified_ref = None;
        for offset in self.arena.live_indices() {
            let lits = self.arena.literals(offset);
            if !lits.is_empty() && lits.iter().all(|lit| self.lit_val(*lit) < 0) {
                falsified_ref = Some(ClauseRef(offset as u32));
                break;
            }
        }
        if let Some(seed) = falsified_ref {
            // NOTE: W23 (293e96bd5) added a collect_forward_bcp_lrat_hints()
            // call for non-root trails, but the method definition was never
            // committed. Fall through to collect_resolution_chain for all
            // cases until the missing method is implemented (#7175).
            let chain = self.collect_resolution_chain(seed, None, &det_hash_set_new());
            return Self::lrat_reverse_hints(&chain);
        }

        // Strategy 2: collect all level-0 unit proof IDs.
        // Every level-0 trail variable with a unit_proof_id contributes a hint.
        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        let mut hints = Vec::new();
        for i in 0..level0_end {
            let lit = self.trail[i];
            let vi = lit.variable().index();
            if let Some(id) = self.visible_unit_proof_id_for_lit(lit) {
                hints.push(id);
            } else if let Some(id) = self.level0_var_proof_id(vi) {
                hints.push(id);
            }
        }
        hints
    }

    /// Declare UNSAT for assumption-based solving, returning the given unsat core.
    ///
    /// Parallel to [`declare_unsat()`] but returns [`AssumeResult::Unsat`].
    /// Includes TLA tracing, proof finalization, and optional proof certificate
    /// construction when LRAT proof output is enabled (#8209).
    #[inline]
    pub(in crate::solver) fn declare_unsat_assume(&mut self, core: Vec<Literal>) -> AssumeResult {
        // #8754: FINALIZE_SAT_FAIL poison — downgrade UNSAT to Unknown if we
        // saw an invalid SAT model earlier in this solve call. Mirror logic
        // in declare_unsat() for the assumption-path.
        if self.cold.finalize_sat_fail_count > 0 {
            tracing::warn!(
                finalize_sat_fail_count = self.cold.finalize_sat_fail_count,
                "declare_unsat_assume: downgrading to Unknown because a prior \
                 SAT model failed finalization (FINALIZE_SAT_FAIL poison)"
            );
            eprintln!(
                "FINALIZE_SAT_FAIL_POISON: downgrading UNSAT (assume) to Unknown \
                 (finalize_sat_fail_count={}).",
                self.cold.finalize_sat_fail_count,
            );
            return self.declare_assume_unknown_with_reason(SatUnknownReason::InvalidSatModel);
        }

        // #core-subset-audit: a returned UNSAT core asserts "the formula plus
        // THESE ASSUMPTION LITERALS is unsatisfiable", so every member must be an
        // assumption of this query. Nothing checked that. A SAT answer IS verified
        // in release against the original ledger and downgraded to Unknown on
        // failure; an UNSAT verdict and its core were verified by nothing, and
        // `VerifiedAssumeResult::from_validated` is a no-op wrapper despite a doc
        // comment claiming "Verification happened at construction time". That
        // asymmetry is why a too-HIGH wrong answer can reach a competition run
        // while a too-LOW one is always caught.
        //
        // ENFORCING since #core-subset-audit-enforce (was observe-only). The old
        // rationale for observe-only was: "`cold.prev_assumptions` is refreshed by
        // `solve_with_assumptions_impl`, but the IC3 path calls this function
        // directly and may leave it stale, so downgrading could turn a CORRECT
        // OPTIMUM into SATISFIABLE." Half of that is true and half is not, and the
        // true half is harmless. The IC3 path DOES call this function directly and
        // DOES pass non-empty cores — but it refreshes `prev_assumptions` itself.
        // The property that actually licenses enforcement is containment:
        //
        //   (a) Exactly two functions ever pass a NON-EMPTY core:
        //         `solve_with_assumptions_impl`  solver/assumptions.rs:175-1067
        //           call sites :578 :603 :802 :838 :861 :883 :910 :1042 :1057
        //         `solve_incremental_ic3_raw`    solver/solve/ic3.rs:127-595
        //           call sites :331 :342 :487
        //       Every other call site passes `vec![]`, which this audit skips:
        //         assumptions.rs :39 :48 :116 :125 :392 :419 :454 :464
        //         ic3.rs :166 :169 :195 :246
        //
        //   (b) BOTH of those functions overwrite `cold.prev_assumptions` with THIS
        //       query's assumption slice — unconditionally, at function-body nesting
        //       depth 1, before entering the search loop: assumptions.rs:515-516 and
        //       ic3.rs:298-299. Every call site in (a) is lexically after its own
        //       function's refresh, and no early return in between carries a
        //       non-empty core.
        //
        //   (c) Neither function shadows or re-composes `assumptions` after the
        //       refresh. Scope/activation composition happens in the callers
        //       (assumptions.rs:34, :111) or before the refresh (ic3.rs:141-162), and
        //       it is the composed slice that gets stored — the same slice the cores
        //       are drawn from.
        //
        // So for every core this audit actually inspects, `prev_assumptions` is
        // exactly this query's assumptions, cannot be stale, and a stray literal is
        // a genuine defect rather than a bookkeeping artifact.
        //
        // WHAT BREAKS THE ARGUMENT — re-verify by hand if any of these change:
        //   1. A `declare_unsat_assume(...)` call with a non-`vec![]` argument added
        //      OUTSIDE those two functions. `core_subset_audit_containment_guard` in
        //      this file's `tests` module re-derives (a) from source on every run and
        //      fails if this happens, so it cannot rot silently.
        //   2. Moving, conditionalizing, or duplicating either `prev_assumptions`
        //      refresh so some path reaches a non-empty-core call site without it.
        //      The guard checks the refresh is unique and lexically above every such
        //      call site in the same function; it does NOT prove unconditionality —
        //      that half of (b) is eyeball-verified and must be re-read.
        //   3. Re-entrant solving. `solve_with_assumptions_impl` takes a
        //      caller-supplied `theory_check: &mut dyn FnMut(&mut Self)`, which hands
        //      out `&mut Solver`. A callback that ran a nested solve would overwrite
        //      `prev_assumptions` and the outer core would be audited against the
        //      wrong set. No in-tree callback does this (the `Extension` trait only
        //      receives `&dyn SolverContext`), and a nested solve would corrupt far
        //      more than this audit, but it is the one hole reasoning cannot close.
        //
        // An EMPTY core is the strictly stronger claim ("UNSAT independent of the
        // assumptions") and needs a level-0 trail audit instead, so it is skipped.
        // The empty-`prev_assumptions` skip is kept for the same reason: with no
        // assumptions recorded there is nothing to check against. That case is
        // believed unreachable with a non-empty core (cores are built out of
        // `assumptions`), but it is left as a skip rather than a downgrade because,
        // unlike the stray-literal case, it has not been measured.
        if !core.is_empty() && !self.cold.prev_assumptions.is_empty() {
            let assumed: std::collections::HashSet<Literal> =
                self.cold.prev_assumptions.iter().copied().collect();
            let stray = core.iter().filter(|l| !assumed.contains(l)).count();
            if stray > 0 {
                tracing::warn!(
                    stray,
                    core_len = core.len(),
                    assumptions = self.cold.prev_assumptions.len(),
                    "CORE-NOT-SUBSET: downgrading UNSAT (assume) to Unknown — core \
                     contains literals that are not assumptions of this query, so it \
                     is not a certified unsat subset"
                );
                eprintln!(
                    "CORE-NOT-SUBSET: downgrading UNSAT (assume) to Unknown \
                     ({stray}/{} core literals are not assumptions, of {} assumed).",
                    core.len(),
                    self.cold.prev_assumptions.len(),
                );
                return self.declare_assume_unknown_with_reason(SatUnknownReason::InvalidUnsatCore);
            }
        }

        self.maybe_append_authorized_fmla_learned_lrat_materialization();

        // Run backward LRAT reconstruction BEFORE finalize_unsat_proof (same
        // ordering as declare_unsat) so the proof certificate captures the full
        // derivation chain. This enables proof-based UNSAT core extraction
        // via ProofCertificate::minimal_core() (#8209).
        let backward_result = self.run_backward_proof_reconstruction();
        if self.cold.backward_proof_failure.is_some()
            || (self.cold.backward_proof_limits.is_some() && !self.cold.empty_clause_in_proof)
        {
            return self
                .declare_assume_unknown_with_reason(SatUnknownReason::ProofFinalizationFailure);
        }
        if let Err(error) = self.finalize_unsat_proof() {
            return self.declare_assume_proof_finalization_unknown(error);
        }
        self.tla_trace_step(CdclTraceState::Unsat, Some(CdclTraceAction::DeclareUnsat));
        self.emit_diagnostic_unsat_summary();

        let streaming_core = if self.cold.retain_unsat_certificate {
            self.finalize_streaming_core();
            self.extract_streaming_core()
        } else {
            None
        };
        let certificate = backward_result.map(|backward| {
            let mut cert =
                ProofCertificate::from_backward_result(backward.steps, backward.complete);
            if let Some(sc) = streaming_core {
                cert.set_streaming_core(sc);
            }
            cert
        });
        AssumeResult::Unsat(core, certificate)
    }

    /// Finalize the streaming UNSAT core by marking level-0 antecedents (#8250).
    ///
    /// Conflict analysis only runs for conflicts at decision level > 0.
    /// For level-0 UNSAT (contradictory unit clauses, BCP at root level),
    /// the streaming core bitmap may be empty because no analyze_conflict
    /// was invoked. This method supplements the bitmap by:
    ///
    /// 1. Finding falsified clauses under the current assignment.
    /// 2. Marking those clauses as core members (if original).
    /// 3. Walking reason clauses for level-0 trail variables that
    ///    falsify the conflict clause, marking their originals.
    ///
    /// Also marks unit clause proof IDs stored in `unit_proof_id` and
    /// `level0_proof_id`, since these represent original clauses whose
    /// arena reference was cleared after propagation.
    pub(in crate::solver) fn finalize_streaming_core(&mut self) {
        let num_originals = self.cold.streaming_core_num_originals;
        if num_originals == 0 || self.cold.streaming_core.is_none() {
            return;
        }

        // Phase 1: Collect original clause IDs to mark (avoids borrow conflicts).
        let mut ids_to_mark: Vec<u64> = Vec::new();

        // Mark any falsified original clause.
        // live_indices (husk adjudication): skip garbage-kept husks, and keep
        // scanning past falsified clauses without a usable original ID
        // (cid==0 husks previously hit the unconditional `break`, silently
        // emptying the streaming-core seed).
        for offset in self.arena.live_indices() {
            let lits = self.arena.literals(offset);
            if lits.is_empty() {
                continue;
            }
            if lits.iter().all(|lit| self.lit_val(*lit) < 0) {
                let cid = if offset < self.cold.clause_ids.len() {
                    self.cold.clause_ids[offset]
                } else {
                    0
                };
                if cid > 0 && cid <= num_originals && self.is_original_clause_id(cid) {
                    ids_to_mark.push(cid);
                    // Only need first falsified original clause.
                    break;
                }
            }
        }

        // Mark original clauses referenced by level-0 trail variable reasons.
        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        for i in 0..level0_end {
            let var_idx = self.trail[i].variable().index();
            if var_idx >= self.var_data.len() || self.var_data[var_idx].level != 0 {
                continue;
            }

            // Check arena reason.
            // #8467: lazy theory reasons are table indexes, not arena offsets —
            // indexing clause_ids with one would mark an unrelated original.
            let reason_raw = self.var_data[var_idx].reason;
            if is_clause_reason(reason_raw) && !self.var_data[var_idx].is_lazy_theory_reason() {
                let reason_offset = reason_raw as usize;
                let reason_id = if reason_offset < self.cold.clause_ids.len() {
                    self.cold.clause_ids[reason_offset]
                } else {
                    0
                };
                if reason_id > 0
                    && reason_id <= num_originals
                    && self.is_original_clause_id(reason_id)
                {
                    ids_to_mark.push(reason_id);
                }
            }

            // Check signed unit proof IDs (for clauses whose arena reference was cleared).
            let lit = self.trail[i];
            if let Some(pid) = self.visible_unit_proof_id_for_lit(lit) {
                if pid > 0 && pid <= num_originals && self.is_original_clause_id(pid) {
                    ids_to_mark.push(pid);
                }
            }

            // Check signed level0_proof_id fallback.
            if let Some(pid) = self.level0_var_proof_id_for_lit(lit) {
                if pid > 0 && pid <= num_originals && self.is_original_clause_id(pid) {
                    ids_to_mark.push(pid);
                }
            }
        }

        // Phase 2: Apply marks to the bitmap.
        if let Some(ref mut bitmap) = self.cold.streaming_core {
            for cid in ids_to_mark {
                bitmap[(cid - 1) as usize] = true;
            }
        }
    }

    fn fmla_learned_lrat_main_proof_authority_replay_admits() -> bool {
        let Ok(path) = std::env::var(FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV) else {
            return false;
        };
        let path = path.trim();
        if path.is_empty() {
            return false;
        }
        let Ok(payload) = std::fs::read_to_string(path) else {
            return false;
        };
        let Ok(value) = serde_json::from_str::<Value>(&payload) else {
            return false;
        };
        let proof_obligation_rows = value
            .get("proof_obligation_rows")
            .and_then(Value::as_u64)
            .unwrap_or(0);
        if value.get("schema").and_then(Value::as_str)
            != Some(FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_SCHEMA)
            || value.get("status").and_then(Value::as_str)
                != Some("committed_checker_backed_admission")
            || proof_obligation_rows == 0
            || value
                .get("external_proof_checker_verdict_artifact_rows")
                .and_then(Value::as_u64)
                != Some(proof_obligation_rows)
            || value
                .get("learned_lrat_main_proof_authority_status")
                .and_then(Value::as_str)
                != Some("authorized")
            || value
                .get("learned_lrat_main_proof_authority_external_checker_verified")
                .and_then(Value::as_bool)
                != Some(true)
            || value
                .get("learned_lrat_main_proof_authority_proof_out_contains_lrat_fragment")
                .and_then(Value::as_bool)
                != Some(true)
            || value
                .get("learned_lrat_main_proof_authority_authorizes_main_proof_out")
                .and_then(Value::as_bool)
                != Some(true)
            || value
                .get("external_proof_checker_verdict")
                .and_then(Value::as_str)
                != Some("VERIFIED_UNSAT")
            || value.get("checker_exit_code").and_then(Value::as_i64) != Some(0)
        {
            return false;
        }

        let Some(authority_proof_out_path) = value
            .get("learned_lrat_main_proof_authority_proof_out_path")
            .and_then(Value::as_str)
        else {
            return false;
        };
        let Some(current_proof_out_path) =
            std::env::var(FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV)
                .ok()
                .map(|path| path.trim().to_string())
                .filter(|path| !path.is_empty())
        else {
            return false;
        };
        if authority_proof_out_path != current_proof_out_path {
            return false;
        }
        let Some(expected_sha256) = value
            .get("learned_lrat_main_proof_authority_proof_out_sha256")
            .and_then(Value::as_str)
        else {
            return false;
        };
        let Some(checker_artifact) = Self::fmla_external_checker_verdict_artifact_from_replay_json(
            &value,
            authority_proof_out_path,
            expected_sha256,
        ) else {
            return false;
        };
        if validate_external_checker_verdict_artifact_file(&checker_artifact).is_err() {
            return false;
        }
        let Ok(proof_out_bytes) = std::fs::read(authority_proof_out_path) else {
            return false;
        };
        Self::sha256_hex(&proof_out_bytes).eq_ignore_ascii_case(expected_sha256)
    }

    fn maybe_append_authorized_fmla_learned_lrat_materialization(&mut self) {
        if !self.cold.ambient_artifacts_enabled {
            return;
        }
        let Some(manager) = self.proof_manager.as_mut() else {
            return;
        };
        if !manager.has_lrat_authority_fail_closed() {
            return;
        }
        let Ok(replay_path) = std::env::var(FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV)
        else {
            return;
        };
        let replay_path = replay_path.trim();
        if replay_path.is_empty() {
            return;
        }
        let Some(current_proof_out_path) =
            std::env::var(FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV)
                .ok()
                .map(|path| path.trim().to_string())
                .filter(|path| !path.is_empty())
        else {
            return;
        };
        let Ok(payload) = std::fs::read_to_string(replay_path) else {
            return;
        };
        let Ok(value) = serde_json::from_str::<Value>(&payload) else {
            return;
        };

        match manager.append_authorized_fmla_learned_lrat_fragment_from_replay_json(
            &value,
            &current_proof_out_path,
        ) {
            Ok(rows) => {
                tracing::info!(
                    rows,
                    "authorized Fmla learned-LRAT fragment rows appended before UNSAT finalization"
                );
            }
            Err(reject) => {
                tracing::debug!(
                    reject = ?reject,
                    "Fmla learned-LRAT proof materialization did not append; finalization remains fail-closed"
                );
            }
        }
    }

    fn fmla_external_checker_verdict_artifact_from_replay_json(
        value: &Value,
        proof_out_path: &str,
        proof_out_sha256: &str,
    ) -> Option<ExternalProofCheckerVerdictArtifactRef> {
        Some(ExternalProofCheckerVerdictArtifactRef {
            schema: Self::json_string(value, "external_proof_checker_verdict_artifact_schema")?,
            runtime_field: Self::json_string(
                value,
                "external_proof_checker_verdict_artifact_runtime_field",
            )?,
            artifact_path: Self::json_string(value, "external_proof_checker_verdict_artifact")?,
            artifact_sha256: Self::json_string(
                value,
                "external_proof_checker_verdict_artifact_sha256",
            )?,
            checker_path: Self::json_string(value, "external_proof_checker_path")?,
            checker_sha256: Self::json_string(value, "external_proof_checker_sha256")?,
            checker_command: Self::json_string(value, "external_proof_checker_command")?,
            checker_argv: Self::json_string_array(value, "external_proof_checker_argv")?,
            checker_exit_code: value.get("checker_exit_code")?.as_i64()?.try_into().ok()?,
            proof_out_path: proof_out_path.to_string(),
            proof_out_sha256: proof_out_sha256.to_string(),
            checked_dimacs_path: Self::json_string(value, "external_proof_checker_dimacs_path")?,
            checked_dimacs_sha256: Self::json_string(
                value,
                "external_proof_checker_dimacs_sha256",
            )?,
            verdict: Self::json_string(value, "external_proof_checker_verdict")?,
        })
    }

    fn json_string(value: &Value, field: &'static str) -> Option<String> {
        value.get(field)?.as_str().map(str::to_string)
    }

    fn json_string_array(value: &Value, field: &'static str) -> Option<Vec<String>> {
        value
            .get(field)?
            .as_array()?
            .iter()
            .map(|item| item.as_str().map(str::to_string))
            .collect()
    }

    fn sha256_hex(bytes: &[u8]) -> String {
        let digest = Sha256::digest(bytes);
        let mut hex = String::with_capacity(64);
        for byte in digest {
            use std::fmt::Write as _;
            let _ = write!(&mut hex, "{byte:02x}");
        }
        hex
    }

    /// Extract the streaming UNSAT core from the solver's bitmap (#8250).
    ///
    /// Converts the internal `streaming_core` bitmap (indexed by clause_id - 1)
    /// into a sorted `Vec<u64>` of 1-based original clause IDs. Returns `None`
    /// if streaming core tracking was not active (e.g., no original clauses).
    ///
    /// Cost: O(num_originals) scan of the bitmap. For typical formulas this is
    /// negligible compared to the solve time.
    pub(in crate::solver) fn extract_streaming_core(&self) -> Option<Vec<u64>> {
        let bitmap = self.cold.streaming_core.as_ref()?;
        let core: Vec<u64> = bitmap
            .iter()
            .enumerate()
            .filter_map(|(i, &marked)| {
                if marked {
                    Some((i as u64) + 1) // Convert 0-based index to 1-based clause ID
                } else {
                    None
                }
            })
            .collect();
        if core.is_empty() {
            None
        } else {
            Some(core)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    // The one workspace env choke point: serialized, restore-on-exit env
    // mutation (unifies the former FMLA_LEARNED_LRAT_ENV_TEST_LOCK + local
    // EnvGuard onto it).
    use ay_test_support::env::{lock_env, ScopedEnvVar};
    use serde_json::json;

    fn fmla_authority_replay_payload(
        dir: &std::path::Path,
        proof_out_path: &std::path::Path,
        proof_out: &[u8],
        proof_rows: u64,
    ) -> Value {
        let checker_path = dir.join("ay-test-lrat-check").display().to_string();
        let checked_dimacs_path = dir.join("input.cnf").display().to_string();
        let checker_artifact_path = dir
            .join("fmla-main-lrat-external-checker-verdict.json")
            .display()
            .to_string();
        std::fs::write(
            dir.join("fmla-main-lrat-external-checker-verdict.json"),
            b"checker verdict",
        )
        .expect("write retained checker verdict artifact");
        let proof_out_path = proof_out_path.display().to_string();
        let checker_command = format!("{checker_path} {checked_dimacs_path} {proof_out_path}");
        json!({
            "schema": FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_SCHEMA,
            "status": "committed_checker_backed_admission",
            "proof_obligation_rows": proof_rows,
            "external_proof_checker_verdict_artifact_rows": proof_rows,
            "external_proof_checker_verdict_artifact": checker_artifact_path,
            "external_proof_checker_verdict_artifact_sha256": Solver::sha256_hex(b"checker verdict"),
            "external_proof_checker_verdict_artifact_schema": crate::fmla_runtime_ledger::FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_SCHEMA,
            "external_proof_checker_verdict_artifact_runtime_field": crate::fmla_runtime_ledger::FMLA_MAIN_LRAT_EXTERNAL_CHECKER_VERDICT_REQUIREMENT.runtime_field,
            "learned_lrat_main_proof_authority_status": "authorized",
            "learned_lrat_main_proof_authority_external_checker_verified": true,
            "learned_lrat_main_proof_authority_proof_out_contains_lrat_fragment": true,
            "learned_lrat_main_proof_authority_authorizes_main_proof_out": true,
            "external_proof_checker_verdict": "VERIFIED_UNSAT",
            "external_proof_checker_path": checker_path,
            "external_proof_checker_sha256": Solver::sha256_hex(b"checker"),
            "external_proof_checker_command": checker_command,
            "external_proof_checker_argv": [checker_path, checked_dimacs_path, proof_out_path],
            "external_proof_checker_dimacs_path": checked_dimacs_path,
            "external_proof_checker_dimacs_sha256": Solver::sha256_hex(b"p cnf 1 2\n1 0\n-1 0\n"),
            "checker_exit_code": 0,
            "learned_lrat_main_proof_authority_proof_out_path": proof_out_path,
            "learned_lrat_main_proof_authority_proof_out_sha256": Solver::sha256_hex(proof_out),
        })
    }

    #[test]
    fn fmla_authority_replay_admits_authorized_checked_proof_out() {
        let _lock = lock_env();
        let dir = tempfile::tempdir().expect("tempdir");
        let proof_out_path = dir.path().join("proof.out");
        let proof_out = b"c checked proof\n9 1 0 1 0\n0 9 0\n";
        std::fs::write(&proof_out_path, proof_out).expect("write proof.out");
        let replay_path = dir
            .path()
            .join("fmla-main-lrat-postcheck-admission-replay.json");
        std::fs::write(
            &replay_path,
            fmla_authority_replay_payload(dir.path(), &proof_out_path, proof_out, 2).to_string(),
        )
        .expect("write replay");
        let _replay_guard = ScopedEnvVar::set(
            FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV,
            replay_path.to_str().expect("temp path is UTF-8"),
        );
        let _proof_guard = ScopedEnvVar::set(
            FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
            proof_out_path.to_str().expect("temp path is UTF-8"),
        );

        assert!(Solver::fmla_learned_lrat_main_proof_authority_replay_admits());
    }

    #[test]
    fn fmla_authority_replay_rejects_stale_proof_out_hash() {
        let _lock = lock_env();
        let dir = tempfile::tempdir().expect("tempdir");
        let proof_out_path = dir.path().join("proof.out");
        let proof_out = b"c checked proof\n9 1 0 1 0\n0 9 0\n";
        std::fs::write(&proof_out_path, proof_out).expect("write proof.out");
        let replay_path = dir
            .path()
            .join("fmla-main-lrat-postcheck-admission-replay.json");
        std::fs::write(
            &replay_path,
            fmla_authority_replay_payload(dir.path(), &proof_out_path, proof_out, 2).to_string(),
        )
        .expect("write replay");
        std::fs::write(&proof_out_path, b"c stale proof\n").expect("rewrite proof.out");
        let _replay_guard = ScopedEnvVar::set(
            FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV,
            replay_path.to_str().expect("temp path is UTF-8"),
        );
        let _proof_guard = ScopedEnvVar::set(
            FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
            proof_out_path.to_str().expect("temp path is UTF-8"),
        );

        assert!(!Solver::fmla_learned_lrat_main_proof_authority_replay_admits());
    }

    #[test]
    fn fmla_authority_replay_rejects_zero_checked_rows() {
        let _lock = lock_env();
        let dir = tempfile::tempdir().expect("tempdir");
        let proof_out_path = dir.path().join("proof.out");
        let proof_out = b"c checked proof\n";
        std::fs::write(&proof_out_path, proof_out).expect("write proof.out");
        let replay_path = dir
            .path()
            .join("fmla-main-lrat-postcheck-admission-replay.json");
        std::fs::write(
            &replay_path,
            fmla_authority_replay_payload(dir.path(), &proof_out_path, proof_out, 0).to_string(),
        )
        .expect("write replay");
        let _replay_guard = ScopedEnvVar::set(
            FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV,
            replay_path.to_str().expect("temp path is UTF-8"),
        );
        let _proof_guard = ScopedEnvVar::set(
            FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
            proof_out_path.to_str().expect("temp path is UTF-8"),
        );

        assert!(!Solver::fmla_learned_lrat_main_proof_authority_replay_admits());
    }

    #[test]
    fn fmla_authority_replay_rejects_missing_checker_verdict_artifact() {
        let _lock = lock_env();
        let dir = tempfile::tempdir().expect("tempdir");
        let proof_out_path = dir.path().join("proof.out");
        let proof_out = b"c checked proof\n9 1 0 1 0\n0 9 0\n";
        std::fs::write(&proof_out_path, proof_out).expect("write proof.out");
        let replay_path = dir
            .path()
            .join("fmla-main-lrat-postcheck-admission-replay.json");
        std::fs::write(
            &replay_path,
            fmla_authority_replay_payload(dir.path(), &proof_out_path, proof_out, 2).to_string(),
        )
        .expect("write replay");
        std::fs::remove_file(
            dir.path()
                .join("fmla-main-lrat-external-checker-verdict.json"),
        )
        .expect("remove retained checker verdict artifact");
        let _replay_guard = ScopedEnvVar::set(
            FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV,
            replay_path.to_str().expect("temp path is UTF-8"),
        );
        let _proof_guard = ScopedEnvVar::set(
            FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
            proof_out_path.to_str().expect("temp path is UTF-8"),
        );

        assert!(!Solver::fmla_learned_lrat_main_proof_authority_replay_admits());
    }

    #[test]
    fn fmla_authority_replay_rejects_different_current_proof_path() {
        let _lock = lock_env();
        let dir = tempfile::tempdir().expect("tempdir");
        let proof_out_path = dir.path().join("proof.out");
        let other_proof_out_path = dir.path().join("other-proof.out");
        let proof_out = b"c checked proof\n9 1 0 1 0\n0 9 0\n";
        std::fs::write(&proof_out_path, proof_out).expect("write proof.out");
        std::fs::write(&other_proof_out_path, proof_out).expect("write other proof.out");
        let replay_path = dir
            .path()
            .join("fmla-main-lrat-postcheck-admission-replay.json");
        std::fs::write(
            &replay_path,
            fmla_authority_replay_payload(dir.path(), &proof_out_path, proof_out, 2).to_string(),
        )
        .expect("write replay");
        let _replay_guard = ScopedEnvVar::set(
            FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV,
            replay_path.to_str().expect("temp path is UTF-8"),
        );
        let _proof_guard = ScopedEnvVar::set(
            FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
            other_proof_out_path
                .to_str()
                .expect("other proof out path utf8"),
        );

        assert!(!Solver::fmla_learned_lrat_main_proof_authority_replay_admits());
    }

    // ── #core-subset-audit ────────────────────────────────────────────────
    //
    // `declare_unsat_assume` downgrades an UNSAT verdict whose core is not a
    // subset of `cold.prev_assumptions`. That is only sound because every call
    // site passing a non-empty core sits inside a function that refreshed
    // `prev_assumptions` from this query's own assumptions first. The guard
    // below re-derives that containment property from the source on every run,
    // so the argument written up in `declare_unsat_assume` cannot silently rot.

    /// A `declare_unsat_assume(<arg>)` call site found in the crate source.
    #[derive(Debug)]
    struct DeclareUnsatAssumeCall {
        /// Path relative to `crates/ay-sat/src`, always `/`-separated.
        rel_path: String,
        /// 1-based line number.
        line: usize,
        /// Whitespace-stripped source text of the first argument.
        arg: String,
    }

    fn ay_sat_src_root() -> std::path::PathBuf {
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src")
    }

    fn ay_sat_rust_sources() -> Vec<std::path::PathBuf> {
        fn walk(dir: &std::path::Path, out: &mut Vec<std::path::PathBuf>) {
            for entry in std::fs::read_dir(dir).expect("read ay-sat src dir") {
                let path = entry.expect("dir entry").path();
                if path.is_dir() {
                    walk(&path, out);
                } else if path.extension().and_then(|ext| ext.to_str()) == Some("rs") {
                    out.push(path);
                }
            }
        }
        let mut out = Vec::new();
        walk(&ay_sat_src_root(), &mut out);
        out.sort();
        out
    }

    // The scanner searches this very crate, so its own needles must never
    // appear verbatim in the source or it would match itself. Assemble them
    // from fragments; do not collapse these back into single literals.
    fn call_needle() -> String {
        format!("declare_unsat_{}", "assume(")
    }

    fn definition_needle() -> String {
        format!("fn declare_unsat_{}", "assume(")
    }

    fn refresh_needle() -> String {
        format!("self.cold.{}", "prev_assumptions.clear();")
    }

    /// Line ranges (1-based, inclusive) of top-level `#[cfg(test)]` modules.
    /// Call sites inside them are exempt: test code sets `prev_assumptions`
    /// explicitly and is not a production path into the audit.
    fn cfg_test_module_ranges(src: &str) -> Vec<(usize, usize)> {
        let lines: Vec<&str> = src.lines().collect();
        let mut ranges = Vec::new();
        let mut idx = 0;
        while idx < lines.len() {
            if lines[idx] == "#[cfg(test)]" {
                let mut header = idx + 1;
                while header < lines.len() && lines[header].starts_with("#[") {
                    header += 1;
                }
                let is_module = header < lines.len()
                    && !lines[header].starts_with(' ')
                    && lines[header].contains("mod ")
                    && lines[header].ends_with('{');
                if is_module {
                    let mut end = header + 1;
                    while end < lines.len() && lines[end] != "}" {
                        end += 1;
                    }
                    ranges.push((idx + 1, end + 1));
                    idx = end + 1;
                    continue;
                }
            }
            idx += 1;
        }
        ranges
    }

    /// Every `declare_unsat_assume(...)` call site in `ay-sat` production code,
    /// excluding the definition, comment mentions, and `#[cfg(test)]` modules.
    /// A call whose argument is split across lines yields an empty `arg`, which
    /// the guard treats as non-`vec![]` — conservative in the direction that
    /// fails rather than passes.
    fn declare_unsat_assume_calls() -> Vec<DeclareUnsatAssumeCall> {
        let needle = call_needle();
        let definition = definition_needle();
        let root = ay_sat_src_root();
        let mut calls = Vec::new();
        for path in ay_sat_rust_sources() {
            let src = std::fs::read_to_string(&path).expect("read rust source");
            let test_ranges = cfg_test_module_ranges(&src);
            let rel_path = path
                .strip_prefix(&root)
                .unwrap_or(&path)
                .to_string_lossy()
                .replace('\\', "/");
            for (idx, line) in src.lines().enumerate() {
                if line.trim_start().starts_with("//") || line.contains(&definition) {
                    continue;
                }
                let line_no = idx + 1;
                if test_ranges
                    .iter()
                    .any(|(start, end)| line_no >= *start && line_no <= *end)
                {
                    continue;
                }
                let Some(pos) = line.find(&needle) else {
                    continue;
                };
                let after = &line[pos + needle.len()..];
                let end = after.find(')').unwrap_or(after.len());
                calls.push(DeclareUnsatAssumeCall {
                    rel_path: rel_path.clone(),
                    line: idx + 1,
                    arg: after[..end].split_whitespace().collect::<String>(),
                });
            }
        }
        calls
    }

    /// True if `line` starts a method at `impl`-block indentation (4 spaces).
    fn is_impl_method_start(line: &str) -> bool {
        let Some(rest) = line.strip_prefix("    ") else {
            return false;
        };
        if rest.starts_with(' ') {
            return false; // nested deeper than the impl block
        }
        let mut rest = rest;
        if let Some(after_pub) = rest.strip_prefix("pub") {
            let after_pub = after_pub.trim_start();
            rest = match after_pub.strip_prefix('(') {
                Some(restriction) => match restriction.find(')') {
                    Some(close) => restriction[close + 1..].trim_start(),
                    None => return false,
                },
                None => after_pub,
            };
        }
        for keyword in ["default ", "const ", "async ", "unsafe ", "extern "] {
            rest = rest.strip_prefix(keyword).unwrap_or(rest).trim_start();
        }
        rest.starts_with("fn ")
    }

    /// 1-based inclusive line range of the unique method whose signature line
    /// contains `signature`. The end is the line before the next method in the
    /// same `impl` block (or EOF), so the range can overshoot the body by the
    /// next method's doc comment — harmless, since comments are not call sites.
    fn impl_method_line_range(src: &str, signature: &str) -> (usize, usize) {
        let lines: Vec<&str> = src.lines().collect();
        let starts: Vec<usize> = (0..lines.len())
            .filter(|&idx| is_impl_method_start(lines[idx]))
            .collect();
        let matching: Vec<usize> = starts
            .iter()
            .copied()
            .filter(|&idx| lines[idx].contains(signature))
            .collect();
        assert_eq!(
            matching.len(),
            1,
            "expected exactly one method signature containing {signature:?}, got lines {:?}",
            matching.iter().map(|idx| idx + 1).collect::<Vec<_>>(),
        );
        let start = matching[0];
        let end = starts
            .iter()
            .copied()
            .find(|&idx| idx > start)
            .unwrap_or(lines.len());
        (start + 1, end)
    }

    /// 1-based line of the unique `prev_assumptions` refresh inside `range`.
    fn unique_prev_assumptions_refresh(src: &str, range: (usize, usize)) -> usize {
        let needle = refresh_needle();
        let hits: Vec<usize> = src
            .lines()
            .enumerate()
            .map(|(idx, line)| (idx + 1, line))
            .filter(|(line_no, line)| {
                *line_no >= range.0
                    && *line_no <= range.1
                    && line.contains(&needle)
                    && !line.trim_start().starts_with("//")
            })
            .map(|(line_no, _)| line_no)
            .collect();
        assert_eq!(
            hits.len(),
            1,
            "expected exactly one `prev_assumptions` refresh in lines {range:?}, found {hits:?}"
        );
        hits[0]
    }

    /// Guards the containment property that licenses the enforcing
    /// `#core-subset-audit` in `declare_unsat_assume`: every call passing a
    /// NON-EMPTY core must lie inside `solve_with_assumptions_impl` or
    /// `solve_incremental_ic3_raw`, after that function's unconditional
    /// `cold.prev_assumptions` refresh. If this fails, do not "fix" the test —
    /// either restore containment or the audit must go back to observe-only.
    #[test]
    fn core_subset_audit_containment_guard() {
        let root = ay_sat_src_root();
        let assumptions_src = std::fs::read_to_string(root.join("solver/assumptions.rs"))
            .expect("read solver/assumptions.rs");
        let ic3_src =
            std::fs::read_to_string(root.join("solver/solve/ic3.rs")).expect("read solve/ic3.rs");

        let assume_range =
            impl_method_line_range(&assumptions_src, "fn solve_with_assumptions_impl");
        let ic3_range = impl_method_line_range(&ic3_src, "fn solve_incremental_ic3_raw");
        let assume_refresh = unique_prev_assumptions_refresh(&assumptions_src, assume_range);
        let ic3_refresh = unique_prev_assumptions_refresh(&ic3_src, ic3_range);

        // Nothing else in the crate may rewrite the audit's reference set.
        let refresh = refresh_needle();
        let total_refreshes: usize = ay_sat_rust_sources()
            .iter()
            .map(|path| {
                std::fs::read_to_string(path)
                    .expect("read rust source")
                    .matches(refresh.as_str())
                    .count()
            })
            .sum();
        assert_eq!(
            total_refreshes, 2,
            "`cold.prev_assumptions` is now refreshed somewhere beyond \
             solve_with_assumptions_impl and solve_incremental_ic3_raw; re-check the \
             #core-subset-audit containment argument in declare_unsat_assume"
        );

        let windows = [
            ("solver/assumptions.rs", assume_range, assume_refresh),
            ("solver/solve/ic3.rs", ic3_range, ic3_refresh),
        ];

        let calls = declare_unsat_assume_calls();
        assert!(
            calls.len() > 10,
            "source scan found only {} declare_unsat_assume call sites; the scanner is \
             probably broken rather than the invariant",
            calls.len()
        );

        let mut nonempty = 0usize;
        let mut violations = Vec::new();
        for call in &calls {
            if call.arg == "vec![]" {
                continue;
            }
            nonempty += 1;
            let contained = windows.iter().any(|(file, (start, end), refresh)| {
                call.rel_path == *file
                    && call.line >= *start
                    && call.line <= *end
                    && call.line > *refresh
            });
            if !contained {
                violations.push(format!(
                    "{}:{} passes `{}`",
                    call.rel_path, call.line, call.arg
                ));
            }
        }

        assert!(
            nonempty >= 12,
            "expected at least the 12 known non-empty-core call sites to still exist, \
             found {nonempty}; the scanner is probably broken"
        );
        assert!(
            violations.is_empty(),
            "#core-subset-audit CONTAINMENT BROKEN: declare_unsat_assume is called with a \
             non-empty core outside solve_with_assumptions_impl \
             (solver/assumptions.rs:{}-{}, refresh at :{}) and solve_incremental_ic3_raw \
             (solver/solve/ic3.rs:{}-{}, refresh at :{}). Such a call site can observe a \
             STALE cold.prev_assumptions, which would make the enforcing audit downgrade \
             CORRECT UNSAT answers to Unknown. Offenders: {violations:?}",
            assume_range.0,
            assume_range.1,
            assume_refresh,
            ic3_range.0,
            ic3_range.1,
            ic3_refresh,
        );
    }

    #[test]
    fn core_subset_audit_downgrades_stray_core_literal() {
        let mut solver = Solver::new(4);
        let assumed = Literal::positive(Variable::new(0));
        let stray = Literal::positive(Variable::new(1));
        solver.cold.prev_assumptions.clear();
        solver.cold.prev_assumptions.push(assumed);

        // `stray` was never assumed, so {assumed, stray} is not a certified
        // unsatisfiable subset of this query's assumptions.
        let result = solver.declare_unsat_assume(vec![assumed, stray]);

        assert!(
            matches!(result, AssumeResult::Unknown),
            "a core literal that is not an assumption must downgrade UNSAT to Unknown, \
             got {result:?}"
        );
        assert_eq!(
            solver.cold.last_unknown_reason,
            Some(SatUnknownReason::InvalidUnsatCore),
        );
    }

    #[test]
    fn core_subset_audit_accepts_genuine_subset_core() {
        let mut solver = Solver::new(4);
        let a = Literal::positive(Variable::new(0));
        let b = Literal::negative(Variable::new(1));
        solver.cold.prev_assumptions.clear();
        solver.cold.prev_assumptions.extend_from_slice(&[a, b]);

        let result = solver.declare_unsat_assume(vec![a]);

        assert!(
            matches!(result, AssumeResult::Unsat(..)),
            "a core that is a subset of this query's assumptions must stay UNSAT, \
             got {result:?}"
        );
    }
}
