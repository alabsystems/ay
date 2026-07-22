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
use crate::solver::backward_proof::BackwardProofResult;
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
        self.finalize_streaming_core();
        if let Some(core) = self.extract_streaming_core() {
            certificate.set_streaming_core(core);
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
            if let Some(ref mut manager) = self.proof_manager {
                manager.clear_last_add();
            }
            // Write empty clause to indicate final derivation of contradiction,
            // unless mark_empty_clause already wrote it (#4123).
            if !self.cold.empty_clause_in_proof {
                // In LRAT mode, build hints for the empty clause from
                // level-0 trail state (#7108). Without hints, external LRAT
                // checkers reject the empty clause derivation.
                #[allow(unused_mut)] // mut needed in debug builds for assumption hint prepend
                let mut hints = if self.cold.lrat_enabled {
                    self.ensure_level0_unit_proof_ids();
                    self.build_finalize_empty_clause_hints()
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
                && !Self::fmla_learned_lrat_main_proof_authority_replay_admits()
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
        self.maybe_append_authorized_fmla_learned_lrat_materialization();

        // Run backward LRAT reconstruction BEFORE finalize_unsat_proof (same
        // ordering as declare_unsat) so the proof certificate captures the full
        // derivation chain. This enables proof-based UNSAT core extraction
        // via ProofCertificate::minimal_core() (#8209).
        let backward_result = self.run_backward_proof_reconstruction();
        if let Err(error) = self.finalize_unsat_proof() {
            return self.declare_assume_proof_finalization_unknown(error);
        }
        self.tla_trace_step(CdclTraceState::Unsat, Some(CdclTraceAction::DeclareUnsat));
        self.emit_diagnostic_unsat_summary();

        self.finalize_streaming_core();
        let streaming_core = self.extract_streaming_core();
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
                if cid > 0 && cid <= num_originals {
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
                if reason_id > 0 && reason_id <= num_originals {
                    ids_to_mark.push(reason_id);
                }
            }

            // Check signed unit proof IDs (for clauses whose arena reference was cleared).
            let lit = self.trail[i];
            if let Some(pid) = self.visible_unit_proof_id_for_lit(lit) {
                if pid > 0 && pid <= num_originals {
                    ids_to_mark.push(pid);
                }
            }

            // Check signed level0_proof_id fallback.
            if let Some(pid) = self.level0_var_proof_id_for_lit(lit) {
                if pid > 0 && pid <= num_originals {
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
    use serde_json::json;

    struct EnvGuard {
        key: &'static str,
        previous: Option<std::ffi::OsString>,
    }

    impl EnvGuard {
        fn capture(key: &'static str) -> Self {
            let previous = std::env::var_os(key);
            std::env::remove_var(key);
            Self { key, previous }
        }
    }

    impl Drop for EnvGuard {
        fn drop(&mut self) {
            if let Some(previous) = self.previous.take() {
                std::env::set_var(self.key, previous);
            } else {
                std::env::remove_var(self.key);
            }
        }
    }

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
        let _lock = crate::fmla_runtime_ledger::FMLA_LEARNED_LRAT_ENV_TEST_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let _replay_guard =
            EnvGuard::capture(FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV);
        let _proof_guard = EnvGuard::capture(FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV);
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
        std::env::set_var(
            FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV,
            &replay_path,
        );
        std::env::set_var(
            FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
            &proof_out_path,
        );

        assert!(Solver::fmla_learned_lrat_main_proof_authority_replay_admits());
    }

    #[test]
    fn fmla_authority_replay_rejects_stale_proof_out_hash() {
        let _lock = crate::fmla_runtime_ledger::FMLA_LEARNED_LRAT_ENV_TEST_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let _replay_guard =
            EnvGuard::capture(FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV);
        let _proof_guard = EnvGuard::capture(FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV);
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
        std::env::set_var(
            FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV,
            &replay_path,
        );
        std::env::set_var(
            FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
            &proof_out_path,
        );

        assert!(!Solver::fmla_learned_lrat_main_proof_authority_replay_admits());
    }

    #[test]
    fn fmla_authority_replay_rejects_zero_checked_rows() {
        let _lock = crate::fmla_runtime_ledger::FMLA_LEARNED_LRAT_ENV_TEST_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let _replay_guard =
            EnvGuard::capture(FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV);
        let _proof_guard = EnvGuard::capture(FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV);
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
        std::env::set_var(
            FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV,
            &replay_path,
        );
        std::env::set_var(
            FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
            &proof_out_path,
        );

        assert!(!Solver::fmla_learned_lrat_main_proof_authority_replay_admits());
    }

    #[test]
    fn fmla_authority_replay_rejects_missing_checker_verdict_artifact() {
        let _lock = crate::fmla_runtime_ledger::FMLA_LEARNED_LRAT_ENV_TEST_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let _replay_guard =
            EnvGuard::capture(FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV);
        let _proof_guard = EnvGuard::capture(FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV);
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
        std::env::set_var(
            FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV,
            &replay_path,
        );
        std::env::set_var(
            FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
            &proof_out_path,
        );

        assert!(!Solver::fmla_learned_lrat_main_proof_authority_replay_admits());
    }

    #[test]
    fn fmla_authority_replay_rejects_different_current_proof_path() {
        let _lock = crate::fmla_runtime_ledger::FMLA_LEARNED_LRAT_ENV_TEST_LOCK
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let _replay_guard =
            EnvGuard::capture(FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV);
        let _proof_guard = EnvGuard::capture(FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV);
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
        std::env::set_var(
            FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_PATH_ENV,
            &replay_path,
        );
        std::env::set_var(
            FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_PATH_ENV,
            &other_proof_out_path,
        );

        assert!(!Solver::fmla_learned_lrat_main_proof_authority_replay_admits());
    }
}
