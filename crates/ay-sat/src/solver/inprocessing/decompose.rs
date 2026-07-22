// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SCC-based equivalent literal substitution (decompose).

use super::super::mutate::{AddResult, ReasonPolicy};
use super::super::*;
use crate::decompose::{
    DecomposeLratDryRunSidecar, DecomposeLratEquivalenceStep, DecomposeProofEmitContext,
    FmlaGuardedEquivLiftPreflight, FmlaGuardedEquivOverlayLratBinaryRow,
    FmlaGuardedEquivOverlayLratSidecar, FmlaGuardedEquivSupportCoverLratSidecar,
};
use crate::fmla_guarded_equiv_scout::{FmlaGuardedEquivScout, FmlaGuardedEquivWitnesses};
use crate::fmla_ledger_preview::FmlaLedgerPreview;
use crate::fmla_runtime_ledger::{
    materialize_fmla_guarded_equiv_lrat_records, materialize_main_lrat_rewrite_records,
    FmlaRuntimeLedger, MainProofRewriteLedgerMaterializerConfig,
    MainProofRewriteLedgerMaterializerReject, SourceBoundMultiplierOriginalSourceBindingReject,
};
use crate::preprocess_transaction::{
    ModelReconstructionWitnessStatus, PlannedSubstitution, PreprocessPass,
    PreprocessTransactionDraft, PreprocessTransactionId, ProofObligationStatus,
    RouteAdmissionPacket, RouteAdmissionPacketKind, RouteAdmissionPacketStatus,
};
use crate::proof_manager::PlannedForwardAddReject;

pub(crate) const FMLA_MAIN_LRAT_PREFLIGHT_MAX_PROOF_ROWS: usize = 2_048;

#[derive(Clone, Debug, PartialEq, Eq)]
enum DecomposeLratTransactionReject {
    MissingProofManager,
    NoSubstitution,
    MissingOrHiddenSourceId { clause_idx: usize, clause_id: u64 },
    MissingChain { literal: Literal },
    MissingChainSourceId { clause_ref: u32, clause_id: u64 },
    NoSubstitutedLiteral { clause_idx: usize },
    MissingSubstitutionHint { literal: Literal },
    MissingVisibleLevel0Unit { literal: Literal, proof_id: u64 },
    MissingTransientEquivalenceId { literal: Literal },
    MalformedRewrite { clause_idx: usize },
    Contradiction,
    PlannedAddRejected(PlannedForwardAddReject),
}

impl Solver {
    // ==================== Decompose (SCC Equivalent Literal Substitution) ====================

    /// Run decompose and reschedule with growing backoff.
    ///
    /// Callers are responsible for applying any scheduling gate before entry.
    /// This preserves forced follow-up rewrites after congruence or sweep even
    /// when the regular interval is not due yet.
    ///
    /// Uses growing backoff when unproductive (no equivalences found): the
    /// interval grows 1.5× per idle call, up to DECOMPOSE_MAX_INTERVAL.
    /// Productive calls reset to base interval. This reduces overhead from
    /// repeated no-op SCC traversals on formulas where decompose finds
    /// equivalences only in early rounds (e.g., FmlaEquivChain: 39 rounds
    /// with 976ms total, most rounds finding 0 equivalences).
    pub(in crate::solver) fn decompose(&mut self) {
        let productive = self.decompose_body();
        if productive {
            self.inproc_ctrl
                .decompose
                .reschedule(self.num_conflicts, DECOMPOSE_INTERVAL);
        } else {
            self.inproc_ctrl.decompose.reschedule_growing(
                self.num_conflicts,
                DECOMPOSE_INTERVAL,
                3,
                2, // 1.5× growth
                DECOMPOSE_MAX_INTERVAL,
            );
        }
    }

    pub(in crate::solver) fn run_fmla_decompose_lrat_preflight_route(
        &mut self,
        passes_run: &mut Vec<&'static str>,
    ) -> bool {
        if !self.fmla_decompose_lrat_preflight_route_active() || self.is_interrupted() {
            return false;
        }
        if !self.require_level_zero() {
            return false;
        }

        self.cold.fmla_decompose_lrat_preflight_route_consumed = true;
        self.stats
            .record_inprocessing_attempt(DiagnosticPass::Decompose);

        let materializer_before = self
            .inproc
            .decompose_engine
            .lrat_main_rewrite_materializer_preflight_enabled();
        self.inproc
            .decompose_engine
            .clear_fmla_guarded_equiv_overlay_lrat_sidecars();
        self.inproc
            .decompose_engine
            .set_lrat_main_rewrite_materializer_preflight_enabled(true);
        self.record_fmla_guarded_equiv_lift_preflight();
        self.record_fmla_guarded_equiv_overlay_lrat_packet();
        let fmla_route_emitted = self.try_emit_fmla_guarded_equiv_overlay_lrat_runtime_rows();
        if fmla_route_emitted {
            self.inproc.decompose_engine.record_lrat_preflight_attempt();
        } else if let Err(reject) = self.preflight_decompose_lrat_transaction() {
            self.record_decompose_lrat_preflight_reject(&reject);
        }
        self.inproc
            .decompose_engine
            .set_lrat_main_rewrite_materializer_preflight_enabled(materializer_before);
        passes_run.push("decompose-lrat-preflight");
        false
    }

    pub(in crate::solver) fn record_fmla_guarded_equiv_lift_preflight(&mut self) {
        let clauses: Vec<Vec<Literal>> = self
            .cold
            .original_ledger
            .iter_clauses()
            .map(<[Literal]>::to_vec)
            .collect();
        let scout = FmlaGuardedEquivScout::scan(self.num_vars, &clauses);
        let preview = FmlaLedgerPreview::from_scout(&scout);
        let all_witnesses = FmlaGuardedEquivWitnesses::scan_all(&clauses);
        let source_audit = all_witnesses.source_audit(|source_id| {
            let source_id = source_id as u64;
            self.lrat_hint_id_visible(source_id)
                && self
                    .proof_manager
                    .as_ref()
                    .is_some_and(|manager| manager.is_known_lrat_id(source_id))
        });
        let mut runtime_ledger = FmlaRuntimeLedger::capture_only();
        let _ = runtime_ledger.capture_representative_guarded_equivalence(&clauses);
        let runtime_stats = runtime_ledger.stats();
        let proof_ready = u64::from(runtime_stats.proof_obligation_ready);
        let model_ready = u64::from(runtime_stats.model_reconstruction_ready);
        let destructive_allowed = u64::from(runtime_stats.destructive_transform_allowed);

        self.inproc
            .decompose_engine
            .record_fmla_guarded_equiv_lift_preflight(FmlaGuardedEquivLiftPreflight {
                attempts: 1,
                detected: u64::from(scout.detected()),
                rejection_code: scout.rejection.code(),
                onehot_groups: scout.onehot_groups as u64,
                guarded_equiv_pairs: scout.guarded_equivalence_pairs as u64,
                guarded_equiv_guards: scout.guarded_equivalence_guards as u64,
                directional_ternary_witnesses: preview
                    .source_counts
                    .directional_ternary_clause_witnesses
                    as u64,
                touched_vars: preview.source_counts.touched_vars as u64,
                runtime_records: runtime_stats.records_emitted,
                witness_checker_passed: runtime_stats.witness_checker_passed,
                all_witness_pairs_checked: source_audit.witness_pairs_checked as u64,
                all_witness_pairs_missing_guard_group: source_audit
                    .witness_pairs_missing_guard_group
                    as u64,
                source_id_refs_checked: source_audit.source_id_refs_checked as u64,
                unique_source_ids_checked: source_audit.unique_source_ids_checked as u64,
                source_ids_checked: source_audit.unique_source_ids_checked as u64,
                source_ids_visible: source_audit.source_ids_visible as u64,
                source_ids_missing: source_audit.source_ids_missing as u64,
                first_missing_source_id: source_audit.first_missing_source_id as u64,
                proof_ready,
                model_ready,
                destructive_allowed,
            });
    }

    pub(in crate::solver) fn record_fmla_guarded_equiv_overlay_lrat_packet(&mut self) {
        self.inproc
            .decompose_engine
            .clear_fmla_guarded_equiv_overlay_lrat_sidecars();
        if !self.cold.lrat_enabled || self.proof_manager.is_none() {
            return;
        }
        self.ensure_level0_unit_proof_ids();

        let clauses: Vec<Vec<Literal>> = self
            .cold
            .original_ledger
            .iter_clauses()
            .map(<[Literal]>::to_vec)
            .collect();
        let witnesses = FmlaGuardedEquivWitnesses::scan_all(&clauses);

        struct OverlayCandidate {
            guard: i32,
            lhs: i32,
            rhs: i32,
            guard_unit_proof_id: u64,
            forward_source_id: u64,
            reverse_source_id: u64,
            forward_clause: [Literal; 2],
            reverse_clause: [Literal; 2],
        }

        struct SupportCoverCandidate {
            support_clause_id: u64,
            support_guards: Vec<i64>,
            source_lit: i64,
            destination_lits: Vec<i64>,
            directional_source_ids: Vec<u64>,
            clause: Vec<Literal>,
            hints: Vec<u64>,
        }

        let mut candidates = Vec::new();
        for witness in &witnesses.guarded_equivalences {
            let guard_lit = Literal::from_dimacs(witness.guard);
            let Some(guard_unit_proof_id) = self.level0_var_proof_id_for_lit(guard_lit) else {
                continue;
            };
            if !self.fmla_overlay_source_id_visible(guard_unit_proof_id) {
                continue;
            }
            let forward_source_id = witness.forward_clause_id as u64;
            if !self.fmla_overlay_source_id_visible(forward_source_id) {
                continue;
            }
            let reverse_source_id = witness.reverse_clause_id as u64;
            if !self.fmla_overlay_source_id_visible(reverse_source_id) {
                continue;
            }

            let lhs_lit = Literal::from_dimacs(witness.lhs);
            let rhs_lit = Literal::from_dimacs(witness.rhs);
            candidates.push(OverlayCandidate {
                guard: witness.guard,
                lhs: witness.lhs,
                rhs: witness.rhs,
                guard_unit_proof_id,
                forward_source_id,
                reverse_source_id,
                forward_clause: [lhs_lit.negated(), rhs_lit],
                reverse_clause: [rhs_lit.negated(), lhs_lit],
            });
        }

        let mut support_candidates = Vec::new();
        for witness in witnesses.support_cover_witnesses() {
            let support_clause_id = witness.support_clause_id as u64;
            if !self.fmla_overlay_source_id_visible(support_clause_id) {
                continue;
            }
            let mut directional_source_ids =
                Vec::with_capacity(witness.ternary_source_clause_ids.len());
            let mut all_sources_visible = true;
            for source_id in witness.ternary_source_clause_ids {
                let source_id = source_id as u64;
                if !self.fmla_overlay_source_id_visible(source_id) {
                    all_sources_visible = false;
                    break;
                }
                directional_source_ids.push(source_id);
            }
            if !all_sources_visible {
                continue;
            }
            let clause: Vec<_> = witness
                .clause_lits
                .iter()
                .copied()
                .map(Literal::from_dimacs)
                .collect();
            let mut hints = directional_source_ids.clone();
            hints.push(support_clause_id);
            support_candidates.push(SupportCoverCandidate {
                support_clause_id,
                support_guards: witness
                    .guard_vars
                    .iter()
                    .map(|&lit| i64::from(lit))
                    .collect(),
                source_lit: i64::from(witness.source_var),
                destination_lits: witness
                    .destination_vars
                    .iter()
                    .map(|&lit| i64::from(lit))
                    .collect(),
                directional_source_ids,
                clause,
                hints,
            });
        }

        let mut remaining_rows = FMLA_MAIN_LRAT_PREFLIGHT_MAX_PROOF_ROWS;
        let max_overlay_candidates = remaining_rows / 2;
        if candidates.len() > max_overlay_candidates {
            candidates.truncate(max_overlay_candidates);
        }
        remaining_rows = remaining_rows.saturating_sub(candidates.len().saturating_mul(2));
        if support_candidates.len() > remaining_rows {
            support_candidates.truncate(remaining_rows);
        }

        if candidates.is_empty() && support_candidates.is_empty() {
            return;
        }

        if let Some(manager) = self.proof_manager.as_mut() {
            let _ = manager.flush();
        }
        let planned_add_count = candidates
            .len()
            .saturating_mul(2)
            .saturating_add(support_candidates.len());
        let planned_add_ids = match self
            .proof_manager
            .as_ref()
            .expect("proof manager checked above")
            .planned_forward_add_ids(planned_add_count)
        {
            Ok(ids) => ids,
            Err(_) => return,
        };

        let Some(manager) = self.proof_manager.as_ref() else {
            return;
        };
        let mut sidecars = Vec::with_capacity(candidates.len());
        let mut support_sidecars = Vec::with_capacity(support_candidates.len());
        let mut planned_visible_ids = Vec::with_capacity(planned_add_ids.len());
        for (candidate_idx, candidate) in candidates.iter().enumerate() {
            let add_cursor = candidate_idx.saturating_mul(2);
            let Some(&forward_add_id) = planned_add_ids.get(add_cursor) else {
                return;
            };
            let Some(&reverse_add_id) = planned_add_ids.get(add_cursor + 1) else {
                return;
            };

            let forward_hints = vec![candidate.forward_source_id, candidate.guard_unit_proof_id];
            if manager
                .preflight_forward_lrat_add_with_planned_ids(
                    &candidate.forward_clause,
                    &forward_hints,
                    ProofAddKind::Derived,
                    planned_visible_ids.as_slice(),
                )
                .is_err()
            {
                return;
            }
            planned_visible_ids.push(forward_add_id);

            let reverse_hints = vec![candidate.reverse_source_id, candidate.guard_unit_proof_id];
            if manager
                .preflight_forward_lrat_add_with_planned_ids(
                    &candidate.reverse_clause,
                    &reverse_hints,
                    ProofAddKind::Derived,
                    planned_visible_ids.as_slice(),
                )
                .is_err()
            {
                return;
            }
            planned_visible_ids.push(reverse_add_id);

            sidecars.push(FmlaGuardedEquivOverlayLratSidecar {
                guard_lit_dimacs: i64::from(candidate.guard),
                lhs_lit_dimacs: i64::from(candidate.lhs),
                rhs_lit_dimacs: i64::from(candidate.rhs),
                guard_unit_proof_id: candidate.guard_unit_proof_id,
                forward_binary: FmlaGuardedEquivOverlayLratBinaryRow {
                    planned_add_id: forward_add_id,
                    clause_lits_dimacs: candidate
                        .forward_clause
                        .iter()
                        .map(|lit| i64::from(lit.to_dimacs()))
                        .collect(),
                    guarded_ternary_source_id: candidate.forward_source_id,
                    guard_unit_proof_id: candidate.guard_unit_proof_id,
                    lrat_hints: forward_hints,
                },
                reverse_binary: FmlaGuardedEquivOverlayLratBinaryRow {
                    planned_add_id: reverse_add_id,
                    clause_lits_dimacs: candidate
                        .reverse_clause
                        .iter()
                        .map(|lit| i64::from(lit.to_dimacs()))
                        .collect(),
                    guarded_ternary_source_id: candidate.reverse_source_id,
                    guard_unit_proof_id: candidate.guard_unit_proof_id,
                    lrat_hints: reverse_hints,
                },
            });
        }
        let support_add_offset = candidates.len().saturating_mul(2);
        for (candidate_idx, candidate) in support_candidates.iter().enumerate() {
            let Some(&planned_add_id) = planned_add_ids.get(support_add_offset + candidate_idx)
            else {
                return;
            };
            if manager
                .preflight_forward_lrat_add_with_planned_ids(
                    &candidate.clause,
                    &candidate.hints,
                    ProofAddKind::Derived,
                    planned_visible_ids.as_slice(),
                )
                .is_err()
            {
                return;
            }
            planned_visible_ids.push(planned_add_id);
            support_sidecars.push(FmlaGuardedEquivSupportCoverLratSidecar {
                planned_add_id,
                support_clause_id: candidate.support_clause_id,
                support_guard_lits_dimacs: candidate.support_guards.clone(),
                source_lit_dimacs: candidate.source_lit,
                destination_lits_dimacs: candidate.destination_lits.clone(),
                clause_lits_dimacs: candidate
                    .clause
                    .iter()
                    .map(|lit| i64::from(lit.to_dimacs()))
                    .collect(),
                directional_ternary_source_ids: candidate.directional_source_ids.clone(),
                lrat_hints: candidate.hints.clone(),
            });
        }

        self.inproc
            .decompose_engine
            .set_fmla_guarded_equiv_overlay_lrat_sidecars(sidecars);
        self.inproc
            .decompose_engine
            .set_fmla_guarded_equiv_support_cover_lrat_sidecars(support_sidecars);
    }

    pub(in crate::solver) fn try_emit_fmla_guarded_equiv_overlay_lrat_runtime_rows(
        &mut self,
    ) -> bool {
        if !self
            .inproc
            .decompose_engine
            .lrat_main_rewrite_materializer_preflight_enabled()
        {
            return false;
        }
        if !self.cold.lrat_enabled || self.proof_manager.is_none() {
            return false;
        }

        let sidecars = self
            .inproc
            .decompose_engine
            .fmla_guarded_equiv_overlay_lrat_sidecars()
            .to_vec();
        let support_sidecars = self
            .inproc
            .decompose_engine
            .fmla_guarded_equiv_support_cover_lrat_sidecars()
            .to_vec();
        if sidecars.is_empty() && support_sidecars.is_empty() {
            return false;
        }

        let transaction_id = self.begin_fmla_guarded_equiv_overlay_lrat_preprocess_transaction(
            &sidecars,
            &support_sidecars,
        );
        let planned_binary_rows = sidecars.len().saturating_mul(2);
        let planned_proof_rows = planned_binary_rows.saturating_add(support_sidecars.len());
        let original_dimacs_rows = sidecars.len().saturating_add(support_sidecars.len());
        let mut emitted_proof_rows = 0usize;
        for sidecar in sidecars {
            for (direction, row) in [
                ("forward", &sidecar.forward_binary),
                ("reverse", &sidecar.reverse_binary),
            ] {
                if emitted_proof_rows.is_multiple_of(256) && self.is_interrupted() {
                    self.finish_fmla_guarded_equiv_overlay_lrat_route_record(
                        transaction_id,
                        original_dimacs_rows,
                        planned_proof_rows,
                        emitted_proof_rows,
                    );
                    return true;
                }
                let sidecar_row_index = emitted_proof_rows / 2;
                let context = DecomposeProofEmitContext::from_fmla_guarded_equiv_overlay_binary(
                    transaction_id.as_u64(),
                    sidecar_row_index,
                    direction,
                    row,
                );
                if !self.fmla_guarded_equiv_next_lrat_add_matches(row.planned_add_id) {
                    self.finish_fmla_guarded_equiv_overlay_lrat_route_record(
                        transaction_id,
                        original_dimacs_rows,
                        planned_proof_rows,
                        emitted_proof_rows,
                    );
                    return true;
                }
                let mut clause = Self::decompose_lrat_sidecar_literals(&row.clause_lits_dimacs);
                let Ok(emitted_id) = self.proof_emit_add_prechecked_with_decompose_context(
                    &clause,
                    &row.lrat_hints,
                    ProofAddKind::Derived,
                    &context,
                ) else {
                    self.finish_fmla_guarded_equiv_overlay_lrat_route_record(
                        transaction_id,
                        original_dimacs_rows,
                        planned_proof_rows,
                        emitted_proof_rows,
                    );
                    return true;
                };
                if emitted_id == 0 {
                    self.finish_fmla_guarded_equiv_overlay_lrat_route_record(
                        transaction_id,
                        original_dimacs_rows,
                        planned_proof_rows,
                        emitted_proof_rows,
                    );
                    return true;
                }
                if emitted_id != row.planned_add_id {
                    self.finish_fmla_guarded_equiv_overlay_lrat_route_record(
                        transaction_id,
                        original_dimacs_rows,
                        planned_proof_rows,
                        emitted_proof_rows,
                    );
                    return true;
                }
                if !self.install_fmla_guarded_equiv_lrat_clause(&mut clause, emitted_id) {
                    self.finish_fmla_guarded_equiv_overlay_lrat_route_record(
                        transaction_id,
                        original_dimacs_rows,
                        planned_proof_rows,
                        emitted_proof_rows,
                    );
                    return true;
                }
                emitted_proof_rows = emitted_proof_rows.saturating_add(1);
            }
        }
        for (sidecar_row_index, row) in support_sidecars.iter().enumerate() {
            if emitted_proof_rows.is_multiple_of(256) && self.is_interrupted() {
                self.finish_fmla_guarded_equiv_overlay_lrat_route_record(
                    transaction_id,
                    original_dimacs_rows,
                    planned_proof_rows,
                    emitted_proof_rows,
                );
                return true;
            }
            let context = DecomposeProofEmitContext::from_fmla_guarded_equiv_support_cover(
                transaction_id.as_u64(),
                sidecar_row_index,
                row,
            );
            if !self.fmla_guarded_equiv_next_lrat_add_matches(row.planned_add_id) {
                self.finish_fmla_guarded_equiv_overlay_lrat_route_record(
                    transaction_id,
                    original_dimacs_rows,
                    planned_proof_rows,
                    emitted_proof_rows,
                );
                return true;
            }
            let mut clause = Self::decompose_lrat_sidecar_literals(&row.clause_lits_dimacs);
            let Ok(emitted_id) = self.proof_emit_add_prechecked_with_decompose_context(
                &clause,
                &row.lrat_hints,
                ProofAddKind::Derived,
                &context,
            ) else {
                self.finish_fmla_guarded_equiv_overlay_lrat_route_record(
                    transaction_id,
                    original_dimacs_rows,
                    planned_proof_rows,
                    emitted_proof_rows,
                );
                return true;
            };
            if emitted_id == 0 {
                self.finish_fmla_guarded_equiv_overlay_lrat_route_record(
                    transaction_id,
                    original_dimacs_rows,
                    planned_proof_rows,
                    emitted_proof_rows,
                );
                return true;
            }
            if emitted_id != row.planned_add_id {
                self.finish_fmla_guarded_equiv_overlay_lrat_route_record(
                    transaction_id,
                    original_dimacs_rows,
                    planned_proof_rows,
                    emitted_proof_rows,
                );
                return true;
            }
            if !self.install_fmla_guarded_equiv_lrat_clause(&mut clause, emitted_id) {
                self.finish_fmla_guarded_equiv_overlay_lrat_route_record(
                    transaction_id,
                    original_dimacs_rows,
                    planned_proof_rows,
                    emitted_proof_rows,
                );
                return true;
            }
            emitted_proof_rows = emitted_proof_rows.saturating_add(1);
        }
        self.finish_fmla_guarded_equiv_overlay_lrat_route_record(
            transaction_id,
            original_dimacs_rows,
            planned_proof_rows,
            emitted_proof_rows,
        );
        true
    }

    fn fmla_guarded_equiv_next_lrat_add_matches(&self, planned_add_id: u64) -> bool {
        planned_add_id != 0
            && self
                .proof_manager
                .as_ref()
                .and_then(|manager| manager.planned_forward_add_ids(1).ok())
                .and_then(|ids| ids.first().copied())
                == Some(planned_add_id)
    }

    fn install_fmla_guarded_equiv_lrat_clause(
        &mut self,
        clause: &mut [Literal],
        emitted_id: u64,
    ) -> bool {
        if emitted_id == 0 {
            return false;
        }
        if self.cold.clause_ids.contains(&emitted_id) {
            return false;
        }

        if self.cold.lrat_enabled {
            self.cold.next_clause_id = emitted_id;
        }

        let add_result = self.add_clause_watched(clause);

        match add_result {
            AddResult::Added(cref) | AddResult::Unit(cref) => {
                if self.clause_id(cref) != emitted_id {
                    return false;
                }
                if self.cold.next_clause_id <= emitted_id {
                    self.cold.next_clause_id = emitted_id + 1;
                }
                let clause_idx = cref.0 as usize;
                let new_lits = self.arena.literals(clause_idx).to_vec();
                self.note_irredundant_clause_added_for_bve(clause_idx, &new_lits);
                self.provenance.tag(
                    clause_idx,
                    crate::clause_provenance::ClauseProvenance::Inprocessing,
                );
                true
            }
            AddResult::Empty => {
                if self.cold.next_clause_id <= emitted_id {
                    self.cold.next_clause_id = emitted_id + 1;
                }
                true
            }
        }
    }

    fn begin_fmla_guarded_equiv_overlay_lrat_preprocess_transaction(
        &mut self,
        sidecars: &[FmlaGuardedEquivOverlayLratSidecar],
        support_sidecars: &[FmlaGuardedEquivSupportCoverLratSidecar],
    ) -> PreprocessTransactionId {
        let mut touched = std::collections::BTreeSet::new();
        for sidecar in sidecars {
            for lit in [
                sidecar.guard_lit_dimacs,
                sidecar.lhs_lit_dimacs,
                sidecar.rhs_lit_dimacs,
            ] {
                touched.insert(Self::decompose_lrat_sidecar_literal(lit).variable().index());
            }
        }
        for sidecar in support_sidecars {
            for lit in sidecar
                .support_guard_lits_dimacs
                .iter()
                .chain(std::iter::once(&sidecar.source_lit_dimacs))
                .chain(sidecar.destination_lits_dimacs.iter())
            {
                touched.insert(
                    Self::decompose_lrat_sidecar_literal(*lit)
                        .variable()
                        .index(),
                );
            }
        }

        self.inproc
            .preprocess_transactions
            .begin(PreprocessTransactionDraft {
                mutation_epoch: self.cold.clause_db_changes,
                pass_name: PreprocessPass::Decompose,
                touched_variables: touched.into_iter().collect(),
                eliminated_variables: Vec::new(),
                equivalent_variables: Vec::new(),
                planned_substitutions: Vec::new(),
                proof_obligation: ProofObligationStatus::Pending,
                model_reconstruction_witness: ModelReconstructionWitnessStatus::NotApplicable,
            })
    }

    fn finish_fmla_guarded_equiv_overlay_lrat_route_record(
        &mut self,
        transaction_id: PreprocessTransactionId,
        original_dimacs_rows: usize,
        planned_proof_rows: usize,
        emitted_proof_rows: usize,
    ) {
        let sidecars = self
            .inproc
            .decompose_engine
            .fmla_guarded_equiv_overlay_lrat_sidecars()
            .to_vec();
        let support_sidecars = self
            .inproc
            .decompose_engine
            .fmla_guarded_equiv_support_cover_lrat_sidecars()
            .to_vec();
        let original_clause_authority_rows =
            Self::fmla_guarded_equiv_original_clause_authority_rows(&sidecars, &support_sidecars);
        let proof_records = self
            .proof_manager
            .as_ref()
            .map(|manager| manager.scoped_decompose_proof_emit_records().to_vec())
            .unwrap_or_default();
        let materialized = materialize_fmla_guarded_equiv_lrat_records(
            MainProofRewriteLedgerMaterializerConfig {
                enabled: true,
                require_external_checker_verdict: true,
                external_checker_verdict_artifact: None,
            },
            transaction_id.as_u64(),
            &sidecars,
            &support_sidecars,
            &proof_records,
        );
        let (status, materialized_records, external_proof_checker_verdict_artifact_rows) =
            match materialized {
                Ok(stats) => {
                    self.inproc
                        .decompose_engine
                        .record_lrat_main_rewrite_materializer_attempt(
                            stats.proof_emit_records_seen,
                            stats.records_materialized,
                        );
                    (
                        if planned_proof_rows != 0
                            && stats.records_materialized == planned_proof_rows as u64
                            && stats.external_checker_verdict_artifact_rows
                                == stats.records_materialized
                        {
                            RouteAdmissionPacketStatus::Complete
                        } else {
                            RouteAdmissionPacketStatus::Incomplete
                        },
                        stats.records_materialized,
                        stats.external_checker_verdict_artifact_rows,
                    )
                }
                Err(reject) => {
                    let materialized_records =
                        Self::decompose_main_lrat_rewrite_materialized_records(&reject);
                    self.inproc
                        .decompose_engine
                        .record_lrat_main_rewrite_materializer_attempt(
                            proof_records.len() as u64,
                            materialized_records,
                        );
                    let (sidecar_row_index, checker_visible_id) =
                        Self::decompose_main_lrat_rewrite_reject_identity(&reject);
                    self.inproc
                        .decompose_engine
                        .record_lrat_main_rewrite_materializer_fail_closed_detail(
                            Self::decompose_main_lrat_rewrite_missing_runtime_record(&reject),
                            sidecar_row_index,
                            checker_visible_id,
                        );
                    (
                        RouteAdmissionPacketStatus::Rejected,
                        materialized_records,
                        0,
                    )
                }
            };
        let all_rows_emitted = planned_proof_rows != 0
            && emitted_proof_rows == planned_proof_rows
            && materialized_records == planned_proof_rows as u64;
        self.inproc
            .decompose_engine
            .record_fmla_guarded_equiv_lift_route_readiness(
                all_rows_emitted,
                all_rows_emitted,
                false,
            );
        let proof_obligation = if all_rows_emitted {
            ProofObligationStatus::Satisfied
        } else {
            ProofObligationStatus::Rejected
        };
        self.inproc
            .preprocess_transactions
            .set_proof_obligation(transaction_id, proof_obligation);
        let _ = self
            .inproc
            .preprocess_transactions
            .set_route_admission_packet(
                transaction_id,
                RouteAdmissionPacket {
                    kind: RouteAdmissionPacketKind::FmlaEquivChainMainLrat,
                    status,
                    original_dimacs_rows: original_dimacs_rows as u64,
                    original_clause_authority_rows,
                    proof_obligation_rows: planned_proof_rows as u64,
                    model_reconstruction_rows: 0,
                    external_proof_checker_verdict_artifact_rows,
                },
            );
        if status == RouteAdmissionPacketStatus::Complete {
            if self
                .inproc
                .preprocess_transactions
                .commit(transaction_id)
                .is_err()
            {}
        } else {
            let reason = if all_rows_emitted {
                "fmla guarded-equivalence overlay LRAT route rejected: missing external checker verdict"
            } else {
                "fmla guarded-equivalence overlay LRAT route rejected: runtime proof rows missing"
            };
            self.inproc
                .preprocess_transactions
                .fail_closed(transaction_id, reason);
        }
    }

    pub(in crate::solver) fn fmla_guarded_equiv_original_clause_authority_rows(
        sidecars: &[FmlaGuardedEquivOverlayLratSidecar],
        support_sidecars: &[FmlaGuardedEquivSupportCoverLratSidecar],
    ) -> u64 {
        let overlay_rows = sidecars
            .iter()
            .flat_map(|sidecar| [&sidecar.forward_binary, &sidecar.reverse_binary])
            .filter(|row| Self::fmla_guarded_equiv_overlay_row_has_original_clause_authority(row))
            .count();
        let support_rows = support_sidecars
            .iter()
            .filter(|row| Self::fmla_guarded_equiv_support_row_has_original_clause_authority(row))
            .count();
        overlay_rows.saturating_add(support_rows) as u64
    }

    fn fmla_guarded_equiv_overlay_row_has_original_clause_authority(
        row: &FmlaGuardedEquivOverlayLratBinaryRow,
    ) -> bool {
        row.guarded_ternary_source_id != 0
            && row.guard_unit_proof_id != 0
            && row.lrat_hints.as_slice()
                == [row.guarded_ternary_source_id, row.guard_unit_proof_id].as_slice()
    }

    fn fmla_guarded_equiv_support_row_has_original_clause_authority(
        row: &FmlaGuardedEquivSupportCoverLratSidecar,
    ) -> bool {
        if row.support_clause_id == 0 || row.directional_ternary_source_ids.is_empty() {
            return false;
        }
        if row.directional_ternary_source_ids.contains(&0) {
            return false;
        }
        let Some((&last_hint, directional_hints)) = row.lrat_hints.split_last() else {
            return false;
        };
        last_hint == row.support_clause_id
            && directional_hints == row.directional_ternary_source_ids.as_slice()
    }

    fn fmla_overlay_source_id_visible(&self, source_id: u64) -> bool {
        source_id != 0
            && self.lrat_hint_id_visible(source_id)
            && self
                .proof_manager
                .as_ref()
                .is_some_and(|manager| manager.is_known_lrat_id(source_id))
    }

    fn fmla_decompose_lrat_preflight_route_active(&self) -> bool {
        let sat_flags = ay_core::sat_disable_flags();
        self.cold.fmla_decompose_lrat_preflight_route_enabled
            && !self.cold.fmla_decompose_lrat_preflight_route_consumed
            && self.cold.lrat_enabled
            && self.proof_manager.is_some()
            && self.sat_comp_main_conflict_pruning_enabled()
            && !self.cold.has_been_incremental
            && !sat_flags.no_inprocess
            && !sat_flags.no_decompose
    }

    /// Decompose body — early returns are safe; wrapper handles rescheduling.
    ///
    /// Builds the binary implication graph, finds SCCs via Tarjan's algorithm,
    /// and substitutes equivalent literals throughout the clause database.
    /// Reference: CaDiCaL `decompose.cpp`.
    ///
    /// Returns `true` if equivalences were found and substituted.
    /// Must be called at decision level 0.
    fn decompose_body(&mut self) -> bool {
        use crate::decompose::rewrite_clauses;
        if !self.require_level_zero() {
            return false;
        }

        // Skip in incremental mode: decompose uses push_equivalence_reconstruction()
        // and rewrites clauses in-place. After pop(), reconstruction entries are
        // truncated but rewritten literals (representatives) persist, causing
        // incorrect model reconstruction (#3710, #3662).
        if self.cold.has_been_incremental {
            return false;
        }
        // Skip in LRAT proof mode (#8197): decompose's SCC BFS chain collection
        // produces binary clause CRefs that may not have LRAT IDs registered in
        // the forward checker's clause-ID map, causing zero clause ID panics.
        if self.cold.lrat_enabled {
            if let Err(reject) = self.preflight_decompose_lrat_transaction() {
                self.record_decompose_lrat_preflight_reject(&reject);
            }
            return false;
        }
        // Decompose rewrites and deletes irredundant clauses — maintained
        // incrementally via apply_decompose_mutation's BVE occ hooks (#8096).

        self.inproc.decompose_engine.ensure_num_vars(self.num_vars);

        // need_chains = false: this body is only reachable with LRAT off
        // (early return above), and the equivalence chains feed LRAT hints
        // exclusively. Building them cost 100+s of memset on 07cea7a6
        // (275K equivalences, 1.57M lits) — see Decompose::run.
        let result = self.inproc.decompose_engine.run(
            &self.watches,
            self.num_vars,
            &self.vals,
            &self.cold.freeze_counts,
            self.var_lifecycle.as_slice(),
            false,
        );

        if std::env::var_os("AY_AB_SUBST_STATS").is_some() {
            eprintln!(
                "AB_DECOMPOSE: substituted={} unsat={} units={}",
                result.substituted,
                result.unsat,
                result.units.len()
            );
        }

        if result.unsat {
            // Phase I (#4606): SCC-UNSAT with LRAT hints.
            // When lit and ¬lit are in the same SCC, ¬lit is derivable as a unit.
            // The binary implication chain lit → ... → ¬lit proves it via RUP.
            // CaDiCaL: decompose_conflicting_scc_lrat (decompose.cpp:48-66).
            for unit in &result.units {
                if !self.var_is_assigned(unit.variable().index()) {
                    let hints = if self.cold.lrat_enabled {
                        self.collect_rup_unit_lrat_hints(*unit)
                    } else {
                        Vec::new()
                    };
                    // When hints are empty (unit not RUP under forward checker's
                    // clause DB), fall back to TrustedTransform. Same pattern as
                    // congruence non-contradiction units.
                    let proof_kind = if hints.is_empty() {
                        ProofAddKind::TrustedTransform
                    } else {
                        ProofAddKind::Derived
                    };
                    self.proof_emit_unit(*unit, &hints, proof_kind);
                    self.enqueue(*unit, None);
                }
            }
            // Let BCP detect the contradiction via propagate_check_unsat.
            // This ensures record_level0_conflict_chain constructs the proper
            // LRAT hint chain for the empty clause, instead of emitting it
            // with no hints (#4596).
            if self.propagate_check_unsat() {
                return true;
            }
            // Fallback: SCC says UNSAT but propagation didn't find it
            // (e.g., units were already assigned). Mark explicitly.
            self.mark_empty_clause_with_level0_hints();
            return true;
        }

        if result.substituted == 0 {
            // CaDiCaL deduplicate.cpp: decompose and clause shrinking can leave
            // duplicate binaries / hyper-unary opportunities even when no new
            // substitutions are found in this specific round.
            self.deduplicate_binary_clauses();
            return false;
        }

        // F1 (#4812): Assert no representative is a removed variable.
        // CaDiCaL: decompose.cpp:432-433 asserts !eliminated() && !substituted()
        // for all representatives. This catches bugs where removed variables
        // enter the SCC (e.g., lifecycle marking race in incremental solving).
        #[cfg(debug_assertions)]
        for (lit_idx, &repr) in result.reprs.iter().enumerate() {
            let repr_lit = Literal(repr.0);
            if repr_lit.index() == lit_idx {
                continue; // self-representative, skip
            }
            let repr_vi = repr_lit.variable().index();
            if repr_vi < self.var_lifecycle.as_slice().len() {
                debug_assert!(
                    !self.var_lifecycle.is_removed(repr_vi),
                    "BUG: decompose representative var {repr_vi} is removed (substituting lit {lit_idx})"
                );
            }
        }

        // Rewrite all clauses using the representative mapping.
        // CaDiCaL order: rewrite clauses → propagate units → mark substituted → flush watches.
        let rewrite = rewrite_clauses(&self.arena, &result.reprs, &self.vals);

        // Clear root-satisfied clause snapshots (#5237): conditioning saves clauses
        // satisfied at level 0, but decompose may substitute variables in those clauses.
        // The saved copies become stale — they reference pre-substitution literals that
        // no longer correspond to the rewritten clause DB.
        if !rewrite.actions.is_empty() {
            self.cold.root_satisfied_saved.clear();
        }

        // LRAT guard (#5067 audit): if rewrite would derive UNSAT (empty clause or
        // contradicting units), LRAT needs resolution hints we cannot produce here.
        // Skip the rewrite and let CDCL re-discover the contradiction with proper
        // LRAT chains. Matches the SCC-UNSAT guard (line 52 above).
        //
        // This check MUST happen before push_equivalence_reconstruction and before
        // mutations are applied. If we bail out after pushing reconstruction entries
        // but without rewriting clauses, the reconstruction stack would have entries
        // for substitutions that never happened, corrupting the model on SAT.
        if self.cold.lrat_enabled {
            let has_contradiction = rewrite.is_unsat || {
                // Check for contradicting units: same variable, opposite polarity.
                let mut seen = vec![0i8; self.num_vars]; // 0=unseen, 1=pos, -1=neg
                let mut conflict = false;
                for unit in result.units.iter().chain(rewrite.new_units.iter()) {
                    let vi = unit.variable().index();
                    let polarity: i8 = if unit.is_positive() { 1 } else { -1 };
                    if seen[vi] == -polarity {
                        conflict = true;
                        break;
                    }
                    // Also check against existing level-0 assignments.
                    if let Some(val) = self.var_value_from_vals(vi) {
                        if val != unit.is_positive() {
                            conflict = true;
                            break;
                        }
                    }
                    seen[vi] = polarity;
                }
                conflict
            };
            if has_contradiction {
                // Cannot produce LRAT hints for empty clause derivation from
                // decompose rewriting. Skip; CDCL will find the contradiction.
                return true;
            }
        }

        // No longer needed: substitute_in_existing() was a workaround for the
        // internal-index reconstruction stack. With external indices (#5250),
        // entries use stable external indices that never change during decompose.

        let proof_obligation = if self.proof_manager.is_some() {
            ProofObligationStatus::Satisfied
        } else {
            ProofObligationStatus::NotRequired
        };
        let transaction_id = self.begin_decompose_preprocess_transaction(
            &result,
            &rewrite.actions,
            proof_obligation,
            ModelReconstructionWitnessStatus::Missing,
        );

        // Push equivalence reconstruction entries for substituted variables.
        // Placed after the LRAT guard: if we bail out above, no reconstruction
        // entries are pushed, avoiding a mismatch between reconstruction stack
        // and actual clause_db state (#5067 audit round 2).
        let reconstruction_before = self.inproc.reconstruction.len();
        self.push_equivalence_reconstruction(&result.reprs);
        let reconstruction_witness = if result.substituted == 0 {
            ModelReconstructionWitnessStatus::NotApplicable
        } else if self.inproc.reconstruction.len() > reconstruction_before {
            ModelReconstructionWitnessStatus::Present
        } else {
            ModelReconstructionWitnessStatus::Missing
        };
        self.inproc
            .preprocess_transactions
            .set_model_reconstruction_witness(transaction_id, reconstruction_witness);
        if reconstruction_witness == ModelReconstructionWitnessStatus::Missing {
            self.inproc.preprocess_transactions.fail_closed(
                transaction_id,
                "decompose model-reconstruction witness missing",
            );
            return false;
        }

        // Phase G (#4606): Derive equivalence binaries with LRAT hints.
        // For each substituted variable, derive two transient binary clauses:
        //   (repr ∨ ¬lit) — proves lit → repr
        //   (lit ∨ ¬repr) — proves repr → lit
        // These are used as LRAT hints for substituted clauses in Phase H.
        // CaDiCaL: decompose.cpp:436-479 (derive + weaken_minus + extension stack).
        //
        // Uses constructive chain approach (not probe-based): binary clause IDs
        // are collected during SCC BFS traversal in the engine, then mapped to
        // proof IDs here. This is deterministic and should always succeed for
        // active SCC members. A failure indicates a clause ID mapping bug.
        let mut decompose_equiv_ids: Vec<u64> = if self.cold.lrat_enabled {
            vec![0; self.num_vars * 2]
        } else {
            Vec::new()
        };
        let mut lrat_equiv_ok = true;
        if self.cold.lrat_enabled {
            for var_idx in 0..self.num_vars {
                let pos = Literal::positive(Variable(var_idx as u32));
                let repr = result.reprs[pos.index()];
                if repr == pos {
                    continue; // self-representative, no substitution
                }
                let lit = pos;

                // Get the pre-computed chains from the engine.
                let chain = if lit.index() < result.equiv_chains.len() {
                    &result.equiv_chains[lit.index()]
                } else {
                    lrat_equiv_ok = false;
                    break;
                };

                // Direction 1: (repr ∨ ¬lit) — proves lit → repr.
                // Hints: binary clause IDs along the path lit → ... → repr.
                // All clause refs must resolve to valid clause IDs; zero-ID
                // entries indicate stale or garbage-collected binary clauses.
                let fwd_hints: Vec<u64> = chain
                    .lit_to_repr
                    .iter()
                    .map(|&cref| self.clause_id(ClauseRef(cref)))
                    .collect();
                let fwd_has_zero = fwd_hints.contains(&0);
                if fwd_hints.is_empty() || fwd_has_zero {
                    // Chain missing or contains invalid clause IDs.
                    // Gracefully degrade to TrustedTransform (lrat_equiv_ok=false).
                    // This can happen when binary clauses were added to the arena
                    // via paths that bypass add_clause_db_checked (e.g., congruence
                    // equivalence binaries) and don't have clause IDs assigned (#8197).
                    lrat_equiv_ok = false;
                    break;
                }
                let id_fwd = self
                    .proof_emit_add(&[repr, lit.negated()], &fwd_hints, ProofAddKind::Derived)
                    .unwrap_or(0);
                decompose_equiv_ids[lit.negated().index()] = id_fwd;

                // Direction 2: (lit ∨ ¬repr) — proves repr → lit.
                // Hints: binary clause IDs along the path repr → ... → lit.
                let bwd_hints: Vec<u64> = chain
                    .repr_to_lit
                    .iter()
                    .map(|&cref| self.clause_id(ClauseRef(cref)))
                    .collect();
                let bwd_has_zero = bwd_hints.contains(&0);
                if bwd_hints.is_empty() || bwd_has_zero {
                    // Gracefully degrade: zero clause IDs from clauses added
                    // without clause_ids coverage (#8197, see lit_to_repr comment).
                    lrat_equiv_ok = false;
                    break;
                }
                let id_bwd = self
                    .proof_emit_add(&[lit, repr.negated()], &bwd_hints, ProofAddKind::Derived)
                    .unwrap_or(0);
                decompose_equiv_ids[lit.index()] = id_bwd;
            }
        }

        // Emit proof records for clause mutations captured by rewrite_clauses.
        //
        // Two-phase emission: ALL additions first, then ALL deletions.
        // Within a single Replaced/Unit pair, add-before-delete is obvious.
        // But across mutations, an earlier Replaced deletion can remove a clause
        // that a later Unit addition needs for RUP verification. Example:
        //   Replaced { old: (x2,x3), new: (x2,x1) } → delete (x2,x3)
        //   Unit { unit: x1, old: (x3,x1) }          → add (x1)
        // The unit (x1) needs (x2,x3) for its RUP chain, but it's already deleted.
        // Fix: emit all adds while the original formula is intact, then delete.
        // Pre-compute clause IDs before borrowing proof_manager mutably.
        // clause_id() reads self.cold.clause_ids which conflicts with &mut self.proof_manager.
        let mutation_ids: Vec<u64> = rewrite
            .actions
            .iter()
            .map(|m| {
                let ci = match m {
                    crate::decompose::ClauseMutation::Deleted { clause_idx, .. }
                    | crate::decompose::ClauseMutation::Replaced { clause_idx, .. }
                    | crate::decompose::ClauseMutation::Unit { clause_idx, .. } => *clause_idx,
                };
                self.clause_id(ClauseRef(ci as u32))
            })
            .collect();

        if self.cold.lrat_enabled && lrat_equiv_ok {
            // Rewritten clauses can drop literals that are already false at
            // level 0. Materialize those unit proofs before building the LRAT
            // substitution chains so the dropped literals are justified.
            self.materialize_level0_unit_proofs();
        }

        // Collect unit proof IDs; store in unit_proof_id afterward (#4636).
        let mut unit_pids: Vec<(Literal, u64)> = Vec::new();
        // Phase 1 / Phase H (#4606): emit all additions while original formula
        // is intact. In LRAT mode (with successful Phase G), collect equivalence
        // binary IDs + unit IDs + original clause ID as hints.
        // CaDiCaL: decompose.cpp:491-576.
        // Also emit SCC units here (before deletions) so the forward checker
        // can still find the original binary clauses forming the SCC cycle
        // for RUP verification (#4966).
        for (mutation, &cid) in rewrite.actions.iter().zip(mutation_ids.iter()) {
            match mutation {
                crate::decompose::ClauseMutation::Replaced {
                    old,
                    new,
                    clause_idx,
                } => {
                    let hints = if self.cold.lrat_enabled && lrat_equiv_ok {
                        self.build_decompose_subst_hints(
                            old,
                            &result.reprs,
                            &decompose_equiv_ids,
                            cid,
                        )
                    } else if cid != 0 {
                        vec![cid]
                    } else {
                        Vec::new()
                    };
                    let kind = if hints.is_empty() {
                        ProofAddKind::TrustedTransform
                    } else {
                        ProofAddKind::Derived
                    };
                    let new_id = self.proof_emit_add(new, &hints, kind).unwrap_or(0);
                    // Update clause_ids so deduplication/later deletions use the
                    // new proof ID, not the stale original that Phase 2 will delete.
                    if new_id != 0 && *clause_idx < self.cold.clause_ids.len() {
                        self.cold.clause_ids[*clause_idx] = new_id;
                    }
                }
                crate::decompose::ClauseMutation::Unit { unit, old, .. } => {
                    let hints = if self.cold.lrat_enabled && lrat_equiv_ok {
                        self.build_decompose_subst_hints(
                            old,
                            &result.reprs,
                            &decompose_equiv_ids,
                            cid,
                        )
                    } else if cid != 0 {
                        vec![cid]
                    } else {
                        Vec::new()
                    };
                    let kind = if hints.is_empty() {
                        ProofAddKind::TrustedTransform
                    } else {
                        ProofAddKind::Derived
                    };
                    let pid = self.proof_emit_unit(*unit, &hints, kind);
                    if pid != 0 {
                        unit_pids.push((*unit, pid));
                    }
                }
                crate::decompose::ClauseMutation::Deleted { .. } => {}
            }
        }
        // Phase 1b: emit SCC-derived units while original binary clauses are
        // still present in the forward checker. These units are derived from
        // the binary implication graph (a variable and its negation in the same
        // SCC), so the original binary clauses must exist for RUP to succeed.
        // Only emit the proof entry here; enqueue() happens later after clause
        // mutations are applied (#4966).
        for unit in &result.units {
            if !self.var_is_assigned(unit.variable().index()) {
                let hints = if self.cold.lrat_enabled {
                    self.collect_rup_unit_lrat_hints(*unit)
                } else {
                    Vec::new()
                };
                self.proof_emit_unit(*unit, &hints, ProofAddKind::Derived);
            }
        }
        // Phase 2: emit all deletions with real clause IDs (not 0).
        for (mutation, &cid) in rewrite.actions.iter().zip(mutation_ids.iter()) {
            match mutation {
                crate::decompose::ClauseMutation::Deleted { old, .. } => {
                    let _ = self.proof_emit_delete(old, cid);
                }
                crate::decompose::ClauseMutation::Replaced { old, .. } => {
                    let _ = self.proof_emit_delete(old, cid);
                }
                crate::decompose::ClauseMutation::Unit { old, .. } => {
                    let _ = self.proof_emit_delete(old, cid);
                }
            }
        }
        // Phase J (#4606): delete transient equivalence binaries from proof.
        // CaDiCaL decompose.cpp:651-676. These were derived in Phase G for
        // LRAT hint purposes; not actual clause DB entries.
        if self.cold.lrat_enabled && lrat_equiv_ok {
            for var_idx in 0..self.num_vars {
                let pos = Literal::positive(Variable(var_idx as u32));
                let repr = result.reprs[pos.index()];
                if repr == pos {
                    continue;
                }
                let lit = pos;
                let id_fwd = decompose_equiv_ids[lit.negated().index()];
                if id_fwd != 0 {
                    let _ = self.proof_emit_delete(&[repr, lit.negated()], id_fwd);
                }
                let id_bwd = decompose_equiv_ids[lit.index()];
                if id_bwd != 0 {
                    let _ = self.proof_emit_delete(&[lit, repr.negated()], id_bwd);
                }
            }
        }
        // Apply deferred unit_proof_id stores outside manager borrow (#4636).
        for (unit, pid) in unit_pids {
            self.record_unit_proof_id_for_lit(unit, pid);
        }

        // Apply clause mutations (#3440).
        // Mark variables in mutated clauses as dirty BVE candidates BEFORE
        // applying the mutation (which may delete the clause). (#7905)
        for action in &rewrite.actions {
            let lits: Option<Vec<Literal>> = match action {
                crate::decompose::ClauseMutation::Deleted { clause_idx, .. }
                | crate::decompose::ClauseMutation::Unit { clause_idx, .. } => {
                    if *clause_idx < self.arena.len()
                        && self.arena.is_active(*clause_idx)
                        && !self.arena.is_learned(*clause_idx)
                    {
                        Some(self.arena.literals(*clause_idx).to_vec())
                    } else {
                        None
                    }
                }
                crate::decompose::ClauseMutation::Replaced {
                    clause_idx, new, ..
                } => {
                    if *clause_idx < self.arena.len()
                        && self.arena.is_active(*clause_idx)
                        && !self.arena.is_learned(*clause_idx)
                    {
                        let old = self.arena.literals(*clause_idx).to_vec();
                        self.inproc.bve.mark_candidates_dirty_clause(new);
                        Some(old)
                    } else {
                        None
                    }
                }
            };
            if let Some(old_lits) = &lits {
                self.inproc.bve.mark_candidates_dirty_clause(old_lits);
            }
            self.apply_decompose_mutation(action);
        }
        self.cold.clause_db_changes += u64::from(rewrite.removed) + u64::from(rewrite.shortened);
        // Mark for BVE re-trigger (CaDiCaL decompose.cpp:613 mark_removed).
        self.cold.bve_marked += u64::from(rewrite.removed) + u64::from(rewrite.shortened);
        self.inproc
            .preprocess_transactions
            .commit(transaction_id)
            .expect("decompose transaction witness was recorded before mutation commit");

        if rewrite.is_unsat {
            self.mark_empty_clause_with_level0_hints();
            return true;
        }

        // Propagate new units before marking variables as substituted.
        // CaDiCaL: decompose.cpp:695-698 — propagate MUST happen while substituted
        // variables are still active, so BCP can traverse their watch lists.
        //
        // SCC units (result.units): proof already emitted in Phase 1b (#4966).
        // Rewrite units (rewrite.new_units): already emitted via actions Unit variant.
        //
        // Contradiction detection (#5067): CaDiCaL interleaves unit assignment
        // with clause rewriting (decompose.cpp:538-590), so val() checks during
        // substitution detect contradicting units as empty clauses. AY separates
        // rewriting (read-only rewrite_clauses) from assignment (here). When two
        // clauses independently reduce to contradicting units (e.g., [+x] and
        // [−x]), the second enqueue must detect the conflict; otherwise the
        // contradicting unit's original clause was already deleted from the DB
        // and the constraint is permanently lost.
        for unit in &result.units {
            let vi = unit.variable().index();
            if let Some(val) = self.var_value_from_vals(vi) {
                if val != unit.is_positive() {
                    // Contradicting unit: variable already assigned opposite polarity.
                    // LRAT: empty clause = resolve existing unit proof with new unit proof.
                    // Use BFS transitive closure for complete LRAT chain (#7108).
                    if self.cold.lrat_enabled {
                        let new_unit_pid = self.visible_unit_proof_id_for_lit(*unit).unwrap_or(0);
                        let hints = self
                            .collect_empty_clause_hints_for_unit_contradiction(new_unit_pid, *unit);
                        self.mark_empty_clause_with_hints(&hints);
                    } else {
                        self.mark_empty_clause();
                    }
                    return true;
                }
                // Same polarity: harmless duplicate, skip.
            } else {
                self.enqueue(*unit, None);
            }
        }
        for unit in &rewrite.new_units {
            let vi = unit.variable().index();
            if let Some(val) = self.var_value_from_vals(vi) {
                if val != unit.is_positive() {
                    // Use BFS transitive closure for complete LRAT chain (#7108).
                    if self.cold.lrat_enabled {
                        let new_unit_pid = self.visible_unit_proof_id_for_lit(*unit).unwrap_or(0);
                        let hints = self
                            .collect_empty_clause_hints_for_unit_contradiction(new_unit_pid, *unit);
                        self.mark_empty_clause_with_hints(&hints);
                    } else {
                        self.mark_empty_clause();
                    }
                    return true;
                }
            } else {
                // Proof ID already captured in actions Unit emission above (#4626).
                self.enqueue(*unit, None);
            }
        }

        // Mark substituted variables as eliminated and remove from VSIDS.
        // CaDiCaL: decompose.cpp:700-714 — marks substituted AFTER propagation.
        // Guard: if the representative is fixed (assigned at level 0), skip marking.
        // CaDiCaL: `if (!flags(other).fixed()) mark_substituted(idx)` at line 712.
        for var_idx in 0..self.num_vars {
            let pos = Literal::positive(Variable(var_idx as u32));
            let repr_pos = result.reprs[pos.index()];
            if repr_pos == pos {
                continue;
            }
            // Skip if already removed (e.g., by BVE in same inprocessing round)
            // or fixed at level 0 (CaDiCaL: `flags(other).fixed()` guard).
            if self.var_lifecycle.is_removed(var_idx) || self.var_lifecycle.is_fixed(var_idx) {
                continue;
            }
            // CaDiCaL fixed() guard: if the representative is assigned at level 0,
            // the substituted variable will get its value through propagation, not
            // through the substitution mechanism. Don't mark as substituted.
            let repr_var = repr_pos.variable().index();
            if repr_var < self.num_vars && self.var_is_assigned(repr_var) {
                continue;
            }

            let var = Variable(var_idx as u32);
            // V4 fix (#3906): decompose marks variables as Substituted, not Eliminated.
            // CaDiCaL: decompose.cpp:712 uses mark_substituted().
            self.var_lifecycle.mark_substituted(var_idx);
            self.vsids.remove_from_heap(var);

            // Diagnostic trace: var_transition active → substituted (Wave 3, #4211)
            if let Some(ref writer) = self.cold.diagnostic_trace {
                writer.emit_var_transition(
                    var.0,
                    crate::diagnostic_trace::VarState::Active,
                    crate::diagnostic_trace::VarState::Substituted,
                    self.cold.diagnostic_pass,
                );
            }
        }

        // GC learned clauses containing substituted variables (#5149).
        // rewrite_clauses processes ALL clauses (learned + irredundant), so
        // this pass is a safety net for learned clauses missed by rewrite.
        // Defer the O(num_vars) stale reason scan during the bulk deletion
        // loop; one pass after the loop handles all stale references.
        self.defer_stale_reason_cleanup = true;
        {
            // Reuse persistent buffer to avoid arena-proportional allocation (#8602).
            self.cold.reduce_indices_buf.clear();
            self.cold.reduce_indices_buf.extend(self.arena.indices());
            for i in 0..self.cold.reduce_indices_buf.len() {
                let idx = self.cold.reduce_indices_buf[i];
                if self.arena.is_empty_clause(idx) || !self.arena.is_active(idx) {
                    continue;
                }
                let has_substituted = self
                    .arena
                    .literals(idx)
                    .iter()
                    .any(|lit| self.var_lifecycle.is_removed(lit.variable().index()));
                if has_substituted {
                    self.delete_clause_checked(idx, ReasonPolicy::ClearLevel0);
                }
            }
        }
        self.defer_stale_reason_cleanup = false;
        self.clear_stale_reasons();

        // Finalize incrementally-maintained watches (#8093). Clause mutations
        // (replacements, deletions) updated watches eagerly inside
        // apply_decompose_mutation(). Only qhead rewinding and debug validation
        // remain.
        // Decompose rewrites clause literals (substitution), so full re-propagation
        // from position 0 is needed (#8095).
        self.mark_trail_affected(0);
        self.finalize_incremental_watches();

        // CaDiCaL does NOT eagerly assign substituted variables here.
        // Model reconstruction handles it: the BCE entries pushed above
        // ((repr ∨ ¬lit) and (¬repr ∨ lit)) correctly set substituted
        // variables from their representative's value during extend_model.
        // Eager assignment with reason=None created inconsistent state:
        // eliminated variables on the trail without reasons, breaking
        // conflict analysis (#3424, #3466).

        // CaDiCaL deduplicate.cpp: equivalent-literal substitution can leave
        // duplicate binaries and discover hyper-unary units.
        if self.deduplicate_binary_clauses() {
            #[allow(clippy::needless_return)]
            return true;
        }

        // Post-condition: every variable whose representative differs from itself
        // (and whose representative is not fixed at level 0) should be marked eliminated.
        // Without this, substituted-but-not-eliminated variables remain on the VSIDS
        // heap and can be decided, causing propagation over dead watch lists.
        #[cfg(debug_assertions)]
        for var_idx in 0..self.num_vars.min(result.reprs.len() / 2) {
            let pos = Literal::positive(Variable(var_idx as u32));
            let repr_pos = result.reprs[pos.index()];
            if repr_pos == pos {
                continue;
            }
            let repr_var = repr_pos.variable().index();
            // Skip the CaDiCaL fixed() guard case: if repr is assigned at level 0,
            // the variable is propagated rather than eliminated.
            if repr_var < self.num_vars && self.var_is_assigned(repr_var) {
                continue;
            }
            debug_assert!(
                self.var_lifecycle.is_removed(var_idx),
                "BUG: decompose substituted var {var_idx} (repr={repr_pos:?}) \
                 but did not mark it as removed"
            );
        }
        true
    }

    fn begin_decompose_preprocess_transaction(
        &mut self,
        result: &crate::decompose::DecomposeResult,
        actions: &[crate::decompose::ClauseMutation],
        proof_obligation: ProofObligationStatus,
        model_reconstruction_witness: ModelReconstructionWitnessStatus,
    ) -> PreprocessTransactionId {
        let mut touched = std::collections::BTreeSet::new();
        let mut eliminated = std::collections::BTreeSet::new();
        let mut planned_substitutions = Vec::new();
        let mut equivalent_variables = Vec::new();

        for var_idx in 0..self.num_vars {
            let lit = Literal::positive(Variable(var_idx as u32));
            let Some(&repr) = result.reprs.get(lit.index()) else {
                continue;
            };
            if repr == lit {
                continue;
            }
            let repr_var = repr.variable().index();
            touched.insert(var_idx);
            touched.insert(repr_var);
            eliminated.insert(var_idx);
            equivalent_variables.push((var_idx, repr_var));
            planned_substitutions.push(PlannedSubstitution {
                variable: var_idx,
                literal_dimacs: lit.to_dimacs(),
                representative_variable: repr_var,
                representative_dimacs: repr.to_dimacs(),
            });
        }

        for action in actions {
            match action {
                crate::decompose::ClauseMutation::Deleted { old, .. } => {
                    Self::record_touched_lits(&mut touched, old);
                }
                crate::decompose::ClauseMutation::Replaced { old, new, .. } => {
                    Self::record_touched_lits(&mut touched, old);
                    Self::record_touched_lits(&mut touched, new);
                }
                crate::decompose::ClauseMutation::Unit { unit, old, .. } => {
                    Self::record_touched_lits(&mut touched, old);
                    touched.insert(unit.variable().index());
                }
            }
        }

        self.inproc
            .preprocess_transactions
            .begin(PreprocessTransactionDraft {
                mutation_epoch: self.cold.clause_db_changes,
                pass_name: PreprocessPass::Decompose,
                touched_variables: touched.into_iter().collect(),
                eliminated_variables: eliminated.into_iter().collect(),
                equivalent_variables,
                planned_substitutions,
                proof_obligation,
                model_reconstruction_witness,
            })
    }

    fn record_touched_lits(touched: &mut std::collections::BTreeSet<usize>, lits: &[Literal]) {
        for lit in lits {
            touched.insert(lit.variable().index());
        }
    }

    fn record_decompose_lrat_preflight_reject(&mut self, reject: &DecomposeLratTransactionReject) {
        self.inproc
            .decompose_engine
            .record_lrat_preflight_dry_run_rejected();
        match reject {
            DecomposeLratTransactionReject::MissingProofManager => self
                .inproc
                .decompose_engine
                .record_lrat_preflight_missing_proof_manager(),
            DecomposeLratTransactionReject::NoSubstitution => self
                .inproc
                .decompose_engine
                .record_lrat_preflight_no_substitution(),
            DecomposeLratTransactionReject::MissingOrHiddenSourceId { .. } => self
                .inproc
                .decompose_engine
                .record_lrat_preflight_missing_source_id(),
            DecomposeLratTransactionReject::MissingChainSourceId { .. } => self
                .inproc
                .decompose_engine
                .record_lrat_preflight_missing_chain_edge_id(),
            DecomposeLratTransactionReject::MissingChain { .. } => self
                .inproc
                .decompose_engine
                .record_lrat_preflight_missing_equiv_chain(),
            DecomposeLratTransactionReject::NoSubstitutedLiteral { .. }
            | DecomposeLratTransactionReject::MalformedRewrite { .. } => self
                .inproc
                .decompose_engine
                .record_lrat_preflight_malformed_rewrite(),
            DecomposeLratTransactionReject::MissingSubstitutionHint { .. } => self
                .inproc
                .decompose_engine
                .record_lrat_preflight_missing_substitution_hint(),
            DecomposeLratTransactionReject::MissingVisibleLevel0Unit { .. } => self
                .inproc
                .decompose_engine
                .record_lrat_preflight_missing_level0_unit_id(),
            DecomposeLratTransactionReject::MissingTransientEquivalenceId { .. } => self
                .inproc
                .decompose_engine
                .record_lrat_preflight_missing_transient_equiv_id(),
            DecomposeLratTransactionReject::Contradiction => self
                .inproc
                .decompose_engine
                .record_lrat_preflight_contradiction(),
            DecomposeLratTransactionReject::PlannedAddRejected(_) => self
                .inproc
                .decompose_engine
                .record_lrat_preflight_planned_add_rejected(),
        }
    }

    fn decompose_lrat_source_id(
        &self,
        clause_idx: usize,
    ) -> Result<u64, DecomposeLratTransactionReject> {
        let clause_id = if clause_idx < self.cold.clause_ids.len() {
            self.clause_id(ClauseRef(clause_idx as u32))
        } else {
            0
        };
        if clause_idx >= self.arena.len() || !self.arena.is_active(clause_idx) {
            return Err(DecomposeLratTransactionReject::MissingOrHiddenSourceId {
                clause_idx,
                clause_id,
            });
        }
        if clause_id == 0 || !self.lrat_hint_id_visible(clause_id) {
            return Err(DecomposeLratTransactionReject::MissingOrHiddenSourceId {
                clause_idx,
                clause_id,
            });
        }
        let Some(manager) = self.proof_manager.as_ref() else {
            return Err(DecomposeLratTransactionReject::MissingProofManager);
        };
        if !manager.is_known_lrat_id(clause_id) {
            return Err(DecomposeLratTransactionReject::MissingOrHiddenSourceId {
                clause_idx,
                clause_id,
            });
        }
        Ok(clause_id)
    }

    fn decompose_lrat_chain_source_ids(
        &self,
        literal: Literal,
        chain: &[u32],
    ) -> Result<Vec<u64>, DecomposeLratTransactionReject> {
        if chain.is_empty() {
            return Err(DecomposeLratTransactionReject::MissingChain { literal });
        }
        let Some(manager) = self.proof_manager.as_ref() else {
            return Err(DecomposeLratTransactionReject::MissingProofManager);
        };
        let mut ids = Vec::with_capacity(chain.len());
        for &cref in chain {
            let clause_id = self.clause_id(ClauseRef(cref));
            if clause_id == 0 || !self.lrat_hint_id_visible(clause_id) {
                return Err(DecomposeLratTransactionReject::MissingChainSourceId {
                    clause_ref: cref,
                    clause_id,
                });
            }
            if !manager.is_known_lrat_id(clause_id) {
                return Err(DecomposeLratTransactionReject::MissingChainSourceId {
                    clause_ref: cref,
                    clause_id,
                });
            }
            ids.push(clause_id);
        }
        Ok(ids)
    }

    fn build_decompose_lrat_dry_run_sidecar(
        &self,
        result: &crate::decompose::DecomposeResult,
        clause_idx: usize,
        old_lits: &[Literal],
        new_lits: &[Literal],
        planned_add_ids: &[u64],
        planned_visible_ids: &mut Vec<u64>,
    ) -> Result<DecomposeLratDryRunSidecar, DecomposeLratTransactionReject> {
        let source_clause_id = self.decompose_lrat_source_id(clause_idx)?;
        let mut steps = Vec::new();

        for &old_lit in old_lits {
            let mapped = result
                .reprs
                .get(old_lit.index())
                .copied()
                .unwrap_or(old_lit);
            if mapped == old_lit {
                continue;
            }
            let chain = result
                .equiv_chains
                .get(old_lit.index())
                .ok_or(DecomposeLratTransactionReject::MissingChain { literal: old_lit })?;
            let lit_to_repr_source_ids =
                self.decompose_lrat_chain_source_ids(old_lit, &chain.lit_to_repr)?;
            let repr_to_lit_source_ids =
                self.decompose_lrat_chain_source_ids(old_lit, &chain.repr_to_lit)?;
            steps.push(DecomposeLratEquivalenceStep {
                original_lit: i64::from(old_lit.to_dimacs()),
                representative_lit: i64::from(mapped.to_dimacs()),
                lit_to_repr_source_ids,
                repr_to_lit_source_ids,
                planned_lit_to_repr_add_id: 0,
                planned_repr_to_lit_add_id: 0,
            });
        }

        if steps.is_empty() {
            return Err(DecomposeLratTransactionReject::NoSubstitutedLiteral { clause_idx });
        }
        let expected_planned_adds = steps.len().saturating_mul(2).saturating_add(1);
        if planned_add_ids.len() != expected_planned_adds {
            return Err(DecomposeLratTransactionReject::MalformedRewrite { clause_idx });
        }

        let Some(manager) = self.proof_manager.as_ref() else {
            return Err(DecomposeLratTransactionReject::MissingProofManager);
        };
        let mut next_planned = 0usize;

        for step in &mut steps {
            let original_lit = Literal::from_dimacs(step.original_lit as i32);
            let representative_lit = Literal::from_dimacs(step.representative_lit as i32);

            let lit_to_repr_id = planned_add_ids[next_planned];
            if lit_to_repr_id == 0 {
                return Err(
                    DecomposeLratTransactionReject::MissingTransientEquivalenceId {
                        literal: original_lit,
                    },
                );
            }
            manager
                .preflight_forward_lrat_add_with_planned_ids(
                    &[representative_lit, original_lit.negated()],
                    &step.lit_to_repr_source_ids,
                    ProofAddKind::Derived,
                    planned_visible_ids.as_slice(),
                )
                .map_err(DecomposeLratTransactionReject::PlannedAddRejected)?;
            step.planned_lit_to_repr_add_id = lit_to_repr_id;
            planned_visible_ids.push(lit_to_repr_id);
            next_planned += 1;

            let repr_to_lit_id = planned_add_ids[next_planned];
            if repr_to_lit_id == 0 {
                return Err(
                    DecomposeLratTransactionReject::MissingTransientEquivalenceId {
                        literal: original_lit,
                    },
                );
            }
            manager
                .preflight_forward_lrat_add_with_planned_ids(
                    &[original_lit, representative_lit.negated()],
                    &step.repr_to_lit_source_ids,
                    ProofAddKind::Derived,
                    planned_visible_ids.as_slice(),
                )
                .map_err(DecomposeLratTransactionReject::PlannedAddRejected)?;
            step.planned_repr_to_lit_add_id = repr_to_lit_id;
            planned_visible_ids.push(repr_to_lit_id);
            next_planned += 1;
        }

        let mut rewrite_hints = Vec::with_capacity(old_lits.len() + 1);
        for &old_lit in old_lits {
            let mapped = result
                .reprs
                .get(old_lit.index())
                .copied()
                .unwrap_or(old_lit);
            if mapped != old_lit {
                if let Some(step) = steps.iter().find(|step| {
                    step.original_lit == i64::from(old_lit.to_dimacs())
                        && step.representative_lit == i64::from(mapped.to_dimacs())
                }) {
                    if step.planned_lit_to_repr_add_id == 0 {
                        return Err(
                            DecomposeLratTransactionReject::MissingTransientEquivalenceId {
                                literal: old_lit,
                            },
                        );
                    }
                    rewrite_hints.push(step.planned_lit_to_repr_add_id);
                } else {
                    return Err(DecomposeLratTransactionReject::MissingSubstitutionHint {
                        literal: old_lit,
                    });
                }
            }
            if self.lit_val(mapped) < 0 {
                let proof_id = self
                    .level0_var_proof_id_for_lit(mapped.negated())
                    .unwrap_or(0);
                if proof_id == 0 || !self.lrat_hint_id_visible(proof_id) {
                    return Err(DecomposeLratTransactionReject::MissingVisibleLevel0Unit {
                        literal: mapped.negated(),
                        proof_id,
                    });
                }
                rewrite_hints.push(proof_id);
            }
        }
        rewrite_hints.push(source_clause_id);

        let planned_rewrite_add_id = planned_add_ids[next_planned];
        if planned_rewrite_add_id == 0 || new_lits.is_empty() {
            return Err(DecomposeLratTransactionReject::MalformedRewrite { clause_idx });
        }
        manager
            .preflight_forward_lrat_add_with_planned_ids(
                new_lits,
                &rewrite_hints,
                ProofAddKind::Derived,
                planned_visible_ids.as_slice(),
            )
            .map_err(DecomposeLratTransactionReject::PlannedAddRejected)?;

        Ok(DecomposeLratDryRunSidecar {
            source_clause_id,
            source_clause_lits: old_lits
                .iter()
                .map(|lit| i64::from(lit.to_dimacs()))
                .collect(),
            rewritten_clause_lits: new_lits
                .iter()
                .map(|lit| i64::from(lit.to_dimacs()))
                .collect(),
            equivalence_steps: steps,
            rewrite_hints,
            planned_rewrite_add_id,
            source_delete_id: source_clause_id,
        })
    }

    fn preflight_decompose_lrat_transaction(
        &mut self,
    ) -> Result<(), DecomposeLratTransactionReject> {
        use crate::decompose::rewrite_clauses;

        self.inproc.decompose_engine.clear_lrat_dry_run_sidecars();
        if !self.cold.lrat_enabled {
            return Ok(());
        }
        self.inproc.decompose_engine.record_lrat_preflight_attempt();
        if self.proof_manager.is_none() {
            return Err(DecomposeLratTransactionReject::MissingProofManager);
        }

        self.inproc.decompose_engine.ensure_num_vars(self.num_vars);
        let stats_before = self.inproc.decompose_engine.stats.clone();
        // need_chains = true: the LRAT preflight consumes the equivalence
        // chains for its dry-run sidecars (decompose_lrat_chain_source_ids).
        let result = self.inproc.decompose_engine.run(
            &self.watches,
            self.num_vars,
            &self.vals,
            &self.cold.freeze_counts,
            self.var_lifecycle.as_slice(),
            true,
        );
        self.inproc.decompose_engine.restore_stats(stats_before);

        if result.unsat {
            return Err(DecomposeLratTransactionReject::Contradiction);
        }
        if result.substituted == 0 {
            return Err(DecomposeLratTransactionReject::NoSubstitution);
        }

        let rewrite = rewrite_clauses(&self.arena, &result.reprs, &self.vals);

        if rewrite.is_unsat {
            return Err(DecomposeLratTransactionReject::Contradiction);
        }
        let mut seen = vec![0i8; self.num_vars];
        for unit in result.units.iter().chain(rewrite.new_units.iter()) {
            let vi = unit.variable().index();
            let polarity: i8 = if unit.is_positive() { 1 } else { -1 };
            if seen[vi] == -polarity {
                return Err(DecomposeLratTransactionReject::Contradiction);
            }
            if let Some(val) = self.var_value_from_vals(vi) {
                if val != unit.is_positive() {
                    return Err(DecomposeLratTransactionReject::Contradiction);
                }
            }
            seen[vi] = polarity;
        }

        struct PreflightCandidate {
            clause_idx: usize,
            old_lits: Vec<Literal>,
            rewritten_lits: Vec<Literal>,
            planned_add_count: usize,
            delete_only: bool,
        }

        let mut candidates = Vec::new();
        for action in &rewrite.actions {
            let (clause_idx, old, rewritten_lits, delete_only) = match action {
                crate::decompose::ClauseMutation::Replaced {
                    old,
                    new,
                    clause_idx,
                } => (*clause_idx, old.as_slice(), new.clone(), false),
                crate::decompose::ClauseMutation::Unit {
                    old,
                    unit,
                    clause_idx,
                } => (*clause_idx, old.as_slice(), vec![*unit], false),
                crate::decompose::ClauseMutation::Deleted { old, clause_idx } => {
                    (*clause_idx, old.as_slice(), Vec::new(), true)
                }
            };

            let substituted_count = old
                .iter()
                .filter(|lit| result.reprs.get(lit.index()).copied().unwrap_or(**lit) != **lit)
                .count();
            if substituted_count == 0 {
                continue;
            }
            let planned_add_count = if delete_only {
                0
            } else {
                substituted_count.saturating_mul(2).saturating_add(1)
            };
            candidates.push(PreflightCandidate {
                clause_idx,
                old_lits: old.to_vec(),
                rewritten_lits,
                planned_add_count,
                delete_only,
            });
        }
        self.inproc
            .decompose_engine
            .record_lrat_preflight_transaction_candidates(candidates.len() as u64);
        if candidates.is_empty() {
            self.inproc
                .decompose_engine
                .record_lrat_preflight_empty_candidates();
            return Ok(());
        }
        let transaction_id = self.begin_decompose_preprocess_transaction(
            &result,
            &rewrite.actions,
            ProofObligationStatus::Pending,
            ModelReconstructionWitnessStatus::NotApplicable,
        );

        let planned_add_count = candidates
            .iter()
            .map(|candidate| candidate.planned_add_count)
            .sum::<usize>();
        let sidecars = match (|| {
            let Some(manager) = self.proof_manager.as_mut() else {
                return Err(DecomposeLratTransactionReject::MissingProofManager);
            };
            let _ = manager.flush();
            let Some(manager) = self.proof_manager.as_ref() else {
                return Err(DecomposeLratTransactionReject::MissingProofManager);
            };
            let planned_add_ids = manager
                .planned_forward_add_ids(planned_add_count)
                .map_err(DecomposeLratTransactionReject::PlannedAddRejected)?;
            let mut planned_visible_ids = Vec::with_capacity(planned_add_ids.len());
            let mut sidecars = Vec::with_capacity(candidates.len());
            let mut planned_cursor = 0usize;
            for candidate in &candidates {
                if candidate.delete_only {
                    continue;
                }
                let planned_end = planned_cursor.saturating_add(candidate.planned_add_count);
                if planned_end > planned_add_ids.len() {
                    return Err(DecomposeLratTransactionReject::MalformedRewrite {
                        clause_idx: candidate.clause_idx,
                    });
                }
                let sidecar = self.build_decompose_lrat_dry_run_sidecar(
                    &result,
                    candidate.clause_idx,
                    &candidate.old_lits,
                    &candidate.rewritten_lits,
                    &planned_add_ids[planned_cursor..planned_end],
                    &mut planned_visible_ids,
                )?;
                planned_cursor = planned_end;
                sidecars.push(sidecar);
            }
            if planned_cursor != planned_add_ids.len() {
                return Err(DecomposeLratTransactionReject::MalformedRewrite {
                    clause_idx: candidates[0].clause_idx,
                });
            }
            for candidate in &candidates {
                if candidate.delete_only {
                    self.decompose_lrat_source_id(candidate.clause_idx)?;
                }
            }
            Ok(sidecars)
        })() {
            Ok(sidecars) => sidecars,
            Err(reject) => {
                self.inproc
                    .preprocess_transactions
                    .set_proof_obligation(transaction_id, ProofObligationStatus::Rejected);
                self.inproc.preprocess_transactions.fail_closed(
                    transaction_id,
                    format!("decompose LRAT preflight rejected: {reject:?}"),
                );
                return Err(reject);
            }
        };
        if !sidecars.is_empty() {
            let proof_emit_contexts = sidecars
                .iter()
                .enumerate()
                .map(|(sidecar_row_index, sidecar)| {
                    DecomposeProofEmitContext::from_sidecar(
                        transaction_id.as_u64(),
                        sidecar_row_index,
                        sidecar,
                    )
                })
                .collect();
            self.inproc
                .decompose_engine
                .set_lrat_dry_run_sidecars_with_contexts(sidecars, proof_emit_contexts);
            self.try_materialize_decompose_main_lrat_rewrite_packet(transaction_id);
        }
        self.inproc
            .preprocess_transactions
            .set_proof_obligation(transaction_id, ProofObligationStatus::Satisfied);
        self.inproc.preprocess_transactions.fail_closed(
            transaction_id,
            "decompose LRAT transaction remains clamped after checker-visible dry-run",
        );
        Ok(())
    }

    fn try_materialize_decompose_main_lrat_rewrite_packet(
        &mut self,
        transaction_id: PreprocessTransactionId,
    ) {
        if !self
            .inproc
            .decompose_engine
            .lrat_main_rewrite_materializer_preflight_enabled()
        {
            return;
        }

        let sidecars = self
            .inproc
            .decompose_engine
            .lrat_dry_run_sidecars()
            .to_vec();
        let contexts = self
            .inproc
            .decompose_engine
            .lrat_proof_emit_contexts()
            .to_vec();
        self.try_emit_decompose_main_lrat_rewrite_runtime_rows(&sidecars, &contexts);
        let proof_records = self
            .proof_manager
            .as_ref()
            .map(|manager| manager.scoped_decompose_proof_emit_records().to_vec())
            .unwrap_or_default();
        let proof_obligation_rows = sidecars
            .iter()
            .map(|sidecar| {
                sidecar
                    .equivalence_steps
                    .len()
                    .saturating_mul(2)
                    .saturating_add(2)
            })
            .sum::<usize>() as u64;
        let model_reconstruction_rows = sidecars
            .iter()
            .map(|sidecar| sidecar.equivalence_steps.len())
            .sum::<usize>() as u64;
        let original_clause_authority_rows =
            Self::decompose_main_lrat_original_clause_authority_rows(&sidecars);

        let materialized = materialize_main_lrat_rewrite_records(
            MainProofRewriteLedgerMaterializerConfig {
                enabled: true,
                require_external_checker_verdict: true,
                external_checker_verdict_artifact: None,
            },
            &sidecars,
            &contexts,
            &proof_records,
        );
        let (status, external_proof_checker_verdict_artifact_rows) = match materialized {
            Ok(materialized) => {
                self.inproc
                    .decompose_engine
                    .record_lrat_main_rewrite_materializer_attempt(
                        materialized.stats.proof_emit_records_seen,
                        materialized.stats.records_materialized,
                    );
                (
                    RouteAdmissionPacketStatus::Incomplete,
                    materialized.stats.external_checker_verdict_artifact_rows,
                )
            }
            Err(reject) => {
                self.inproc
                    .decompose_engine
                    .record_lrat_main_rewrite_materializer_attempt(
                        proof_records.len() as u64,
                        Self::decompose_main_lrat_rewrite_materialized_records(&reject),
                    );
                let (sidecar_row_index, checker_visible_id) =
                    Self::decompose_main_lrat_rewrite_reject_identity(&reject);
                self.inproc
                    .decompose_engine
                    .record_lrat_main_rewrite_materializer_fail_closed_detail(
                        Self::decompose_main_lrat_rewrite_missing_runtime_record(&reject),
                        sidecar_row_index,
                        checker_visible_id,
                    );
                (RouteAdmissionPacketStatus::Rejected, 0)
            }
        };

        let _ = self
            .inproc
            .preprocess_transactions
            .set_route_admission_packet(
                transaction_id,
                RouteAdmissionPacket {
                    kind: RouteAdmissionPacketKind::FmlaEquivChainMainLrat,
                    status,
                    original_dimacs_rows: sidecars.len() as u64,
                    original_clause_authority_rows,
                    proof_obligation_rows,
                    model_reconstruction_rows,
                    external_proof_checker_verdict_artifact_rows,
                },
            );
    }

    pub(in crate::solver) fn decompose_main_lrat_original_clause_authority_rows(
        sidecars: &[DecomposeLratDryRunSidecar],
    ) -> u64 {
        sidecars
            .iter()
            .map(|sidecar| {
                let equivalence_rows = sidecar
                    .equivalence_steps
                    .iter()
                    .map(|step| {
                        u64::from(Self::source_id_list_has_authority(
                            &step.lit_to_repr_source_ids,
                        )) + u64::from(Self::source_id_list_has_authority(
                            &step.repr_to_lit_source_ids,
                        ))
                    })
                    .sum::<u64>();
                let rewrite_row =
                    u64::from(Self::rewrite_hints_have_original_clause_authority(sidecar));
                let delete_row = u64::from(
                    sidecar.source_delete_id != 0
                        && sidecar.source_delete_id == sidecar.source_clause_id
                        && !sidecar.source_clause_lits.is_empty(),
                );
                equivalence_rows
                    .saturating_add(rewrite_row)
                    .saturating_add(delete_row)
            })
            .sum()
    }

    fn source_id_list_has_authority(source_ids: &[u64]) -> bool {
        !source_ids.is_empty() && source_ids.iter().all(|source_id| *source_id != 0)
    }

    fn rewrite_hints_have_original_clause_authority(sidecar: &DecomposeLratDryRunSidecar) -> bool {
        sidecar.source_clause_id != 0
            && sidecar.rewrite_hints.last() == Some(&sidecar.source_clause_id)
            && Self::source_id_list_has_authority(&sidecar.rewrite_hints)
    }

    fn try_emit_decompose_main_lrat_rewrite_runtime_rows(
        &mut self,
        sidecars: &[DecomposeLratDryRunSidecar],
        contexts: &[DecomposeProofEmitContext],
    ) {
        if sidecars.len() != contexts.len() {
            return;
        }

        for (sidecar, context) in sidecars.iter().zip(contexts) {
            for step in &sidecar.equivalence_steps {
                let original_lit = Self::decompose_lrat_sidecar_literal(step.original_lit);
                let representative_lit =
                    Self::decompose_lrat_sidecar_literal(step.representative_lit);
                let lit_to_repr_clause = [representative_lit, original_lit.negated()];
                let Ok(lit_to_repr_id) = self.proof_emit_add_with_decompose_context(
                    &lit_to_repr_clause,
                    &step.lit_to_repr_source_ids,
                    ProofAddKind::Derived,
                    context,
                ) else {
                    return;
                };
                if lit_to_repr_id != step.planned_lit_to_repr_add_id {
                    return;
                }

                let repr_to_lit_clause = [original_lit, representative_lit.negated()];
                let Ok(repr_to_lit_id) = self.proof_emit_add_with_decompose_context(
                    &repr_to_lit_clause,
                    &step.repr_to_lit_source_ids,
                    ProofAddKind::Derived,
                    context,
                ) else {
                    return;
                };
                if repr_to_lit_id != step.planned_repr_to_lit_add_id {
                    return;
                }
            }

            let rewritten_clause =
                Self::decompose_lrat_sidecar_literals(sidecar.rewritten_clause_lits.as_slice());
            let Ok(rewrite_add_id) = self.proof_emit_add_with_decompose_context(
                &rewritten_clause,
                &sidecar.rewrite_hints,
                ProofAddKind::Derived,
                context,
            ) else {
                return;
            };
            if rewrite_add_id != sidecar.planned_rewrite_add_id {
                return;
            }

            let source_clause =
                Self::decompose_lrat_sidecar_literals(sidecar.source_clause_lits.as_slice());
            if self
                .proof_emit_delete_with_decompose_context(
                    &source_clause,
                    sidecar.source_delete_id,
                    context,
                )
                .is_err()
            {
                return;
            }
        }
    }

    fn decompose_lrat_sidecar_literals(lits: &[i64]) -> Vec<Literal> {
        lits.iter()
            .map(|&lit| Self::decompose_lrat_sidecar_literal(lit))
            .collect()
    }

    fn decompose_lrat_sidecar_literal(lit: i64) -> Literal {
        Literal::from_dimacs(
            i32::try_from(lit).expect("decompose LRAT sidecar literal must fit DIMACS i32"),
        )
    }

    fn decompose_main_lrat_rewrite_missing_runtime_record(
        reject: &MainProofRewriteLedgerMaterializerReject,
    ) -> bool {
        matches!(
            reject,
            MainProofRewriteLedgerMaterializerReject::MissingAddRecord { .. }
                | MainProofRewriteLedgerMaterializerReject::MissingDeleteRecord { .. }
        )
    }

    fn decompose_main_lrat_rewrite_materialized_records(
        reject: &MainProofRewriteLedgerMaterializerReject,
    ) -> u64 {
        match reject {
            MainProofRewriteLedgerMaterializerReject::MissingExternalCheckerVerdict {
                materialized_records,
                ..
            } => *materialized_records as u64,
            _ => 0,
        }
    }

    fn decompose_main_lrat_rewrite_reject_identity(
        reject: &MainProofRewriteLedgerMaterializerReject,
    ) -> (usize, u64) {
        match reject {
            MainProofRewriteLedgerMaterializerReject::ZeroId {
                sidecar_row_index, ..
            }
            | MainProofRewriteLedgerMaterializerReject::MissingAddRecord {
                sidecar_row_index,
                ..
            }
            | MainProofRewriteLedgerMaterializerReject::MissingDeleteRecord {
                sidecar_row_index,
                ..
            }
            | MainProofRewriteLedgerMaterializerReject::MismatchedProofRecord {
                sidecar_row_index,
                ..
            }
            | MainProofRewriteLedgerMaterializerReject::ProofRecordPayloadMismatch {
                sidecar_row_index,
                ..
            }
            | MainProofRewriteLedgerMaterializerReject::ProofWriterIoError {
                sidecar_row_index,
                ..
            }
            | MainProofRewriteLedgerMaterializerReject::RuntimeProofRecordNotEmitted {
                sidecar_row_index,
                ..
            }
            | MainProofRewriteLedgerMaterializerReject::ExternalCheckerVerdictNotAccepted {
                sidecar_row_index,
                ..
            }
            | MainProofRewriteLedgerMaterializerReject::MissingExternalCheckerVerdict {
                sidecar_row_index,
                ..
            } => (
                *sidecar_row_index,
                Self::decompose_main_lrat_rewrite_reject_checker_visible_id(reject),
            ),
            MainProofRewriteLedgerMaterializerReject::OriginalSourceBinding(reason) => (
                Self::source_bound_original_source_binding_reject_row(reason),
                0,
            ),
            MainProofRewriteLedgerMaterializerReject::SidecarContextCountMismatch { .. }
            | MainProofRewriteLedgerMaterializerReject::ContextRowMismatch { .. } => (0, 0),
        }
    }

    fn decompose_main_lrat_rewrite_reject_checker_visible_id(
        reject: &MainProofRewriteLedgerMaterializerReject,
    ) -> u64 {
        match reject {
            MainProofRewriteLedgerMaterializerReject::MissingAddRecord {
                checker_visible_id,
                ..
            }
            | MainProofRewriteLedgerMaterializerReject::MismatchedProofRecord {
                checker_visible_id,
                ..
            }
            | MainProofRewriteLedgerMaterializerReject::ProofRecordPayloadMismatch {
                checker_visible_id,
                ..
            }
            | MainProofRewriteLedgerMaterializerReject::ProofWriterIoError {
                checker_visible_id,
                ..
            }
            | MainProofRewriteLedgerMaterializerReject::RuntimeProofRecordNotEmitted {
                checker_visible_id,
                ..
            }
            | MainProofRewriteLedgerMaterializerReject::ExternalCheckerVerdictNotAccepted {
                checker_visible_id,
                ..
            }
            | MainProofRewriteLedgerMaterializerReject::MissingExternalCheckerVerdict {
                checker_visible_id,
                ..
            } => *checker_visible_id,
            MainProofRewriteLedgerMaterializerReject::MissingDeleteRecord {
                delete_source_id,
                ..
            } => *delete_source_id,
            MainProofRewriteLedgerMaterializerReject::ZeroId { .. }
            | MainProofRewriteLedgerMaterializerReject::SidecarContextCountMismatch { .. }
            | MainProofRewriteLedgerMaterializerReject::ContextRowMismatch { .. }
            | MainProofRewriteLedgerMaterializerReject::OriginalSourceBinding(_) => 0,
        }
    }

    fn source_bound_original_source_binding_reject_row(
        reject: &SourceBoundMultiplierOriginalSourceBindingReject,
    ) -> usize {
        match reject {
            SourceBoundMultiplierOriginalSourceBindingReject::ZeroSourceClauseId {
                sidecar_row_index,
            }
            | SourceBoundMultiplierOriginalSourceBindingReject::SourceClauseIdOverflow {
                sidecar_row_index,
                ..
            }
            | SourceBoundMultiplierOriginalSourceBindingReject::SourceClauseIdOutOfRange {
                sidecar_row_index,
                ..
            }
            | SourceBoundMultiplierOriginalSourceBindingReject::SourceClauseLiteralMismatch {
                sidecar_row_index,
                ..
            }
            | SourceBoundMultiplierOriginalSourceBindingReject::DeleteSourceIdMismatch {
                sidecar_row_index,
                ..
            } => *sidecar_row_index,
        }
    }

    /// Build LRAT hints for a substituted clause in decompose.
    ///
    /// Phase H (#4606): For each literal in the original clause:
    /// - If substituted: include the equivalence binary ID that proves orig → repr
    /// - If false at level 0: include its unit proof ID
    ///
    /// Appends the original clause ID last. CaDiCaL: decompose.cpp:526-576.
    fn build_decompose_subst_hints(
        &self,
        old_lits: &[Literal],
        reprs: &[Literal],
        decompose_equiv_ids: &[u64],
        original_cid: u64,
    ) -> Vec<u64> {
        let mut hints = Vec::new();
        for orig_lit in old_lits {
            let li = orig_lit.index();
            let mapped = reprs.get(li).copied().unwrap_or(*orig_lit);
            // Check if this literal was substituted (repr differs).
            if mapped != *orig_lit {
                // Include the equivalence binary proving orig_lit → repr.
                // The binary (repr ∨ ¬orig_lit) is stored at equiv_ids[orig_lit.negated()].
                let neg_idx = orig_lit.negated().index();
                if neg_idx < decompose_equiv_ids.len() {
                    let equiv_id = decompose_equiv_ids[neg_idx];
                    if equiv_id != 0 {
                        hints.push(equiv_id);
                    }
                }
            }
            // If the rewritten literal is false at level 0, include the proof
            // of its negation. This covers both unchanged literals already
            // falsified at the root and substituted literals whose mapped
            // representative is falsified at level 0.
            if self.lit_val(mapped) < 0 {
                if let Some(uid) = self.level0_var_proof_id_for_lit(mapped.negated()) {
                    hints.push(uid);
                }
            }
        }
        // Original clause ID last (CaDiCaL decompose.cpp:576).
        if original_cid != 0 {
            hints.push(original_cid);
        }
        hints
    }
}
