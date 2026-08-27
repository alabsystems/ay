// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Applies one successful BVE elimination result to solver state.

use super::super::super::mutate::{AddResult, ReasonPolicy, ReplaceResult};
use super::super::super::*;
use super::state::{BveBodyScratch, BveBodyStats};
use crate::bve::EliminationResult;
use crate::literal::Literal;
use crate::proof_manager::PlannedForwardAddReject;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct BveLratPlannedAdd {
    pub(super) expected_id: u64,
    pub(super) hints: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct BveLratTransactionPlan {
    pub(super) strengthening_adds: Vec<(usize, BveLratPlannedAdd)>,
    pub(super) resolvent_adds: Vec<(usize, BveLratPlannedAdd)>,
    pub(super) source_delete_ids: Vec<(usize, u64)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum BveLratRetainedPlanMismatch {
    AddShape {
        expected_strengthening: usize,
        retained_strengthening: usize,
        expected_resolvents: usize,
        retained_resolvents: usize,
    },
    StrengtheningClause {
        position: usize,
        expected: usize,
        retained: usize,
    },
    ResolventIndex {
        position: usize,
        expected: usize,
        retained: usize,
    },
    OutputId {
        position: usize,
        expected: u64,
        retained: u64,
    },
    HintChain {
        position: usize,
    },
    SourceDeleteShape {
        expected: usize,
        retained: usize,
    },
    SourceDeleteClause {
        position: usize,
        expected: usize,
        retained: usize,
    },
    SourceDeleteId {
        position: usize,
        expected: u64,
        retained: u64,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum BveLratTransactionReject {
    MissingProofManager,
    MissingOrHiddenSourceId { clause_idx: usize, clause_id: u64 },
    DeletionTargetNotLive { clause_idx: usize, clause_id: u64 },
    MalformedStrengthening { clause_idx: usize },
    MalformedResolvent { resolvent_idx: usize },
    ReplacementCleanupWouldEmitUnit { clause_idx: usize },
    PlannedAddRejected(PlannedForwardAddReject),
    RetainedPlanMismatch(BveLratRetainedPlanMismatch),
}

impl Solver {
    pub(super) fn record_bve_lrat_preflight_reject(&mut self, reject: &BveLratTransactionReject) {
        let stats = self.inproc.bve.stats_mut();
        stats.lrat_preflight_rejected = stats.lrat_preflight_rejected.saturating_add(1);
        match reject {
            BveLratTransactionReject::MissingProofManager => {
                stats.lrat_preflight_missing_proof_manager =
                    stats.lrat_preflight_missing_proof_manager.saturating_add(1);
            }
            BveLratTransactionReject::MissingOrHiddenSourceId { .. } => {
                stats.lrat_preflight_missing_or_hidden_source_id = stats
                    .lrat_preflight_missing_or_hidden_source_id
                    .saturating_add(1);
            }
            BveLratTransactionReject::DeletionTargetNotLive { .. } => {
                stats.lrat_preflight_deletion_target_not_live = stats
                    .lrat_preflight_deletion_target_not_live
                    .saturating_add(1);
            }
            BveLratTransactionReject::MalformedStrengthening { .. } => {
                stats.lrat_preflight_malformed_strengthening = stats
                    .lrat_preflight_malformed_strengthening
                    .saturating_add(1);
            }
            BveLratTransactionReject::MalformedResolvent { .. } => {
                stats.lrat_preflight_malformed_resolvent =
                    stats.lrat_preflight_malformed_resolvent.saturating_add(1);
            }
            BveLratTransactionReject::ReplacementCleanupWouldEmitUnit { .. } => {
                stats.lrat_preflight_replacement_cleanup_unit = stats
                    .lrat_preflight_replacement_cleanup_unit
                    .saturating_add(1);
            }
            BveLratTransactionReject::PlannedAddRejected(reason) => {
                stats.lrat_preflight_planned_add_rejected =
                    stats.lrat_preflight_planned_add_rejected.saturating_add(1);
                match reason {
                    PlannedForwardAddReject::NotLrat => {
                        stats.lrat_preflight_planned_not_lrat =
                            stats.lrat_preflight_planned_not_lrat.saturating_add(1);
                    }
                    PlannedForwardAddReject::LratBlocked => {
                        stats.lrat_preflight_planned_lrat_blocked =
                            stats.lrat_preflight_planned_lrat_blocked.saturating_add(1);
                    }
                    PlannedForwardAddReject::IoFailed => {
                        stats.lrat_preflight_planned_io_failed =
                            stats.lrat_preflight_planned_io_failed.saturating_add(1);
                    }
                    PlannedForwardAddReject::PendingDeletions => {
                        stats.lrat_preflight_planned_pending_deletions = stats
                            .lrat_preflight_planned_pending_deletions
                            .saturating_add(1);
                    }
                    PlannedForwardAddReject::OutputIdMismatch => {
                        stats.lrat_preflight_planned_output_id_mismatch = stats
                            .lrat_preflight_planned_output_id_mismatch
                            .saturating_add(1);
                    }
                    PlannedForwardAddReject::InvalidClause => {
                        stats.lrat_preflight_planned_invalid_clause = stats
                            .lrat_preflight_planned_invalid_clause
                            .saturating_add(1);
                    }
                    PlannedForwardAddReject::SuppressedAxiom => {
                        stats.lrat_preflight_planned_suppressed_axiom = stats
                            .lrat_preflight_planned_suppressed_axiom
                            .saturating_add(1);
                    }
                    PlannedForwardAddReject::UnverifiedTrustedTransform => {
                        stats.lrat_preflight_planned_hidden_trusted_unit = stats
                            .lrat_preflight_planned_hidden_trusted_unit
                            .saturating_add(1);
                    }
                    PlannedForwardAddReject::DerivedMissingHints => {
                        stats.lrat_preflight_planned_missing_hints =
                            stats.lrat_preflight_planned_missing_hints.saturating_add(1);
                    }
                    PlannedForwardAddReject::ZeroHint => {
                        stats.lrat_preflight_planned_zero_hint =
                            stats.lrat_preflight_planned_zero_hint.saturating_add(1);
                    }
                    PlannedForwardAddReject::DuplicateHint => {
                        stats.lrat_preflight_planned_duplicate_hint = stats
                            .lrat_preflight_planned_duplicate_hint
                            .saturating_add(1);
                    }
                    PlannedForwardAddReject::UnknownHint => {
                        stats.lrat_preflight_planned_unknown_hint =
                            stats.lrat_preflight_planned_unknown_hint.saturating_add(1);
                    }
                    PlannedForwardAddReject::TrustedHint => {
                        stats.lrat_preflight_planned_trusted_hint =
                            stats.lrat_preflight_planned_trusted_hint.saturating_add(1);
                    }
                    PlannedForwardAddReject::BackwardReservedHint => {
                        stats.lrat_preflight_planned_backward_reserved_hint = stats
                            .lrat_preflight_planned_backward_reserved_hint
                            .saturating_add(1);
                    }
                    PlannedForwardAddReject::IdOverflow => {
                        stats.lrat_preflight_planned_id_overflow =
                            stats.lrat_preflight_planned_id_overflow.saturating_add(1);
                    }
                }
            }
            BveLratTransactionReject::RetainedPlanMismatch(_) => {}
        }
    }

    fn bve_lrat_source_id(&self, clause_idx: usize) -> Result<u64, BveLratTransactionReject> {
        let clause_id = self.clause_id(ClauseRef(clause_idx as u32));
        if clause_idx >= self.arena.len() || !self.arena.is_active(clause_idx) {
            return Err(BveLratTransactionReject::MissingOrHiddenSourceId {
                clause_idx,
                clause_id,
            });
        }
        if clause_id == 0 || !self.lrat_hint_id_visible(clause_id) {
            return Err(BveLratTransactionReject::MissingOrHiddenSourceId {
                clause_idx,
                clause_id,
            });
        }
        match self.proof_manager.as_ref() {
            Some(manager) if manager.is_known_lrat_id(clause_id) => Ok(clause_id),
            Some(_) => Err(BveLratTransactionReject::MissingOrHiddenSourceId {
                clause_idx,
                clause_id,
            }),
            None => Err(BveLratTransactionReject::MissingProofManager),
        }
    }

    fn bve_lrat_current_source_id(
        &self,
        clause_idx: usize,
        current_ids: &std::collections::BTreeMap<usize, u64>,
    ) -> Result<u64, BveLratTransactionReject> {
        if let Some(&clause_id) = current_ids.get(&clause_idx) {
            if clause_idx < self.arena.len() && self.arena.is_active(clause_idx) {
                return Ok(clause_id);
            }
            return Err(BveLratTransactionReject::MissingOrHiddenSourceId {
                clause_idx,
                clause_id,
            });
        }
        self.bve_lrat_source_id(clause_idx)
    }

    fn bve_lrat_clause_well_formed(&self, clause: &[Literal]) -> bool {
        if clause.is_empty() {
            return false;
        }
        for (i, &lit) in clause.iter().enumerate() {
            if lit.variable().index() >= self.num_vars {
                return false;
            }
            for &prev in &clause[..i] {
                if prev.variable() == lit.variable() {
                    return false;
                }
            }
        }
        true
    }

    fn bve_lrat_delete_id(&self, clause_idx: usize) -> Result<u64, BveLratTransactionReject> {
        let clause_id = self.clause_id(ClauseRef(clause_idx as u32));
        if clause_idx >= self.arena.len() || !self.arena.is_active(clause_idx) {
            return Err(BveLratTransactionReject::DeletionTargetNotLive {
                clause_idx,
                clause_id,
            });
        }
        self.bve_lrat_source_id(clause_idx)
    }

    fn bve_lrat_push_delete_id(
        &self,
        clause_idx: usize,
        seen: &mut std::collections::BTreeSet<u64>,
        out: &mut Vec<(usize, u64)>,
    ) -> Result<(), BveLratTransactionReject> {
        let clause_id = self.bve_lrat_delete_id(clause_idx)?;
        if !seen.insert(clause_id) {
            return Ok(());
        }
        out.push((clause_idx, clause_id));
        Ok(())
    }

    fn bve_lrat_replacement_cleanup_would_emit_unit(
        &self,
        clause_idx: usize,
        new_lits: &[Literal],
    ) -> bool {
        if !self.cold.lrat_enabled || self.clause_id(ClauseRef(clause_idx as u32)) == 0 {
            return false;
        }
        let clause_ref = ClauseRef(clause_idx as u32);
        for &old_lit in self.arena.literals(clause_idx) {
            let vi = old_lit.variable().index();
            if vi >= self.num_vars
                || self.var_data[vi].reason != clause_ref.0
                || self.var_data[vi].level != 0
            {
                continue;
            }
            let Some(val) = self.var_value_from_vals(vi) else {
                continue;
            };
            let assigned_lit = if val {
                Literal::positive(Variable(vi as u32))
            } else {
                Literal::negative(Variable(vi as u32))
            };
            if !new_lits.contains(&assigned_lit) {
                return true;
            }
        }
        false
    }

    pub(super) fn preflight_bve_lrat_transaction(
        &mut self,
        result: &EliminationResult,
    ) -> Result<BveLratTransactionPlan, BveLratTransactionReject> {
        if !self.cold.lrat_enabled {
            return Ok(BveLratTransactionPlan {
                strengthening_adds: Vec::new(),
                resolvent_adds: Vec::new(),
                source_delete_ids: Vec::new(),
            });
        }
        let Some(manager) = self.proof_manager.as_mut() else {
            return Err(BveLratTransactionReject::MissingProofManager);
        };
        let _ = manager.flush();
        let Some(manager) = self.proof_manager.as_ref() else {
            return Err(BveLratTransactionReject::MissingProofManager);
        };
        let planned_add_count = result.strengthened.len() + result.resolvents.len();
        let planned_add_ids = manager
            .planned_forward_add_ids(planned_add_count)
            .map_err(BveLratTransactionReject::PlannedAddRejected)?;

        let mut current_ids = std::collections::BTreeMap::new();
        let mut planned_visible_ids = Vec::with_capacity(planned_add_ids.len());
        let mut strengthening_adds = Vec::with_capacity(result.strengthened.len());
        let mut resolvent_adds = Vec::with_capacity(result.resolvents.len());
        let mut planned_add_pos = 0usize;
        let mut source_delete_ids = Vec::new();
        let mut source_delete_seen = std::collections::BTreeSet::new();

        for strengthening in &result.strengthened {
            let clause_idx = strengthening.clause_idx;
            let old_clause_id = self.bve_lrat_current_source_id(clause_idx, &current_ids)?;
            let pos_id = self.bve_lrat_current_source_id(strengthening.pos_ante, &current_ids)?;
            let neg_id = self.bve_lrat_current_source_id(strengthening.neg_ante, &current_ids)?;
            if clause_idx != strengthening.pos_ante && clause_idx != strengthening.neg_ante {
                return Err(BveLratTransactionReject::MalformedStrengthening { clause_idx });
            }
            if !self.bve_lrat_clause_well_formed(&strengthening.new_lits)
                || strengthening.new_lits.len() > self.arena.len_of(clause_idx)
                || (strengthening.new_lits.len() == 1
                    && self.lit_value(strengthening.new_lits[0]) == Some(false))
            {
                return Err(BveLratTransactionReject::MalformedStrengthening { clause_idx });
            }
            if self
                .bve_lrat_replacement_cleanup_would_emit_unit(clause_idx, &strengthening.new_lits)
            {
                return Err(BveLratTransactionReject::ReplacementCleanupWouldEmitUnit {
                    clause_idx,
                });
            }

            let exclude: Vec<usize> = strengthening
                .new_lits
                .iter()
                .map(|l| l.variable().index())
                .collect();
            let chain = self.collect_level0_reason_chain(&strengthening.pruned_vars, &exclude);
            let mut hints = Vec::with_capacity(2 + chain.len());
            hints.extend_from_slice(&chain);
            Self::push_lrat_hint(&mut hints, old_clause_id);
            let other_ante_id = if clause_idx == strengthening.pos_ante {
                neg_id
            } else {
                pos_id
            };
            if other_ante_id != old_clause_id {
                Self::push_lrat_hint(&mut hints, other_ante_id);
            }

            let expected_id = planned_add_ids[planned_add_pos];
            self.proof_manager
                .as_ref()
                .ok_or(BveLratTransactionReject::MissingProofManager)?
                .preflight_forward_lrat_add_with_planned_ids(
                    &strengthening.new_lits,
                    &hints,
                    ProofAddKind::Derived,
                    &planned_visible_ids,
                )
                .map_err(BveLratTransactionReject::PlannedAddRejected)?;
            strengthening_adds.push((clause_idx, BveLratPlannedAdd { expected_id, hints }));
            current_ids.insert(clause_idx, expected_id);
            planned_visible_ids.push(expected_id);
            planned_add_pos += 1;
            self.bve_lrat_push_delete_id(
                clause_idx,
                &mut source_delete_seen,
                &mut source_delete_ids,
            )?;
        }

        for (resolvent_idx, (resolvent, pos_ante, neg_ante, pruned_vars)) in
            result.resolvents.iter().enumerate()
        {
            if (!resolvent.is_empty() && !self.bve_lrat_clause_well_formed(resolvent))
                || resolvent.iter().any(|l| l.variable() == result.variable)
                || (resolvent.len() == 1 && self.lit_value(resolvent[0]) == Some(false))
            {
                return Err(BveLratTransactionReject::MalformedResolvent { resolvent_idx });
            }

            let pos_id = self.bve_lrat_current_source_id(*pos_ante, &current_ids)?;
            let neg_id = self.bve_lrat_current_source_id(*neg_ante, &current_ids)?;
            let exclude: Vec<usize> = resolvent.iter().map(|l| l.variable().index()).collect();
            let chain_hints = self.collect_level0_reason_chain(pruned_vars, &exclude);
            let mut hints = Vec::with_capacity(2 + chain_hints.len());
            hints.extend_from_slice(&chain_hints);
            Self::push_lrat_hint(&mut hints, neg_id);
            Self::push_lrat_hint(&mut hints, pos_id);

            let expected_id = planned_add_ids[planned_add_pos];
            self.proof_manager
                .as_ref()
                .ok_or(BveLratTransactionReject::MissingProofManager)?
                .preflight_forward_lrat_add_with_planned_ids(
                    resolvent,
                    &hints,
                    ProofAddKind::Derived,
                    &planned_visible_ids,
                )
                .map_err(BveLratTransactionReject::PlannedAddRejected)?;
            resolvent_adds.push((resolvent_idx, BveLratPlannedAdd { expected_id, hints }));
            planned_visible_ids.push(expected_id);
            planned_add_pos += 1;
        }

        let strengthened_targets: std::collections::BTreeSet<usize> = result
            .strengthened
            .iter()
            .map(|strengthening| strengthening.clause_idx)
            .collect();
        for &clause_idx in &result.satisfied_parents {
            self.bve_lrat_push_delete_id(
                clause_idx,
                &mut source_delete_seen,
                &mut source_delete_ids,
            )?;
        }
        for &clause_idx in &result.to_delete {
            if strengthened_targets.contains(&clause_idx) {
                continue;
            }
            self.bve_lrat_push_delete_id(
                clause_idx,
                &mut source_delete_seen,
                &mut source_delete_ids,
            )?;
        }

        debug_assert_eq!(planned_add_pos, planned_add_ids.len());
        Ok(BveLratTransactionPlan {
            strengthening_adds,
            resolvent_adds,
            source_delete_ids,
        })
    }

    fn classify_bve_lrat_retained_plan_mismatch(
        expected: &BveLratTransactionPlan,
        retained: &BveLratTransactionPlan,
    ) -> BveLratRetainedPlanMismatch {
        if expected.strengthening_adds.len() != retained.strengthening_adds.len()
            || expected.resolvent_adds.len() != retained.resolvent_adds.len()
        {
            return BveLratRetainedPlanMismatch::AddShape {
                expected_strengthening: expected.strengthening_adds.len(),
                retained_strengthening: retained.strengthening_adds.len(),
                expected_resolvents: expected.resolvent_adds.len(),
                retained_resolvents: retained.resolvent_adds.len(),
            };
        }

        let mut add_position = 0usize;
        for (
            strengthening_position,
            ((expected_clause_idx, expected_add), (retained_clause_idx, retained_add)),
        ) in expected
            .strengthening_adds
            .iter()
            .zip(retained.strengthening_adds.iter())
            .enumerate()
        {
            if expected_clause_idx != retained_clause_idx {
                return BveLratRetainedPlanMismatch::StrengtheningClause {
                    position: strengthening_position,
                    expected: *expected_clause_idx,
                    retained: *retained_clause_idx,
                };
            }
            if expected_add.expected_id != retained_add.expected_id {
                return BveLratRetainedPlanMismatch::OutputId {
                    position: add_position,
                    expected: expected_add.expected_id,
                    retained: retained_add.expected_id,
                };
            }
            if expected_add.hints != retained_add.hints {
                return BveLratRetainedPlanMismatch::HintChain {
                    position: add_position,
                };
            }
            add_position += 1;
        }

        for (
            resolvent_position,
            ((expected_resolvent_idx, expected_add), (retained_resolvent_idx, retained_add)),
        ) in expected
            .resolvent_adds
            .iter()
            .zip(retained.resolvent_adds.iter())
            .enumerate()
        {
            if expected_resolvent_idx != retained_resolvent_idx {
                return BveLratRetainedPlanMismatch::ResolventIndex {
                    position: resolvent_position,
                    expected: *expected_resolvent_idx,
                    retained: *retained_resolvent_idx,
                };
            }
            if expected_add.expected_id != retained_add.expected_id {
                return BveLratRetainedPlanMismatch::OutputId {
                    position: add_position,
                    expected: expected_add.expected_id,
                    retained: retained_add.expected_id,
                };
            }
            if expected_add.hints != retained_add.hints {
                return BveLratRetainedPlanMismatch::HintChain {
                    position: add_position,
                };
            }
            add_position += 1;
        }

        if expected.source_delete_ids.len() != retained.source_delete_ids.len() {
            return BveLratRetainedPlanMismatch::SourceDeleteShape {
                expected: expected.source_delete_ids.len(),
                retained: retained.source_delete_ids.len(),
            };
        }
        for (
            delete_position,
            ((expected_clause_idx, expected_id), (retained_clause_idx, retained_id)),
        ) in expected
            .source_delete_ids
            .iter()
            .zip(retained.source_delete_ids.iter())
            .enumerate()
        {
            if expected_clause_idx != retained_clause_idx {
                return BveLratRetainedPlanMismatch::SourceDeleteClause {
                    position: delete_position,
                    expected: *expected_clause_idx,
                    retained: *retained_clause_idx,
                };
            }
            if expected_id != retained_id {
                return BveLratRetainedPlanMismatch::SourceDeleteId {
                    position: delete_position,
                    expected: *expected_id,
                    retained: *retained_id,
                };
            }
        }

        BveLratRetainedPlanMismatch::AddShape {
            expected_strengthening: expected.strengthening_adds.len(),
            retained_strengthening: retained.strengthening_adds.len(),
            expected_resolvents: expected.resolvent_adds.len(),
            retained_resolvents: retained.resolvent_adds.len(),
        }
    }

    pub(super) fn validate_bve_lrat_retained_plan(
        &mut self,
        result: &EliminationResult,
        retained: &BveLratTransactionPlan,
    ) -> Result<(), BveLratTransactionReject> {
        let expected = self.preflight_bve_lrat_transaction(result)?;
        if expected == *retained {
            return Ok(());
        }
        Err(BveLratTransactionReject::RetainedPlanMismatch(
            Self::classify_bve_lrat_retained_plan_mismatch(&expected, retained),
        ))
    }

    /// Apply one BVE elimination to solver state.
    ///
    /// The reconstruction completeness guard (both polarities present in
    /// witness entries) is checked during elimination planning in
    /// `eliminate.rs` (#8179). By the time we reach application, the
    /// elimination has been approved. The witness-entry loop below
    /// gracefully skips entries whose clauses were deleted between
    /// planning and application (`literals_or_deleted` returns empty),
    /// preserving reconstruction correctness without rejecting the
    /// elimination entirely.
    ///
    /// The previous pre-flight check here (removed in #8186) rejected
    /// eliminations when `literals_or_deleted` returned empty for witness
    /// clauses deleted by prior eliminations in the same round. This was
    /// overly strict and caused a 40%+ BVE regression on FmlaEquivChain.
    pub(super) fn apply_bve_elimination_result(
        &mut self,
        result: &EliminationResult,
        scratch: &mut BveBodyScratch,
        stats: &mut BveBodyStats,
        pending_gc_indices: &mut Vec<usize>,
        derived_unsat: &mut bool,
        lrat_plan: Option<&BveLratTransactionPlan>,
    ) -> Result<(), BveLratTransactionReject> {
        let var = result.variable;
        assert!(
            !self.cold.lrat_enabled || lrat_plan.is_some(),
            "BUG: BVE LRAT apply called without a transaction plan"
        );
        let lrat_plan = if self.cold.lrat_enabled {
            if let Some(plan) = lrat_plan {
                self.validate_bve_lrat_retained_plan(result, plan)?;
            }
            lrat_plan
        } else {
            None
        };

        self.inproc
            .bve
            .update_occs_after_elimination(&result.to_delete, &self.arena);
        stats.total_eliminations += 1;
        self.var_lifecycle.mark_eliminated(var.index());
        self.vsids.remove_from_heap(var);
        // Track eliminated variables for occ-guided post-elimination GC (#3521).
        scratch.eliminated_vars.push(var);

        scratch.kept_strengthened.clear();
        let mut strengthening_plan_pos = 0usize;
        let mut source_delete_plan_pos = 0usize;
        for strengthening in &result.strengthened {
            let clause_idx = strengthening.clause_idx;
            if !self.arena.is_active(clause_idx) {
                debug_assert!(
                    lrat_plan.is_none(),
                    "BUG: LRAT BVE plan accepted inactive strengthening target {clause_idx}"
                );
                continue;
            }
            let planned_strengthening =
                lrat_plan.and_then(|plan| plan.strengthening_adds.get(strengthening_plan_pos));
            if let Some((planned_clause_idx, _)) = planned_strengthening {
                debug_assert_eq!(*planned_clause_idx, clause_idx);
            }
            scratch.old_lits_buf.clear();
            scratch
                .old_lits_buf
                .extend_from_slice(self.arena.literals(clause_idx));
            let old_clause_id = self.clause_id(ClauseRef(clause_idx as u32));
            if let Some(plan) = lrat_plan {
                let (planned_clause_idx, planned_delete_id) =
                    plan.source_delete_ids[source_delete_plan_pos];
                debug_assert_eq!(planned_clause_idx, clause_idx);
                debug_assert_eq!(planned_delete_id, old_clause_id);
            }
            let otfs_hints: Vec<u64> = if let Some((_, planned)) = planned_strengthening {
                planned.hints.clone()
            } else if self.cold.lrat_enabled {
                let pid = self.clause_id(ClauseRef(strengthening.pos_ante as u32));
                let nid = self.clause_id(ClauseRef(strengthening.neg_ante as u32));
                let other_ante_id = if clause_idx == strengthening.pos_ante {
                    nid
                } else {
                    pid
                };
                let exclude: Vec<usize> = strengthening
                    .new_lits
                    .iter()
                    .map(|l| l.variable().index())
                    .collect();
                let chain = self.collect_level0_reason_chain(&strengthening.pruned_vars, &exclude);

                let mut h = Vec::with_capacity(2 + chain.len());
                h.extend_from_slice(&chain);
                if old_clause_id != 0 {
                    h.push(old_clause_id);
                }
                if other_ante_id != 0 && other_ante_id != old_clause_id {
                    h.push(other_ante_id);
                }
                h
            } else {
                vec![]
            };
            match self.replace_clause_with_final_hints(
                clause_idx,
                &strengthening.new_lits,
                &otfs_hints,
            ) {
                ReplaceResult::Replaced | ReplaceResult::Unit => {
                    if let Some((_, planned)) = planned_strengthening {
                        debug_assert_eq!(
                            self.clause_id(ClauseRef(clause_idx as u32)),
                            planned.expected_id
                        );
                    }
                    strengthening_plan_pos += 1;
                    source_delete_plan_pos += 1;
                    scratch.new_lits_buf.clear();
                    scratch
                        .new_lits_buf
                        .extend_from_slice(self.arena.literals(clause_idx));
                    self.inproc.bve.notify_clause_replaced(
                        clause_idx,
                        &scratch.old_lits_buf,
                        &scratch.new_lits_buf,
                    );
                    pending_gc_indices.push(clause_idx);
                    let pos_lit = Literal::positive(var);
                    let neg_lit = Literal::negative(var);
                    let pivot_in_old = scratch
                        .old_lits_buf
                        .iter()
                        .find(|&&l| l == pos_lit || l == neg_lit)
                        .copied();
                    if let Some(pivot) = pivot_in_old {
                        scratch.otfs_old_clauses.push((
                            clause_idx,
                            pivot,
                            scratch.old_lits_buf.clone(),
                        ));
                    }
                    scratch.kept_strengthened.push(clause_idx);
                }
                ReplaceResult::Empty => {
                    if let Some((_, planned)) = planned_strengthening {
                        debug_assert_eq!(
                            self.clause_id(ClauseRef(clause_idx as u32)),
                            planned.expected_id
                        );
                    }
                    strengthening_plan_pos += 1;
                    source_delete_plan_pos += 1;
                    *derived_unsat = true;
                    break;
                }
                ReplaceResult::Skipped => {
                    debug_assert!(
                        lrat_plan.is_none(),
                        "BUG: LRAT BVE planned strengthening was skipped"
                    );
                }
            }
        }
        if let Some(plan) = lrat_plan {
            debug_assert_eq!(strengthening_plan_pos, plan.strengthening_adds.len());
        }
        scratch.kept_strengthened.sort_unstable();

        if *derived_unsat {
            return Ok(());
        }

        if let Some(ref writer) = self.cold.diagnostic_trace {
            writer.emit_var_transition(
                var.0,
                crate::diagnostic_trace::VarState::Active,
                crate::diagnostic_trace::VarState::Eliminated,
                self.cold.diagnostic_pass,
            );
        }

        // Keep every earlier conditional-autarky entry, including BCE/CCE
        // witnesses on this pivot. Those entries can describe clauses already
        // deleted from the occurrence lists, so this BVE transaction cannot
        // replace their reconstruction obligations. Reverse chronological
        // replay composes the transformations soundly. CaDiCaL likewise pushes
        // the witness before checking its external `marked(witness, lit)` bit;
        // that bit tracks external witness literals and does not deduplicate
        // entries.
        for entry in &result.witness_entries {
            let idx = entry.clause_idx;
            if scratch.kept_strengthened.binary_search(&idx).is_ok() {
                continue;
            }
            // CaDiCaL elim.cpp:624-625: skip clauses already marked as
            // garbage. In CaDiCaL, root-level-satisfied parent clauses are
            // marked garbage during resolve_clauses (elim.cpp:319) and are
            // therefore skipped in mark_eliminated_clauses_as_garbage
            // (elim.cpp:624). They are NOT pushed onto the extension stack.
            //
            // Why this matters (#8356): if a satisfied parent clause P
            // contains literal `a` that is true at level 0, reconstruction
            // expects `a` to still be true when processing P. But if `a`'s
            // variable is eliminated in a later BVE round, its
            // reconstruction (processed first in reverse) can flip `a` to
            // false. Then P is no longer satisfied, and the witness variable
            // gets incorrectly flipped, corrupting the model.
            //
            // Fix: skip satisfied parents, matching CaDiCaL's behavior.
            // The reconstruction does not need these clauses because the
            // corresponding resolution pairs were never generated (the
            // resolution returned ParentSatisfied, so no resolvent exists
            // to guarantee the negative clause's satisfaction).
            if result.satisfied_parents.contains(&idx) {
                continue;
            }
            // CaDiCaL pushes ALL defining clauses onto the extension stack
            // before any deletion (external.cpp:55-69, elim.cpp:628-670).
            // AY must do the same: a prior variable's elim_propagate may have
            // deleted this clause, but we still need its literals for
            // reconstruction. Use literals_or_deleted() to recover literals
            // from garbage-marked arena slots (#5059).
            let lits = self.arena.literals_or_deleted(idx);
            if lits.is_empty() {
                continue;
            }
            let ext_witness = self.externalize(entry.witness);
            let ext_lits = self.externalize_lits(lits);
            self.inproc
                .reconstruction
                .push_witness_clause(vec![ext_witness], ext_lits);
        }

        // CaDiCaL does NOT push OTFS-strengthened original clauses onto the
        // extension stack (elim.cpp:209-230, 623-638). The original clause is
        // marked garbage during resolution; the strengthened replacement (pivot
        // removed) stays in the formula. When the extension stack is populated,
        // garbage clauses are skipped (line 625). The strengthened clause no
        // longer contains the pivot, so it does not appear in the pivot's
        // occurrence list and is not pushed either.
        //
        // Pushing old OTFS clauses is unsound: the old clause contains the
        // pivot AND other literals whose truth values may be changed by
        // reconstruction of other eliminated variables. The extra entry can
        // force the pivot variable to a value that breaks clauses already
        // satisfied by the CDCL assignment. (#8133)
        //
        // The strengthened clause (without pivot) constrains the model directly
        // through CDCL search — it does not need reconstruction.
        scratch.otfs_old_clauses.clear();

        let mut resolvent_plan_pos = 0usize;
        for (resolvent_idx, (resolvent, pos_ante, neg_ante, pruned_vars)) in
            result.resolvents.iter().enumerate()
        {
            let planned_resolvent =
                lrat_plan.and_then(|plan| plan.resolvent_adds.get(resolvent_plan_pos));
            if let Some((planned_resolvent_idx, _)) = planned_resolvent {
                debug_assert_eq!(*planned_resolvent_idx, resolvent_idx);
            }
            let hints = if let Some((_, planned)) = planned_resolvent {
                planned.hints.clone()
            } else if self.cold.lrat_enabled {
                let pos_id = self.clause_id(ClauseRef(*pos_ante as u32));
                let neg_id = self.clause_id(ClauseRef(*neg_ante as u32));
                debug_assert!(
                    pos_id != 0,
                    "BUG: BVE positive antecedent clause (arena offset {pos_ante}) has LRAT ID 0. \
                     Resolvent: {resolvent:?}, var: {var:?}",
                );
                debug_assert!(
                    neg_id != 0,
                    "BUG: BVE negative antecedent clause (arena offset {neg_ante}) has LRAT ID 0. \
                     Resolvent: {resolvent:?}, var: {var:?}",
                );
                let exclude: Vec<usize> = resolvent.iter().map(|l| l.variable().index()).collect();
                let chain_hints = self.collect_level0_reason_chain(pruned_vars, &exclude);

                let mut hints_vec: Vec<u64> = Vec::with_capacity(2 + chain_hints.len());
                hints_vec.extend_from_slice(&chain_hints);
                hints_vec.push(neg_id);
                hints_vec.push(pos_id);
                hints_vec
            } else {
                Vec::new()
            };

            if resolvent.is_empty() {
                *derived_unsat = true;
                self.mark_empty_clause_with_hints(&hints);
                if let Some((_, planned)) = planned_resolvent {
                    debug_assert_eq!(self.cold.empty_clause_lrat_id, Some(planned.expected_id));
                }
                resolvent_plan_pos += 1;
                continue;
            }

            debug_assert!(
                !resolvent.iter().any(|l| l.variable() == var),
                "BUG: BVE resolvent contains eliminated variable {var:?}",
            );
            debug_assert!(
                !resolvent.iter().any(|l| resolvent.contains(&l.negated())),
                "BUG: BVE resolvent is a tautology (contains l and ~l)",
            );

            if let Ok(new_id) =
                self.proof_emit_add_prechecked(resolvent, &hints, ProofAddKind::Derived)
            {
                if let Some((_, planned)) = planned_resolvent {
                    debug_assert_eq!(new_id, planned.expected_id);
                }
                if self.cold.lrat_enabled && new_id != 0 {
                    self.cold.next_clause_id = new_id;
                }
            }
            resolvent_plan_pos += 1;

            scratch.add_buf.clear();
            scratch.add_buf.extend_from_slice(resolvent);
            let add_result = self.add_clause_watched(&mut scratch.add_buf);

            match add_result {
                AddResult::Added(cref) | AddResult::Unit(cref) => {
                    let clause_idx = cref.0 as usize;
                    scratch.new_lits_buf.clear();
                    scratch
                        .new_lits_buf
                        .extend_from_slice(self.arena.literals(clause_idx));

                    self.inproc
                        .bve
                        .notify_resolvent_added(clause_idx, &scratch.new_lits_buf);
                    self.inproc
                        .bve
                        .update_schedule_after_clause_addition(&scratch.new_lits_buf);
                    // Keep the resolvent for a later subsume pass, but do not
                    // let fresh same-round BVE resolvents cascade into
                    // backward subsumption or strengthening (#7916).
                    self.mark_subsume_dirty_if_kept(clause_idx);
                    // Collect for inter-round backward subsumption (#5049).
                    scratch.resolvent_indices.push(clause_idx);
                    stats.resolvents_total += 1;
                }
                AddResult::Empty => {}
            }

            if self.has_empty_clause {
                *derived_unsat = true;
            }
        }
        if let Some(plan) = lrat_plan {
            debug_assert_eq!(resolvent_plan_pos, plan.resolvent_adds.len());
        }

        let mut deleted_source_indices = std::collections::BTreeSet::new();
        for &c_idx in &result.satisfied_parents {
            if !deleted_source_indices.insert(c_idx) {
                continue;
            }
            scratch.old_lits_buf.clear();
            scratch
                .old_lits_buf
                .extend_from_slice(self.arena.literals(c_idx));
            if let Some(plan) = lrat_plan {
                let (planned_clause_idx, planned_delete_id) =
                    plan.source_delete_ids[source_delete_plan_pos];
                debug_assert_eq!(planned_clause_idx, c_idx);
                debug_assert_eq!(planned_delete_id, self.clause_id(ClauseRef(c_idx as u32)));
            }
            self.delete_clause_checked(c_idx, ReasonPolicy::ClearLevel0);
            source_delete_plan_pos += usize::from(lrat_plan.is_some());
            self.inproc.bve.update_schedule_after_clause_removal(
                &scratch.old_lits_buf,
                var,
                &self.vals,
                &self.cold.freeze_counts,
            );
        }

        for &clause_idx in &result.to_delete {
            if scratch.kept_strengthened.binary_search(&clause_idx).is_ok() {
                continue;
            }
            if !deleted_source_indices.insert(clause_idx) {
                continue;
            }
            scratch.old_lits_buf.clear();
            scratch
                .old_lits_buf
                .extend_from_slice(self.arena.literals(clause_idx));
            if let Some(plan) = lrat_plan {
                let (planned_clause_idx, planned_delete_id) =
                    plan.source_delete_ids[source_delete_plan_pos];
                debug_assert_eq!(planned_clause_idx, clause_idx);
                debug_assert_eq!(
                    planned_delete_id,
                    self.clause_id(ClauseRef(clause_idx as u32))
                );
            }
            self.delete_clause_checked(clause_idx, ReasonPolicy::ClearLevel0);
            source_delete_plan_pos += usize::from(lrat_plan.is_some());
            self.inproc.bve.update_schedule_after_clause_removal(
                &scratch.old_lits_buf,
                var,
                &self.vals,
                &self.cold.freeze_counts,
            );
        }
        if let Some(plan) = lrat_plan {
            debug_assert_eq!(source_delete_plan_pos, plan.source_delete_ids.len());
        }

        // CaDiCaL elim.cpp:251-263: do NOT run elim_propagate after adding
        // resolvents. CaDiCaL only propagates eagerly during the *counting*
        // phase (elim_resolvents_are_bounded with propagate_eagerly=true),
        // never after adding resolvents (elim_add_resolvents passes false).
        //
        // Why: elim_propagate deletes root-level-satisfied clauses from occ
        // lists. A resolvent R added for variable A may be satisfied by a
        // unit derived from another resolvent. If elim_propagate deletes R,
        // then when variable B is later eliminated, R is missing from B's
        // occ lists. No witness entry is created for R in B's reconstruction
        // stack, causing cascading reconstruction corruption (#8356).
        //
        // Units from resolvent addition are already enqueued on the trail by
        // add_clause_watched. They will be propagated via search_propagate
        // after watches are reconnected post-BVE. UNSAT detection is
        // preserved: add_clause_watched handles empty resolvents and
        // contradictory units at level 0.
        //
        // Satisfied clauses remain in occ lists until the next occ rebuild
        // (next round or next BVE phase). This may cause slightly more
        // resolution attempts for subsequent variables, but is correct.

        // Resolvent indices are collected for per-variable backward
        // subsumption in body.rs (#7998). After apply returns, the caller
        // runs backward subsumption on these resolvents immediately, matching
        // CaDiCaL's inline elim_backward_clauses pattern (elim.cpp:731).
        // The extension stack entries have been pushed above, so backward
        // subsumption is safe: any clause it deletes was already saved.
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::super::FASTELIM_OCC_LIMIT;
    use super::*;
    use crate::{
        bve::EliminationResult, ProofOutput, SatFeatures, SolverVariant, VariantInput,
        VariantProfilePlan, VariantProofMode::Lrat, VariantRouteProfile, VariantStartupPolicy,
    };
    use ay_test_support::{build_ay_lrat_checker, BuiltWorkspaceBinary};
    use std::fs;
    use std::path::{Path, PathBuf};
    use std::sync::OnceLock;

    fn read_circuit_multiplier22_formula() -> crate::DimacsFormula {
        let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(
            "../../benchmarks/sat/satcomp2024-sample/\
             c5ae0ec49de0959cd14431ce851c14f8-Circuit_multiplier22.cnf.xz",
        );
        let bytes = crate::test_xz::decompress_required_xz_path(&path);
        let content = String::from_utf8(bytes)
            .unwrap_or_else(|error| panic!("Circuit_multiplier22 is not UTF-8: {error}"));
        crate::parse_dimacs(&content).expect("parse required tracked Circuit_multiplier22 fixture")
    }

    fn official_main_lrat_solver(formula: &crate::DimacsFormula) -> Solver {
        let proof = ProofOutput::lrat_text(Vec::<u8>::new(), formula.num_clauses as u64);
        let mut solver = Solver::with_proof_output(formula.num_vars, proof);
        let features = SatFeatures::extract(formula.num_vars, &formula.clauses);
        let input = VariantInput::new(formula.num_vars, formula.num_clauses, Lrat)
            .with_route_profile(VariantRouteProfile::OfficialSatCompMainLrat)
            .with_startup_policy(VariantStartupPolicy::DisableWarmupWalk);
        let plan = VariantProfilePlan::for_features(SolverVariant::Default, input, &features);
        plan.apply_to_solver(&mut solver);
        for clause in &formula.clauses {
            solver.add_clause(clause.clone());
        }
        solver
    }

    fn first_lrat_preflightable_bve_candidate(
        solver: &mut Solver,
    ) -> Option<(Variable, EliminationResult, BveLratTransactionPlan)> {
        solver.inproc.bve.set_growth_bound(16);
        solver
            .inproc
            .bve
            .rebuild_with_vals(&solver.arena, &solver.vals);

        while let Some(var) = solver.inproc.bve.next_candidate(
            &solver.arena,
            &solver.vals,
            &solver.cold.freeze_counts,
        ) {
            let pos_occs = solver.inproc.bve.get_occs(Literal::positive(var));
            let neg_occs = solver.inproc.bve.get_occs(Literal::negative(var));
            if pos_occs.len() > FASTELIM_OCC_LIMIT || neg_occs.len() > FASTELIM_OCC_LIMIT {
                continue;
            }
            let has_oversized = pos_occs
                .iter()
                .chain(neg_occs.iter())
                .any(|&idx| solver.arena.len_of(idx) > 100);
            if has_oversized {
                continue;
            }

            let stats_before = solver.inproc.bve.stats().clone();
            let result = solver.inproc.bve.try_eliminate_with_gate_with_marks(
                var,
                &solver.arena,
                None,
                false,
                &mut solver.lit_marks,
                &solver.vals,
                u64::MAX,
            );
            solver.inproc.bve.clear_removed_external(var.index());
            solver.inproc.bve.restore_stats(stats_before);

            if !result.eliminated {
                continue;
            }
            if let Ok(plan) = solver.preflight_bve_lrat_transaction(&result) {
                return Some((var, result, plan));
            }
        }
        None
    }

    #[derive(Debug)]
    struct BveDryRunLratSidecar {
        cnf_text: String,
        lrat_text: String,
        source_count: usize,
        blocker_count: usize,
        bve_clause_len: usize,
        bve_add_id: u64,
        empty_add_id: u64,
        old_expected_id: u64,
    }

    fn sidecar_clause_line(lits: &[Literal]) -> String {
        let mut line = String::new();
        for lit in lits {
            line.push_str(&lit.to_dimacs().to_string());
            line.push(' ');
        }
        line.push_str("0\n");
        line
    }

    fn sidecar_lrat_add_line(id: u64, clause: &[Literal], hints: &[u64]) -> String {
        let mut line = String::new();
        line.push_str(&id.to_string());
        line.push(' ');
        for lit in clause {
            line.push_str(&lit.to_dimacs().to_string());
            line.push(' ');
        }
        line.push_str("0 ");
        for hint in hints {
            line.push_str(&hint.to_string());
            line.push(' ');
        }
        line.push_str("0\n");
        line
    }

    fn sidecar_lrat_delete_line(id: u64, deletions: &[u64]) -> String {
        let mut line = String::new();
        line.push_str(&id.to_string());
        line.push_str(" d ");
        for deletion in deletions {
            line.push_str(&deletion.to_string());
            line.push(' ');
        }
        line.push_str("0\n");
        line
    }

    fn max_dimacs_var(clauses: &[Vec<Literal>]) -> usize {
        clauses
            .iter()
            .flat_map(|clause| clause.iter())
            .map(|lit| lit.variable().index() + 1)
            .max()
            .unwrap_or(0)
    }

    fn active_lrat_clause_map(solver: &Solver) -> std::collections::BTreeMap<u64, Vec<Literal>> {
        let mut clauses = std::collections::BTreeMap::new();
        for clause_idx in solver.arena.indices() {
            if !solver.arena.is_active(clause_idx) {
                continue;
            }
            let clause_id = solver.clause_id(ClauseRef(clause_idx as u32));
            if clause_id == 0 {
                continue;
            }
            clauses.insert(
                clause_id,
                solver.externalize_lits(solver.arena.literals(clause_idx)),
            );
        }
        clauses
    }

    #[derive(Clone, Debug)]
    struct BveLratSidecarAdd {
        old_expected_id: u64,
        clause: Vec<Literal>,
        hints: Vec<u64>,
    }

    #[derive(Debug)]
    struct BveLratTransactionSidecar {
        cnf_text: String,
        lrat_text: String,
        source_count: usize,
        blocker_count: usize,
        planned_add_count: usize,
        planned_delete_count: usize,
        first_old_expected_id: u64,
        first_bve_add_id: u64,
        delete_step_id: Option<u64>,
        empty_add_id: u64,
    }

    fn planned_bve_lrat_sidecar_adds(
        solver: &Solver,
        result: &EliminationResult,
        plan: &BveLratTransactionPlan,
    ) -> Vec<BveLratSidecarAdd> {
        assert_eq!(
            plan.strengthening_adds.len(),
            result.strengthened.len(),
            "retained BVE LRAT plan must cover every strengthening"
        );
        assert_eq!(
            plan.resolvent_adds.len(),
            result.resolvents.len(),
            "retained BVE LRAT plan must cover every resolvent"
        );

        let mut adds =
            Vec::with_capacity(plan.strengthening_adds.len() + plan.resolvent_adds.len());
        for (strengthening_pos, strengthening) in result.strengthened.iter().enumerate() {
            let (planned_clause_idx, planned) = &plan.strengthening_adds[strengthening_pos];
            assert_eq!(
                *planned_clause_idx, strengthening.clause_idx,
                "strengthening target must match retained plan"
            );
            adds.push(BveLratSidecarAdd {
                old_expected_id: planned.expected_id,
                clause: solver.externalize_lits(&strengthening.new_lits),
                hints: planned.hints.clone(),
            });
        }
        for (resolvent_pos, (resolvent_idx, planned)) in plan.resolvent_adds.iter().enumerate() {
            assert_eq!(
                *resolvent_idx, resolvent_pos,
                "resolvent plan order must match BVE result order"
            );
            let (resolvent, _, _, _) = &result.resolvents[*resolvent_idx];
            adds.push(BveLratSidecarAdd {
                old_expected_id: planned.expected_id,
                clause: solver.externalize_lits(resolvent),
                hints: planned.hints.clone(),
            });
        }
        adds
    }

    fn build_checked_bve_dry_run_sidecar(
        source_by_old_id: &std::collections::BTreeMap<u64, Vec<Literal>>,
        old_expected_id: u64,
        derived_clause: &[Literal],
        old_hints: &[u64],
    ) -> Option<BveDryRunLratSidecar> {
        if derived_clause.is_empty() || old_hints.is_empty() {
            return None;
        }

        let mut source_old_ids = Vec::new();
        let mut seen_old_ids = std::collections::BTreeSet::new();
        for &old_hint in old_hints {
            if !source_by_old_id.contains_key(&old_hint) {
                return None;
            }
            if seen_old_ids.insert(old_hint) {
                source_old_ids.push(old_hint);
            }
        }

        let mut sidecar_clauses = Vec::with_capacity(source_old_ids.len() + derived_clause.len());
        let mut old_to_sidecar_id = std::collections::BTreeMap::new();
        for old_id in &source_old_ids {
            let sidecar_id = (sidecar_clauses.len() + 1) as u64;
            old_to_sidecar_id.insert(*old_id, sidecar_id);
            sidecar_clauses.push(source_by_old_id[old_id].clone());
        }

        let source_count = sidecar_clauses.len();
        let mut blocker_ids = Vec::with_capacity(derived_clause.len());
        for &lit in derived_clause {
            let sidecar_id = (sidecar_clauses.len() + 1) as u64;
            blocker_ids.push(sidecar_id);
            sidecar_clauses.push(vec![lit.negated()]);
        }

        let bve_add_id = (sidecar_clauses.len() + 1) as u64;
        let empty_add_id = bve_add_id + 1;
        let num_vars = max_dimacs_var(&sidecar_clauses);

        let mut cnf_text = String::new();
        cnf_text.push_str("c ay Circuit_multiplier22 BVE LRAT dry-run sidecar\n");
        cnf_text.push_str("c source: #9294 checker-backed synthetic UNSAT harness\n");
        cnf_text.push_str(&format!("c old_expected_id {old_expected_id}\n"));
        cnf_text.push_str("c old_hint_ids");
        for old_hint in old_hints {
            cnf_text.push(' ');
            cnf_text.push_str(&old_hint.to_string());
        }
        cnf_text.push('\n');
        cnf_text.push_str(&format!("p cnf {num_vars} {}\n", sidecar_clauses.len()));
        for clause in &sidecar_clauses {
            cnf_text.push_str(&sidecar_clause_line(clause));
        }

        let remapped_hints: Vec<u64> = old_hints
            .iter()
            .map(|old_hint| old_to_sidecar_id[old_hint])
            .collect();
        let mut empty_hints = blocker_ids;
        empty_hints.push(bve_add_id);

        let mut lrat_text = String::new();
        lrat_text.push_str("c ay Circuit_multiplier22 BVE LRAT dry-run sidecar\n");
        lrat_text.push_str(&sidecar_lrat_add_line(
            bve_add_id,
            derived_clause,
            &remapped_hints,
        ));
        lrat_text.push_str(&sidecar_lrat_add_line(empty_add_id, &[], &empty_hints));

        Some(BveDryRunLratSidecar {
            cnf_text,
            lrat_text,
            source_count,
            blocker_count: derived_clause.len(),
            bve_clause_len: derived_clause.len(),
            bve_add_id,
            empty_add_id,
            old_expected_id,
        })
    }

    fn build_checked_bve_transaction_sidecar(
        source_by_old_id: &std::collections::BTreeMap<u64, Vec<Literal>>,
        adds: &[BveLratSidecarAdd],
        source_delete_ids: &[(usize, u64)],
    ) -> Option<BveLratTransactionSidecar> {
        if adds.is_empty() {
            return None;
        }
        let closure_add_pos = adds.iter().position(|add| !add.clause.is_empty())?;

        let mut planned_old_ids = std::collections::BTreeMap::new();
        for (add_pos, add) in adds.iter().enumerate() {
            if planned_old_ids
                .insert(add.old_expected_id, add_pos)
                .is_some()
            {
                return None;
            }
        }

        let mut source_old_ids = Vec::new();
        let mut seen_old_ids = std::collections::BTreeSet::new();
        for add in adds {
            for &old_hint in &add.hints {
                if planned_old_ids.contains_key(&old_hint) {
                    continue;
                }
                if !source_by_old_id.contains_key(&old_hint) {
                    return None;
                }
                if seen_old_ids.insert(old_hint) {
                    source_old_ids.push(old_hint);
                }
            }
        }
        for &(_, old_delete_id) in source_delete_ids {
            if !source_by_old_id.contains_key(&old_delete_id) {
                return None;
            }
            if seen_old_ids.insert(old_delete_id) {
                source_old_ids.push(old_delete_id);
            }
        }

        let mut sidecar_clauses =
            Vec::with_capacity(source_old_ids.len() + adds[closure_add_pos].clause.len());
        let mut old_to_sidecar_id = std::collections::BTreeMap::new();
        for old_id in &source_old_ids {
            let sidecar_id = (sidecar_clauses.len() + 1) as u64;
            old_to_sidecar_id.insert(*old_id, sidecar_id);
            sidecar_clauses.push(source_by_old_id[old_id].clone());
        }

        let source_count = sidecar_clauses.len();
        let mut blocker_ids = Vec::with_capacity(adds[closure_add_pos].clause.len());
        for &lit in &adds[closure_add_pos].clause {
            let sidecar_id = (sidecar_clauses.len() + 1) as u64;
            blocker_ids.push(sidecar_id);
            sidecar_clauses.push(vec![lit.negated()]);
        }

        let first_bve_add_id = (sidecar_clauses.len() + 1) as u64;
        let mut old_add_to_sidecar_id = std::collections::BTreeMap::new();
        for (add_pos, add) in adds.iter().enumerate() {
            old_add_to_sidecar_id.insert(add.old_expected_id, first_bve_add_id + add_pos as u64);
        }

        let num_vars = max_dimacs_var(&sidecar_clauses);
        let mut cnf_text = String::new();
        cnf_text.push_str("c ay Circuit_multiplier22 BVE LRAT transaction sidecar\n");
        cnf_text.push_str("c source: #9307 proof-manager retained mutation bridge\n");
        cnf_text.push_str(&format!(
            "c planned_add_count {} planned_delete_count {}\n",
            adds.len(),
            source_delete_ids.len()
        ));
        cnf_text.push_str("c old_expected_ids");
        for add in adds {
            cnf_text.push(' ');
            cnf_text.push_str(&add.old_expected_id.to_string());
        }
        cnf_text.push('\n');
        cnf_text.push_str("c old_delete_ids");
        for &(_, old_delete_id) in source_delete_ids {
            cnf_text.push(' ');
            cnf_text.push_str(&old_delete_id.to_string());
        }
        cnf_text.push('\n');
        cnf_text.push_str(&format!("p cnf {num_vars} {}\n", sidecar_clauses.len()));
        for clause in &sidecar_clauses {
            cnf_text.push_str(&sidecar_clause_line(clause));
        }

        let mut lrat_text = String::new();
        lrat_text.push_str("c ay Circuit_multiplier22 BVE LRAT transaction sidecar\n");
        for (add_pos, add) in adds.iter().enumerate() {
            let mut remapped_hints = Vec::with_capacity(add.hints.len());
            for &old_hint in &add.hints {
                if let Some(&sidecar_source_id) = old_to_sidecar_id.get(&old_hint) {
                    remapped_hints.push(sidecar_source_id);
                    continue;
                }
                let &planned_pos = planned_old_ids.get(&old_hint)?;
                if planned_pos >= add_pos {
                    return None;
                }
                remapped_hints.push(old_add_to_sidecar_id[&old_hint]);
            }
            lrat_text.push_str(&sidecar_lrat_add_line(
                old_add_to_sidecar_id[&add.old_expected_id],
                &add.clause,
                &remapped_hints,
            ));
        }

        let mut next_step_id = first_bve_add_id + adds.len() as u64;
        let delete_step_id = if source_delete_ids.is_empty() {
            None
        } else {
            let mut remapped_deletions = Vec::with_capacity(source_delete_ids.len());
            for &(_, old_delete_id) in source_delete_ids {
                remapped_deletions.push(old_to_sidecar_id[&old_delete_id]);
            }
            let delete_step_id = next_step_id;
            lrat_text.push_str(&sidecar_lrat_delete_line(
                delete_step_id,
                &remapped_deletions,
            ));
            next_step_id += 1;
            Some(delete_step_id)
        };

        let empty_add_id = next_step_id;
        let mut empty_hints = blocker_ids.clone();
        empty_hints.push(old_add_to_sidecar_id[&adds[closure_add_pos].old_expected_id]);
        lrat_text.push_str(&sidecar_lrat_add_line(empty_add_id, &[], &empty_hints));

        Some(BveLratTransactionSidecar {
            cnf_text,
            lrat_text,
            source_count,
            blocker_count: blocker_ids.len(),
            planned_add_count: adds.len(),
            planned_delete_count: source_delete_ids.len(),
            first_old_expected_id: adds[0].old_expected_id,
            first_bve_add_id,
            delete_step_id,
            empty_add_id,
        })
    }

    fn first_checker_backed_bve_dry_run_sidecar(
        solver: &Solver,
        result: &EliminationResult,
        plan: &BveLratTransactionPlan,
    ) -> Option<BveDryRunLratSidecar> {
        let source_by_old_id = active_lrat_clause_map(solver);

        for (strengthening_pos, strengthening) in result.strengthened.iter().enumerate() {
            let (_, planned) = &plan.strengthening_adds[strengthening_pos];
            let derived_clause = solver.externalize_lits(&strengthening.new_lits);
            if let Some(sidecar) = build_checked_bve_dry_run_sidecar(
                &source_by_old_id,
                planned.expected_id,
                &derived_clause,
                &planned.hints,
            ) {
                return Some(sidecar);
            }
        }

        for (resolvent_pos, (resolvent_idx, planned)) in plan.resolvent_adds.iter().enumerate() {
            debug_assert_eq!(*resolvent_idx, resolvent_pos);
            let (resolvent, _, _, _) = &result.resolvents[*resolvent_idx];
            let derived_clause = solver.externalize_lits(resolvent);
            if let Some(sidecar) = build_checked_bve_dry_run_sidecar(
                &source_by_old_id,
                planned.expected_id,
                &derived_clause,
                &planned.hints,
            ) {
                return Some(sidecar);
            }
        }

        None
    }

    fn assert_lrat_fixture_verifies_with_embedded_checker(
        cnf_text: &str,
        lrat_text: &str,
        label: &str,
    ) {
        let cnf = ay_lrat_check::dimacs::parse_cnf_with_ids(cnf_text.as_bytes())
            .expect("sidecar CNF should parse");
        let steps = ay_lrat_check::lrat_parser::parse_text_lrat(lrat_text)
            .expect("sidecar LRAT should parse");
        let mut checker = ay_lrat_check::checker::LratChecker::new(cnf.num_vars);
        for (id, clause) in &cnf.clauses {
            assert!(
                checker.add_original(*id, clause),
                "sidecar original clause {id} should load"
            );
        }
        assert!(
            checker.verify_proof(&steps),
            "{label} LRAT proof should verify with embedded checker"
        );
    }

    fn assert_lrat_sidecar_verifies_with_embedded_checker(sidecar: &BveDryRunLratSidecar) {
        assert_lrat_fixture_verifies_with_embedded_checker(
            &sidecar.cnf_text,
            &sidecar.lrat_text,
            "BVE dry-run sidecar",
        );
    }

    fn assert_lrat_transaction_sidecar_verifies_with_embedded_checker(
        sidecar: &BveLratTransactionSidecar,
    ) {
        assert_lrat_fixture_verifies_with_embedded_checker(
            &sidecar.cnf_text,
            &sidecar.lrat_text,
            "BVE transaction sidecar",
        );
    }

    fn workspace_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("AY workspace root")
            .canonicalize()
            .expect("AY workspace root should be canonicalizable")
    }

    fn require_workspace_lrat_checker() -> &'static BuiltWorkspaceBinary {
        static CHECKER: OnceLock<BuiltWorkspaceBinary> = OnceLock::new();
        CHECKER.get_or_init(|| build_ay_lrat_checker(&workspace_root()))
    }

    fn assert_lrat_fixture_verifies_with_standalone_checker(
        cnf_text: &str,
        lrat_text: &str,
        file_stem: &str,
    ) {
        let checker = require_workspace_lrat_checker();

        let temp_dir = tempfile::tempdir().expect("create BVE LRAT sidecar tempdir");
        let cnf_path = temp_dir.path().join(format!("{file_stem}.cnf"));
        let lrat_path = temp_dir.path().join(format!("{file_stem}.lrat"));
        fs::write(&cnf_path, cnf_text).expect("write BVE LRAT sidecar CNF");
        fs::write(&lrat_path, lrat_text).expect("write BVE LRAT sidecar proof");

        let output = checker
            .command()
            .arg(&cnf_path)
            .arg(&lrat_path)
            .output()
            .unwrap_or_else(|error| {
                panic!(
                    "failed to run exact-source standalone ay-lrat-check at {}: {error}",
                    checker.artifact_display()
                )
            });
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success(),
            "standalone ay-lrat-check rejected BVE sidecar: status={:?}\nstdout:\n{}\nstderr:\n{}",
            output.status.code(),
            stdout,
            stderr
        );
        assert!(
            stdout.contains("VERIFIED") || stderr.contains("VERIFIED"),
            "standalone ay-lrat-check exited successfully but did not print VERIFIED\nstdout:\n{stdout}\nstderr:\n{stderr}"
        );
    }

    fn assert_lrat_sidecar_verifies_with_standalone_checker(sidecar: &BveDryRunLratSidecar) {
        assert_lrat_fixture_verifies_with_standalone_checker(
            &sidecar.cnf_text,
            &sidecar.lrat_text,
            "circuit-bve-dry-run-sidecar",
        );
    }

    fn assert_lrat_transaction_sidecar_verifies_with_standalone_checker(
        sidecar: &BveLratTransactionSidecar,
    ) {
        assert_lrat_fixture_verifies_with_standalone_checker(
            &sidecar.cnf_text,
            &sidecar.lrat_text,
            "circuit-bve-transaction-sidecar",
        );
    }

    fn persist_lrat_sidecar_if_requested(sidecar: &BveDryRunLratSidecar) {
        let Ok(dir) = std::env::var("AY_BVE_LRAT_SIDECAR_DIR") else {
            return;
        };
        let dir = Path::new(&dir);
        fs::create_dir_all(dir).expect("create requested BVE LRAT sidecar directory");
        let cnf_path = dir.join("circuit-bve-dry-run-sidecar.cnf");
        let lrat_path = dir.join("circuit-bve-dry-run-sidecar.lrat");
        fs::write(&cnf_path, &sidecar.cnf_text).expect("persist BVE LRAT sidecar CNF");
        fs::write(&lrat_path, &sidecar.lrat_text).expect("persist BVE LRAT sidecar proof");
        eprintln!(
            "Circuit_multiplier22 LRAT BVE dry-run sidecar persisted: cnf={} lrat={}",
            cnf_path.display(),
            lrat_path.display()
        );
    }

    fn persist_lrat_transaction_sidecar_if_requested(sidecar: &BveLratTransactionSidecar) {
        let Ok(dir) = std::env::var("AY_BVE_LRAT_SIDECAR_DIR") else {
            return;
        };
        let dir = Path::new(&dir);
        fs::create_dir_all(dir).expect("create requested BVE LRAT sidecar directory");
        let cnf_path = dir.join("circuit-bve-transaction-sidecar.cnf");
        let lrat_path = dir.join("circuit-bve-transaction-sidecar.lrat");
        fs::write(&cnf_path, &sidecar.cnf_text).expect("persist BVE LRAT transaction CNF");
        fs::write(&lrat_path, &sidecar.lrat_text).expect("persist BVE LRAT transaction proof");
        eprintln!(
            "Circuit_multiplier22 LRAT BVE transaction sidecar persisted: cnf={} lrat={}",
            cnf_path.display(),
            lrat_path.display()
        );
    }

    #[derive(Debug)]
    struct BveMutationSnapshot {
        active_clause_count: usize,
        num_vars: usize,
        clause_ids: Vec<u64>,
        reconstruction_len: usize,
        lifecycle_removed: usize,
        proof_added: u64,
        proof_deleted: u64,
    }

    impl BveMutationSnapshot {
        fn capture(solver: &Solver) -> Self {
            Self {
                active_clause_count: solver.arena.active_clause_count(),
                num_vars: solver.num_vars,
                clause_ids: solver.cold.clause_ids.clone(),
                reconstruction_len: solver.inproc.reconstruction.len(),
                lifecycle_removed: solver.var_lifecycle.count_removed(),
                proof_added: solver.proof_manager.as_ref().unwrap().added_count(),
                proof_deleted: solver.proof_manager.as_ref().unwrap().deleted_count(),
            }
        }

        fn assert_unchanged(&self, solver: &Solver) {
            assert_eq!(
                solver.arena.active_clause_count(),
                self.active_clause_count,
                "rejected BVE LRAT bridge must not mutate active clause count"
            );
            assert_eq!(
                solver.num_vars, self.num_vars,
                "rejected BVE LRAT bridge must not allocate variables"
            );
            assert_eq!(
                solver.cold.clause_ids, self.clause_ids,
                "rejected BVE LRAT bridge must not mutate clause IDs"
            );
            assert_eq!(
                solver.inproc.reconstruction.len(),
                self.reconstruction_len,
                "rejected BVE LRAT bridge must not record reconstruction"
            );
            assert_eq!(
                solver.var_lifecycle.count_removed(),
                self.lifecycle_removed,
                "rejected BVE LRAT bridge must not remove variables"
            );
            assert_eq!(
                solver.proof_manager.as_ref().unwrap().added_count(),
                self.proof_added,
                "rejected BVE LRAT bridge must not emit proof additions"
            );
            assert_eq!(
                solver.proof_manager.as_ref().unwrap().deleted_count(),
                self.proof_deleted,
                "rejected BVE LRAT bridge must not emit proof deletions"
            );
        }
    }

    fn mutate_first_planned_add(
        plan: &mut BveLratTransactionPlan,
        mut f: impl FnMut(&mut BveLratPlannedAdd),
    ) {
        if let Some((_, add)) = plan.strengthening_adds.first_mut() {
            f(add);
            return;
        }
        if let Some((_, add)) = plan.resolvent_adds.first_mut() {
            f(add);
            return;
        }
        panic!("test fixture requires at least one retained BVE LRAT add");
    }

    #[test]
    fn test_circuit_multiplier22_lrat_bve_candidate_preflights_without_mutation() {
        let formula = read_circuit_multiplier22_formula();
        let mut solver = official_main_lrat_solver(&formula);

        assert!(
            solver.cold.lrat_enabled,
            "Circuit census must run with LRAT proof state active"
        );
        assert!(
            !solver.is_bve_enabled(),
            "official Main/LRAT must keep global BVE clamped"
        );
        assert!(
            !solver.is_factor_enabled(),
            "Circuit BVE preflight test must not rely on factor reopening"
        );
        assert!(
            !solver.is_sbva_enabled(),
            "official Main/LRAT must keep SBVA clamped"
        );
        assert!(
            !solver.is_sweep_enabled(),
            "official Main/LRAT must keep sweep clamped"
        );

        let active_before = solver.arena.active_clause_count();
        let num_vars_before = solver.num_vars;
        let clause_ids_before = solver.cold.clause_ids.clone();
        let reconstruction_before = solver.inproc.reconstruction.len();
        let lifecycle_removed_before = solver.var_lifecycle.count_removed();
        let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
        let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

        let (var, result, plan) = first_lrat_preflightable_bve_candidate(&mut solver)
            .expect("Circuit_multiplier22 should expose at least one bounded BVE LRAT candidate");

        eprintln!(
            "Circuit_multiplier22 LRAT BVE dry-run candidate: var={} delete={} \
             resolvents={} strengthened={} plan_resolvents={} plan_strengthen={} plan_deletes={}",
            var.index(),
            result.to_delete.len(),
            result.resolvents.len(),
            result.strengthened.len(),
            plan.resolvent_adds.len(),
            plan.strengthening_adds.len(),
            plan.source_delete_ids.len(),
        );

        assert!(
            !plan.resolvent_adds.is_empty() || !plan.strengthening_adds.is_empty(),
            "accepted BVE LRAT preflight should reserve at least one checked add"
        );
        let sidecar = first_checker_backed_bve_dry_run_sidecar(&solver, &result, &plan)
            .expect("Circuit_multiplier22 BVE LRAT dry-run should export one checker sidecar");
        assert_lrat_sidecar_verifies_with_embedded_checker(&sidecar);
        assert_lrat_sidecar_verifies_with_standalone_checker(&sidecar);
        persist_lrat_sidecar_if_requested(&sidecar);
        eprintln!(
            "Circuit_multiplier22 LRAT BVE dry-run sidecar verified: old_expected_id={} \
             bve_add_id={} empty_add_id={} sources={} blockers={} bve_clause_len={}",
            sidecar.old_expected_id,
            sidecar.bve_add_id,
            sidecar.empty_add_id,
            sidecar.source_count,
            sidecar.blocker_count,
            sidecar.bve_clause_len,
        );
        assert_eq!(
            plan.source_delete_ids.len(),
            result.to_delete.len(),
            "every deleted BVE parent must have a checker-visible source ID"
        );
        assert_eq!(
            solver.arena.active_clause_count(),
            active_before,
            "BVE LRAT preflight must not add or delete clauses"
        );
        assert_eq!(
            solver.num_vars, num_vars_before,
            "BVE LRAT preflight must not allocate variables"
        );
        assert_eq!(
            solver.cold.clause_ids, clause_ids_before,
            "BVE LRAT preflight must not mutate clause IDs"
        );
        assert_eq!(
            solver.inproc.reconstruction.len(),
            reconstruction_before,
            "BVE LRAT preflight must not record reconstruction witnesses"
        );
        assert_eq!(
            solver.var_lifecycle.count_removed(),
            lifecycle_removed_before,
            "BVE LRAT preflight must not remove variables"
        );
        assert_eq!(
            solver.proof_manager.as_ref().unwrap().added_count(),
            proof_added_before,
            "BVE LRAT preflight must not emit proof additions"
        );
        assert_eq!(
            solver.proof_manager.as_ref().unwrap().deleted_count(),
            proof_deleted_before,
            "BVE LRAT preflight must not emit proof deletions"
        );
        assert!(
            !solver.is_bve_enabled(),
            "dry-run preflight must not reopen the global LRAT BVE clamp"
        );
    }

    #[test]
    fn test_circuit_multiplier22_lrat_bve_candidate_mutation_bridge_emits_retained_obligations() {
        let formula = read_circuit_multiplier22_formula();
        let mut solver = official_main_lrat_solver(&formula);
        assert!(
            !solver.is_bve_enabled(),
            "official Main/LRAT clamp must remain closed; this is a test-only direct apply"
        );

        let active_before = solver.arena.active_clause_count();
        let num_vars_before = solver.num_vars;
        let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
        let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

        let (var, result, plan) = first_lrat_preflightable_bve_candidate(&mut solver)
            .expect("Circuit_multiplier22 should expose one BVE LRAT bridge candidate");
        let planned_adds = plan.strengthening_adds.len() + plan.resolvent_adds.len();
        let planned_deletes = plan.source_delete_ids.len();
        assert!(planned_adds > 0, "bridge candidate must retain proof adds");
        assert!(
            planned_deletes > 0,
            "bridge candidate must retain proof deletes"
        );

        let source_by_old_id = active_lrat_clause_map(&solver);
        let sidecar_adds = planned_bve_lrat_sidecar_adds(&solver, &result, &plan);
        let transaction_sidecar = build_checked_bve_transaction_sidecar(
            &source_by_old_id,
            &sidecar_adds,
            &plan.source_delete_ids,
        )
        .expect("Circuit_multiplier22 BVE transaction should export checker sidecar");
        assert_lrat_transaction_sidecar_verifies_with_embedded_checker(&transaction_sidecar);
        assert_lrat_transaction_sidecar_verifies_with_standalone_checker(&transaction_sidecar);
        persist_lrat_transaction_sidecar_if_requested(&transaction_sidecar);
        eprintln!(
            "Circuit_multiplier22 LRAT BVE transaction sidecar verified: \
             first_old_expected_id={} first_bve_add_id={} delete_step_id={:?} \
             empty_add_id={} sources={} blockers={} adds={} deletes={}",
            transaction_sidecar.first_old_expected_id,
            transaction_sidecar.first_bve_add_id,
            transaction_sidecar.delete_step_id,
            transaction_sidecar.empty_add_id,
            transaction_sidecar.source_count,
            transaction_sidecar.blocker_count,
            transaction_sidecar.planned_add_count,
            transaction_sidecar.planned_delete_count,
        );

        let mut scratch = BveBodyScratch::default();
        let mut stats = BveBodyStats::default();
        let mut pending_gc_indices = Vec::new();
        let mut derived_unsat = false;
        solver.defer_proof_deletions = true;
        solver
            .apply_bve_elimination_result(
                &result,
                &mut scratch,
                &mut stats,
                &mut pending_gc_indices,
                &mut derived_unsat,
                Some(&plan),
            )
            .expect("retained Circuit BVE LRAT plan should validate before mutation");
        solver.defer_proof_deletions = false;
        solver.flush_deferred_proof_deletions();
        assert!(matches!(solver.flush_proof_writer(), Ok(true)));

        assert!(
            !derived_unsat,
            "first Circuit_multiplier22 BVE bridge candidate should not derive UNSAT"
        );
        assert_eq!(
            solver.num_vars, num_vars_before,
            "BVE mutation bridge must not allocate variables"
        );
        assert!(
            solver.var_lifecycle.is_removed(var.index()),
            "BVE mutation bridge must mark the eliminated variable"
        );
        let strengthened_targets: std::collections::BTreeSet<usize> = plan
            .strengthening_adds
            .iter()
            .map(|(clause_idx, _)| *clause_idx)
            .collect();
        let clause_db_deletes = plan
            .source_delete_ids
            .iter()
            .filter(|(clause_idx, _)| !strengthened_targets.contains(clause_idx))
            .count();
        assert_eq!(
            solver.arena.active_clause_count(),
            active_before - clause_db_deletes + plan.resolvent_adds.len(),
            "BVE mutation bridge active-clause delta must match retained add/delete plan"
        );
        assert_eq!(
            solver.proof_manager.as_ref().unwrap().added_count() - proof_added_before,
            planned_adds as u64,
            "proof manager must emit exactly the retained BVE add obligations"
        );
        assert_eq!(
            solver.proof_manager.as_ref().unwrap().deleted_count() - proof_deleted_before,
            planned_deletes as u64,
            "proof manager must emit exactly the retained BVE delete obligations"
        );

        let active_after = active_lrat_clause_map(&solver);
        for (_, planned) in plan
            .strengthening_adds
            .iter()
            .chain(plan.resolvent_adds.iter())
        {
            assert!(
                active_after.contains_key(&planned.expected_id),
                "retained BVE add ID {} must remain live after mutation",
                planned.expected_id
            );
        }
        for &(_, source_id) in &plan.source_delete_ids {
            assert!(
                !active_after.contains_key(&source_id),
                "retained BVE source delete ID {source_id} must not remain live"
            );
        }
        assert!(
            !solver.is_bve_enabled(),
            "test-only direct apply must not reopen the official Main/LRAT BVE clamp"
        );

        let proof = solver.take_proof_writer().expect("proof writer").into_vec();
        let proof = String::from_utf8(proof.expect("extract LRAT proof bytes"))
            .expect("BVE LRAT proof stream should be UTF-8 text");
        for (_, planned) in plan
            .strengthening_adds
            .iter()
            .chain(plan.resolvent_adds.iter())
        {
            let prefix = format!("{} ", planned.expected_id);
            assert!(
                proof.lines().any(|line| line.starts_with(&prefix)),
                "proof stream must contain retained BVE add ID {}",
                planned.expected_id
            );
        }
        assert!(
            proof.lines().any(|line| line.contains(" d ")),
            "proof stream must contain the retained BVE delete batch"
        );
    }

    #[test]
    fn test_circuit_multiplier22_lrat_bve_route_mutates_one_retained_candidate_and_restores_clamps()
    {
        let formula = read_circuit_multiplier22_formula();
        let mut solver = official_main_lrat_solver(&formula);

        let (var, result, plan) = first_lrat_preflightable_bve_candidate(&mut solver)
            .expect("Circuit_multiplier22 should expose one BVE LRAT route candidate");
        assert_eq!(
            var.index(),
            97,
            "first retained Circuit BVE candidate shape changed"
        );
        assert_eq!(result.strengthened.len(), 1);
        assert_eq!(result.resolvents.len(), 9);
        assert_eq!(
            plan.strengthening_adds.len() + plan.resolvent_adds.len(),
            10
        );
        assert_eq!(plan.source_delete_ids.len(), 9);

        let active_before = solver.arena.active_clause_count();
        let num_vars_before = solver.num_vars;
        let reconstruction_before = solver.inproc.reconstruction.len();
        let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
        let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();
        let bve_limit_before = solver.cold.bve_limit;
        let bve_growth_bound_before = solver.inproc.bve.growth_bound();
        let bve_fastelim_mode_before = solver.inproc.bve.is_fastelim_mode();
        let bve_quick_elim_mode_before = solver.inproc.bve.is_quick_elim_mode();

        solver.set_circuit_bve_lrat_route_enabled(true);
        assert!(
            !solver.is_bve_enabled(),
            "enabling the private Circuit route must not globally reopen BVE"
        );
        let inproc_ctrl_before = format!("{:?}", solver.inproc_ctrl);
        let watches_disconnected_before = solver.watches_disconnected;

        let outcome = solver.run_circuit_bve_lrat_preprocess_route(false);

        assert!(
            !outcome.found_unsat,
            "first retained Circuit BVE route candidate should not derive UNSAT"
        );
        assert!(
            outcome.rebuilt_watches,
            "route-level BVE must reconnect watches after the bounded mutation"
        );
        assert_eq!(
            format!("{:?}", solver.inproc_ctrl),
            inproc_ctrl_before,
            "Circuit route must restore caller inprocessing controls"
        );
        assert_eq!(
            solver.watches_disconnected, watches_disconnected_before,
            "Circuit route must restore watch connection state"
        );
        assert_eq!(
            solver.cold.bve_limit, bve_limit_before,
            "Circuit route must restore the caller's BVE limit"
        );
        assert_eq!(
            solver.inproc.bve.growth_bound(),
            bve_growth_bound_before,
            "Circuit route must restore the caller's BVE growth bound"
        );
        assert_eq!(
            solver.inproc.bve.is_fastelim_mode(),
            bve_fastelim_mode_before,
            "Circuit route must restore the caller's BVE fastelim mode"
        );
        assert_eq!(
            solver.inproc.bve.is_quick_elim_mode(),
            bve_quick_elim_mode_before,
            "Circuit route must restore the caller's BVE quick-elim mode"
        );
        assert!(
            !solver.is_bve_enabled(),
            "Circuit route must leave the official Main/LRAT BVE clamp closed"
        );
        assert_eq!(
            solver.bve_stats().vars_eliminated,
            1,
            "Circuit route should mutate exactly one bounded retained candidate"
        );
        assert!(
            solver.var_lifecycle.is_removed(var.index()),
            "Circuit route must mark the retained candidate variable eliminated"
        );
        assert_eq!(
            solver.num_vars, num_vars_before,
            "Circuit BVE route must not allocate variables"
        );
        assert!(
            solver.inproc.reconstruction.len() > reconstruction_before,
            "destructive Circuit BVE must retain model reconstruction entries; SAT promotion still requires original-DIMACS model checking"
        );

        let strengthened_targets: std::collections::BTreeSet<usize> = plan
            .strengthening_adds
            .iter()
            .map(|(clause_idx, _)| *clause_idx)
            .collect();
        let clause_db_deletes = plan
            .source_delete_ids
            .iter()
            .filter(|(clause_idx, _)| !strengthened_targets.contains(clause_idx))
            .count();
        let actual_clause_db_deletes =
            active_before + plan.resolvent_adds.len() - solver.arena.active_clause_count();
        assert!(
            actual_clause_db_deletes >= clause_db_deletes,
            "route-level BVE must delete at least the retained source clauses"
        );
        let proof_delete_delta =
            solver.proof_manager.as_ref().unwrap().deleted_count() - proof_deleted_before;
        assert!(
            proof_delete_delta >= plan.source_delete_ids.len() as u64,
            "route-level proof stream must emit at least the retained BVE delete obligations"
        );
        assert!(
            proof_delete_delta >= actual_clause_db_deletes as u64,
            "route-level proof delete count must cover normal BVE cleanup"
        );
        assert_eq!(
            solver.proof_manager.as_ref().unwrap().added_count() - proof_added_before,
            10,
            "route-level proof stream must emit every retained BVE add obligation"
        );

        let active_after = active_lrat_clause_map(&solver);
        for (_, planned) in plan
            .strengthening_adds
            .iter()
            .chain(plan.resolvent_adds.iter())
        {
            assert!(
                active_after.contains_key(&planned.expected_id),
                "retained route BVE add ID {} must remain live after mutation",
                planned.expected_id
            );
        }
        for &(_, source_id) in &plan.source_delete_ids {
            assert!(
                !active_after.contains_key(&source_id),
                "retained route BVE source delete ID {source_id} must not remain live"
            );
        }

        assert!(matches!(solver.flush_proof_writer(), Ok(true)));
        let proof = solver.take_proof_writer().expect("proof writer").into_vec();
        let proof = String::from_utf8(proof.expect("extract LRAT proof bytes"))
            .expect("Circuit BVE route LRAT proof stream should be UTF-8 text");
        for (_, planned) in plan
            .strengthening_adds
            .iter()
            .chain(plan.resolvent_adds.iter())
        {
            let prefix = format!("{} ", planned.expected_id);
            assert!(
                proof.lines().any(|line| line.starts_with(&prefix)),
                "route proof stream must contain retained BVE add ID {}; UNSAT promotion still requires final solver proof checking",
                planned.expected_id
            );
        }
        assert!(
            proof.lines().any(|line| line.contains(" d ")),
            "route proof stream must contain the retained BVE delete batch"
        );
    }

    #[test]
    fn test_circuit_bve_lrat_route_rejects_before_mutation_on_missing_source_id() {
        let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 2);
        let mut solver = Solver::with_proof_output(3, proof);
        let x = Variable::new(0);
        let a = Variable::new(1);
        let b = Variable::new(2);

        assert!(solver.add_clause(vec![Literal::positive(x), Literal::positive(a)]));
        assert!(solver.add_clause(vec![Literal::negative(x), Literal::positive(b)]));
        solver.freeze(a);
        solver.freeze(b);
        let clause_indices: Vec<usize> = solver.arena.indices().collect();
        solver.cold.clause_ids[clause_indices[0]] = 0;

        solver.set_circuit_bve_lrat_route_enabled(true);
        let inproc_ctrl_before = format!("{:?}", solver.inproc_ctrl);
        let bve_growth_bound_before = solver.inproc.bve.growth_bound();
        let bve_fastelim_mode_before = solver.inproc.bve.is_fastelim_mode();
        let bve_quick_elim_mode_before = solver.inproc.bve.is_quick_elim_mode();
        let before = BveMutationSnapshot::capture(&solver);
        let outcome = solver.run_circuit_bve_lrat_preprocess_route(false);

        assert!(!outcome.found_unsat);
        assert!(
            outcome.rebuilt_watches,
            "route should still reconnect watches after a fail-closed BVE attempt"
        );
        before.assert_unchanged(&solver);
        assert_eq!(
            solver.bve_stats().vars_eliminated,
            0,
            "missing LRAT source ID must reject before route-level mutation"
        );
        assert_eq!(
            solver.bve_stats().lrat_preflight_rejected,
            1,
            "route-level LRAT preflight rejection must be counted"
        );
        assert!(
            !solver.var_lifecycle.is_removed(x.index()),
            "failed route candidate must leave variable lifecycle unchanged"
        );
        assert!(
            !solver.is_bve_enabled(),
            "failed route attempt must leave the Main/LRAT BVE clamp closed"
        );
        assert_eq!(
            format!("{:?}", solver.inproc_ctrl),
            inproc_ctrl_before,
            "failed route attempt must restore caller inprocessing controls"
        );
        assert_eq!(
            solver.inproc.bve.growth_bound(),
            bve_growth_bound_before,
            "failed route attempt must restore the caller's BVE growth bound"
        );
        assert_eq!(
            solver.inproc.bve.is_fastelim_mode(),
            bve_fastelim_mode_before,
            "failed route attempt must restore the caller's BVE fastelim mode"
        );
        assert_eq!(
            solver.inproc.bve.is_quick_elim_mode(),
            bve_quick_elim_mode_before,
            "failed route attempt must restore the caller's BVE quick-elim mode"
        );
    }

    #[test]
    fn test_circuit_multiplier22_lrat_bve_retained_plan_corruption_rejects_before_mutation() {
        let formula = read_circuit_multiplier22_formula();
        let mut solver = official_main_lrat_solver(&formula);
        let (_, result, plan) = first_lrat_preflightable_bve_candidate(&mut solver)
            .expect("Circuit_multiplier22 should expose one BVE LRAT bridge candidate");
        assert!(
            !plan.source_delete_ids.is_empty(),
            "corruption fixture needs retained delete obligations"
        );

        let mut bad_output_id = plan.clone();
        mutate_first_planned_add(&mut bad_output_id, |add| {
            add.expected_id = add.expected_id.saturating_add(1);
        });
        let before = BveMutationSnapshot::capture(&solver);
        let reject = solver
            .validate_bve_lrat_retained_plan(&result, &bad_output_id)
            .expect_err("bad retained output ID must reject");
        assert!(matches!(
            reject,
            BveLratTransactionReject::RetainedPlanMismatch(
                BveLratRetainedPlanMismatch::OutputId { .. }
            )
        ));
        before.assert_unchanged(&solver);

        let mut bad_hint = plan.clone();
        mutate_first_planned_add(&mut bad_hint, |add| {
            let first_hint = add
                .hints
                .first_mut()
                .expect("retained BVE LRAT add should have at least one source hint");
            *first_hint = first_hint.saturating_add(1);
        });
        let before = BveMutationSnapshot::capture(&solver);
        let reject = solver
            .validate_bve_lrat_retained_plan(&result, &bad_hint)
            .expect_err("bad retained hint chain must reject");
        assert!(matches!(
            reject,
            BveLratTransactionReject::RetainedPlanMismatch(
                BveLratRetainedPlanMismatch::HintChain { .. }
            )
        ));
        before.assert_unchanged(&solver);

        let mut bad_source_id = plan.clone();
        bad_source_id.source_delete_ids[0].1 =
            bad_source_id.source_delete_ids[0].1.saturating_add(1);
        let before = BveMutationSnapshot::capture(&solver);
        let reject = solver
            .validate_bve_lrat_retained_plan(&result, &bad_source_id)
            .expect_err("bad retained source delete ID must reject");
        assert!(matches!(
            reject,
            BveLratTransactionReject::RetainedPlanMismatch(
                BveLratRetainedPlanMismatch::SourceDeleteId { .. }
            )
        ));
        before.assert_unchanged(&solver);

        let mut bad_delete_side = plan;
        bad_delete_side.source_delete_ids.pop();
        let before = BveMutationSnapshot::capture(&solver);
        let reject = solver
            .validate_bve_lrat_retained_plan(&result, &bad_delete_side)
            .expect_err("bad retained delete-side shape must reject");
        assert!(matches!(
            reject,
            BveLratTransactionReject::RetainedPlanMismatch(
                BveLratRetainedPlanMismatch::SourceDeleteShape { .. }
            )
        ));
        before.assert_unchanged(&solver);
    }

    #[test]
    fn test_bve_lrat_missing_parent_id_preflight_rejects_before_mutation() {
        let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 2);
        let mut solver = Solver::with_proof_output(3, proof);
        let x = Variable::new(0);
        let a = Variable::new(1);
        let b = Variable::new(2);

        assert!(solver.add_clause(vec![Literal::positive(x), Literal::positive(a),]));
        assert!(solver.add_clause(vec![Literal::negative(x), Literal::positive(b),]));

        let clause_indices: Vec<usize> = solver.arena.indices().collect();
        assert_eq!(clause_indices.len(), 2);
        let pos_ante = clause_indices[0];
        let neg_ante = clause_indices[1];
        assert_ne!(solver.clause_id(ClauseRef(pos_ante as u32)), 0);
        assert_ne!(solver.clause_id(ClauseRef(neg_ante as u32)), 0);

        solver.cold.clause_ids[pos_ante] = 0;
        let active_before = solver.arena.active_clause_count();
        let clause_ids_before = solver.cold.clause_ids.clone();
        let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
        let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

        let result = EliminationResult {
            variable: x,
            to_delete: vec![pos_ante, neg_ante],
            witness_entries: Vec::new(),
            resolvents: vec![(
                vec![Literal::positive(a), Literal::positive(b)],
                pos_ante,
                neg_ante,
                Vec::new(),
            )],
            strengthened: Vec::new(),
            satisfied_parents: Vec::new(),
            eliminated: true,
            resolution_attempts: 1,
        };

        let reject = solver
            .preflight_bve_lrat_transaction(&result)
            .expect_err("missing BVE LRAT parent ID must reject before apply");
        assert!(matches!(
            reject,
            BveLratTransactionReject::MissingOrHiddenSourceId {
                clause_idx,
                clause_id: 0
            } if clause_idx == pos_ante
        ));
        assert!(
            !solver.var_lifecycle.is_removed(x.index()),
            "BVE must abort before marking the pivot eliminated",
        );
        assert_eq!(
            solver.arena.active_clause_count(),
            active_before,
            "BVE must abort before deleting or adding clauses",
        );
        assert_eq!(
            solver.cold.clause_ids, clause_ids_before,
            "BVE must abort before changing LRAT clause ID state",
        );
        assert_eq!(
            solver.proof_manager.as_ref().unwrap().added_count(),
            proof_added_before
        );
        assert_eq!(
            solver.proof_manager.as_ref().unwrap().deleted_count(),
            proof_deleted_before
        );
    }

    #[test]
    fn test_bve_lrat_hidden_trusted_parent_preflight_rejects_before_mutation() {
        let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 2);
        let mut solver = Solver::with_proof_output(4, proof);
        let x = Variable::new(0);
        let a = Variable::new(1);
        let b = Variable::new(2);
        let c = Variable::new(3);

        assert!(solver.add_clause(vec![Literal::positive(x), Literal::positive(a)]));
        assert!(solver.add_clause(vec![Literal::negative(x), Literal::positive(b)]));

        let clause_indices: Vec<usize> = solver.arena.indices().collect();
        let pos_ante = clause_indices[0];
        let neg_ante = clause_indices[1];
        let hidden_id = solver
            .proof_manager
            .as_mut()
            .unwrap()
            .emit_add(&[Literal::positive(c)], &[], ProofAddKind::TrustedTransform)
            .expect("hidden trusted unit ID");
        assert_ne!(hidden_id, 0);
        assert!(!solver.lrat_hint_id_visible(hidden_id));
        solver.cold.clause_ids[pos_ante] = hidden_id;

        let active_before = solver.arena.active_clause_count();
        let clause_ids_before = solver.cold.clause_ids.clone();
        let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
        let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

        let result = EliminationResult {
            variable: x,
            to_delete: vec![pos_ante, neg_ante],
            witness_entries: Vec::new(),
            resolvents: vec![(
                vec![Literal::positive(a), Literal::positive(b)],
                pos_ante,
                neg_ante,
                Vec::new(),
            )],
            strengthened: Vec::new(),
            satisfied_parents: Vec::new(),
            eliminated: true,
            resolution_attempts: 1,
        };

        let reject = solver
            .preflight_bve_lrat_transaction(&result)
            .expect_err("trusted-only parent ID must reject before apply");
        assert!(matches!(
            reject,
            BveLratTransactionReject::MissingOrHiddenSourceId {
                clause_idx,
                clause_id
            } if clause_idx == pos_ante && clause_id == hidden_id
        ));
        assert!(!solver.var_lifecycle.is_removed(x.index()));
        assert_eq!(solver.arena.active_clause_count(), active_before);
        assert_eq!(solver.cold.clause_ids, clause_ids_before);
        assert_eq!(
            solver.proof_manager.as_ref().unwrap().added_count(),
            proof_added_before
        );
        assert_eq!(
            solver.proof_manager.as_ref().unwrap().deleted_count(),
            proof_deleted_before
        );
    }

    #[test]
    fn test_bve_lrat_dead_delete_target_preflight_rejects_before_mutation() {
        let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 3);
        let mut solver = Solver::with_proof_output(4, proof);
        let x = Variable::new(0);
        let a = Variable::new(1);
        let b = Variable::new(2);
        let c = Variable::new(3);

        assert!(solver.add_clause(vec![Literal::positive(x), Literal::positive(a)]));
        assert!(solver.add_clause(vec![Literal::negative(x), Literal::positive(b)]));
        assert!(solver.add_clause(vec![Literal::positive(x), Literal::positive(c)]));

        let clause_indices: Vec<usize> = solver.arena.indices().collect();
        let pos_ante = clause_indices[0];
        let neg_ante = clause_indices[1];
        let dead_idx = clause_indices[2];
        let dead_id = solver.clause_id(ClauseRef(dead_idx as u32));
        solver.arena.delete(dead_idx);
        assert!(!solver.arena.is_active(dead_idx));

        let active_before = solver.arena.active_clause_count();
        let clause_ids_before = solver.cold.clause_ids.clone();
        let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
        let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

        let result = EliminationResult {
            variable: x,
            to_delete: vec![pos_ante, neg_ante, dead_idx],
            witness_entries: Vec::new(),
            resolvents: vec![(
                vec![Literal::positive(a), Literal::positive(b)],
                pos_ante,
                neg_ante,
                Vec::new(),
            )],
            strengthened: Vec::new(),
            satisfied_parents: Vec::new(),
            eliminated: true,
            resolution_attempts: 1,
        };

        let reject = solver
            .preflight_bve_lrat_transaction(&result)
            .expect_err("dead BVE deletion target must reject before apply");
        match reject {
            BveLratTransactionReject::DeletionTargetNotLive { clause_idx, .. } => {
                assert_eq!(clause_idx, dead_idx);
            }
            other => panic!("expected dead delete target rejection, got {other:?}"),
        }
        assert_ne!(dead_id, 0);
        assert!(!solver.var_lifecycle.is_removed(x.index()));
        assert_eq!(solver.arena.active_clause_count(), active_before);
        assert_eq!(solver.cold.clause_ids, clause_ids_before);
        assert_eq!(
            solver.proof_manager.as_ref().unwrap().added_count(),
            proof_added_before
        );
        assert_eq!(
            solver.proof_manager.as_ref().unwrap().deleted_count(),
            proof_deleted_before
        );
    }

    #[test]
    fn test_bve_lrat_missing_strengthening_target_preflight_rejects_without_replacement() {
        let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 2);
        let mut solver = Solver::with_proof_output(3, proof);
        let x = Variable::new(0);
        let a = Variable::new(1);
        let b = Variable::new(2);

        assert!(solver.add_clause(vec![
            Literal::positive(x),
            Literal::positive(a),
            Literal::positive(b),
        ]));
        assert!(solver.add_clause(vec![Literal::negative(x), Literal::positive(a)]));

        let clause_indices: Vec<usize> = solver.arena.indices().collect();
        let target = clause_indices[0];
        let neg_ante = clause_indices[1];
        let target_before = solver.arena.literals(target).to_vec();
        solver.cold.clause_ids[target] = 0;

        let active_before = solver.arena.active_clause_count();
        let clause_ids_before = solver.cold.clause_ids.clone();
        let proof_added_before = solver.proof_manager.as_ref().unwrap().added_count();
        let proof_deleted_before = solver.proof_manager.as_ref().unwrap().deleted_count();

        let result = EliminationResult {
            variable: x,
            to_delete: vec![target, neg_ante],
            witness_entries: Vec::new(),
            resolvents: Vec::new(),
            strengthened: vec![crate::bve::ClauseStrengthening {
                clause_idx: target,
                new_lits: vec![Literal::positive(a), Literal::positive(b)],
                pos_ante: target,
                neg_ante,
                pruned_vars: Vec::new(),
            }],
            satisfied_parents: Vec::new(),
            eliminated: true,
            resolution_attempts: 1,
        };

        let reject = solver
            .preflight_bve_lrat_transaction(&result)
            .expect_err("missing strengthening target ID must reject before apply");
        assert!(matches!(
            reject,
            BveLratTransactionReject::MissingOrHiddenSourceId {
                clause_idx,
                clause_id: 0
            } if clause_idx == target
        ));
        assert_eq!(solver.arena.literals(target), target_before.as_slice());
        assert!(!solver.var_lifecycle.is_removed(x.index()));
        assert_eq!(solver.arena.active_clause_count(), active_before);
        assert_eq!(solver.cold.clause_ids, clause_ids_before);
        assert_eq!(
            solver.proof_manager.as_ref().unwrap().added_count(),
            proof_added_before
        );
        assert_eq!(
            solver.proof_manager.as_ref().unwrap().deleted_count(),
            proof_deleted_before
        );
    }
}
