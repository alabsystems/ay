// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Factorization: extension variable compression.

use super::super::mutate::{AddResult, ReasonPolicy};
use super::super::*;
use crate::er_proof::ErDefinition;
use crate::factor::{FactorLratDryRunSidecar, FactorResult, FACTOR_SIZE_LIMIT};
use crate::proof_manager::PlannedForwardAddReject;

const FACTOR_CANDIDATE_FILTER_ROUNDS: usize = 2;

/// Candidate scheduling rounds per factorize call. After the priority-queue
/// schedule drains, the schedule is rebuilt from the CURRENT occurrence state
/// and drained again (only when the previous round applied at least one
/// factoring — an unchanged occ state would drain identically). Incremental
/// `reschedule_literal` only re-inserts literals whose own occ lists changed;
/// a full re-round also re-exposes candidates whose occ lists are unchanged
/// but whose PARTNER structure improved — cascade-created divider/quotient
/// clauses change the quotient-chain matches reachable from an old candidate
/// even when that candidate's own occurrence list is untouched. This is an AY
/// extension: kissat/CaDiCaL run a single drain per factor() call (their
/// `factorcandrounds` is the candidate CLAUSE filter in occ construction,
/// mirrored by FACTOR_CANDIDATE_FILTER_ROUNDS above) but recover missed
/// cascades across calls via persistent `flags.factor` candidate bits; AY
/// rebuilds its schedule per call, so the re-round recovers them within the
/// call. Rounds share the honest tick budget, so re-runs never exceed the
/// per-call effort limit. 3 matches the former 3-pass rebuild driver's
/// fixpoint depth; re-rounds are progress-gated, so this is a safety bound,
/// not a fixed cost.
const FACTOR_SCHEDULE_ROUNDS: usize = 3;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum FactorizeOutcome {
    Productive,
    Unproductive,
    RejectedLratPreflight,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct FactorLratTransactionPlan {
    pub(super) planned_add_ids: Vec<u64>,
    pub(super) live_add_ids: Vec<u64>,
    pub(super) source_delete_ids: Vec<u64>,
    pub(super) proof_only_delete_ids: Vec<u64>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum FactorLratTransactionReject {
    MissingProofManager,
    ExtensionVarCountMismatch { expected: usize, actual: usize },
    FreshVarOutOfRange { fresh_var: usize, max_vars: usize },
    DuplicateFreshVar { fresh_var: usize },
    MalformedApplication,
    SelfSubsumingUnsupported,
    MissingOrHiddenSourceId { clause_idx: usize, clause_id: u64 },
    DuplicateSourceId { clause_id: u64 },
    MalformedClause,
    MissingErModelReconstructionObligation,
    NewClauseCountMismatch { expected: usize, actual: usize },
    PlannedAddSliceMismatch { expected_end: usize, actual: usize },
    CheckerVisibleObligationMismatch,
    PlannedAddRejected(PlannedForwardAddReject),
}

fn positive_lrat_hints_to_signed(hints: &[u64]) -> Option<Vec<i64>> {
    let mut signed = Vec::with_capacity(hints.len());
    for &hint in hints {
        signed.push(i64::try_from(hint).ok()?);
    }
    Some(signed)
}

impl Solver {
    // ==================== Factorization (Extension Variable Compression) ====================

    fn factor_lrat_source_id(&self, clause_idx: usize) -> Result<u64, FactorLratTransactionReject> {
        let clause_id = if clause_idx < self.cold.clause_ids.len() {
            self.clause_id(ClauseRef(clause_idx as u32))
        } else {
            0
        };
        // is_garbage_any (husk adjudication): garbage-kept husks pass
        // is_active but are logically deleted — reject them as LRAT sources.
        if clause_idx >= self.arena.len()
            || !self.arena.is_active(clause_idx)
            || self.arena.is_garbage_any(clause_idx)
        {
            return Err(FactorLratTransactionReject::MissingOrHiddenSourceId {
                clause_idx,
                clause_id,
            });
        }
        if clause_id == 0 || !self.lrat_hint_id_visible(clause_id) {
            return Err(FactorLratTransactionReject::MissingOrHiddenSourceId {
                clause_idx,
                clause_id,
            });
        }
        let Some(manager) = self.proof_manager.as_ref() else {
            return Err(FactorLratTransactionReject::MissingProofManager);
        };
        if !manager.is_known_lrat_id(clause_id) {
            return Err(FactorLratTransactionReject::MissingOrHiddenSourceId {
                clause_idx,
                clause_id,
            });
        }
        Ok(clause_id)
    }

    fn factor_lrat_clause_well_formed(&self, clause: &[Literal], max_vars: usize) -> bool {
        if clause.is_empty() {
            return false;
        }
        for (i, &lit) in clause.iter().enumerate() {
            if lit.variable().index() >= max_vars {
                return false;
            }
            for &prev in &clause[..i] {
                if prev == lit || prev == lit.negated() {
                    return false;
                }
            }
        }
        true
    }

    fn factor_lrat_source_ids_complete(
        &self,
        clause_indices: &[usize],
    ) -> Result<Vec<u64>, FactorLratTransactionReject> {
        let mut ids = std::collections::BTreeSet::new();
        let mut ordered = Vec::with_capacity(clause_indices.len());
        for &clause_idx in clause_indices {
            let clause_id = self.factor_lrat_source_id(clause_idx)?;
            if !ids.insert(clause_id) {
                return Err(FactorLratTransactionReject::DuplicateSourceId { clause_id });
            }
            ordered.push(clause_id);
        }
        Ok(ordered)
    }

    fn factor_er_source_id(&self, clause_idx: usize) -> Result<u64, FactorLratTransactionReject> {
        let clause_id = if clause_idx < self.cold.clause_ids.len() {
            self.clause_id(ClauseRef(clause_idx as u32))
        } else {
            0
        };
        // is_garbage_any (husk adjudication): reject garbage-kept husks as ER
        // sources, mirroring factor_lrat_source_id above.
        if clause_idx >= self.arena.len()
            || !self.arena.is_active(clause_idx)
            || self.arena.is_garbage_any(clause_idx)
            || clause_id == 0
        {
            return Err(FactorLratTransactionReject::MissingOrHiddenSourceId {
                clause_idx,
                clause_id,
            });
        }
        Ok(clause_id)
    }

    fn factor_er_source_ids_complete(
        &self,
        clause_indices: &[usize],
    ) -> Result<Vec<u64>, FactorLratTransactionReject> {
        let mut ids = std::collections::BTreeSet::new();
        let mut ordered = Vec::with_capacity(clause_indices.len());
        for &clause_idx in clause_indices {
            let clause_id = self.factor_er_source_id(clause_idx)?;
            if !ids.insert(clause_id) {
                return Err(FactorLratTransactionReject::DuplicateSourceId { clause_id });
            }
            ordered.push(clause_id);
        }
        Ok(ordered)
    }

    fn preflight_factor_er_definitions(
        &self,
        result: &FactorResult,
    ) -> Result<Vec<ErDefinition>, FactorLratTransactionReject> {
        if result.extension_vars_needed != result.applications.len() {
            return Err(FactorLratTransactionReject::ExtensionVarCountMismatch {
                expected: result.applications.len(),
                actual: result.extension_vars_needed,
            });
        }

        let mut definitions = Vec::with_capacity(result.applications.len());
        for app in &result.applications {
            let source_clause_ids = self.factor_er_source_ids_complete(&app.to_delete)?;
            let expected_sources = app
                .divider_clauses
                .len()
                .checked_mul(app.quotient_clauses.len())
                .ok_or(FactorLratTransactionReject::MalformedApplication)?;
            if source_clause_ids.len() != expected_sources {
                return Err(FactorLratTransactionReject::MalformedApplication);
            }
            let definition = ErDefinition::factor_checked(
                app.fresh_var,
                app.divider_clauses.clone(),
                app.quotient_clauses.clone(),
                app.blocked_clause.clone(),
                source_clause_ids,
            )
            .ok_or(FactorLratTransactionReject::MissingErModelReconstructionObligation)?;
            definitions.push(definition);
        }

        Ok(definitions)
    }

    fn factor_lrat_dry_run_obligations(
        &self,
        result: &FactorResult,
        plan: &FactorLratTransactionPlan,
    ) -> Result<Vec<FactorLratDryRunSidecar>, FactorLratTransactionReject> {
        if !result.self_subsuming.is_empty() {
            return Err(FactorLratTransactionReject::SelfSubsumingUnsupported);
        }

        let mut sidecars = Vec::with_capacity(result.applications.len());
        let mut add_start = 0usize;
        for app in &result.applications {
            let add_count = app
                .divider_clauses
                .len()
                .checked_add(1)
                .and_then(|count| count.checked_add(app.quotient_clauses.len()))
                .ok_or(FactorLratTransactionReject::MalformedApplication)?;
            let add_end = add_start
                .checked_add(add_count)
                .ok_or(FactorLratTransactionReject::MalformedApplication)?;
            let Some(planned_add_ids) = plan.planned_add_ids.get(add_start..add_end) else {
                return Err(FactorLratTransactionReject::PlannedAddSliceMismatch {
                    expected_end: add_end,
                    actual: plan.planned_add_ids.len(),
                });
            };
            let source_ids = self.factor_lrat_source_ids_complete(&app.to_delete)?;
            let source_lits = app
                .to_delete
                .iter()
                .map(|&ci| {
                    self.arena
                        .literals(ci)
                        .iter()
                        .map(|lit| i64::from(lit.to_dimacs()))
                        .collect::<Vec<_>>()
                })
                .collect();

            let sidecar = FactorLratDryRunSidecar::from_transaction_parts(
                i64::from(Literal::positive(app.fresh_var).to_dimacs()),
                app.factors
                    .iter()
                    .map(|lit| i64::from(lit.to_dimacs()))
                    .collect(),
                app.quotient_clauses
                    .iter()
                    .map(|clause| {
                        clause
                            .iter()
                            .map(|lit| i64::from(lit.to_dimacs()))
                            .collect()
                    })
                    .collect(),
                source_ids.clone(),
                source_lits,
                planned_add_ids.to_vec(),
                source_ids,
            )
            .ok_or(FactorLratTransactionReject::CheckerVisibleObligationMismatch)?;
            sidecars.push(sidecar);
            add_start = add_end;
        }

        if add_start != plan.planned_add_ids.len() {
            return Err(FactorLratTransactionReject::PlannedAddSliceMismatch {
                expected_end: add_start,
                actual: plan.planned_add_ids.len(),
            });
        }

        Ok(sidecars)
    }

    pub(super) fn preflight_factor_lrat_transaction(
        &mut self,
        result: &FactorResult,
    ) -> Result<FactorLratTransactionPlan, FactorLratTransactionReject> {
        if !self.cold.lrat_enabled {
            return Ok(FactorLratTransactionPlan {
                planned_add_ids: Vec::new(),
                live_add_ids: Vec::new(),
                source_delete_ids: Vec::new(),
                proof_only_delete_ids: Vec::new(),
            });
        }
        if self.proof_manager.is_none() {
            return Err(FactorLratTransactionReject::MissingProofManager);
        }

        let max_vars = self.num_vars + result.extension_vars_needed;
        if result.extension_vars_needed != result.applications.len() {
            return Err(FactorLratTransactionReject::ExtensionVarCountMismatch {
                expected: result.applications.len(),
                actual: result.extension_vars_needed,
            });
        }
        let mut fresh_vars = std::collections::BTreeSet::new();
        let mut expected_new_clauses = 0usize;
        let mut planned_add_count = 0usize;
        for app in &result.applications {
            let fresh_idx = app.fresh_var.index();
            if fresh_idx < self.num_vars || fresh_idx >= max_vars {
                return Err(FactorLratTransactionReject::FreshVarOutOfRange {
                    fresh_var: fresh_idx,
                    max_vars,
                });
            }
            if !fresh_vars.insert(fresh_idx) {
                return Err(FactorLratTransactionReject::DuplicateFreshVar {
                    fresh_var: fresh_idx,
                });
            }
            if app.divider_clauses.len() != app.factors.len()
                || app.quotient_clauses.is_empty()
                || app.blocked_clause.len() != app.factors.len() + 1
                || app.to_delete.len() != app.factors.len() * app.quotient_clauses.len()
            {
                return Err(FactorLratTransactionReject::MalformedApplication);
            }
            self.factor_lrat_source_ids_complete(&app.to_delete)?;

            let fresh_pos = Literal::positive(app.fresh_var);
            let fresh_neg = Literal::negative(app.fresh_var);
            for (idx, divider) in app.divider_clauses.iter().enumerate() {
                if divider.len() != 2
                    || divider[0] != fresh_pos
                    || divider[1] != app.factors[idx]
                    || !self.factor_lrat_clause_well_formed(divider, max_vars)
                {
                    return Err(FactorLratTransactionReject::MalformedClause);
                }
                expected_new_clauses += 1;
                planned_add_count += 1;
            }
            if app.blocked_clause.first().copied() != Some(fresh_neg)
                || !self.factor_lrat_clause_well_formed(&app.blocked_clause, max_vars)
            {
                return Err(FactorLratTransactionReject::MalformedClause);
            }
            planned_add_count += 1;
            for quotient in &app.quotient_clauses {
                if quotient.first().copied() != Some(fresh_neg)
                    || !self.factor_lrat_clause_well_formed(quotient, max_vars)
                {
                    return Err(FactorLratTransactionReject::MalformedClause);
                }
                expected_new_clauses += 1;
                planned_add_count += 1;
            }
        }

        for app in &result.self_subsuming {
            if app.resolvents.len() != app.proof_pairs.len() || app.to_delete.is_empty() {
                return Err(FactorLratTransactionReject::MalformedApplication);
            }
            self.factor_lrat_source_ids_complete(&app.to_delete)?;
            for &(lhs, rhs) in &app.proof_pairs {
                self.factor_lrat_source_id(lhs)?;
                self.factor_lrat_source_id(rhs)?;
            }
            for resolvent in &app.resolvents {
                if !self.factor_lrat_clause_well_formed(resolvent, max_vars) {
                    return Err(FactorLratTransactionReject::MalformedClause);
                }
                expected_new_clauses += 1;
                planned_add_count += 1;
            }
        }

        if expected_new_clauses != result.new_clauses.len() {
            return Err(FactorLratTransactionReject::NewClauseCountMismatch {
                expected: expected_new_clauses,
                actual: result.new_clauses.len(),
            });
        }

        let Some(manager) = self.proof_manager.as_mut() else {
            return Err(FactorLratTransactionReject::MissingProofManager);
        };
        let _ = manager.flush();
        let Some(manager) = self.proof_manager.as_ref() else {
            return Err(FactorLratTransactionReject::MissingProofManager);
        };
        let planned_add_ids = manager
            .planned_forward_add_ids(planned_add_count)
            .map_err(FactorLratTransactionReject::PlannedAddRejected)?;
        let mut source_delete_ids = Vec::with_capacity(result.to_delete.len());
        let mut delete_seen = std::collections::BTreeSet::new();
        for &clause_idx in &result.to_delete {
            let clause_id = self.factor_lrat_source_id(clause_idx)?;
            if !delete_seen.insert(clause_id) {
                return Err(FactorLratTransactionReject::DuplicateSourceId { clause_id });
            }
            source_delete_ids.push(clause_id);
        }
        let mut proof_only_delete_ids = Vec::with_capacity(result.applications.len());
        let mut live_add_ids = Vec::with_capacity(expected_new_clauses);
        let mut id_pos = 0usize;
        for app in &result.applications {
            for _ in &app.divider_clauses {
                if let Some(&divider_id) = planned_add_ids.get(id_pos) {
                    live_add_ids.push(divider_id);
                }
                id_pos += 1;
            }
            if let Some(&blocked_id) = planned_add_ids.get(id_pos) {
                proof_only_delete_ids.push(blocked_id);
            }
            id_pos += 1;
            for _ in &app.quotient_clauses {
                if let Some(&quotient_id) = planned_add_ids.get(id_pos) {
                    live_add_ids.push(quotient_id);
                }
                id_pos += 1;
            }
        }
        for app in &result.self_subsuming {
            for _ in &app.resolvents {
                if let Some(&resolvent_id) = planned_add_ids.get(id_pos) {
                    live_add_ids.push(resolvent_id);
                }
                id_pos += 1;
            }
        }
        debug_assert_eq!(id_pos, planned_add_ids.len());
        debug_assert_eq!(live_add_ids.len(), expected_new_clauses);

        Ok(FactorLratTransactionPlan {
            planned_add_ids,
            live_add_ids,
            source_delete_ids,
            proof_only_delete_ids,
        })
    }

    pub(super) fn factor_result_has_lrat_transaction_contract(
        &mut self,
        result: &FactorResult,
    ) -> bool {
        self.preflight_factor_lrat_transaction(result).is_ok()
    }

    fn factor_lrat_additions_have_checker_visible_obligations(
        &self,
        result: &FactorResult,
        sidecars: &[FactorLratDryRunSidecar],
    ) -> bool {
        if !self.cold.lrat_enabled || result.factored_count == 0 {
            return true;
        }

        if !result.self_subsuming.is_empty() || sidecars.len() != result.applications.len() {
            return false;
        }
        let Some(manager) = self.proof_manager.as_ref() else {
            return false;
        };
        for (app, sidecar) in result.applications.iter().zip(sidecars) {
            if !sidecar.has_checker_visible_transaction_contract() {
                return false;
            }
            let planned_visible_ids = sidecar.planned_add_ids.as_slice();
            for divider in &app.divider_clauses {
                if manager
                    .preflight_forward_lrat_add_with_planned_ids(
                        divider,
                        &[],
                        ProofAddKind::TrustedTransform,
                        planned_visible_ids,
                    )
                    .is_err()
                {
                    return false;
                }
            }
            if manager
                .preflight_forward_lrat_add_signed_with_planned_ids(
                    &app.blocked_clause,
                    &sidecar.blocked_signed_lrat_hints,
                    ProofAddKind::Derived,
                    planned_visible_ids,
                )
                .is_err()
            {
                return false;
            }
            if app.quotient_clauses.len() != sidecar.quotient_lrat_hints.len() {
                return false;
            }
            for (quotient, hints) in app
                .quotient_clauses
                .iter()
                .zip(&sidecar.quotient_lrat_hints)
            {
                let Some(signed_hints) = positive_lrat_hints_to_signed(hints) else {
                    return false;
                };
                if manager
                    .preflight_forward_lrat_add_signed_with_planned_ids(
                        quotient,
                        &signed_hints,
                        ProofAddKind::Derived,
                        planned_visible_ids,
                    )
                    .is_err()
                {
                    return false;
                }
            }
        }
        true
    }

    /// Run factorization with growing backoff scheduling.
    ///
    /// Uses growing backoff when unproductive (0 factored clauses): the
    /// interval grows 1.5× per idle call, up to FACTOR_MAX_INTERVAL.
    /// Productive calls reset to base interval.
    pub(in crate::solver) fn factorize(&mut self) {
        let outcome = self.factorize_body();
        if outcome == FactorizeOutcome::RejectedLratPreflight {
            return;
        }
        if outcome == FactorizeOutcome::Productive {
            self.inproc_ctrl
                .factor
                .reschedule(self.num_conflicts, FACTOR_INTERVAL);
        } else {
            self.inproc_ctrl.factor.reschedule_growing(
                self.num_conflicts,
                FACTOR_INTERVAL,
                3,
                2, // 1.5× growth
                FACTOR_MAX_INTERVAL,
            );
        }
    }

    /// Factorization body — early returns are safe; wrapper handles rescheduling.
    ///
    /// Identifies groups of clauses differing in exactly one literal (the "factor")
    /// and introduces fresh extension variables to replace `f*q` clauses with `f+q`.
    ///
    /// Uses an iterative feedback loop: after each pass applies factoring results
    /// to the clause DB, the occ list is rebuilt and a new pass discovers cascading
    /// opportunities from the newly-created divider/quotient clauses. This matches
    /// CaDiCaL's `update_factored` priority-queue re-insertion (factor.cpp:698-748).
    ///
    /// Reference: CaDiCaL `factor.cpp`.
    /// Returns whether any clauses were factored or the LRAT preflight rejected
    /// before mutation.
    /// Must be called at decision level 0.
    fn factorize_body(&mut self) -> FactorizeOutcome {
        self.inproc.factor_engine.clear_lrat_dry_run_sidecars();

        if !self.require_level_zero() {
            return FactorizeOutcome::Unproductive;
        }

        // Skip in incremental mode: factorization introduces extension variables
        // and rewrites clauses, which cannot be reversed across solve boundaries (#5031, #5166).
        if self.cold.has_been_incremental {
            return FactorizeOutcome::Unproductive;
        }

        // #8397 (relaxed #8482): Factoring introduces extension variables
        // whose divider clauses interact with BVE reconstruction ordering.
        // The per-variable BVE guard (#8397 body.rs:295-313) prevents
        // eliminating variables whose clauses contain unelimianted extension
        // variables, providing sound interaction between BVE and factoring.
        //
        // Previously, this function returned early when ANY reconstruction
        // entries existed, preventing ALL inprocessing factoring. This
        // caused AY to find only 16 factors on braun.12 vs CaDiCaL's 173,
        // contributing to a 2.5x performance gap on circuit equivalence
        // benchmarks. CaDiCaL does not have this restriction — it runs
        // factoring during inprocessing alongside BVE.
        //
        // The guard is now removed: the per-variable BVE guard is the
        // correct level of protection, not a blanket factoring disable.

        // LRAT override handled centrally by inproc_ctrl.with_proof_overrides() (#4557).
        let drat_proof = self.proof_manager.is_some();

        // Compute tick-proportional effort limit (CaDiCaL factor.cpp:962-964).
        // Budget = (search_ticks_delta * factoreffort / 1000) + initial bonus on first call.
        let ticks_now = self.search_ticks[0] + self.search_ticks[1];
        let ticks_delta = ticks_now.saturating_sub(self.cold.last_factor_ticks);
        let mut effort = ticks_delta * FACTOR_EFFORT_PERMILLE / 1000;
        if self.cold.factor_rounds == 0 {
            // #factor-dense-init: the first factoring call gets an init bonus
            // so it can drain the candidate schedule instead of stalling on
            // the (near-zero during preprocess) proportional budget. In the
            // SMALL DENSE band the schedule needs the full per-call max to
            // drain: the sparse 500M bonus truncated dense discovery
            // mid-schedule (measured 46355da: full drain = 591M ticks / 318
            // factorings / UNSAT; 500M cut it at 76 → timeout). Below the
            // density band factoring drains well under 500M (nothing to
            // raise); above the residual cap (~3M clauses) factoring is
            // marginal and the extra budget only perturbs search (0ec8c5e9:
            // SAT@88s → timeout, same 3 factors). So the raise is scoped to
            // density >= FACTOR_DENSE_MIN_DENSITY AND active_clauses <=
            // FACTOR_DENSE_INIT_MAX_CLAUSES, and kill-switched
            // (AY_AB_FACTOR_DENSE_INIT=0). Density is computed the same way as
            // the call-site factor-dense gate (bve_density / formula_density =
            // active clauses / active vars).
            let init = {
                let active_cls = self.arena.active_clause_count();
                let active_vars = self
                    .num_vars
                    .saturating_sub(self.var_lifecycle.count_removed());
                let density = if active_vars > 0 {
                    active_cls as f64 / active_vars as f64
                } else {
                    0.0
                };
                let dense_enabled = config_preprocess_policy::factor_dense_init_enabled();
                let max_clauses = config_preprocess_policy::factor_dense_init_max_clauses();
                if config_preprocess_policy::factor_dense_init_applies(
                    dense_enabled,
                    density,
                    active_cls,
                    max_clauses,
                ) {
                    config_preprocess_policy::factor_dense_init_ticks()
                } else {
                    FACTOR_INIT_TICKS
                }
            };
            effort = effort.saturating_add(init);
        }
        // Per-call effort ceiling. DEFAULT-INERT env override
        // (AY_FACTOR_MAX_EFFORT, unset → FACTOR_MAX_EFFORT = 1B) so the
        // huge-binary-dense band can be measured/drained without a recompile;
        // see config_preprocess_policy::factor_max_effort (measured-negative
        // for a default flip — do not raise the constant).
        let effort = effort.min(config_preprocess_policy::factor_max_effort());

        // Incremental kissat/CaDiCaL-style driver (#rank6, replaces the
        // former 3-pass full-rebuild loop #7399): build the occurrence list
        // and the candidate priority queue ONCE, then alternate discovery
        // (one factoring per `step`) with application. After each applied
        // factoring the occurrence list is updated incrementally (consumed
        // matrix clauses removed, new divider/quotient clauses added) and
        // only the literals whose occ lists changed are re-inserted into the
        // schedule (CaDiCaL factor.cpp:698-748). Newly-created clauses are
        // immediately visible to discovery, so the cascade needs no occ
        // rebuilds and no full-candidate rescans — the former passes re-ran
        // every candidate against tombstone-bloated occ lists up to 3 times.
        let mut remaining_effort = effort;
        let mut any_completed = false;
        let mut any_factored = false;

        // Build occurrence lists and the candidate schedule once.
        self.inproc.factor_engine.ensure_num_vars(self.num_vars);
        let mut occ = self.build_factor_occ();
        self.inproc.factor_engine.schedule_candidates(
            &occ,
            &self.vals,
            self.var_lifecycle.as_slice(),
        );
        // One scheduling round per factorize call (the former loop counted
        // one round per full pass, 1-3 per call). Incremented inside the
        // loop after the first step's preflights succeed: a rejected
        // preflight must not count as an applied factor round.
        let mut rounds_incremented = false;

        // Scratch reused across steps.
        let mut added_clauses: Vec<usize> = Vec::new();
        let mut changed_lits: Vec<Literal> = Vec::new();

        // Candidate re-run rounds (FACTOR_SCHEDULE_ROUNDS): tracks the
        // current round and whether it applied any factoring since the last
        // (re)schedule — a drained schedule with no state change would drain
        // identically, so re-rounds are gated on progress.
        let mut schedule_round = 1usize;
        let mut factored_since_schedule = false;

        loop {
            // CaDiCaL factor.cpp:118: capture the current BVE elimination
            // bound. Factoring only fires when clause reduction exceeds this
            // bound, ensuring BVE cannot profitably undo the factoring.
            // `AY_FACTOR_ELIM_BOUND` overrides it, because whether this is the
            // right threshold at all is an open question: Kissat's
            // `best_quotient` (factor.c:608-640) accepts ANY strictly
            // decreasing quotient (delta >= 1), while `growth_bound` is 8 in
            // fastelim mode — so AY may be demanding a >= 9-clause reduction
            // where Kissat takes >= 1. On `mexam_17_15_2` AY factors 0
            // variables against Kissat's 545.
            let elim_bound = match std::env::var("AY_FACTOR_ELIM_BOUND")
                .ok()
                .and_then(|v| v.parse::<i64>().ok())
            {
                Some(forced) => forced,
                None => self.inproc.bve.growth_bound() as i64,
            };

            let factor_config = crate::factor::FactorConfig {
                next_var_id: self.num_vars,
                effort_limit: remaining_effort,
                elim_bound,
            };
            let mut result = self.inproc.factor_engine.step(
                &self.arena,
                &occ,
                &self.vals,
                self.var_lifecycle.as_slice(),
                &factor_config,
            );
            let er_definitions = if result.factored_count > 0 {
                match self.preflight_factor_er_definitions(&result) {
                    Ok(definitions) => definitions,
                    Err(_) => {
                        self.inproc
                            .factor_engine
                            .record_lrat_preflight_er_obligation_missing();
                        return FactorizeOutcome::RejectedLratPreflight;
                    }
                }
            } else {
                Vec::new()
            };
            let mut lrat_sidecars = None;
            let lrat_plan = if self.cold.lrat_enabled && result.factored_count > 0 {
                self.inproc
                    .factor_engine
                    .record_lrat_preflight_transaction_candidates(result.factored_count as u64);
                match self.preflight_factor_lrat_transaction(&result) {
                    Ok(plan) => {
                        let sidecars = match self.factor_lrat_dry_run_obligations(&result, &plan) {
                            Ok(sidecars) => sidecars,
                            Err(_) => {
                                self.inproc
                                    .factor_engine
                                    .record_lrat_preflight_dry_run_rejected();
                                return FactorizeOutcome::RejectedLratPreflight;
                            }
                        };
                        self.inproc
                            .factor_engine
                            .set_lrat_dry_run_sidecars(sidecars.clone());
                        if !self.factor_lrat_additions_have_checker_visible_obligations(
                            &result, &sidecars,
                        ) {
                            self.inproc
                                .factor_engine
                                .record_lrat_preflight_checker_obligation_missing();
                            return FactorizeOutcome::RejectedLratPreflight;
                        }
                        lrat_sidecars = Some(sidecars);
                        Some(plan)
                    }
                    Err(FactorLratTransactionReject::PlannedAddRejected(_)) => {
                        self.inproc
                            .factor_engine
                            .record_lrat_preflight_checker_obligation_missing();
                        return FactorizeOutcome::RejectedLratPreflight;
                    }
                    Err(_) => return FactorizeOutcome::RejectedLratPreflight,
                }
            } else {
                None
            };
            let factor_state_before_apply = if drat_proof && result.factored_count > 0 {
                Some((
                    self.cold.factor_candidate_marks.clone(),
                    self.cold.factor_rounds,
                    self.cold.factor_factored_total,
                    self.cold.factor_extension_vars_total,
                ))
            } else {
                None
            };
            self.consume_factor_candidate_marks(&result.consumed_candidates);

            if !rounds_incremented {
                rounds_incremented = true;
                self.cold.factor_rounds += 1;
            }
            self.cold.factor_factored_total += result.factored_count as u64;
            self.cold.factor_extension_vars_total += result.extension_vars_needed as u64;

            // Validate structured application data against flattened result.
            assert_eq!(
                result.applications.len() + result.self_subsuming.len(),
                result.factored_count
            );
            for app in &result.applications {
                assert_eq!(app.blocked_clause.len(), 1 + app.factors.len());
                assert_eq!(app.divider_clauses.len(), app.factors.len());
                assert!(app.fresh_var.index() < self.num_vars + result.extension_vars_needed);
                assert_eq!(
                    app.to_delete.len(),
                    app.factors.len() * app.quotient_clauses.len()
                );
            }

            // Decrement the shared effort budget by the TICKS this step
            // consumed. #14-factor-cost: honest tick accounting — the budget
            // genuinely binds across all steps of this call.
            remaining_effort = remaining_effort.saturating_sub(result.ticks_consumed);

            if result.completed {
                // Candidate schedule fully drained with no factoring found.
                any_completed = true;
            }
            if result.factored_count == 0 {
                // Nothing to apply: schedule exhausted or budget ran out
                // mid-discovery. If the schedule drained, earlier rounds made
                // progress, and budget remains, rebuild the schedule from the
                // current occ state and run another discovery round
                // (FACTOR_SCHEDULE_ROUNDS): consumed candidates whose partner
                // structure improved via cascade-created clauses re-enter.
                // Charge the occ + filter rebuild scans to the shared
                // budget (honest tick accounting, #14-factor-cost): the
                // rebuild visits every active clause once per filter
                // round plus the initial collection pass, and the
                // schedule scan visits every literal. The re-round is
                // gated on the remaining budget COVERING that cost: a
                // rebuild the budget cannot pay for would still cost real
                // wall time (~50-200ms on multi-million-clause arenas)
                // and then hand `step` a near-zero budget — pure overhead.
                // Layout-invariant accounting units (legacy 5-word headers,
                // see `accounting_len`) keep this cost estimate — and hence
                // the re-round decision — identical across the R2 clause
                // header slimming.
                let rebuild_cost = (self.arena.accounting_len() as u64)
                    .saturating_mul(1 + FACTOR_CANDIDATE_FILTER_ROUNDS as u64)
                    .saturating_add(2 * self.num_vars as u64);
                if result.completed
                    && schedule_round < FACTOR_SCHEDULE_ROUNDS
                    && factored_since_schedule
                    && remaining_effort > rebuild_cost
                {
                    schedule_round += 1;
                    factored_since_schedule = false;
                    remaining_effort -= rebuild_cost;
                    // FULL occ rebuild, not just a schedule rebuild: the
                    // candidate CLAUSE filter (bincount+largecount >= 2)
                    // froze at the original formula, so clauses whose
                    // literal profiles only became factorable through the
                    // cascade's divider/quotient clauses never entered the
                    // occ list. The former 3-pass driver rebuilt the occ
                    // between passes and discovered strictly more factors
                    // (219 vs 204 on SAT-COMP 82851650) for exactly this
                    // reason.
                    occ = self.build_factor_occ();
                    self.inproc.factor_engine.schedule_candidates(
                        &occ,
                        &self.vals,
                        self.var_lifecycle.as_slice(),
                    );
                    continue;
                }
                break;
            }
            any_factored = true;
            factored_since_schedule = true;

            // Per-application shape diagnostics (debug-gated, zero cost when
            // no subscriber is installed).
            for app in &result.applications {
                tracing::debug!(
                    "[factor-app] round={} ext f={} q={}",
                    schedule_round,
                    app.factors.len(),
                    app.quotient_clauses.len(),
                );
            }
            for app in &result.self_subsuming {
                tracing::debug!(
                    "[factor-app] round={} selfsub resolvents={}",
                    schedule_round,
                    app.resolvents.len(),
                );
            }

            // Incremental occ maintenance (#rank6): capture the affected
            // literals and remove the consumed matrix clauses from the occ
            // list BEFORE applying — apply deletes them from the arena.
            changed_lits.clear();
            for &ci in &result.to_delete {
                let lits = self.arena.literals(ci);
                changed_lits.extend_from_slice(lits);
                occ.remove_clause(ci, lits);
            }

            // Apply this factoring to the clause DB.
            added_clauses.clear();
            if !self.apply_factor_result(
                &mut result,
                drat_proof,
                lrat_plan.as_ref(),
                lrat_sidecars.as_deref(),
                &er_definitions,
                &mut added_clauses,
            ) {
                if let Some((marks, rounds, factored_total, extension_vars_total)) =
                    factor_state_before_apply
                {
                    self.cold.factor_candidate_marks = marks;
                    self.cold.factor_rounds = rounds;
                    self.cold.factor_factored_total = factored_total;
                    self.cold.factor_extension_vars_total = extension_vars_total;
                }
                return FactorizeOutcome::RejectedLratPreflight;
            }
            if self.has_empty_clause {
                break;
            }

            // The fresh extension variable was installed: grow the
            // literal-indexed structures before touching occ or the schedule.
            self.inproc.factor_engine.ensure_num_vars(self.num_vars);
            occ.ensure_num_vars(self.num_vars);

            // Add the new divider/quotient clauses to the occ list so the
            // cascade sees them immediately (CaDiCaL factor.cpp:698-748).
            for &ci in &added_clauses {
                if !self.arena.is_active(ci) || self.arena.is_learned(ci) {
                    continue;
                }
                let len = self.arena.len_of(ci);
                if !(2..=FACTOR_SIZE_LIMIT).contains(&len) {
                    continue;
                }
                let lits = self.arena.literals(ci);
                occ.add_clause(ci, lits);
                changed_lits.extend_from_slice(lits);
            }

            // kissat `update_factored` (factor.c:800-822) parity: reschedule
            // the NEGATION of every factor literal too. The factors
            // themselves are in the consumed/divider clauses (covered by
            // changed_lits), but kissat also re-runs their complements,
            // whose complementary-factor (self-subsuming) matches change.
            for app in &result.applications {
                for &f in &app.factors {
                    changed_lits.push(f.negated());
                }
            }

            // Re-insert only the literals whose occ lists changed into the
            // candidate schedule — this is what lets factoring exploit the
            // newly-created clauses without any full rescan.
            changed_lits.sort_unstable();
            changed_lits.dedup();
            for &lit in &changed_lits {
                self.inproc.factor_engine.reschedule_literal(
                    lit,
                    &occ,
                    &self.vals,
                    self.var_lifecycle.as_slice(),
                );
            }

            if remaining_effort == 0 {
                break;
            }
        }

        self.cold.last_factor_ticks = self.search_ticks[0] + self.search_ticks[1];

        tracing::debug!(
            "[factorize] budget={} consumed={} completed={} factored_total={}",
            effort,
            effort.saturating_sub(remaining_effort),
            any_completed,
            self.cold.factor_factored_total,
        );

        if any_completed {
            self.cold.factor_last_completed_epoch = self.cold.factor_marked_epoch;
        }

        if any_factored {
            FactorizeOutcome::Productive
        } else {
            FactorizeOutcome::Unproductive
        }
    }

    fn build_factor_occ(&mut self) -> crate::occ_list::OccList {
        // CaDiCaL factor.cpp:factor_mode() keeps all binary clauses but filters
        // larger candidates before building the hot occurrence lists. Clauses
        // containing a literal that appears only once across the remaining
        // binary+large candidate pool cannot participate in factoring, so
        // dropping them shrinks the scans in `find_next_factor` (#7399).
        let mut occ = crate::occ_list::OccList::new(self.num_vars);
        // Binary-partner fast path (kissat inline binary branch): track the
        // other literal of each binary clause so `find_next_factor` reads it
        // without a clause-arena dereference. Enabled BEFORE any add_clause so
        // the partner array is populated in lockstep. Kill switch
        // AY_AB_FACTOR_BIN_FASTPATH=0 skips this, and `find_next_factor` then
        // falls back to the byte-identical generic occ scan.
        if crate::factor::factor_bin_fastpath_enabled() {
            occ.enable_partner_tracking();
        }

        // Use persistent buffers from the factor engine, resized in
        // ensure_num_vars(). Take ownership to avoid borrow conflicts with
        // self.arena; returned to persistent storage before each exit point.
        // Reset via fill(0)/clear() instead of allocating new Vecs (#8543).
        let lit_count = self.num_vars * 2;
        let mut binary_counts = std::mem::take(&mut self.inproc.factor_engine.occ_binary_counts);
        let mut large_counts = std::mem::take(&mut self.inproc.factor_engine.occ_large_counts);
        let mut candidates = std::mem::take(&mut self.inproc.factor_engine.occ_candidates);
        binary_counts[..lit_count].fill(0);
        large_counts[..lit_count].fill(0);
        candidates.clear();

        // live_indices (husk adjudication): garbage-kept husks must not enter
        // the factor matrix — factoring on a husk can reintroduce eliminated
        // variables into live clauses and wastes the factoring quota.
        for ci in self.arena.live_indices() {
            if self.arena.is_learned(ci) {
                continue;
            }
            let lits = self.arena.literals(ci);
            match lits.len() {
                2 => {
                    for &lit in lits {
                        binary_counts[lit.index()] += 1;
                    }
                    occ.add_clause(ci, lits);
                }
                3..=FACTOR_SIZE_LIMIT => {
                    candidates.push(ci);
                    for &lit in lits {
                        large_counts[lit.index()] += 1;
                    }
                }
                _ => {}
            }
        }

        if candidates.is_empty() {
            // Return buffers to persistent storage before early return.
            self.inproc.factor_engine.occ_binary_counts = binary_counts;
            self.inproc.factor_engine.occ_large_counts = large_counts;
            self.inproc.factor_engine.occ_candidates = candidates;
            return occ;
        }

        // Take the swap buffer for the filter loop.
        let mut next_large_counts =
            std::mem::take(&mut self.inproc.factor_engine.occ_next_large_counts);

        for _ in 0..FACTOR_CANDIDATE_FILTER_ROUNDS {
            let prev_len = candidates.len();
            // Reuse persistent next_large_counts buffer instead of
            // allocating a new Vec each iteration (#8543).
            next_large_counts[..lit_count].fill(0);
            candidates.retain(|&ci| {
                let lits = self.arena.literals(ci);
                let keep = lits
                    .iter()
                    .all(|lit| binary_counts[lit.index()] + large_counts[lit.index()] >= 2);
                if keep {
                    for &lit in lits {
                        next_large_counts[lit.index()] += 1;
                    }
                }
                keep
            });
            // Swap large_counts and next_large_counts so the freshly
            // computed counts become the current large_counts for the
            // next iteration, without any allocation.
            std::mem::swap(&mut large_counts, &mut next_large_counts);
            if candidates.len() == prev_len {
                break;
            }
        }

        for &ci in &candidates {
            let lits = self.arena.literals(ci);
            occ.add_clause(ci, lits);
        }

        // Return all buffers to persistent storage.
        self.inproc.factor_engine.occ_binary_counts = binary_counts;
        self.inproc.factor_engine.occ_large_counts = large_counts;
        self.inproc.factor_engine.occ_next_large_counts = next_large_counts;
        self.inproc.factor_engine.occ_candidates = candidates;

        occ
    }

    fn add_factor_live_lrat_clause(
        &mut self,
        lits: &mut [Literal],
        expected_id: Option<u64>,
    ) -> AddResult {
        if let Some(id) = expected_id.filter(|&id| id != 0) {
            debug_assert!(self.cold.lrat_enabled);
            self.cold.next_clause_id = id;
        }

        let add_result = self.add_clause_watched(lits);

        if let Some(expected_id) = expected_id.filter(|&id| id != 0) {
            match add_result {
                AddResult::Added(cref) | AddResult::Unit(cref) => {
                    debug_assert_eq!(
                        self.clause_id(cref),
                        expected_id,
                        "factor live clause must reuse its emitted LRAT proof ID"
                    );
                    if self.cold.next_clause_id <= expected_id {
                        self.cold.next_clause_id = expected_id + 1;
                    }
                }
                AddResult::Empty => {}
            }
        }

        add_result
    }

    fn install_factor_extension_vars(&mut self, result: &FactorResult) {
        let ext_var_start = self.num_vars;
        // Record the boundary where extension variables begin (#8397).
        if result.extension_vars_needed > 0 && self.cold.first_extension_var_index == usize::MAX {
            self.cold.first_extension_var_index = ext_var_start;
        }
        for _ in 0..result.extension_vars_needed {
            self.new_var_internal();
        }
        // Bury extension vars in VSIDS: zero activity so search doesn't
        // branch on them before BVE eliminates them.
        // CaDiCaL: factor.cpp:769-839 `adjust_scores_and_phases_of_fresh_variables`.
        for vi in ext_var_start..self.num_vars {
            self.vsids.set_activity(Variable(vi as u32), 0.0);
        }
    }

    fn record_factor_er_definitions(&mut self, definitions: &[ErDefinition]) {
        // NOTE: CaDiCaL does NOT push reconstruction entries for factored
        // clauses (factor.cpp has no push_clause_on_extension_stack calls).
        // AY records a checked ER/model projection artifact before mutation.
        for definition in definitions {
            self.cold.er_proof_log.push(definition.clone());
        }
    }

    fn emit_factor_planned_proof_add(
        &mut self,
        clause: &[Literal],
        lrat_plan: Option<&FactorLratTransactionPlan>,
        planned_add_pos: &mut usize,
    ) -> Option<u64> {
        let emitted = self
            .proof_emit_add(clause, &[], ProofAddKind::TrustedTransform)
            .ok()?;
        if let Some(plan) = lrat_plan {
            let expected = *plan.planned_add_ids.get(*planned_add_pos)?;
            if emitted != expected {
                return None;
            }
            *planned_add_pos += 1;
        }
        Some(emitted)
    }

    fn emit_factor_planned_signed_lrat_add(
        &mut self,
        clause: &[Literal],
        hints: &[i64],
        lrat_plan: &FactorLratTransactionPlan,
        planned_add_pos: &mut usize,
    ) -> Option<u64> {
        let emitted = self
            .proof_emit_add_signed_lrat(clause, hints, ProofAddKind::Derived)
            .ok()?;
        let expected = *lrat_plan.planned_add_ids.get(*planned_add_pos)?;
        if emitted != expected {
            return None;
        }
        *planned_add_pos += 1;
        Some(emitted)
    }

    /// Apply a single factor step's results to the clause DB.
    ///
    /// `added_out` receives the arena indices of the live clauses installed
    /// by this application, so the incremental driver can add them to its
    /// occurrence list (#rank6).
    fn apply_factor_result(
        &mut self,
        result: &mut FactorResult,
        drat_proof: bool,
        lrat_plan: Option<&FactorLratTransactionPlan>,
        lrat_sidecars: Option<&[FactorLratDryRunSidecar]>,
        er_definitions: &[ErDefinition],
        added_out: &mut Vec<usize>,
    ) -> bool {
        if er_definitions.len() != result.applications.len() {
            return false;
        }
        if drat_proof {
            if lrat_plan.is_some()
                && lrat_sidecars.is_none_or(|sidecars| sidecars.len() != result.applications.len())
            {
                return false;
            }
            let mut planned_add_pos = 0usize;
            let mut blocked_deletions: Vec<(Vec<Literal>, u64)> =
                Vec::with_capacity(result.applications.len());
            // DRAT proof transaction per FactorApplication, following CaDiCaL's
            // factor.cpp:595-663 proof sequence. Order matters for checker:
            //   1. Add divider clauses  (fresh ∨ f_j)        — RAT on fresh
            //   2. Add blocked clause   (¬fresh ∨ ¬f_1 ∨ …)  — RAT on ¬fresh (proof-only)
            //   3. Add quotient clauses (¬fresh ∨ Q_i)       — RUP derivable
            //   4. Delete blocked clauses from proof stream
            //   5. Delete original clauses from proof stream + clause DB
            //
            // NOTE (confirmed dead-end — do not re-chase): the blocked clause
            // (¬fresh ∨ ¬f_1 ∨ …) is the *base* clause of the AND-gate
            // `¬fresh ↔ AND(f_1..f_n)`, but it is PROOF-ONLY (step 2 above, then
            // deleted at step 4). It is never inserted into the live clause DB
            // (see `expected_new_clauses`/`live_add_ids` above — only dividers +
            // quotients go live). Consequences, all measured/verified:
            //   • AY's AND-gate detector (gates/and.rs Phase 2) scans `base_occs`
            //     for that long clause; with it absent it returns None, so no
            //     fresh-var gate is ever extracted (kissat is identical:
            //     apply_factoring adds no blocked clause either).
            //   • Wiring factoring's known gate into gate-restricted BVE would be
            //     a no-op anyway: for a fresh var ALL pos occs are dividers
            //     (gate) and ALL neg occs are quotients (non-gate), so
            //     gate×non-gate resolution (bve/resolve.rs) equals full n×m —
            //     nothing is skipped. And every fresh var has ≥1 non-gate
            //     quotient (factor.rs), so `gate_restriction_is_sound`
            //     (bve/eliminate.rs) nullifies the gate to full resolution.
            // The elim gap vs kissat (fresh-var post-factor plateau) is a
            // reconstruction-guard (#8397) + additive-budget + factor↔BVE
            // scheduling problem, NOT a gate-detection/gate-wiring one.
            //
            // Delete proof-only blocked clauses after all additions so strict
            // LRAT transaction plans can reserve contiguous forward add IDs.
            for (app_idx, app) in result.applications.iter().enumerate() {
                #[cfg(debug_assertions)]
                {
                    let num_vars = self.num_vars + result.extension_vars_needed;
                    let check_proof_clause = |lits: &[Literal], label: &str| {
                        debug_assert!(
                            !lits.is_empty(),
                            "BUG: empty {label} clause in factorization proof"
                        );
                        debug_assert!(
                            lits.iter().all(|l| l.variable().index() < num_vars),
                            "BUG: {label} clause variable out of range \
                             (num_vars={num_vars}): {lits:?}"
                        );
                        let mut codes: Vec<u32> = lits.iter().map(|l| l.0).collect();
                        codes.sort_unstable();
                        debug_assert!(
                            codes.windows(2).all(|w| w[0] != w[1]),
                            "BUG: duplicate literal in {label} clause: {lits:?}"
                        );
                    };
                    for div in &app.divider_clauses {
                        check_proof_clause(div, "divider");
                    }
                    check_proof_clause(&app.blocked_clause, "blocked");
                    for quot in &app.quotient_clauses {
                        check_proof_clause(quot, "quotient");
                    }
                }
                for div in &app.divider_clauses {
                    if self
                        .emit_factor_planned_proof_add(div, lrat_plan, &mut planned_add_pos)
                        .is_none()
                    {
                        return false;
                    }
                }
                let Some(blocked_emitted) =
                    (if let (Some(plan), Some(sidecars)) = (lrat_plan, lrat_sidecars) {
                        sidecars.get(app_idx).and_then(|sidecar| {
                            self.emit_factor_planned_signed_lrat_add(
                                &app.blocked_clause,
                                &sidecar.blocked_signed_lrat_hints,
                                plan,
                                &mut planned_add_pos,
                            )
                        })
                    } else {
                        self.emit_factor_planned_proof_add(
                            &app.blocked_clause,
                            lrat_plan,
                            &mut planned_add_pos,
                        )
                    })
                else {
                    return false;
                };
                let blocked_id = (blocked_emitted != 0).then_some(blocked_emitted);
                for (quot_idx, quot) in app.quotient_clauses.iter().enumerate() {
                    if let (Some(plan), Some(sidecars)) = (lrat_plan, lrat_sidecars) {
                        let Some(sidecar) = sidecars.get(app_idx) else {
                            return false;
                        };
                        let Some(hints) = sidecar
                            .quotient_lrat_hints
                            .get(quot_idx)
                            .and_then(|hints| positive_lrat_hints_to_signed(hints))
                        else {
                            return false;
                        };
                        if self
                            .emit_factor_planned_signed_lrat_add(
                                quot,
                                &hints,
                                plan,
                                &mut planned_add_pos,
                            )
                            .is_none()
                        {
                            return false;
                        }
                    } else if self
                        .emit_factor_planned_proof_add(quot, lrat_plan, &mut planned_add_pos)
                        .is_none()
                    {
                        return false;
                    }
                }
                if let Some(blocked_id) = blocked_id {
                    blocked_deletions.push((app.blocked_clause.clone(), blocked_id));
                }
            }

            // Self-subsuming proof emissions: resolvents are RUP
            // (derivable from the two complementary parent clauses).
            for app in &result.self_subsuming {
                for resolvent in &app.resolvents {
                    if self
                        .emit_factor_planned_proof_add(resolvent, lrat_plan, &mut planned_add_pos)
                        .is_none()
                    {
                        return false;
                    }
                }
            }
            if let Some(plan) = lrat_plan {
                if planned_add_pos != plan.planned_add_ids.len()
                    || blocked_deletions.len() != plan.proof_only_delete_ids.len()
                {
                    return false;
                }
                for ((_, emitted_id), expected_id) in
                    blocked_deletions.iter().zip(&plan.proof_only_delete_ids)
                {
                    if emitted_id != expected_id {
                        return false;
                    }
                }
            }
            for (blocked_clause, blocked_id) in blocked_deletions {
                if self.proof_emit_delete(&blocked_clause, blocked_id).is_err() {
                    return false;
                }
            }

            self.install_factor_extension_vars(result);
            self.record_factor_er_definitions(er_definitions);

            // Add new clauses to clause DB (no proof emit — already done above).
            // LRAT plans reserve proof IDs in emission order. Install live factor
            // clauses in that same order so later BVE preflight can cite them.
            let mut live_add_pos = 0usize;
            for app in &result.applications {
                for div in &app.divider_clauses {
                    let mut lits = div.clone();
                    let expected_id =
                        lrat_plan.and_then(|plan| plan.live_add_ids.get(live_add_pos).copied());
                    live_add_pos += 1;
                    let add_result = self.add_factor_live_lrat_clause(&mut lits, expected_id);
                    // Notify BVE occ lists of new irredundant clause (#8096).
                    match add_result {
                        AddResult::Added(cref) | AddResult::Unit(cref) => {
                            let ci = cref.0 as usize;
                            let new_lits = self.arena.literals(ci).to_vec();
                            self.note_irredundant_clause_added_for_bve(ci, &new_lits);
                            added_out.push(ci);
                        }
                        AddResult::Empty => {}
                    }
                    if self.has_empty_clause {
                        return true;
                    }
                }
                for quot in &app.quotient_clauses {
                    let mut lits = quot.clone();
                    let expected_id =
                        lrat_plan.and_then(|plan| plan.live_add_ids.get(live_add_pos).copied());
                    live_add_pos += 1;
                    let add_result = self.add_factor_live_lrat_clause(&mut lits, expected_id);
                    // Notify BVE occ lists of new irredundant clause (#8096).
                    match add_result {
                        AddResult::Added(cref) | AddResult::Unit(cref) => {
                            let ci = cref.0 as usize;
                            let new_lits = self.arena.literals(ci).to_vec();
                            self.note_irredundant_clause_added_for_bve(ci, &new_lits);
                            added_out.push(ci);
                        }
                        AddResult::Empty => {}
                    }
                    if self.has_empty_clause {
                        return true;
                    }
                }
            }
            for app in &result.self_subsuming {
                for resolvent in &app.resolvents {
                    let mut lits = resolvent.clone();
                    let expected_id =
                        lrat_plan.and_then(|plan| plan.live_add_ids.get(live_add_pos).copied());
                    live_add_pos += 1;
                    let add_result = self.add_factor_live_lrat_clause(&mut lits, expected_id);
                    // Notify BVE occ lists of new irredundant clause (#8096).
                    match add_result {
                        AddResult::Added(cref) | AddResult::Unit(cref) => {
                            let ci = cref.0 as usize;
                            let new_lits = self.arena.literals(ci).to_vec();
                            self.note_irredundant_clause_added_for_bve(ci, &new_lits);
                            added_out.push(ci);
                        }
                        AddResult::Empty => {}
                    }
                    if self.has_empty_clause {
                        return true;
                    }
                }
            }
            if let Some(plan) = lrat_plan {
                debug_assert_eq!(live_add_pos, plan.live_add_ids.len());
                if let Some(&last_id) = plan.planned_add_ids.last() {
                    if self.cold.next_clause_id <= last_id {
                        self.cold.next_clause_id = last_id + 1;
                    }
                }
            }
            result.new_clauses.clear();

            // Delete originals from clause DB.
            self.ensure_reason_clause_marks_current();
            let mut source_delete_pos = 0usize;
            for &clause_idx in &result.to_delete {
                if let Some(plan) = lrat_plan {
                    let Some(&expected_id) = plan.source_delete_ids.get(source_delete_pos) else {
                        return false;
                    };
                    let clause_id = self.clause_id(ClauseRef(clause_idx as u32));
                    if clause_id != expected_id {
                        return false;
                    }
                    source_delete_pos += 1;
                }
                // Notify BVE occ lists of irredundant clause removal (#8096).
                if !self.arena.is_learned(clause_idx) {
                    let old_lits = self.arena.literals(clause_idx).to_vec();
                    self.note_irredundant_clause_removed_for_bve(clause_idx, &old_lits);
                }
                self.delete_clause_checked(clause_idx, ReasonPolicy::Skip);
            }
            if let Some(plan) = lrat_plan {
                if source_delete_pos != plan.source_delete_ids.len() {
                    return false;
                }
            }
        } else {
            self.install_factor_extension_vars(result);
            self.record_factor_er_definitions(er_definitions);

            // Non-proof path: delete originals first (order doesn't matter).
            self.ensure_reason_clause_marks_current();
            for &clause_idx in &result.to_delete {
                // Notify BVE occ lists of irredundant clause removal (#8096).
                if !self.arena.is_learned(clause_idx) {
                    let old_lits = self.arena.literals(clause_idx).to_vec();
                    self.note_irredundant_clause_removed_for_bve(clause_idx, &old_lits);
                }
                self.delete_clause_checked(clause_idx, ReasonPolicy::Skip);
            }

            for mut lits in std::mem::take(&mut result.new_clauses) {
                let add_result = self.add_clause_watched(&mut lits);
                // Notify BVE occ lists of new irredundant clause (#8096).
                match add_result {
                    AddResult::Added(cref) | AddResult::Unit(cref) => {
                        let ci = cref.0 as usize;
                        let new_lits = self.arena.literals(ci).to_vec();
                        self.note_irredundant_clause_added_for_bve(ci, &new_lits);
                        added_out.push(ci);
                    }
                    AddResult::Empty => {}
                }
                if self.has_empty_clause {
                    return true;
                }
            }
        }
        true
    }
}

#[cfg(test)]
#[path = "factorize_tests.rs"]
mod tests;
