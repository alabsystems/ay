// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Proof, ProofId, TermId};
use ay_sat::{
    ClauseTrace, ClauseTraceEntryRef, Literal, ResolutionValidationError,
    ResolutionValidationResource,
};

use super::types::{
    ExactOriginalClauseBinding, ExactOriginalProofError, ExactOriginalProofFragment, OrFoldUnitPlan,
};
use super::{exact_checked_add, exact_checked_mul, exact_sort_work};
use crate::sat_proof_manager::SatProofManager;

struct FragmentBuildState<'a> {
    /// When `Some`, only original trace entries whose stable id is in this
    /// set — the empty-clause hint-closure CONE of the validated DAG — get a
    /// proof step and binding (#cone-scoped-authority). Entries outside the
    /// cone are never premises of the published refutation; skipping them is
    /// what makes authentication cost proportional to the refutation, not
    /// the whole search. `None` keeps the historical exhaustive build.
    original_id_cone: Option<&'a HashSet<u64>>,
    authored_problem_terms: &'a [TermId],
    authored_problem_term_set: HashSet<TermId>,
    authored_conjunct_closure: HashSet<TermId>,
    /// Boolean-ITE closure members (#ite-expansion-authority); activation
    /// units of their branch implications authenticate via the strict
    /// checker's shared matcher.
    authored_bool_ites: Vec<(TermId, TermId, TermId)>,
    or_fold_unit_plans: HashMap<TermId, OrFoldUnitPlan>,
    proof: Proof,
    bindings: HashMap<u64, ExactOriginalClauseBinding>,
    unit_chain_memo: HashMap<TermId, ProofId>,
    term_store_baseline: usize,
    charged_term_store_growth: usize,
    unit_authority: bool,
}

impl SatProofManager<'_> {
    /// Build a fail-closed proof fragment for every `is_original` trace entry.
    ///
    /// This is stricter than [`Self::process_trace`]. It consults only the two
    /// annotation tables indexed by stable clause ID: normalized-content
    /// theory lookup, minimized-lemma superset bridging, and generic assumption
    /// fallback are all intentionally excluded. An unannotated entry is
    /// accepted only when it is an exact unit assertion from
    /// `authored_problem_terms`.
    ///
    /// Every original ID gets its own proof step and binding, including two
    /// different IDs whose clauses have identical content. That one-to-one
    /// identity is required when a later SAT-premise authenticator composes the
    /// fragment with a checked propositional derivation.
    #[cfg(test)]
    pub(crate) fn build_exact_original_proof_fragment(
        &mut self,
        trace: &ClauseTrace,
        authored_problem_terms: &[TermId],
    ) -> Result<ExactOriginalProofFragment, ExactOriginalProofError> {
        let mut unbounded = |_: usize, _: usize| Ok(());
        self.build_exact_original_proof_fragment_metered(
            trace,
            authored_problem_terms,
            None,
            &mut unbounded,
        )
    }

    /// Metered form used by the checked-SAT-refutation publication gate.
    ///
    /// `progress(work, bytes)` continues the caller's single conversion/replay
    /// allowance and polls its inherited external controls. Byte charges are
    /// conservative retained/allocation estimates; rejecting early is safe.
    pub(crate) fn build_exact_original_proof_fragment_metered(
        &mut self,
        trace: &ClauseTrace,
        authored_problem_terms: &[TermId],
        original_id_cone: Option<&HashSet<u64>>,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<ExactOriginalProofFragment, ExactOriginalProofError> {
        let initial_work = exact_checked_add(
            authored_problem_terms.len(),
            trace.entries().len(),
            ResolutionValidationResource::Work,
        )?;
        let authored_bytes = exact_checked_mul(
            authored_problem_terms.len(),
            64,
            ResolutionValidationResource::Bytes,
        )?;
        progress(initial_work, authored_bytes)?;
        let (term_store_baseline, charged_term_store_growth) =
            self.precharge_term_store_growth(trace, progress)?;
        let mut authored_problem_term_set = HashSet::default();
        for (index, &term) in authored_problem_terms.iter().enumerate() {
            if index % 1024 == 0 {
                progress(0, 0)?;
            }
            authored_problem_term_set.insert(term);
        }
        // One flag per build keeps every quantifier-unit campaign channel
        // consistently on or off within a single fragment construction.
        let unit_authority = crate::quant_unit_authority::quant_unit_authority_enabled();
        let (authored_conjunct_closure, or_fold_unit_plans, authored_bool_ites) =
            self.build_folded_unit_authority(authored_problem_terms, unit_authority, progress)?;
        let mut state = FragmentBuildState {
            original_id_cone,
            authored_problem_terms,
            authored_problem_term_set,
            authored_conjunct_closure,
            or_fold_unit_plans,
            authored_bool_ites,
            proof: Proof::new(),
            bindings: HashMap::default(),
            // Distinct original IDs may carry the same unit. Share its sealed
            // derivation chain while retaining one binding per trace identity.
            unit_chain_memo: HashMap::default(),
            term_store_baseline,
            charged_term_store_growth,
            unit_authority,
        };
        for (trace_index, entry) in trace.entries().iter().enumerate() {
            self.emit_exact_original_entry(trace_index, entry, &mut state, progress)?;
        }
        progress(0, 0)?;
        Ok(ExactOriginalProofFragment {
            proof: state.proof,
            bindings: state.bindings,
        })
    }

    fn emit_exact_original_entry(
        &mut self,
        trace_index: usize,
        entry: ClauseTraceEntryRef<'_>,
        state: &mut FragmentBuildState<'_>,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<(), ExactOriginalProofError> {
        if trace_index % 1024 == 0 {
            progress(0, 0)?;
        }
        if !entry.is_original {
            return Ok(());
        }
        // #cone-scoped-authority: an original outside the refutation's
        // hint-closure cone is never a premise of the published proof.
        if state
            .original_id_cone
            .is_some_and(|cone| !cone.contains(&entry.id))
        {
            return Ok(());
        }
        // Charge all retained per-entry structures before their allocations.
        Self::preflight_exact_original_entry(entry, state, progress)?;
        let clause = self.translate_exact_original_clause(
            entry.id,
            entry.clause,
            state.term_store_baseline,
            &mut state.charged_term_store_growth,
            progress,
        )?;
        let proof_id = match self.emit_indexed_original_step(
            &mut state.proof,
            entry.id,
            &clause,
            state.term_store_baseline,
            &mut state.charged_term_store_growth,
            progress,
        )? {
            Some(step) => step,
            None => self.emit_unannotated_original_step(
                &mut state.proof,
                entry.id,
                &clause,
                &state.authored_problem_term_set,
                &state.authored_conjunct_closure,
                &state.authored_bool_ites,
                state.authored_problem_terms,
                &state.or_fold_unit_plans,
                &mut state.unit_chain_memo,
                state.unit_authority,
                state.term_store_baseline,
                &mut state.charged_term_store_growth,
                progress,
            )?,
        };
        let binding = ExactOriginalClauseBinding {
            proof_id,
            clause: Self::normalize_clause(&clause),
            trace_id: entry.id,
            trace_index,
            source_sat_clause: entry.clause.to_vec(),
        };
        let previous = state.bindings.insert(entry.id, binding);
        debug_assert!(previous.is_none(), "duplicate IDs were rejected above");
        progress(0, 0)?;
        Ok(())
    }

    fn preflight_exact_original_entry(
        entry: ClauseTraceEntryRef<'_>,
        state: &mut FragmentBuildState<'_>,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<(), ExactOriginalProofError> {
        let base_work = exact_checked_add(
            exact_checked_mul(
                exact_sort_work(entry.clause.len())?,
                2,
                ResolutionValidationResource::Work,
            )?,
            exact_checked_add(
                exact_checked_mul(entry.clause.len(), 4, ResolutionValidationResource::Work)?,
                1,
                ResolutionValidationResource::Work,
            )?,
            ResolutionValidationResource::Work,
        )?;
        let base_bytes = exact_checked_add(
            exact_checked_mul(entry.clause.len(), 256, ResolutionValidationResource::Bytes)?,
            512,
            ResolutionValidationResource::Bytes,
        )?;
        progress(base_work, base_bytes)?;
        state.proof.steps.try_reserve(1).map_err(|_| {
            ResolutionValidationError::AllocationFailed {
                resource: ResolutionValidationResource::Bytes,
            }
        })?;
        if entry.id == 0 {
            return Err(ExactOriginalProofError::ZeroClauseId);
        }
        if state.bindings.contains_key(&entry.id) {
            return Err(ExactOriginalProofError::DuplicateClauseId {
                clause_id: entry.id,
            });
        }
        if entry.clause.is_empty() {
            return Err(ExactOriginalProofError::EmptyOriginalClause {
                clause_id: entry.id,
            });
        }
        Ok(())
    }

    fn translate_exact_original_clause(
        &mut self,
        clause_id: u64,
        literals: &[Literal],
        term_store_baseline: usize,
        charged_term_store_growth: &mut usize,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<Vec<TermId>, ExactOriginalProofError> {
        let mut clause = Vec::new();
        clause.try_reserve_exact(literals.len()).map_err(|_| {
            ResolutionValidationError::AllocationFailed {
                resource: ResolutionValidationResource::Bytes,
            }
        })?;
        for (literal_index, &literal) in literals.iter().enumerate() {
            if literal_index % 1024 == 0 {
                progress(0, 0)?;
            }
            let variable = literal.variable().index() as u32;
            if self.is_scope_assumption_variable(variable) {
                if !literal.is_positive() {
                    return Err(ExactOriginalProofError::SatisfiedScopeGuard {
                        clause_id,
                        variable,
                    });
                }
                // This positive guard is false under the exact negative unit
                // premise sealed into the trace snapshot. Structural replay
                // already checked the raw row; authenticate its projection.
                continue;
            }
            let Some(&mapped_term) = self.var_to_term.get(&variable) else {
                return Err(ExactOriginalProofError::UnmappedVariable {
                    clause_id,
                    variable,
                });
            };
            if mapped_term.index() >= self.terms.len() {
                return Err(ExactOriginalProofError::StaleMappedTerm {
                    clause_id,
                    variable,
                    term: mapped_term,
                });
            }
            let Some(term) = self.lit_to_term(literal) else {
                return Err(ExactOriginalProofError::UnmappedVariable {
                    clause_id,
                    variable,
                });
            };
            self.reconcile_term_store_growth(
                term_store_baseline,
                charged_term_store_growth,
                progress,
            )?;
            clause.push(term);
        }
        Ok(clause)
    }
}
