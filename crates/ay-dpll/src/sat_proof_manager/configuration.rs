// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Construction and authority-input configuration for `SatProofManager`.

use super::*;

/// Trace entries replayed between two stop polls. One poll is an atomic load,
/// a lock and a clock read; one entry is at least a clause translation.
const STOP_POLL_STRIDE: usize = 64;

impl<'a> SatProofManager<'a> {
    pub(crate) fn new(var_to_term: &'a HashMap<u32, TermId>, terms: &'a mut TermStore) -> Self {
        Self {
            var_to_term,
            terms,
            clausification_proofs: None,
            original_clause_theory_proofs: None,
            theory_lemma_proofs: None,
            scope_assumptions: &[],
            instance_derivations: None,
            skolem_derivations: None,
            propagation_environment: None,
            instance_root_derivations: None,
            trust_fallback_count: 0,
            materialized_lemma_versions: Default::default(),
            untranslatable_entries: 0,
            unmapped_var_min: None,
            unmapped_var_max: None,
            step_budget: None,
            should_stop: None,
            dt_registry_data: None,
            context_derivations: None,
            context_discharge_failures: Default::default(),
            ground_refuter_memo: Default::default(),
            context_deep_retry: false,
            context_premise_budget: 0,
            dt_unit_kind_memo: Default::default(),
            equality_neighbour_index: None,
        }
    }

    /// Install the sealed context-derivation map (#dt-context-derivation).
    pub(crate) fn set_context_derivations(
        &mut self,
        derivations: &'a HashMap<Vec<TermId>, FragmentContextDerivation>,
    ) {
        self.context_derivations = Some(derivations);
    }

    pub(crate) fn set_dt_registry_data(
        &mut self,
        data: Option<&'a crate::theory_inference::DatatypeRegistryData>,
    ) {
        self.dt_registry_data = data;
    }

    pub(crate) fn set_step_budget(&mut self, budget: Option<u64>) {
        self.step_budget = budget;
    }

    /// Stop the trace replay once `should_stop` reports the caller's interrupt
    /// or deadline; the replay then returns `None`, as on budget exhaustion.
    pub(crate) fn set_should_stop(&mut self, should_stop: &'a dyn Fn() -> bool) {
        self.should_stop = Some(should_stop);
    }

    /// Whether the replay must stop before trace entry `entry_index`: the stop
    /// predicate is consulted once per [`STOP_POLL_STRIDE`] entries.
    pub(super) fn stop_requested_at(&self, entry_index: usize) -> bool {
        entry_index % STOP_POLL_STRIDE == 0 && self.should_stop.is_some_and(|stop| stop())
    }

    /// Validate and install solver-minted active-scope premises.
    pub(crate) fn set_scope_assumptions(
        &mut self,
        assumptions: &'a [Literal],
    ) -> Result<(), ExactOriginalProofError> {
        let mut previous = None;
        for &assumption in assumptions {
            let variable = assumption.variable().index() as u32;
            if assumption.is_positive() {
                return Err(ExactOriginalProofError::PositiveScopeAssumption { variable });
            }
            if self.var_to_term.contains_key(&variable) {
                return Err(ExactOriginalProofError::MappedScopeAssumption { variable });
            }
            if let Some(prior) = previous {
                if variable == prior {
                    return Err(ExactOriginalProofError::DuplicateScopeAssumption { variable });
                }
                if variable < prior {
                    return Err(ExactOriginalProofError::UnorderedScopeAssumption {
                        previous: prior,
                        variable,
                    });
                }
            }
            previous = Some(variable);
        }
        self.scope_assumptions = assumptions;
        Ok(())
    }

    pub(super) fn is_scope_assumption_variable(&self, variable: u32) -> bool {
        self.scope_assumptions
            .binary_search_by_key(&variable, |assumption| assumption.variable().index() as u32)
            .is_ok()
    }

    pub(crate) fn set_clausification_proofs(&mut self, proofs: &'a [Option<ClausificationProof>]) {
        self.clausification_proofs = Some(proofs);
    }

    pub(super) fn original_annotation_by_id<T>(
        annotations: Option<&[Option<T>]>,
        clause_id: u64,
    ) -> Option<&T> {
        let index = usize::try_from(clause_id.checked_sub(1)?).ok()?;
        annotations?.get(index)?.as_ref()
    }

    pub(crate) fn set_original_clause_theory_proofs(
        &mut self,
        proofs: &'a [Option<TheoryLemmaProof>],
    ) {
        self.original_clause_theory_proofs = Some(proofs);
    }

    pub(crate) fn set_instance_derivations(
        &mut self,
        derivations: &'a HashMap<TermId, FragmentInstanceDerivation>,
    ) {
        self.instance_derivations = Some(derivations);
    }

    pub(crate) fn set_skolem_derivations(
        &mut self,
        derivations: &'a HashMap<TermId, FragmentSkolemDerivation>,
    ) {
        self.skolem_derivations = Some(derivations);
    }

    pub(crate) fn set_propagation_environment(
        &mut self,
        environment: &'a FragmentPropagationEnvironment,
    ) {
        self.propagation_environment = Some(environment);
    }

    pub(crate) fn set_instance_root_derivations(
        &mut self,
        derivations: &'a [FragmentInstanceRootDerivation],
    ) {
        self.instance_root_derivations = Some(derivations);
    }

    pub(crate) fn set_theory_lemma_proofs(
        &mut self,
        proofs: &'a HashMap<Vec<TermId>, TheoryLemmaProof>,
    ) {
        self.theory_lemma_proofs = Some(proofs);
    }
}

#[cfg(test)]
#[path = "configuration_stop_tests.rs"]
mod stop_tests;
