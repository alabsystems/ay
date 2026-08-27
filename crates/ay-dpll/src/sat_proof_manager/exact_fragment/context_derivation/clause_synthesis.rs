// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certified bridges for originals without a sealed clause-level record.

use ay_core::{Proof, ProofId, ProofStep, TermData, TermId, TheoryLemmaKind};

use super::transition_structure::{datatype_of_sort, datatype_sorted_subjects};
use super::{ContextDerivationState, CONTEXT_DERIVATION_MAX_DEPTH};
use crate::sat_proof_manager::{ExactOriginalProofError, SatProofManager};
use crate::theory_inference::DatatypeRegistries;

impl SatProofManager<'_> {
    /// Authenticate recordless datatype units and small conflict clauses.
    ///
    /// Each bridge is accepted only after the same ground refuter used by the
    /// strict checker validates its widened lemma, and every added premise is
    /// discharged through the ordinary context-premise authority chain.
    pub(in crate::sat_proof_manager::exact_fragment) fn emit_context_synthesis(
        &mut self,
        proof: &mut Proof,
        clause: &[TermId],
        state: &mut ContextDerivationState<'_>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        if !state.unit_authority {
            return Ok(None);
        }
        if let [unit] = clause {
            if let Some(step) =
                self.emit_context_premise_step(proof, *unit, state, CONTEXT_DERIVATION_MAX_DEPTH)?
            {
                return Ok(Some(step));
            }
        }
        if !(2..=24).contains(&clause.len()) {
            return Ok(None);
        }
        let Some(registry) = self.dt_registry_data else {
            return Ok(None);
        };
        let view = DatatypeRegistries::from_data(registry);
        let subjects = clause_datatype_subjects(self.terms, clause, view.datatypes);
        if let Some(step) =
            self.emit_clause_tester_bridge(proof, clause, state, &subjects, &view)?
        {
            return Ok(Some(step));
        }
        self.emit_clause_value_bridge(proof, clause, state, &subjects, &view)
    }

    fn emit_clause_tester_bridge(
        &mut self,
        proof: &mut Proof,
        clause: &[TermId],
        state: &mut ContextDerivationState<'_>,
        subjects: &[TermId],
        view: &DatatypeRegistries<'_>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        for &subject in subjects {
            let Some(datatype) = datatype_of_sort(self.terms.sort(subject), view.datatypes) else {
                continue;
            };
            let constructors = view
                .datatypes
                .iter()
                .find(|(name, _)| name == datatype)
                .map(|(_, constructors)| constructors.clone())
                .unwrap_or_default();
            for constructor in constructors {
                let tester = self.terms.mk_app(
                    ay_core::Symbol::named(format!("is-{constructor}")),
                    vec![subject],
                    ay_core::Sort::Bool,
                );
                let not_tester = self.terms.mk_not(tester);
                self.reconcile_term_store_growth(
                    state.term_store_baseline,
                    state.charged_term_store_growth,
                    state.progress,
                )?;
                let mut widened = clause.to_vec();
                if widened.contains(&not_tester) {
                    continue;
                }
                widened.push(not_tester);
                if !self.context_refuter_accepts(&widened, view.datatypes, view.ctor_selectors) {
                    continue;
                }
                let Some(tester_step) = self.emit_context_premise_step(
                    proof,
                    tester,
                    state,
                    CONTEXT_DERIVATION_MAX_DEPTH,
                )?
                else {
                    continue;
                };
                let (work, bytes) = Self::unit_chain_charge(2, widened.len())?;
                (state.progress)(work, bytes)?;
                let lemma = proof.add_step(ProofStep::TheoryLemma {
                    theory: "dt".to_owned(),
                    clause: widened,
                    farkas: None,
                    kind: TheoryLemmaKind::DatatypeGroundConflict,
                    lia: None,
                });
                return Ok(Some(proof.add_resolution(
                    clause.to_vec(),
                    tester,
                    lemma,
                    tester_step,
                )));
            }
        }
        Ok(None)
    }

    fn emit_clause_value_bridge(
        &mut self,
        proof: &mut Proof,
        clause: &[TermId],
        state: &mut ContextDerivationState<'_>,
        subjects: &[TermId],
        view: &DatatypeRegistries<'_>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        let Some(derivations) = self.context_derivations else {
            return Ok(None);
        };
        let mut value_candidates = Vec::new();
        for key in derivations.keys() {
            let [equality] = key.as_slice() else {
                continue;
            };
            let TermData::App(symbol, arguments) = self.terms.get(*equality) else {
                continue;
            };
            if symbol.name() != "=" || arguments.len() != 2 {
                continue;
            }
            if (subjects.contains(&arguments[0]) || subjects.contains(&arguments[1]))
                && !value_candidates.contains(equality)
                && value_candidates.len() < 24
            {
                value_candidates.push(*equality);
            }
        }
        let candidate_sets = value_candidate_sets(&value_candidates);
        'candidate_sets: for premises in candidate_sets.into_iter().take(256) {
            let mut widened = clause.to_vec();
            let mut negated = Vec::with_capacity(premises.len());
            for &premise in &premises {
                let negation = self.terms.mk_not(premise);
                if widened.contains(&negation) {
                    continue 'candidate_sets;
                }
                negated.push(negation);
                widened.push(negation);
            }
            self.reconcile_term_store_growth(
                state.term_store_baseline,
                state.charged_term_store_growth,
                state.progress,
            )?;
            if !self.context_refuter_accepts(&widened, view.datatypes, view.ctor_selectors) {
                continue;
            }
            let mut premise_steps = Vec::with_capacity(premises.len());
            for &premise in &premises {
                let Some(step) = self.emit_context_premise_step(
                    proof,
                    premise,
                    state,
                    CONTEXT_DERIVATION_MAX_DEPTH,
                )?
                else {
                    continue 'candidate_sets;
                };
                premise_steps.push(step);
            }
            let (work, bytes) = Self::unit_chain_charge(1 + premises.len(), widened.len())?;
            (state.progress)(work, bytes)?;
            return Ok(Some(emit_value_resolution_chain(
                proof,
                widened,
                &premises,
                &negated,
                &premise_steps,
            )));
        }
        Ok(None)
    }
}

fn clause_datatype_subjects(
    terms: &ay_core::TermStore,
    clause: &[TermId],
    datatypes: &[(String, Vec<String>)],
) -> Vec<TermId> {
    let mut subjects = Vec::new();
    for &literal in clause {
        for subject in datatype_sorted_subjects(terms, literal, datatypes) {
            if !subjects.contains(&subject) && subjects.len() < 16 {
                subjects.push(subject);
            }
        }
    }
    subjects
}

fn value_candidate_sets(candidates: &[TermId]) -> Vec<Vec<TermId>> {
    let mut sets: Vec<Vec<TermId>> = candidates.iter().copied().map(|term| vec![term]).collect();
    for first in 0..candidates.len() {
        for second in (first + 1)..candidates.len() {
            sets.push(vec![candidates[first], candidates[second]]);
        }
    }
    sets
}

fn emit_value_resolution_chain(
    proof: &mut Proof,
    widened: Vec<TermId>,
    premises: &[TermId],
    negated: &[TermId],
    premise_steps: &[ProofId],
) -> ProofId {
    let mut previous = proof.add_step(ProofStep::TheoryLemma {
        theory: "dt".to_owned(),
        clause: widened.clone(),
        farkas: None,
        kind: TheoryLemmaKind::DatatypeGroundConflict,
        lia: None,
    });
    let mut remaining = widened;
    for ((&premise, &negation), &premise_step) in premises.iter().zip(negated).zip(premise_steps) {
        remaining.retain(|&literal| literal != negation);
        previous = proof.add_resolution(remaining.clone(), premise, previous, premise_step);
    }
    previous
}
