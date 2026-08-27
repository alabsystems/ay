// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Premise-carrying exact fragments for context-dependent datatype clauses.

mod clause_synthesis;
mod transition_structure;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Proof, ProofId, ProofStep, TermData, TermId, TheoryLemmaKind};
use ay_sat::ResolutionValidationError;

use crate::sat_proof_manager::{ExactOriginalProofError, SatProofManager};

/// Premise-chaining recursion bound. Depth exhaustion declines fail-closed.
const CONTEXT_DERIVATION_MAX_DEPTH: usize = 32;

pub(super) struct ContextDerivationState<'a> {
    pub(super) authored_terms: &'a HashSet<TermId>,
    pub(super) authored_conjuncts: &'a HashSet<TermId>,
    pub(super) authored_bool_ites: &'a [(TermId, TermId, TermId)],
    pub(super) unit_authority: bool,
    pub(super) unit_chain_memo: &'a mut HashMap<TermId, ProofId>,
    pub(super) term_store_baseline: usize,
    pub(super) charged_term_store_growth: &'a mut usize,
    pub(super) progress: &'a mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
}

impl SatProofManager<'_> {
    /// Probe the deterministic ground refuter once per normalized clause.
    ///
    /// Context synthesis revisits the same widened clauses across recursive
    /// chains and authentication passes. Caching the independently checked
    /// verdict keeps that replay bounded without granting new authority.
    fn context_refuter_accepts(
        &mut self,
        widened: &[TermId],
        datatypes: &[(String, Vec<String>)],
        ctor_selectors: &[(String, Vec<String>)],
    ) -> bool {
        let key = Self::normalize_clause(widened);
        if let Some(&verdict) = self.ground_refuter_memo.get(&key) {
            return verdict;
        }
        let verdict = ay_proof::recognize_datatype_ground_conflict(
            self.terms,
            widened,
            datatypes,
            ctor_selectors,
        );
        self.ground_refuter_memo.insert(key, verdict);
        verdict
    }

    pub(super) fn emit_context_derivation(
        &mut self,
        proof: &mut Proof,
        clause: &[TermId],
        state: &mut ContextDerivationState<'_>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        self.emit_context_derivation_chain(proof, clause, state, CONTEXT_DERIVATION_MAX_DEPTH)
    }

    /// Authenticate one original clause through a sealed premise derivation.
    ///
    /// The strict checker re-validates the widened datatype lemma and every
    /// authored premise before binary resolution recovers the traced clause.
    fn emit_context_derivation_chain(
        &mut self,
        proof: &mut Proof,
        clause: &[TermId],
        state: &mut ContextDerivationState<'_>,
        depth: usize,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        let Some(derivations) = self.context_derivations else {
            return Ok(None);
        };
        let Some(registry) = self.dt_registry_data else {
            return Ok(None);
        };
        let Some(derivation) = derivations.get(&Self::normalize_clause(clause)) else {
            crate::executor::probe_cert_reject_raw(|| {
                format!(
                    "c context-lane-debug decline=no-record lits={}",
                    clause.len()
                )
            });
            return Ok(None);
        };
        for premises in derivation.premise_sets.clone() {
            if premises.is_empty() {
                continue;
            }
            let Some(premise_steps) =
                self.discharge_context_premises(proof, &premises, state, depth)?
            else {
                crate::executor::probe_cert_reject_raw(|| {
                    format!(
                        "c context-lane-debug decline=premise lits={} depth={depth}",
                        clause.len()
                    )
                });
                continue;
            };
            let Some((widened, negated)) = self.widen_context_clause(clause, &premises) else {
                continue;
            };
            self.reconcile_term_store_growth(
                state.term_store_baseline,
                state.charged_term_store_growth,
                state.progress,
            )?;
            let view = crate::theory_inference::DatatypeRegistries::from_data(registry);
            if !self.context_refuter_accepts(&widened, view.datatypes, view.ctor_selectors) {
                crate::executor::probe_cert_reject_raw(|| {
                    format!(
                        "c context-lane-debug decline=refuter lits={} premises={}",
                        clause.len(),
                        premises.len()
                    )
                });
                continue;
            }
            let (work, bytes) =
                Self::unit_chain_charge(1 + 2 * premises.len(), widened.len() + premises.len())?;
            (state.progress)(work, bytes)?;
            return Ok(Some(self.emit_context_resolution_chain(
                proof,
                widened,
                &premises,
                &negated,
                &premise_steps,
            )));
        }
        Ok(None)
    }

    fn discharge_context_premises(
        &mut self,
        proof: &mut Proof,
        premises: &[TermId],
        state: &mut ContextDerivationState<'_>,
        depth: usize,
    ) -> Result<Option<Vec<ProofId>>, ExactOriginalProofError> {
        let mut steps = Vec::with_capacity(premises.len());
        for &premise in premises {
            let Some(step) = self.emit_context_premise_step(proof, premise, state, depth)? else {
                return Ok(None);
            };
            steps.push(step);
        }
        Ok(Some(steps))
    }

    fn widen_context_clause(
        &mut self,
        clause: &[TermId],
        premises: &[TermId],
    ) -> Option<(Vec<TermId>, Vec<TermId>)> {
        let clause_literals: HashSet<TermId> = clause.iter().copied().collect();
        let mut widened = clause.to_vec();
        let mut negated = Vec::with_capacity(premises.len());
        for &premise in premises {
            let negation = match self.terms.get(premise) {
                TermData::Not(inner) => *inner,
                _ => self.terms.mk_not(premise),
            };
            if clause_literals.contains(&negation) || negated.contains(&negation) {
                return None;
            }
            negated.push(negation);
            widened.push(negation);
        }
        Some((widened, negated))
    }

    fn emit_context_resolution_chain(
        &self,
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
        for ((&premise, &negation), &premise_step) in
            premises.iter().zip(negated).zip(premise_steps)
        {
            remaining.retain(|&literal| literal != negation);
            let pivot = match self.terms.get(premise) {
                TermData::Not(inner) => *inner,
                _ => premise,
            };
            previous = proof.add_resolution(remaining.clone(), pivot, previous, premise_step);
        }
        previous
    }

    /// Discharge a premise that is a standalone typed DT unit tautology.
    /// The recognition runs eight recognizers plus the full bounded ground
    /// refuter, so its verdict is memoized per unit term for this build.
    fn emit_typed_unit_lemma(
        &mut self,
        proof: &mut Proof,
        premise: TermId,
        state: &mut ContextDerivationState<'_>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        let Some(registry) = self.dt_registry_data else {
            return Ok(None);
        };
        let recognized = match self.dt_unit_kind_memo.get(&premise) {
            Some(&cached) => cached,
            None => {
                let view = crate::theory_inference::DatatypeRegistries::from_data(registry);
                let kind =
                    crate::theory_inference::infer_dt_lemma_kind(self.terms, &[premise], &view);
                self.dt_unit_kind_memo.insert(premise, kind);
                kind
            }
        };
        let Some(kind) = recognized else {
            return Ok(None);
        };
        let (work, bytes) = Self::unit_chain_charge(1, 1)?;
        (state.progress)(work, bytes)?;
        let step = proof.add_step(ProofStep::TheoryLemma {
            theory: "dt".to_owned(),
            clause: vec![premise],
            farkas: None,
            kind,
            lia: None,
        });
        state.unit_chain_memo.insert(premise, step);
        Ok(Some(step))
    }

    fn emit_context_premise_step(
        &mut self,
        proof: &mut Proof,
        premise: TermId,
        state: &mut ContextDerivationState<'_>,
        depth: usize,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        if let Some(&step) = state.unit_chain_memo.get(&premise) {
            return Ok(Some(step));
        }
        if self.context_premise_budget == 0 {
            return Ok(None);
        }
        self.context_premise_budget -= 1;
        if !self.context_deep_retry
            && self.context_discharge_failures.get(&premise).is_some_and(
                |&(tried_depth, memo_size)| {
                    depth <= tried_depth && state.unit_chain_memo.len() <= memo_size
                },
            )
        {
            return Ok(None);
        }
        if state.authored_terms.contains(&premise)
            || (state.unit_authority && state.authored_conjuncts.contains(&premise))
            || (state.unit_authority
                && ay_proof::assumed_is_authored_bool_ite_consequence(
                    self.terms,
                    premise,
                    state.authored_bool_ites,
                ))
        {
            let (work, bytes) = Self::unit_chain_charge(1, 1)?;
            (state.progress)(work, bytes)?;
            let step = proof.add_assume(premise, None);
            state.unit_chain_memo.insert(premise, step);
            return Ok(Some(step));
        }
        if depth == 0 {
            return Ok(None);
        }
        if let Some(step) = self.emit_typed_unit_lemma(proof, premise, state)? {
            return Ok(Some(step));
        }
        let mut step = self.emit_context_derivation_chain(proof, &[premise], state, depth - 1)?;
        if let Some(step) = step {
            state.unit_chain_memo.insert(premise, step);
            return Ok(Some(step));
        }
        step = self.emit_context_transition_structure(proof, premise, state, depth)?;
        if let Some(step) = step {
            state.unit_chain_memo.insert(premise, step);
            return Ok(Some(step));
        }
        if !self.context_deep_retry {
            // Fast passes memoize every failed search together with the
            // information available at that point. More depth or a larger
            // success memo makes a retry meaningful; the final deep pass
            // deliberately ignores this cache.
            let memo_size = state.unit_chain_memo.len();
            let entry = self
                .context_discharge_failures
                .entry(premise)
                .or_insert((0, 0));
            if depth > entry.0 {
                entry.0 = depth;
            }
            entry.1 = memo_size;
        }
        crate::executor::probe_cert_reject_raw(|| {
            format!(
                "c context-premise-debug undischarged: {}",
                ay_proof::render_term_canonical(self.terms, premise)
            )
        });
        Ok(None)
    }
}
