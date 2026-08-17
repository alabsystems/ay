// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! c7 fragment channel (#ppp-c7): derive one non-authored original unit by
//! replaying sealed `PropagateValues` provenance — and, where sealed, the
//! qpf premise-forced instance root — through the SAME plan machinery as the
//! L1 proof-rebuild lane (`executor::proof_propagated_rewrite`).
//!
//! Authority discipline is unchanged from c2-c6: the sealed environment is
//! hints only; the planner replays every rewrite independently, and every
//! emitted step terminates in rules the untouched strict premise
//! authenticator re-derives (`forall_inst` exact-substitution replay, `or`
//! exact disjunct vectors, `and_pos`, `cong`/`trans`/`eq_symmetric`,
//! `equiv_pos1/2`, `evaluate`, and zero-variable `BvBitBlast` lemmas decided
//! by the exhaustive bounded evaluator). A wrong plan can only be rejected
//! downstream — fail-closed to today's `UnauthenticatedOriginalClause`.
//!
//! Metering: the bounded plan walk is charged as work, then the exact step
//! and retained-slot counts of the ACTUAL planned chain are charged through
//! `unit_chain_charge` BEFORE any step is spliced into the fragment;
//! `unit_chain_memo` shares one chain per distinct unit (the P3b duplicate
//! precharge blowout guard) and the caller reconciles real term-store
//! growth afterwards.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Proof, ProofId, ProofStep, TermId};
use ay_sat::{ResolutionValidationError, ResolutionValidationResource};

use super::exact_checked_add;
use crate::executor::proof_propagated_rewrite::{
    PlanCx, PropagationChainPlanner, PLAN_NODE_BUDGET,
};
use crate::sat_proof_manager::{ExactOriginalProofError, SatProofManager};

fn propagated_chain_slots(chain: &Proof) -> Result<usize, ResolutionValidationError> {
    let mut slots = 0usize;
    for step in &chain.steps {
        let step_slots = match step {
            ProofStep::Assume(_) => 1,
            ProofStep::Step {
                clause,
                premises,
                args,
                ..
            } => exact_checked_add(
                exact_checked_add(
                    clause.len(),
                    premises.len(),
                    ResolutionValidationResource::Bytes,
                )?,
                exact_checked_add(args.len(), 1, ResolutionValidationResource::Bytes)?,
                ResolutionValidationResource::Bytes,
            )?,
            ProofStep::Resolution { clause, .. } => {
                exact_checked_add(clause.len(), 3, ResolutionValidationResource::Bytes)?
            }
            ProofStep::TheoryLemma { clause, .. } => {
                exact_checked_add(clause.len(), 2, ResolutionValidationResource::Bytes)?
            }
            _ => 2,
        };
        slots = exact_checked_add(slots, step_slots, ResolutionValidationResource::Bytes)?;
    }
    Ok(slots)
}

fn remap_chain_step(id: ProofId, chain_map: &[ProofId]) -> ProofId {
    chain_map.get(id.0 as usize).copied().unwrap_or(id)
}

fn splice_propagated_chain(proof: &mut Proof, chain: Proof, conclusion: ProofId) -> ProofId {
    let mut chain_map = Vec::with_capacity(chain.steps.len());
    for chain_step in chain.steps {
        let appended = match chain_step {
            ProofStep::Step {
                rule,
                clause,
                premises,
                args,
            } => proof.add_step(ProofStep::Step {
                rule,
                clause,
                premises: premises
                    .into_iter()
                    .map(|premise| remap_chain_step(premise, &chain_map))
                    .collect(),
                args,
            }),
            ProofStep::Resolution {
                clause,
                pivot,
                clause1,
                clause2,
            } => proof.add_step(ProofStep::Resolution {
                clause,
                pivot,
                clause1: remap_chain_step(clause1, &chain_map),
                clause2: remap_chain_step(clause2, &chain_map),
            }),
            other => proof.add_step(other),
        };
        chain_map.push(appended);
    }
    remap_chain_step(conclusion, &chain_map)
}

impl SatProofManager<'_> {
    /// Plan and emit the c7 chain for one unit, or decline with `Ok(None)`.
    pub(in crate::sat_proof_manager) fn emit_propagated_unit_chain(
        &mut self,
        proof: &mut Proof,
        unit: TermId,
        authored_terms: &HashSet<TermId>,
        authored_problem_terms: &[TermId],
        unit_chain_memo: &mut HashMap<TermId, ProofId>,
        term_store_baseline: usize,
        charged_term_store_growth: &mut usize,
        progress: &mut dyn FnMut(usize, usize) -> Result<(), ResolutionValidationError>,
    ) -> Result<Option<ProofId>, ExactOriginalProofError> {
        let empty_env = super::types::FragmentPropagationEnvironment::default();
        let env = self.propagation_environment.unwrap_or(&empty_env);
        let instance_roots = self.instance_root_derivations.unwrap_or(&[]);
        if env.is_empty() && instance_roots.is_empty() {
            return Ok(None);
        }
        // The whole bounded plan walk is covered before it runs; the exact
        // spend is bounded by PLAN_NODE_BUDGET per unit.
        progress(PLAN_NODE_BUDGET, 0)?;
        let mut cx = PlanCx::new(
            authored_terms,
            authored_problem_terms,
            &env.record_by_after,
            &env.entry_by_expr,
            instance_roots,
            true,
        );
        let mut planner = PropagationChainPlanner { terms: self.terms };
        let Some(conclusion) = planner.plan_derive_clause(&mut cx, unit) else {
            return Ok(None);
        };
        let chain = cx.chain;

        // Exact metering BEFORE emission: the retained-slot count is the
        // actual clause-literal + argument + premise footprint of the
        // planned chain, and each spliced step is one proof step.
        let slots = propagated_chain_slots(&chain)?;
        let (work, bytes) = Self::unit_chain_charge(chain.steps.len(), slots)?;
        progress(work, bytes)?;
        proof.steps.try_reserve(chain.steps.len()).map_err(|_| {
            ResolutionValidationError::AllocationFailed {
                resource: ResolutionValidationResource::Bytes,
            }
        })?;

        // Splice with an old->new id map so every premise reference stays
        // backward (the exact L1 rebuild-lane splice).
        let step = splice_propagated_chain(proof, chain, conclusion);
        self.reconcile_term_store_growth(term_store_baseline, charged_term_store_growth, progress)?;
        unit_chain_memo.insert(unit, step);
        Ok(Some(step))
    }
}
