// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Re-home an elaborated authored conjunction onto its exact raw spelling.
//!
//! Many refutation builders assume a problem root by its ELABORATED term and
//! project its conjuncts with `and_pos`. When the retained authored text of
//! that root is an `(and ...)` that elaboration deduplicated, reordered or
//! folded, the Alethe printer has to present those projections against the
//! authored operands, and it can only do so for a few printed shapes. A
//! native program that retains its assertion sources otherwise loses a proof
//! the strict checker already accepted.
//!
//! This pass replaces such an `assume` by the exact raw re-intern of the
//! authored conjunction and derives the elaborated root from it: one
//! `and_pos` per authored operand, a checked transport onto each elaborated
//! conjunct (`evaluate`/`cong`, `(= p false)`, pruned `false` disjuncts, an
//! equality lifted over an `ite`, a one-row Farkas reorientation, an
//! equality flip), and `and_neg` to rebuild the root. Every other step is
//! kept. The candidate is published only after the strict checker accepts it
//! over the authored premise scope; otherwise the proof is left unchanged.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Symbol, TermId};
use ay_frontend::command::Term as FrontendTerm;

use super::super::proof_original_rebuild::is_api_placeholder;
use super::super::proof_surface_syntax::strip_frontend_annotations;
use super::super::proof_trust_surgery::TransportPlan;
use super::super::Executor;
use super::remap_step_premises;

/// Largest authored conjunction this pass re-homes.
const MAX_REHOMED_CONJUNCTS: usize = 256;

/// How one elaborated conjunct is obtained from the authored operands.
struct ConjunctSource {
    /// Index of the authored operand projected with `and_pos`.
    operand: usize,
    /// `None` when the raw operand IS the elaborated conjunct.
    transport: Option<TransportPlan>,
}

struct RehomePlan {
    canonical: TermId,
    raw: TermId,
    raw_operands: Vec<TermId>,
    conjuncts: Vec<TermId>,
    sources: Vec<ConjunctSource>,
    /// Set instead of `sources` when some elaborated conjunct is not the
    /// elaboration of one authored operand (nested conjunctions flattened,
    /// pruned disjunctions): one transport of the whole conjunction.
    whole: Option<TransportPlan>,
}

impl Executor {
    /// See the module docs.
    pub(in crate::executor::proof) fn rehome_elaborated_conjunction_assumes(
        &mut self,
        proof: &mut Proof,
    ) {
        if !self.ctx.retains_parsed_assertions()
            || proof
                .steps
                .iter()
                .any(|step| matches!(step, ProofStep::Anchor { .. }))
        {
            return;
        }
        let parsed = self.ctx.assertions_parsed().to_vec();
        if parsed.is_empty() || parsed.iter().all(is_api_placeholder) {
            return;
        }
        let originals = self.proof_original_problem_assertions();
        if originals.len() != parsed.len() {
            return;
        }
        let assumed: Vec<TermId> = proof
            .steps
            .iter()
            .filter_map(|step| match step {
                ProofStep::Assume(term) => Some(*term),
                _ => None,
            })
            .collect();
        let mut plans: Vec<RehomePlan> = Vec::new();
        for (&canonical, surface) in originals.iter().zip(parsed.iter()) {
            if !assumed.contains(&canonical) || plans.iter().any(|plan| plan.canonical == canonical)
            {
                continue;
            }
            if let Some(plan) = self.plan_conjunction_rehome(canonical, surface) {
                plans.push(plan);
            }
        }
        if plans.is_empty() {
            return;
        }

        let saved_rebuild = self.last_proof_rebuild_originals.clone();
        let saved_raw = self.last_proof_raw_original_assertions.clone();
        for plan in &plans {
            self.record_raw_authored_problem_assertion(plan.raw);
        }
        let candidate = self.emit_rehomed_proof(proof, &plans);
        let accepted = candidate.as_ref().is_some_and(|candidate| {
            self.check_proof_strict_with_datatypes(candidate)
                .is_ok_and(|quality| quality.is_complete())
        });
        match candidate {
            Some(candidate) if accepted => {
                *proof = candidate;
                let roots: Vec<TermId> = plans.iter().map(|plan| plan.canonical).collect();
                self.drop_surface_overrides_below(&roots);
            }
            _ => {
                self.last_proof_rebuild_originals = saved_rebuild;
                self.last_proof_raw_original_assertions = saved_raw;
            }
        }
    }

    fn plan_conjunction_rehome(
        &mut self,
        canonical: TermId,
        surface: &FrontendTerm,
    ) -> Option<RehomePlan> {
        let stripped = strip_frontend_annotations(surface);
        let FrontendTerm::App(head, operands) = stripped else {
            return None;
        };
        if head != "and" || operands.len() < 2 || operands.len() > MAX_REHOMED_CONJUNCTS {
            return None;
        }
        let TermData::App(Symbol::Named(canonical_head), conjuncts) =
            self.ctx.terms.get(canonical).clone()
        else {
            return None;
        };
        if canonical_head != "and" || conjuncts.len() > MAX_REHOMED_CONJUNCTS {
            return None;
        }
        let raw = self.raw_intern_surface(stripped)?;
        if raw == canonical {
            return None;
        }
        let TermData::App(Symbol::Named(raw_head), raw_operands) = self.ctx.terms.get(raw).clone()
        else {
            return None;
        };
        if raw_head != "and" || raw_operands.len() != operands.len() {
            return None;
        }
        let mut elaborated = Vec::with_capacity(operands.len());
        for operand in operands {
            elaborated.push(
                self.ctx
                    .elaborate_surface_subterm(strip_frontend_annotations(operand)),
            );
        }
        let mut sources = Vec::with_capacity(conjuncts.len());
        for &conjunct in &conjuncts {
            // Prefer an operand that already IS the conjunct, then one whose
            // elaboration is the conjunct and has a checked transport.
            if let Some(operand) = raw_operands.iter().position(|&raw| raw == conjunct) {
                sources.push(ConjunctSource {
                    operand,
                    transport: None,
                });
                continue;
            }
            let mut found = None;
            for (operand, &raw_operand) in raw_operands.iter().enumerate() {
                if elaborated[operand] != Some(conjunct) {
                    continue;
                }
                if let Some(plan) = self.plan_conjunct_transport(raw_operand, conjunct) {
                    found = Some(ConjunctSource {
                        operand,
                        transport: Some(plan),
                    });
                    break;
                }
            }
            match found {
                Some(found) => sources.push(found),
                None => {
                    let whole = self.plan_conjunct_transport(raw, canonical)?;
                    return Some(RehomePlan {
                        canonical,
                        raw,
                        raw_operands,
                        conjuncts,
                        sources: Vec::new(),
                        whole: Some(whole),
                    });
                }
            }
        }
        Some(RehomePlan {
            canonical,
            raw,
            raw_operands,
            conjuncts,
            sources,
            whole: None,
        })
    }

    /// Build the candidate: every kept `assume` and every raw root first, then
    /// the derivations of the re-homed roots, then the original steps with
    /// their premises remapped. `None` if a step references a later id.
    fn emit_rehomed_proof(&mut self, proof: &Proof, plans: &[RehomePlan]) -> Option<Proof> {
        let mut candidate = Proof::new();
        let mut remap: Vec<ProofId> = vec![ProofId(u32::MAX); proof.steps.len()];
        let mut raw_assume: HashMap<TermId, ProofId> = HashMap::default();
        for (index, step) in proof.steps.iter().enumerate() {
            if let ProofStep::Assume(term) = step {
                if !plans.iter().any(|plan| plan.canonical == *term) {
                    remap[index] = candidate.add_step(step.clone());
                }
            }
        }
        for plan in plans {
            let id = candidate.add_assume(plan.raw, None);
            raw_assume.insert(plan.raw, id);
        }
        let mut derived: HashMap<TermId, ProofId> = HashMap::default();
        for plan in plans {
            let unit = *raw_assume.get(&plan.raw)?;
            let root = self.emit_rehomed_root(&mut candidate, plan, unit)?;
            derived.insert(plan.canonical, root);
        }
        for (index, step) in proof.steps.iter().enumerate() {
            match step {
                ProofStep::Assume(term) => {
                    if let Some(&root) = derived.get(term) {
                        remap[index] = root;
                    }
                }
                _ => {
                    let remapped = remap_step_premises(step.clone(), &remap);
                    if step_references_unmapped(&remapped) {
                        return None;
                    }
                    remap[index] = candidate.add_step(remapped);
                }
            }
        }
        Some(candidate)
    }

    fn emit_rehomed_root(
        &mut self,
        proof: &mut Proof,
        plan: &RehomePlan,
        unit: ProofId,
    ) -> Option<ProofId> {
        if let Some(whole) = &plan.whole {
            return Some(self.emit_conjunct_transport(
                proof,
                unit,
                plan.raw,
                plan.canonical,
                whole,
            ));
        }
        let not_raw = self.ctx.terms.mk_not_raw(plan.raw);
        let mut projected: HashMap<usize, ProofId> = HashMap::default();
        let mut conjunct_units = Vec::with_capacity(plan.conjuncts.len());
        for (&conjunct, source) in plan.conjuncts.iter().zip(plan.sources.iter()) {
            let raw_operand = plan.raw_operands[source.operand];
            let raw_unit = match projected.get(&source.operand) {
                Some(&id) => id,
                None => {
                    let position = u32::try_from(source.operand).ok()?;
                    let extraction = proof.add_rule_step(
                        AletheRule::AndPos(position),
                        vec![not_raw, raw_operand],
                        Vec::new(),
                        vec![plan.raw],
                    );
                    let id = proof.add_resolution(vec![raw_operand], plan.raw, extraction, unit);
                    projected.insert(source.operand, id);
                    id
                }
            };
            let conjunct_unit = match &source.transport {
                None => raw_unit,
                Some(transport) => {
                    self.emit_conjunct_transport(proof, raw_unit, raw_operand, conjunct, transport)
                }
            };
            conjunct_units.push(conjunct_unit);
        }
        let mut clause = Vec::with_capacity(plan.conjuncts.len() + 1);
        clause.push(plan.canonical);
        for &conjunct in &plan.conjuncts {
            clause.push(self.ctx.terms.mk_not_raw(conjunct));
        }
        let mut current = proof.add_rule_step(
            AletheRule::AndNeg,
            clause.clone(),
            Vec::new(),
            vec![plan.canonical],
        );
        for (&conjunct, &conjunct_unit) in plan.conjuncts.iter().zip(conjunct_units.iter()) {
            let complement = self.ctx.terms.mk_not_raw(conjunct);
            let position = clause.iter().position(|&literal| literal == complement)?;
            let _ = clause.remove(position);
            current = proof.add_resolution(clause.clone(), conjunct, current, conjunct_unit);
        }
        Some(current)
    }
}

fn step_references_unmapped(step: &ProofStep) -> bool {
    let unmapped = |id: &ProofId| id.0 == u32::MAX;
    match step {
        ProofStep::Resolution {
            clause1, clause2, ..
        } => unmapped(clause1) || unmapped(clause2),
        ProofStep::Step { premises, .. } => premises.iter().any(unmapped),
        ProofStep::Anchor { end_step, .. } => unmapped(end_step),
        _ => false,
    }
}
