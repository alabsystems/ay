// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact authored `not(and ..)` reconstruction for a rewritten packed `or`.
//!
//! NIA preprocessing can eliminate one proved conjunct and rewrite the other
//! conjuncts through authored definitions, leaving a premiseless `trust` unit
//! `(cl (or ..))`.  That unit is not a tautology.  This lane reconstructs it
//! from the exact raw source assertion: premise-based `not_and`, explicit
//! definition equalities, exact polynomial identities, predicate congruence
//! (or a checked Farkas order bridge), and a final checked re-pack.

mod direct_refutation;
mod emit_bridge;
mod eq_plan;
mod shape;
mod surface_budget;

use ay_core::kani_compat::DetHashMap;
use ay_core::{
    AletheRule, FarkasAnnotation, Proof, ProofStep, Symbol, TermData, TermId, TheoryLemmaKind,
};
use ay_proof::CongruenceDerivation;

use self::emit_bridge::emit_literal_bridge;
#[cfg(test)]
use self::eq_plan::MAX_POLY_ATTEMPTS;
use self::eq_plan::{
    collect_definitions, emit_eq_plan, plan_numeric_equality, Definition, EqBudget, EqPlan,
};
use self::shape::{
    choose_sources_with_discharges, decode_relation, has_duplicates, packed_children,
    packed_trust_unit, raw_negated_conjuncts, same_unique_set,
};
use super::super::Executor;

const MAX_AUTHORED_ROOTS: usize = 128;
const MAX_DEFINITIONS: usize = 64;
const MAX_CONJUNCTS: usize = 16;
const MAX_CANDIDATE_LEAVES: usize = 4;
const MAX_INPUT_PROOF_STEPS: usize = 4_096;
const MAX_FRAGMENT_STEPS: usize = 4_096;
const MAX_WEAKENED_GOALS: usize = 2;
const MAX_DISCHARGED_CONJUNCTS: usize = 3;
const EQ_WORK: u32 = 100_000;

#[derive(Clone, Copy, Eq, PartialEq)]
enum RelationKind {
    Eq,
    Le,
    Lt,
}

struct Relation {
    kind: RelationKind,
    semantic_args: [TermId; 2],
    symbol: Symbol,
}

enum BridgeAuthority {
    Direct,
    Euf {
        clause: Vec<TermId>,
    },
    Farkas {
        clause: Vec<TermId>,
        annotation: FarkasAnnotation,
        kind: TheoryLemmaKind,
    },
}

struct LiteralBridge {
    source_index: usize,
    source_atom: TermId,
    source_negative: TermId,
    goal: TermId,
    equalities: Vec<EqPlan>,
    authority: BridgeAuthority,
}

struct SourcePlan {
    root: TermId,
    source_negatives: Vec<TermId>,
    bridges: Vec<LiteralBridge>,
    discharged: Vec<(usize, EqPlan)>,
    weakened_goals: Vec<TermId>,
}

impl LiteralBridge {
    fn emitted_step_upper_bound(&self) -> Option<usize> {
        if matches!(&self.authority, BridgeAuthority::Direct) {
            return Some(0);
        }
        let equality_steps = self.equalities.iter().try_fold(0usize, |total, plan| {
            total.checked_add(plan.emitted_step_upper_bound()?)
        })?;
        // One bridge theory lemma, at most one resolution per equality, and
        // one resolution replacing the source literal in the running clause.
        equality_steps
            .checked_add(1)?
            .checked_add(self.equalities.len())?
            .checked_add(1)
    }
}

impl SourcePlan {
    fn common_prefix_step_upper_bound(&self) -> Option<usize> {
        // Exact authored root `assume` plus its `not_and` projection.
        let mut steps = 2usize;
        for bridge in &self.bridges {
            steps = steps.checked_add(bridge.emitted_step_upper_bound()?)?;
        }
        for (_, plan) in &self.discharged {
            steps = steps
                .checked_add(plan.emitted_step_upper_bound()?)?
                .checked_add(1)?;
        }
        Some(steps)
    }

    fn fragment_step_upper_bound(&self, goal_count: usize) -> Option<usize> {
        let mut steps = self.common_prefix_step_upper_bound()?;
        if !self.weakened_goals.is_empty() {
            steps = steps.checked_add(1)?;
        }
        // Conservatively reserve reordering even when the planned order already
        // matches, then two repack steps for every disjunct.
        steps
            .checked_add(1)?
            .checked_add(goal_count.checked_mul(2)?)
    }
}

fn emitted_steps_admitted(upper_bound: Option<usize>, limit: usize) -> bool {
    upper_bound.is_some_and(|steps| steps <= limit)
}

impl Executor {
    pub(super) fn replace_with_exact_authored_negated_conjunct_bridge(
        &mut self,
        proof: &mut Proof,
    ) {
        if proof.steps.len() > MAX_INPUT_PROOF_STEPS {
            return;
        }
        let raw_roots = self.authenticated_raw_roots_for_negated_conjunct_bridge();
        if raw_roots.is_empty() {
            return;
        }
        let candidates: Vec<(usize, TermId, Vec<TermId>)> = proof
            .steps
            .iter()
            .enumerate()
            .filter_map(|(index, step)| {
                let packed = packed_trust_unit(&self.ctx.terms, step)?;
                let goals = packed_children(&self.ctx.terms, packed)?;
                Some((index, packed, goals))
            })
            .take(MAX_CANDIDATE_LEAVES + 1)
            .collect();
        if candidates.is_empty() || candidates.len() > MAX_CANDIDATE_LEAVES {
            return;
        }
        let mut surfaces = Vec::with_capacity(
            raw_roots.len()
                + candidates
                    .iter()
                    .map(|(_, _, goals)| goals.len() + 1)
                    .sum::<usize>(),
        );
        surfaces.extend(raw_roots.iter().copied());
        for (_, packed, goals) in &candidates {
            surfaces.push(*packed);
            surfaces.extend(goals.iter().copied());
        }
        if !surface_budget::surfaces_admitted(&self.ctx.terms, &surfaces) {
            return;
        }
        let definitions = collect_definitions(&self.ctx.terms, &raw_roots);
        if definitions.is_empty() || definitions.len() > MAX_DEFINITIONS {
            return;
        }
        if self.authored_cascade_publishable(proof) {
            return;
        }

        let mut replacements: Vec<Option<Vec<ProofStep>>> = std::iter::repeat_with(|| None)
            .take(proof.steps.len())
            .collect();
        let mut budget = EqBudget::new(EQ_WORK);
        for (index, packed, goals) in candidates {
            let Some((fragment, source_plan)) = self.plan_negated_conjunct_fragment(
                packed,
                &goals,
                &raw_roots,
                &definitions,
                &mut budget,
            ) else {
                continue;
            };
            if self.bridge_fragment_is_unrenderable(
                &fragment,
                packed,
                self.last_proof_term_overrides.as_ref(),
            ) {
                if let Some(candidate) = self.plan_direct_negated_conjunct_refutation(source_plan) {
                    *proof = candidate;
                    return;
                }
                continue;
            }
            replacements[index] = Some(fragment);
        }
        if replacements.iter().all(Option::is_none) {
            return;
        }
        let _ = self.commit_bridge_fragments(proof, replacements);
    }

    fn authenticated_raw_roots_for_negated_conjunct_bridge(&self) -> Vec<TermId> {
        if self.last_proof_raw_original_assertions.len() > MAX_AUTHORED_ROOTS
            || self.last_proof_rebuild_originals.len() > MAX_AUTHORED_ROOTS * 3
        {
            return Vec::new();
        }
        let mut roots = Vec::new();
        for &root in &self.last_proof_raw_original_assertions {
            if self.last_proof_rebuild_originals.contains(&root) && !roots.contains(&root) {
                roots.push(root);
            }
        }
        roots
    }

    fn plan_negated_conjunct_fragment(
        &mut self,
        packed: TermId,
        goals: &[TermId],
        raw_roots: &[TermId],
        definitions: &[Definition],
        budget: &mut EqBudget,
    ) -> Option<(Vec<ProofStep>, SourcePlan)> {
        if goals.len() < 2 || goals.len() >= MAX_CONJUNCTS || has_duplicates(goals) {
            return None;
        }
        for &root in raw_roots {
            let Some(conjuncts) = raw_negated_conjuncts(&self.ctx.terms, root) else {
                continue;
            };
            if !matches!(conjuncts.len(), count if count == goals.len() || count == goals.len() + 1)
                || conjuncts.len() > MAX_CONJUNCTS
            {
                continue;
            }
            let Some(plan) = self.plan_source_mapping(root, &conjuncts, goals, definitions, budget)
            else {
                continue;
            };
            if !emitted_steps_admitted(
                plan.fragment_step_upper_bound(goals.len()),
                MAX_FRAGMENT_STEPS,
            ) {
                continue;
            }
            let derivation = self.emit_source_plan(&plan, packed, goals)?;
            if derivation.steps.len() > MAX_FRAGMENT_STEPS {
                continue;
            }
            let closed = ay_proof::close_congruence_derivation(&mut self.ctx.terms, &derivation);
            if ay_proof::check_proof_strict(&closed, &self.ctx.terms).is_ok() {
                return Some((derivation.steps, plan));
            }
        }
        None
    }

    fn plan_source_mapping(
        &mut self,
        root: TermId,
        conjuncts: &[TermId],
        goals: &[TermId],
        definitions: &[Definition],
        budget: &mut EqBudget,
    ) -> Option<SourcePlan> {
        let mut candidates = Vec::with_capacity(goals.len());
        let mut weakened_goals = Vec::new();
        let mut reserved_sources = Vec::new();
        for &goal in goals {
            let mut goal_candidates = Vec::new();
            for (source_index, &source) in conjuncts.iter().enumerate() {
                if reserved_sources.contains(&source_index) {
                    continue;
                }
                if let Some(bridge) =
                    self.plan_literal_bridge(source_index, source, goal, definitions, budget)
                {
                    goal_candidates.push(bridge);
                    // This focused lane keeps only the first exact authority.
                    // If those choices do not form a perfect matching, the
                    // checked matching gate below declines rather than
                    // widening polynomial search on hostile clauses.
                    reserved_sources.push(source_index);
                    break;
                }
            }
            if goal_candidates.is_empty() {
                weakened_goals.push(goal);
            } else {
                candidates.push(goal_candidates);
            }
        }
        if candidates.is_empty() || weakened_goals.len() > MAX_WEAKENED_GOALS {
            return None;
        }
        let source_negatives = conjuncts
            .iter()
            .map(|&conjunct| self.ctx.terms.mk_not_raw(conjunct))
            .collect::<Vec<_>>();
        let discharge_count = conjuncts.len().checked_sub(candidates.len())?;
        if discharge_count > MAX_DISCHARGED_CONJUNCTS {
            return None;
        }
        // Plan every independently provable equality once, then reserve the
        // exact number of source conjuncts that cannot participate in the
        // non-empty target mapping.  Dummy discharge rows share one perfect
        // matching with the real goal rows, so every source is accounted for
        // and only exact equality plans can occupy the dummy rows. Zero-edge
        // target literals are added later by the standard weakening rule.
        let mut dischargeable = Vec::new();
        for (discharged_index, &conjunct) in conjuncts.iter().enumerate() {
            let Some(relation) = decode_relation(&self.ctx.terms, conjunct) else {
                continue;
            };
            if relation.kind != RelationKind::Eq {
                continue;
            }
            let Some(discharged_equality) = plan_numeric_equality(
                &mut self.ctx.terms,
                relation.semantic_args[0],
                relation.semantic_args[1],
                definitions,
                budget,
            ) else {
                continue;
            };
            if discharged_equality.equality() != conjunct {
                continue;
            }
            dischargeable.push((discharged_index, discharged_equality));
        }
        let dischargeable_indices: Vec<usize> =
            dischargeable.iter().map(|(index, _)| *index).collect();
        let (bridges, discharged_indices) = choose_sources_with_discharges(
            candidates,
            &dischargeable_indices,
            conjuncts.len(),
            discharge_count,
        )?;
        let discharged = discharged_indices
            .into_iter()
            .map(|index| {
                let position = dischargeable
                    .iter()
                    .position(|(candidate, _)| *candidate == index)?;
                Some(dischargeable.swap_remove(position))
            })
            .collect::<Option<Vec<_>>>()?;
        Some(SourcePlan {
            root,
            source_negatives,
            bridges,
            discharged,
            weakened_goals,
        })
    }

    fn plan_literal_bridge(
        &mut self,
        source_index: usize,
        source_atom: TermId,
        goal: TermId,
        definitions: &[Definition],
        budget: &mut EqBudget,
    ) -> Option<LiteralBridge> {
        let TermData::Not(goal_atom) = self.ctx.terms.get(goal) else {
            return None;
        };
        let goal_atom = *goal_atom;
        let source = decode_relation(&self.ctx.terms, source_atom)?;
        let target = decode_relation(&self.ctx.terms, goal_atom)?;
        if source.kind != target.kind {
            return None;
        }
        let source_negative = self.ctx.terms.mk_not_raw(source_atom);
        if source_negative == goal {
            return Some(LiteralBridge {
                source_index,
                source_atom,
                source_negative,
                goal,
                equalities: Vec::new(),
                authority: BridgeAuthority::Direct,
            });
        }
        let mut equalities = Vec::new();
        let same_symbol = source.symbol == target.symbol;
        for (&left, &right) in source.semantic_args.iter().zip(target.semantic_args.iter()) {
            // Carcara's `eq_congruent_pred` wire rule requires one equality
            // hypothesis for every predicate argument, including positions
            // that are already syntactically identical.  Keep the shorter
            // premise list only for the arithmetic/Farkas fallback, where a
            // reflexive negative equality would be a redundant literal.
            if same_symbol || left != right {
                equalities.push(plan_numeric_equality(
                    &mut self.ctx.terms,
                    left,
                    right,
                    definitions,
                    budget,
                )?);
            }
        }
        let mut clause: Vec<TermId> = equalities
            .iter()
            .map(|plan| self.ctx.terms.mk_not_raw(plan.equality()))
            .collect();
        clause.push(goal);
        clause.push(source_atom);
        let authority =
            if same_symbol && ay_proof::recognize_euf_congruent_pred(&self.ctx.terms, &clause) {
                BridgeAuthority::Euf { clause }
            } else {
                if !budget.spend_bridge_farkas_attempt() {
                    return None;
                }
                let mut annotation = None;
                let mut kind = TheoryLemmaKind::Generic;
                if !super::super::proof_farkas::try_lra_farkas_reconstruction(
                    &self.ctx.terms,
                    &clause,
                    &mut annotation,
                    &mut kind,
                ) || kind.is_trust()
                {
                    return None;
                }
                let annotation = annotation?;
                if !ay_proof::la_generic_farkas_lowering_supported(
                    &self.ctx.terms,
                    &clause,
                    &annotation,
                    self.last_proof_term_overrides.as_ref(),
                ) {
                    return None;
                }
                BridgeAuthority::Farkas {
                    clause,
                    annotation,
                    kind,
                }
            };
        Some(LiteralBridge {
            source_index,
            source_atom,
            source_negative,
            goal,
            equalities,
            authority,
        })
    }

    fn emit_source_plan(
        &mut self,
        plan: &SourcePlan,
        packed: TermId,
        goals: &[TermId],
    ) -> Option<CongruenceDerivation> {
        let mut proof = Proof::new();
        let root = proof.add_assume(plan.root, None);
        let mut assumptions = DetHashMap::default();
        assumptions.insert(plan.root, root);
        let mut running = plan.source_negatives.clone();
        let mut current =
            proof.add_rule_step(AletheRule::NotAnd, running.clone(), vec![root], Vec::new());
        for bridge in &plan.bridges {
            if matches!(&bridge.authority, BridgeAuthority::Direct) {
                continue;
            }
            let bridge_unit = emit_literal_bridge(&mut proof, bridge, &mut assumptions)?;
            let position = running
                .iter()
                .position(|&literal| literal == bridge.source_negative)?;
            let _ = running.remove(position);
            if !running.contains(&bridge.goal) {
                running.push(bridge.goal);
            }
            current =
                proof.add_resolution(running.clone(), bridge.source_atom, current, bridge_unit);
        }
        for (discharged_index, discharged_equality) in &plan.discharged {
            let discharged = emit_eq_plan(&mut proof, discharged_equality, &mut assumptions)?;
            let discharged_atom = discharged_equality.equality();
            let position = running
                .iter()
                .position(|&literal| literal == plan.source_negatives[*discharged_index])?;
            let _ = running.remove(position);
            current = proof.add_resolution(running.clone(), discharged_atom, current, discharged);
        }
        if !plan.weakened_goals.is_empty() {
            running.extend(plan.weakened_goals.iter().copied());
            current = proof.add_rule_step(
                AletheRule::Weakening,
                running.clone(),
                vec![current],
                Vec::new(),
            );
        }
        if !same_unique_set(&running, goals) {
            return None;
        }
        if running != goals {
            let _ = proof.add_rule_step(
                AletheRule::Reordering,
                goals.to_vec(),
                vec![current],
                Vec::new(),
            );
            running = goals.to_vec();
        }
        let derivation = CongruenceDerivation {
            steps: proof.steps,
            clause: running,
        };
        self.repack_derivation(derivation, packed)
    }
}

#[cfg(test)]
#[path = "authored_negated_conjunct_bridge/tests.rs"]
mod tests;
