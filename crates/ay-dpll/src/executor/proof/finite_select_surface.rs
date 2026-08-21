// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checkable Alethe surface for Bool-indexed finite select expansion.
//!
//! The native `ArrayFiniteSelectExpansion` checker accepts the exact theorem
//!
//! ```text
//! ite p (select a true = select a p) (select a false = select a p)
//! ```
//!
//! but the pinned Alethe dialect has no monolithic finite-domain array rule.
//! This module lowers that exact normalized Bool shape to primitive
//! `eq_reflexive`, `eq_congruent`, `equiv_neg*`, `ite_neg*`, and `resolution`
//! steps.  The whole rebuilt proof is checked atomically before installation;
//! every wider finite-carrier or surface-override shape remains fail-closed.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{AletheRule, Constant, Proof, ProofId, ProofStep, Sort, Symbol, TermData, TermId};

use super::super::proof::remap_step_premises;
use super::super::proof_trust_surgery_provenance::ProvenanceSurfaceAudit;
use super::super::Executor;

/// Defensive output bound shared in spirit with the other proof promotions.
const MAX_REBUILT_STEPS: usize = 262_144;
const STEPS_PER_REPLACEMENT: usize = 19;
const MAX_SURFACE_CONE_TERMS: usize = 16_384;
const MAX_SURFACE_CONE_WORK: usize = 100_000;
const MAX_SURFACE_RENDER_WORK: u64 = 8 * 1024 * 1024;

#[derive(Clone, Copy)]
struct BranchPlan {
    equality: TermId,
    left_array: TermId,
    right_array: TermId,
    left_index: TermId,
    right_index: TermId,
    point: bool,
}

#[derive(Clone, Copy)]
struct SelectPlan {
    goal: TermId,
    condition: TermId,
    then_branch: BranchPlan,
    else_branch: BranchPlan,
}

fn decode_equality(terms: &ay_core::TermStore, term: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(Symbol::Named(name), arguments) = terms.get(term) else {
        return None;
    };
    (name == "=" && arguments.len() == 2).then_some((arguments[0], arguments[1]))
}

fn decode_select(terms: &ay_core::TermStore, term: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(Symbol::Named(name), arguments) = terms.get(term) else {
        return None;
    };
    (name == "select" && arguments.len() == 2).then_some((arguments[0], arguments[1]))
}

fn bool_constant(terms: &ay_core::TermStore, term: TermId) -> Option<bool> {
    match terms.get(term) {
        TermData::Const(Constant::Bool(value)) => Some(*value),
        _ => None,
    }
}

fn branch_plan(
    terms: &ay_core::TermStore,
    equality: TermId,
    condition: TermId,
    expected_point: bool,
) -> Option<BranchPlan> {
    let (left, right) = decode_equality(terms, equality)?;
    let (left_array, left_index) = decode_select(terms, left)?;
    let (right_array, right_index) = decode_select(terms, right)?;
    if left_array != right_array || terms.sort(left) != terms.sort(right) {
        return None;
    }
    let point = if left_index == condition {
        bool_constant(terms, right_index)?
    } else if right_index == condition {
        bool_constant(terms, left_index)?
    } else {
        return None;
    };
    (point == expected_point).then_some(BranchPlan {
        equality,
        left_array,
        right_array,
        left_index,
        right_index,
        point,
    })
}

fn select_plan(terms: &ay_core::TermStore, clause: &[TermId]) -> Option<SelectPlan> {
    let [goal] = clause else {
        return None;
    };
    if !ay_proof::recognize_array_finite_select_expansion(terms, clause) {
        return None;
    }
    let TermData::Ite(condition, then_equality, else_equality) = terms.get(*goal) else {
        return None;
    };
    if terms.sort(*condition) != &Sort::Bool {
        return None;
    }
    Some(SelectPlan {
        goal: *goal,
        condition: *condition,
        then_branch: branch_plan(terms, *then_equality, *condition, true)?,
        else_branch: branch_plan(terms, *else_equality, *condition, false)?,
    })
}

fn cone_intersects_surface_hazard(
    terms: &ay_core::TermStore,
    root: TermId,
    hazards: &HashSet<TermId>,
    work: &mut usize,
) -> bool {
    let mut pending = vec![root];
    let mut seen = HashSet::default();
    while let Some(term) = pending.pop() {
        *work = work.saturating_add(1);
        if *work > MAX_SURFACE_CONE_WORK {
            return true;
        }
        if hazards.contains(&term) {
            return true;
        }
        if !seen.insert(term) {
            continue;
        }
        if seen.len() > MAX_SURFACE_CONE_TERMS {
            return true;
        }
        pending.extend(terms.children(term));
    }
    false
}

fn collect_surface_hazards(
    terms: &ay_core::TermStore,
    overrides: Option<&HashMap<TermId, String>>,
) -> Option<HashSet<TermId>> {
    let Some(overrides) = overrides else {
        return Some(HashSet::default());
    };
    if !ProvenanceSurfaceAudit::default().active_map_is_bounded(overrides) {
        return None;
    }

    let mut roots: Vec<TermId> = overrides.keys().copied().collect();
    roots.sort_unstable();
    let canonical = ay_proof::format_terms_alethe_with_overrides_bounded(
        terms,
        &roots,
        &HashMap::default(),
        MAX_SURFACE_RENDER_WORK,
    )
    .ok()?;
    Some(
        overrides
            .iter()
            .filter_map(|(&term, spelling)| {
                canonical
                    .get(&term)
                    .is_none_or(|canonical| spelling != canonical)
                    .then_some(term)
            })
            .collect(),
    )
}

impl Executor {
    fn emit_bool_select_branch(
        &mut self,
        proof: &mut Proof,
        condition: TermId,
        branch: BranchPlan,
        hazards: &HashSet<TermId>,
    ) -> Option<(ProofId, TermId)> {
        let terms = &mut self.ctx.terms;
        let array_equality = terms.mk_app(
            Symbol::named("="),
            [branch.left_array, branch.right_array],
            Sort::Bool,
        );
        let index_equality = terms.mk_app(
            Symbol::named("="),
            [branch.left_index, branch.right_index],
            Sort::Bool,
        );
        let not_array_equality = terms.mk_not_raw(array_equality);
        let not_index_equality = terms.mk_not_raw(index_equality);
        if [
            array_equality,
            index_equality,
            not_array_equality,
            not_index_equality,
        ]
        .iter()
        .any(|term| hazards.contains(term))
        {
            return None;
        }

        let array_reflexive = proof.add_rule_step(
            AletheRule::EqReflexive,
            vec![array_equality],
            Vec::new(),
            Vec::new(),
        );
        let congruence = proof.add_rule_step(
            AletheRule::EqCongruent,
            vec![not_array_equality, not_index_equality, branch.equality],
            Vec::new(),
            Vec::new(),
        );
        let congruence = proof.add_resolution(
            vec![not_index_equality, branch.equality],
            array_equality,
            congruence,
            array_reflexive,
        );

        let (equivalence, constant_axiom, constant, guard) = if branch.point {
            let not_left = terms.mk_not_raw(branch.left_index);
            let not_right = terms.mk_not_raw(branch.right_index);
            if hazards.contains(&not_left) || hazards.contains(&not_right) {
                return None;
            }
            let equivalence = proof.add_rule_step(
                AletheRule::EquivNeg1,
                vec![index_equality, not_left, not_right],
                Vec::new(),
                Vec::new(),
            );
            let truth = terms.true_term();
            let axiom = proof.add_rule_step(AletheRule::True, vec![truth], Vec::new(), Vec::new());
            (equivalence, axiom, truth, terms.mk_not_raw(condition))
        } else {
            let equivalence = proof.add_rule_step(
                AletheRule::EquivNeg2,
                vec![index_equality, branch.left_index, branch.right_index],
                Vec::new(),
                Vec::new(),
            );
            let falsity = terms.false_term();
            let not_false = terms.mk_not_raw(falsity);
            if hazards.contains(&not_false) {
                return None;
            }
            let axiom =
                proof.add_rule_step(AletheRule::False, vec![not_false], Vec::new(), Vec::new());
            (equivalence, axiom, falsity, condition)
        };
        let index_implication = proof.add_resolution(
            vec![index_equality, guard],
            constant,
            equivalence,
            constant_axiom,
        );
        let branch_implication = proof.add_resolution(
            vec![guard, branch.equality],
            index_equality,
            congruence,
            index_implication,
        );
        Some((branch_implication, guard))
    }

    fn emit_bool_finite_select_plan(
        &mut self,
        proof: &mut Proof,
        plan: SelectPlan,
        hazards: &HashSet<TermId>,
    ) -> Option<ProofId> {
        let (then_implication, not_condition) =
            self.emit_bool_select_branch(proof, plan.condition, plan.then_branch, hazards)?;
        let (else_implication, condition) =
            self.emit_bool_select_branch(proof, plan.condition, plan.else_branch, hazards)?;
        if condition != plan.condition {
            return None;
        }

        let terms = &mut self.ctx.terms;
        let not_then = terms.mk_not_raw(plan.then_branch.equality);
        let not_else = terms.mk_not_raw(plan.else_branch.equality);
        if hazards.contains(&not_then) || hazards.contains(&not_else) {
            return None;
        }
        let then_link = proof.add_rule_step(
            AletheRule::IteNeg2,
            vec![plan.goal, not_condition, not_then],
            Vec::new(),
            Vec::new(),
        );
        let then_goal = proof.add_resolution(
            vec![plan.goal, not_condition],
            plan.then_branch.equality,
            then_link,
            then_implication,
        );
        let else_link = proof.add_rule_step(
            AletheRule::IteNeg1,
            vec![plan.goal, condition, not_else],
            Vec::new(),
            Vec::new(),
        );
        let else_goal = proof.add_resolution(
            vec![plan.goal, condition],
            plan.else_branch.equality,
            else_link,
            else_implication,
        );
        Some(proof.add_resolution(vec![plan.goal], condition, then_goal, else_goal))
    }

    /// Replace exact Bool finite-select theory units with primitive proof
    /// steps whose native and Alethe checkers share the same semantics.
    pub(super) fn promote_bool_finite_select_expansion_surface(&mut self, proof: &mut Proof) {
        if proof.steps.len() > MAX_REBUILT_STEPS {
            return;
        }
        // Source assumptions commonly carry orientation-preserving render
        // overrides. They are copied byte-for-byte and do not affect this
        // replacement. Only a noncanonical override inside the emitted
        // finite-select operand cone can change one of its positional roles.
        let Some(hazards) =
            collect_surface_hazards(&self.ctx.terms, self.last_proof_term_overrides.as_ref())
        else {
            return;
        };

        let mut surface_work = 0usize;
        let plans: Vec<Option<SelectPlan>> = proof
            .steps
            .iter()
            .map(|step| match step {
                ProofStep::TheoryLemma {
                    clause,
                    kind: ay_core::TheoryLemmaKind::ArrayFiniteSelectExpansion,
                    ..
                } => select_plan(&self.ctx.terms, clause).filter(|plan| {
                    !cone_intersects_surface_hazard(
                        &self.ctx.terms,
                        plan.goal,
                        &hazards,
                        &mut surface_work,
                    )
                }),
                _ => None,
            })
            .collect();
        let replacements = plans.iter().filter(|plan| plan.is_some()).count();
        if replacements == 0 {
            return;
        }
        if proof
            .steps
            .len()
            .checked_add(replacements.saturating_mul(STEPS_PER_REPLACEMENT))
            .is_none_or(|steps| steps > MAX_REBUILT_STEPS)
        {
            return;
        }

        let mut rebuilt = Proof::new();
        let mut remap = Vec::with_capacity(proof.steps.len());
        for (step, plan) in proof.steps.iter().cloned().zip(plans) {
            if let Some(plan) = plan {
                let Some(replacement) =
                    self.emit_bool_finite_select_plan(&mut rebuilt, plan, &hazards)
                else {
                    return;
                };
                remap.push(replacement);
            } else {
                remap.push(rebuilt.add_step(remap_step_premises(step, &remap)));
            }
        }

        let mut named_steps = proof.named_steps.clone();
        named_steps.retain(|_, id| {
            let Some(replacement) = remap.get(id.0 as usize) else {
                return false;
            };
            *id = *replacement;
            true
        });
        rebuilt.named_steps = named_steps;

        if self
            .check_proof_strict_derivation_with_datatypes(&rebuilt)
            .is_ok()
        {
            *proof = rebuilt;
        }
    }
}

#[cfg(test)]
#[path = "finite_select_surface_tests.rs"]
mod tests;
