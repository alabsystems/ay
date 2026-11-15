// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Emit only checked source projections and the chosen simple equality path.

use super::*;

pub(super) fn build(
    terms: &mut TermStore,
    plan: &shape::Plan,
    goal: &shape::Goal,
    path: &[usize],
    budget: &mut Budget<'_>,
) -> Option<(Proof, ProofId)> {
    if path.is_empty() || path.len() > MAX_EQUALITIES {
        return None;
    }
    let mut proof = Proof::new();
    let mut units = Vec::new();
    let mut negative_equalities = Vec::new();
    for &edge_index in path {
        let edge = plan.edges.get(edge_index)?;
        let unit = leaf(terms, plan, edge.node, &mut proof, budget)?;
        budget.push(&mut units, unit)?;
        budget.charge(1, 128)?;
        let negative = terms.mk_not_raw(edge.equality);
        budget.push(&mut negative_equalities, negative)?;
    }
    let disequality = leaf(terms, plan, goal.node, &mut proof, budget)?;
    let mut clause = budget.copy(&negative_equalities)?;
    budget.push(&mut clause, goal.equality)?;
    let mut current = rule(
        &mut proof,
        AletheRule::EqTransitive,
        &clause,
        &[],
        &[],
        budget,
    )?;
    for (position, (&edge_index, &unit)) in path.iter().zip(&units).enumerate() {
        let mut residual = budget.copy(&negative_equalities[position + 1..])?;
        budget.push(&mut residual, goal.equality)?;
        current = resolution(
            &mut proof,
            &residual,
            plan.edges.get(edge_index)?.equality,
            current,
            unit,
            budget,
        )?;
    }
    let conclusion = resolution(&mut proof, &[], goal.equality, current, disequality, budget)?;
    Some((proof, conclusion))
}

fn leaf(
    terms: &mut TermStore,
    plan: &shape::Plan,
    index: usize,
    proof: &mut Proof,
    budget: &mut Budget<'_>,
) -> Option<ProofId> {
    let node = plan.nodes.get(index)?;
    let source = plan.sources.get(node.source)?;
    let mut path = Vec::new();
    let mut cursor = index;
    while let Some((parent, position)) = plan.nodes.get(cursor)?.parent {
        if parent >= cursor || path.len() == MAX_DEPTH {
            return None;
        }
        budget.push(
            &mut path,
            (
                plan.nodes.get(parent)?.term,
                position,
                plan.nodes.get(cursor)?.term,
            ),
        )?;
        cursor = parent;
    }
    if plan.nodes.get(cursor)?.term != source.body {
        return None;
    }
    let mut current = assume(proof, source.root, budget)?;
    if let Some(activation) = source.activation {
        let TermData::App(Symbol::Named(name), args) = terms.get(source.root) else {
            return None;
        };
        if name != "or" || args.len() != 2 {
            return None;
        }
        current = rule(proof, AletheRule::Or, args, &[current], &[], budget)?;
        let guard = assume(proof, activation, budget)?;
        current = resolution(proof, &[source.body], activation, current, guard, budget)?;
    }
    for &(parent, position, child) in path.iter().rev() {
        budget.charge(1, 128)?;
        let not_parent = terms.mk_not_raw(parent);
        let projected = rule(
            proof,
            AletheRule::AndPos(position),
            &[not_parent, child],
            &[],
            &[parent],
            budget,
        )?;
        current = resolution(proof, &[child], parent, projected, current, budget)?;
    }
    Some(current)
}

fn slot(proof: &mut Proof, budget: &mut Budget<'_>) -> Option<()> {
    if proof.steps.len() >= MAX_PROOF_STEPS {
        return None;
    }
    budget.charge(1, 0)?;
    budget.reserve(&mut proof.steps, 1)
}

fn assume(proof: &mut Proof, term: TermId, budget: &mut Budget<'_>) -> Option<ProofId> {
    slot(proof, budget)?;
    Some(proof.add_assume(term, None))
}

fn rule(
    proof: &mut Proof,
    rule: AletheRule,
    clause: &[TermId],
    premises: &[ProofId],
    args: &[TermId],
    budget: &mut Budget<'_>,
) -> Option<ProofId> {
    let clause = budget.copy(clause)?;
    let premises = budget.copy(premises)?;
    let args = budget.copy(args)?;
    slot(proof, budget)?;
    Some(proof.add_rule_step(rule, clause, premises, args))
}

fn resolution(
    proof: &mut Proof,
    clause: &[TermId],
    pivot: TermId,
    left: ProofId,
    right: ProofId,
    budget: &mut Budget<'_>,
) -> Option<ProofId> {
    let clause = budget.copy(clause)?;
    slot(proof, budget)?;
    Some(proof.add_resolution(clause, pivot, left, right))
}
