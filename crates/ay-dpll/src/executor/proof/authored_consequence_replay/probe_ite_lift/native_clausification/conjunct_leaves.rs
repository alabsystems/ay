// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact positive-conjunction projections from the immutable native sources.
//! An extracted child is a derived unit, never a new problem assumption.

use super::*;

pub(super) type Edge = (TermId, u32, TermId);

#[cfg(test)]
pub(super) fn find_path(
    exec: &Executor,
    current: TermId,
    target: TermId,
    path: &mut Vec<Edge>,
    remaining: &mut usize,
    budget: &RepairBudget,
) -> Option<bool> {
    *remaining = remaining.checked_sub(1)?;
    if !budget.pay(1, 0)
        || path.len() > MAX_NATIVE_DEPTH
        || exec.ctx.terms.entry_stamp(current).is_none()
        || exec.ctx.terms.sort(current) != &Sort::Bool
    {
        return None;
    }
    if current == target {
        return Some(true);
    }
    let TermData::App(Symbol::Named(name), children) = exec.ctx.terms.get(current) else {
        return Some(false);
    };
    if name != "and" || children.is_empty() {
        return Some(false);
    }
    if children.len() > *remaining || !budget.pay(children.len(), 0) {
        return None;
    }
    // AndPos is a Boolean rule. Validate every immediate child before using
    // the parent, including the children outside the selected path. Earlier
    // IDs also rule out forged cycles before recursive descent.
    if children.iter().any(|&child| {
        child.0 >= current.0
            || exec.ctx.terms.entry_stamp(child).is_none()
            || exec.ctx.terms.sort(child) != &Sort::Bool
    }) {
        return None;
    }
    for (position, &child) in children.iter().enumerate() {
        if path.len() == MAX_NATIVE_DEPTH {
            return None;
        }
        path.push((current, u32::try_from(position).ok()?, child));
        if find_path(exec, child, target, path, remaining, budget)? {
            return Some(true);
        }
        path.pop();
    }
    Some(false)
}

/// Index only the proof's actual unit-Trust targets in one source traversal.
/// Repeated physical edges are still paid, but a nonconjunct target no longer
/// re-walks every wide source independently under the same occurrence bound.
fn index_paths(
    exec: &Executor,
    root: TermId,
    current: TermId,
    targets: &mut [(TermId, Option<LiftPlan>)],
    path: &mut Vec<Edge>,
    remaining: &mut usize,
    budget: &RepairBudget,
) -> Option<()> {
    *remaining = remaining.checked_sub(1)?;
    let terms = &exec.ctx.terms;
    if !budget.pay(1, 0)
        || path.len() > MAX_NATIVE_DEPTH
        || terms.entry_stamp(current).is_none()
        || terms.sort(current) != &Sort::Bool
    {
        return None;
    }
    if !budget.pay(targets.len(), 0) {
        return None;
    }
    if let Some((_, slot)) = targets.iter_mut().find(|(target, _)| *target == current) {
        if slot.is_none() {
            if !budget.pay(
                path.len(),
                path.len().checked_mul(std::mem::size_of::<Edge>())?,
            ) {
                return None;
            }
            *slot = Some(LiftPlan {
                root,
                path: path.clone(),
                source: current,
            });
        }
    }
    let TermData::App(Symbol::Named(name), children) = terms.get(current) else {
        return Some(());
    };
    if name != "and" || children.is_empty() {
        return Some(());
    }
    if children.len() > *remaining || !budget.pay(children.len(), 0) {
        return None;
    }
    if children.iter().any(|&child| {
        child.0 >= current.0
            || terms.entry_stamp(child).is_none()
            || terms.sort(child) != &Sort::Bool
    }) {
        return None;
    }
    for (position, &child) in children.iter().enumerate() {
        if path.len() == MAX_NATIVE_DEPTH {
            return None;
        }
        path.push((current, u32::try_from(position).ok()?, child));
        index_paths(exec, root, child, targets, path, remaining, budget)?;
        path.pop();
    }
    Some(())
}

impl Executor {
    /// Stage exact AndPos/resolution derivations in the caller's candidate.
    /// The caller retains the full source/epoch/arena/strict commit gate.
    pub(super) fn stage_native_conjunct_leaves(
        &mut self,
        proof: &mut Proof,
        roots: &[TermId],
        budget: &RepairBudget,
    ) -> Option<usize> {
        let mut targets = Vec::new();
        for step in &proof.steps {
            if !budget.pay(1, 0) {
                return None;
            }
            if let ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                args,
            } = step
            {
                if clause.len() == 1 && premises.is_empty() && args.is_empty() {
                    if !budget.pay(targets.len(), 0) {
                        return None;
                    }
                    if !targets.iter().any(|(target, _)| *target == clause[0]) {
                        budget.reserve(&mut targets, 1)?;
                        targets.push((clause[0], None));
                    }
                }
            }
        }
        if targets.is_empty() {
            return Some(0);
        }
        let mut remaining = MAX_NATIVE_TERM_OCCURRENCES;
        let mut path = Vec::new();
        budget.reserve(&mut path, MAX_NATIVE_DEPTH)?;
        for &root in roots {
            index_paths(
                self,
                root,
                root,
                &mut targets,
                &mut path,
                &mut remaining,
                budget,
            )?;
        }
        let mut remap = Vec::new();
        budget.reserve(&mut remap, proof.steps.len())?;
        let original = std::mem::take(&mut proof.steps);
        let mut derived = 0;
        for step in original {
            if !budget.pay(1, 0) {
                return None;
            }
            let target = match &step {
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    args,
                } if clause.len() == 1 && premises.is_empty() && args.is_empty() => Some(clause[0]),
                _ => None,
            };
            let mut replacement = None;
            if let Some(target) = target {
                if !budget.pay(targets.len(), 0) {
                    return None;
                }
                if let Some((_, Some(plan))) = targets.iter().find(|(term, _)| *term == target) {
                    // Reserve all emitted owned clauses/argument vectors
                    // before the first assume or term is constructed.
                    if !budget.pay(
                        plan.path.len().checked_mul(8)?.checked_add(1)?,
                        plan.path.len().checked_mul(512)?.checked_add(256)?,
                    ) {
                        return None;
                    }
                    let mut unit = proof.add_assume(plan.root, None);
                    for &(parent, position, child) in &plan.path {
                        let not_parent = self.ctx.terms.mk_not_raw(parent);
                        let projection = proof.add_rule_step(
                            AletheRule::AndPos(position),
                            vec![not_parent, child],
                            Vec::new(),
                            vec![parent],
                        );
                        unit = proof.add_resolution(vec![child], parent, projection, unit);
                    }
                    replay_note(|| {
                        format!(
                            "native-conjunct-clauses: original={} target={} depth={}",
                            plan.root.0,
                            target.0,
                            plan.path.len()
                        )
                    });
                    replacement = Some(unit);
                    derived += 1;
                }
            }
            let unit = match replacement {
                Some(unit) => unit,
                None => {
                    let step = crate::executor::proof::remap_step_premises(step, &remap);
                    proof.add_step(step)
                }
            };
            remap.push(unit);
        }
        if !budget.pay(proof.named_steps.capacity().checked_mul(2)?, 0) {
            return None;
        }
        proof.named_steps.retain(|_, id| {
            let Some(&new) = remap.get(id.0 as usize) else {
                return false;
            };
            *id = new;
            true
        });
        budget.pay(0, 0).then_some(derived)
    }
}
