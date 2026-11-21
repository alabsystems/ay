// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrow the final refutation cone before copying owned proof payload.
//! The full original query remains the authority window throughout.

use super::*;
use crate::executor::proof::rule_owned_payload::{rule_owned_payload, RuleOwnedPayload};
use std::mem::size_of;

#[derive(Default)]
struct Totals {
    assumes: usize,
    vectors: usize,
    names: usize,
    annotations: usize,
    rule_text: usize,
    theory_text: usize,
}

fn metadata_owner(rule: &AletheRule) -> bool {
    matches!(
        rule,
        AletheRule::FreshDefEq
            | AletheRule::FreshDefBound
            | AletheRule::Skolem
            | AletheRule::Bind
            | AletheRule::Subproof
            | AletheRule::QntNegExists
            | AletheRule::ArrayExtDiffIntro
    )
}

fn coefficients(step: &ProofStep) -> Option<usize> {
    let ProofStep::TheoryLemma { farkas, lia, .. } = step else {
        return Some(0);
    };
    let mut count = farkas.as_ref().map_or(0, |hint| hint.coefficients.len());
    match lia {
        Some(ay_core::LiaAnnotation::CuttingPlane(hint)) => {
            count = count.checked_add(hint.farkas.coefficients.len())?;
        }
        Some(
            ay_core::LiaAnnotation::BoundsGap
            | ay_core::LiaAnnotation::Divisibility
            | ay_core::LiaAnnotation::LinearIdentity,
        )
        | None => {}
        _ => return None,
    }
    Some(count)
}

fn term_slice(exec: &Executor, values: &[TermId], budget: &RepairBudget) -> Option<()> {
    budget.pay(values.len(), 0).then_some(())?;
    values
        .iter()
        .all(|&term| exec.ctx.terms.entry_stamp(term).is_some())
        .then_some(())
}

fn validate_row(
    exec: &Executor,
    proof: &Proof,
    index: usize,
    roots: &[TermId],
    totals: &mut Totals,
    budget: &RepairBudget,
) -> Option<bool> {
    budget.pay(1, 0).then_some(())?;
    let valid_premise = |id: ay_core::ProofId| (id.0 as usize) < index;
    let owner = match &proof.steps[index] {
        ProofStep::Assume(term) => {
            // Even unused assumptions are authenticated before projection.
            budget.pay(roots.len().checked_add(1)?, 0).then_some(())?;
            if exec.ctx.terms.entry_stamp(*term).is_none() || !roots.contains(term) {
                replay_note(|| format!("native-proof-copy: foreign assume row={index}"));
                return None;
            }
            totals.assumes = totals.assumes.saturating_add(1);
            false
        }
        ProofStep::Resolution {
            clause,
            pivot,
            clause1,
            clause2,
        } => {
            term_slice(exec, clause, budget)?;
            if exec.ctx.terms.entry_stamp(*pivot).is_none()
                || !valid_premise(*clause1)
                || !valid_premise(*clause2)
            {
                return None;
            }
            totals.vectors = totals.vectors.saturating_add(clause.len());
            false
        }
        ProofStep::Step {
            rule,
            clause,
            premises,
            args,
        } => {
            // A future typed rule may own lexical or identity metadata.
            match rule_owned_payload(rule) {
                Some(RuleOwnedPayload::Text(name)) => {
                    totals.rule_text = totals.rule_text.saturating_add(name.len());
                }
                Some(RuleOwnedPayload::Fixed) => {}
                None => {
                    replay_note(|| format!("native-proof-copy: unknown rule metadata row={index}"));
                    return None;
                }
            }
            term_slice(exec, clause, budget)?;
            term_slice(exec, args, budget)?;
            budget.pay(premises.len(), 0).then_some(())?;
            if !premises.iter().copied().all(valid_premise) {
                return None;
            }
            totals.vectors = totals
                .vectors
                .saturating_add(clause.len())
                .saturating_add(premises.len())
                .saturating_add(args.len());
            metadata_owner(rule)
        }
        ProofStep::TheoryLemma { theory, clause, .. } => {
            term_slice(exec, clause, budget)?;
            totals.vectors = totals.vectors.saturating_add(clause.len());
            totals.theory_text = totals.theory_text.saturating_add(theory.len());
            totals.annotations = totals
                .annotations
                .saturating_add(coefficients(&proof.steps[index])?);
            false
        }
        // An anchor scopes a lexical interval, not merely a dependency edge.
        // Preserve the existing refusal instead of guessing a projected scope.
        ProofStep::Anchor { .. } => {
            replay_note(|| format!("native-proof-copy: anchor refused row={index}"));
            return None;
        }
        _ => {
            replay_note(|| format!("native-proof-copy: unsupported row metadata row={index}"));
            return None;
        }
    };
    Some(owner)
}

fn owned_payload(step: &ProofStep) -> Option<usize> {
    let bytes = |count: usize, width: usize| count.checked_mul(width);
    match step {
        ProofStep::Assume(_) => Some(0),
        ProofStep::Resolution { clause, .. } => bytes(clause.len(), size_of::<TermId>()),
        ProofStep::Step {
            rule,
            clause,
            premises,
            args,
        } => {
            let text = match rule_owned_payload(rule)? {
                RuleOwnedPayload::Text(name) => name.len(),
                RuleOwnedPayload::Fixed => 0,
            };
            bytes(clause.len().checked_add(args.len())?, size_of::<TermId>())?
                .checked_add(bytes(premises.len(), size_of::<ay_core::ProofId>())?)?
                .checked_add(text)
        }
        ProofStep::TheoryLemma { theory, clause, .. } => bytes(clause.len(), size_of::<TermId>())?
            .checked_add(bytes(
                coefficients(step)?,
                size_of::<num_rational::Rational64>(),
            )?)?
            .checked_add(theory.len()),
        _ => None,
    }
}

/// The common checked emitter rebuilds the current candidate by cloning its
/// retained rows and names. Admit that repeated copy before entering it; this
/// shares the original owner instead of renewing storage for each source.
pub(super) fn admit_rebuild_copy(proof: &Proof, budget: &RepairBudget) -> Option<()> {
    let step_storage = proof
        .steps
        .len()
        .checked_mul(size_of::<ProofStep>())?
        .checked_mul(2)?;
    let named_storage = proof
        .named_steps
        .capacity()
        .checked_mul(size_of::<(String, ay_core::ProofId)>())?
        .checked_mul(4)?;
    if !budget.pay(
        proof
            .steps
            .len()
            .checked_add(proof.named_steps.capacity().checked_mul(2)?)?,
        step_storage.checked_add(named_storage)?,
    ) {
        return None;
    }
    for step in &proof.steps {
        let bytes = owned_payload(step)?;
        if !budget.pay(bytes, bytes) {
            return None;
        }
    }
    for name in proof.named_steps.keys() {
        if !budget.pay(name.len(), name.len()) {
            return None;
        }
    }
    Some(())
}

pub(super) fn copy(
    exec: &Executor,
    proof: &Proof,
    roots: &[TermId],
    budget: &RepairBudget,
) -> Option<Proof> {
    let result = copy_inner(exec, proof, roots, budget);
    if result.is_none() {
        let _ = budget.refuse();
        let (work, storage) = budget.remaining();
        replay_note(|| {
            format!("native-proof-copy: declined work_left={work} storage_left={storage}")
        });
    }
    result
}

fn copy_inner(
    exec: &Executor,
    proof: &Proof,
    roots: &[TermId],
    budget: &RepairBudget,
) -> Option<Proof> {
    if proof.steps.len() > MAX_PROBE_PROOF_STEPS || !budget.pay(512, 512) {
        return None;
    }
    let count = proof.steps.len();
    let mut keep = Vec::new();
    let mut pending = Vec::new();
    budget.reserve(&mut keep, count)?;
    budget.reserve(&mut pending, count)?;
    keep.resize(count, false);
    let mut totals = Totals::default();
    let mut target = None;
    for index in 0..count {
        if validate_row(exec, proof, index, roots, &mut totals, budget)? {
            keep[index] = true;
            pending.push(index);
        }
        if matches!(&proof.steps[index],
            ProofStep::Resolution { clause, .. } | ProofStep::Step { clause, .. }
            if clause.is_empty())
        {
            target = Some(index);
        }
    }
    // Hash-map iteration scans sparse storage before yielding its live names.
    budget
        .pay(
            proof
                .named_steps
                .capacity()
                .checked_mul(2)?
                .checked_add(1)?,
            0,
        )
        .then_some(())?;
    for (name, id) in &proof.named_steps {
        budget.pay(1, 0).then_some(())?;
        if (id.0 as usize) >= count {
            return None;
        }
        totals.names = totals.names.saturating_add(name.len());
    }
    let full_slots = count
        .saturating_add(proof.named_steps.capacity())
        .saturating_add(totals.assumes)
        .saturating_add(totals.vectors)
        .saturating_add(totals.names)
        .saturating_add(totals.annotations)
        .saturating_add(totals.rule_text)
        .saturating_add(totals.theory_text);
    replay_note(|| {
        format!(
        "native-proof-copy: input_rows={count} named_capacity={} names={} vectors={} coefficients={} rule_text={} theory_text={} full_slots={full_slots} old_limit={MAX_NATIVE_PAYLOAD}",
        proof.named_steps.capacity(), totals.names, totals.vectors, totals.annotations,
        totals.rule_text, totals.theory_text
    )
    });
    let target = target?;
    if !keep[target] {
        keep[target] = true;
        pending.push(target);
    }
    while let Some(index) = pending.pop() {
        budget.pay(1, 0).then_some(())?;
        let mut include = |id: ay_core::ProofId| -> Option<()> {
            budget.pay(1, 0).then_some(())?;
            let index = id.0 as usize;
            if !keep[index] {
                keep[index] = true;
                pending.push(index);
            }
            Some(())
        };
        match &proof.steps[index] {
            ProofStep::Resolution {
                clause1, clause2, ..
            } => {
                include(*clause1)?;
                include(*clause2)?;
            }
            ProofStep::Step { premises, .. } => {
                for &premise in premises {
                    include(premise)?;
                }
            }
            _ => {}
        }
    }
    budget.pay(count, 0).then_some(())?;
    let kept = keep.iter().filter(|&&value| value).count();
    let mut remap = Vec::new();
    budget.reserve(&mut remap, count)?;
    remap.resize(count, None);
    let mut result = Proof::new();
    budget.reserve(&mut result.steps, kept)?;
    for (index, step) in proof.steps.iter().enumerate() {
        budget.pay(1, 0).then_some(())?;
        if !keep[index] {
            continue;
        }
        let payload = owned_payload(step)?;
        budget
            .pay(payload.checked_add(1)?, payload.checked_mul(2)?)
            .then_some(())?;
        let mut step = step.clone();
        match &mut step {
            ProofStep::Resolution {
                clause1, clause2, ..
            } => {
                *clause1 = remap[clause1.0 as usize]?;
                *clause2 = remap[clause2.0 as usize]?;
            }
            ProofStep::Step { premises, .. } => {
                for id in premises {
                    *id = remap[id.0 as usize]?;
                }
            }
            _ => {}
        }
        let id = ay_core::ProofId(u32::try_from(result.steps.len()).ok()?);
        result.steps.push(step);
        remap[index] = Some(id);
    }
    budget
        .pay(
            proof
                .named_steps
                .capacity()
                .checked_mul(2)?
                .checked_add(1)?,
            0,
        )
        .then_some(())?;
    let named = proof
        .named_steps
        .iter()
        .filter(|(_, id)| {
            keep[id.0 as usize] && matches!(proof.steps[id.0 as usize], ProofStep::Assume(_))
        })
        .count();
    let bytes = named
        .checked_mul(4)?
        .checked_mul(size_of::<(String, ay_core::ProofId)>() + 1)?
        .checked_add(64)?;
    budget.pay(named, bytes).then_some(())?;
    result.named_steps.try_reserve(named).ok()?;
    for (name, id) in &proof.named_steps {
        budget.pay(1, 0).then_some(())?;
        if !keep[id.0 as usize] || !matches!(proof.steps[id.0 as usize], ProofStep::Assume(_)) {
            continue;
        }
        let work = result
            .named_steps
            .capacity()
            .checked_mul(2)?
            .checked_add(8)?
            .checked_mul(name.len().checked_add(1)?)?;
        budget.pay(work, name.len().checked_mul(2)?).then_some(())?;
        result
            .named_steps
            .insert(name.clone(), remap[id.0 as usize]?);
    }
    let target = remap[target]?;
    if target.0 as usize + 1 != result.steps.len() {
        // Required identity metadata may follow the original refutation.
        // Keep it and derive the same empty clause again at the new end.
        budget.reserve(&mut result.steps, 1)?;
        budget
            .pay(4, size_of::<ay_core::ProofId>() * 2)
            .then_some(())?;
        result.add_rule_step(AletheRule::Reordering, Vec::new(), vec![target], Vec::new());
    }
    budget.pay(0, 0).then_some(())?;
    replay_note(|| {
        format!(
            "native-proof-copy: retained_rows={} retained_names={} full_rows={count}",
            result.steps.len(),
            result.named_steps.len()
        )
    });
    Some(result)
}
