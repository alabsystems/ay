// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! L1 replay of checked structural-array units. Stored derivations are data:
//! fresh source authentication precedes every append to the current plan.

use super::*;

mod budget;
pub(super) use budget::ArrayReplayBudget;
mod storage;
pub(super) use storage::{prepay_indexes, prepay_splice};
mod preprocessing;

impl PropagationChainPlanner<'_> {
    pub(super) fn plan_array_unit_base(
        &mut self,
        cx: &mut PlanCx<'_>,
        term: TermId,
    ) -> Option<ProofId> {
        if cx.refuses_constant_conclusion(term) {
            return None;
        }
        let units = cx.array_units;
        let mut selected = None;
        for unit in units {
            spend_payload(cx, 1, 0)?;
            if unit.term() == term {
                selected = Some(unit);
                break;
            }
        }
        let selected = selected?;
        let roots = cx.problem_roots;
        // Full checker work belongs to the shared semantic-work/byte envelope,
        // not the much smaller planner-node counter. Inventory traversal and
        // actual copied proof nodes/payload still debit both below. A missing
        // shared meter cannot license this independent authentication.
        let progress = cx.array_progress?;
        let (proof, conclusion) =
            selected.reauthenticate(self.terms, roots, &mut |work, bytes| progress(work, bytes))?;
        let mark = cx.mark();
        let result = append_unit_fragment(cx, proof, conclusion);
        if result.is_none() {
            cx.rollback(mark);
        }
        result
    }
}

/// Keep planner traversal and copied storage inside the existing plan envelope.
/// A 64-byte storage quantum is charged in addition to every reported node;
/// checked arithmetic refuses oversized payloads instead of wrapping a charge.
fn spend_payload(cx: &mut PlanCx<'_>, work: usize, bytes: usize) -> Option<()> {
    if cx
        .array_progress
        .is_some_and(|progress| !progress(work, bytes))
    {
        return None;
    }
    cx.spend(work.checked_add(bytes.div_ceil(64))?)
}

/// Append only the small, closed proof vocabulary the structural producer uses.
/// In particular, no anchor, annotated arithmetic certificate or future variant
/// is copied speculatively. Every premise is local and strictly backwards.
fn append_unit_fragment(
    cx: &mut PlanCx<'_>,
    proof: &Proof,
    conclusion: ProofId,
) -> Option<ProofId> {
    if conclusion.0 as usize >= proof.steps.len() {
        return None;
    }
    let offset = u32::try_from(cx.chain.steps.len()).ok()?;
    let count = u32::try_from(proof.steps.len()).ok()?;
    offset.checked_add(count)?;
    for (index, step) in proof.steps.iter().enumerate() {
        spend_payload(cx, 1, std::mem::size_of::<ProofStep>().checked_mul(2)?)?;
        let copied = copy_unit_step(cx, step, index, offset)?;
        cx.chain.add_step(copied);
    }
    Some(ProofId(offset.checked_add(conclusion.0)?))
}

fn copy_unit_step(
    cx: &mut PlanCx<'_>,
    step: &ProofStep,
    index: usize,
    offset: u32,
) -> Option<ProofStep> {
    let remap = |id: ProofId| {
        ((id.0 as usize) < index)
            .then(|| offset.checked_add(id.0).map(ProofId))
            .flatten()
    };
    match step {
        ProofStep::Assume(term) => Some(ProofStep::Assume(*term)),
        ProofStep::Resolution {
            clause,
            pivot,
            clause1,
            clause2,
        } => {
            spend_terms(cx, clause.len())?;
            Some(ProofStep::Resolution {
                clause: clause.clone(),
                pivot: *pivot,
                clause1: remap(*clause1)?,
                clause2: remap(*clause2)?,
            })
        }
        ProofStep::Step {
            rule,
            clause,
            premises,
            args,
        } if matches!(
            rule,
            AletheRule::AndPos(_) | AletheRule::Or | AletheRule::ThResolution
        ) =>
        {
            spend_terms(cx, clause.len().checked_add(args.len())?)?;
            spend_payload(
                cx,
                premises.len(),
                premises.len().checked_mul(std::mem::size_of::<ProofId>())?,
            )?;
            let premises = premises
                .iter()
                .map(|id| remap(*id))
                .collect::<Option<Vec<_>>>()?;
            Some(ProofStep::Step {
                rule: rule.clone(),
                clause: clause.clone(),
                premises,
                args: args.clone(),
            })
        }
        ProofStep::TheoryLemma {
            theory,
            clause,
            farkas: None,
            kind,
            lia: None,
        } if matches!(
            kind,
            TheoryLemmaKind::IteBranchProjection
                | TheoryLemmaKind::EufCongruent
                | TheoryLemmaKind::EufTransitive
        ) =>
        {
            spend_terms(cx, clause.len())?;
            spend_payload(cx, theory.len(), theory.len())?;
            Some(ProofStep::TheoryLemma {
                theory: theory.clone(),
                clause: clause.clone(),
                farkas: None,
                kind: kind.clone(),
                lia: None,
            })
        }
        _ => None,
    }
}

fn spend_terms(cx: &mut PlanCx<'_>, terms: usize) -> Option<()> {
    spend_payload(cx, terms, terms.checked_mul(std::mem::size_of::<TermId>())?)
}

#[cfg(test)]
mod tests;
