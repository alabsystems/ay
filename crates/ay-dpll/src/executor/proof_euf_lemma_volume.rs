// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conservative emitted-volume accounting for EUF proof recipes.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{AletheRule, LiaAnnotation, Proof, ProofId, ProofStep, TermId};

use super::{EufConcl, EufDeriv, EufJust, EufLemmaPlan, EufTarget};

const MAX_PROMOTION_STEPS: usize = 100_000;
pub(super) const MAX_PROMOTION_EDGES: usize = 100_000;
pub(super) const MAX_PROMOTION_VECTOR_ENTRIES: usize = 262_144;
const MAX_PROMOTION_TEXT_BYTES: usize = 8 * 1024 * 1024;

pub(super) struct PromotionPreflight {
    pub(super) reachable: Vec<bool>,
    pub(super) input_volume: usize,
}

fn spend_bounded(total: &mut usize, amount: usize, limit: usize) -> Option<()> {
    *total = total.checked_add(amount)?;
    (*total <= limit).then_some(())
}

/// Bound the complete input proof before the generic-EUF promoter clones any
/// proof-owned vector or string. Reachability is computed in the same pass so
/// a wide/repeated premise list cannot bypass the aggregate edge cap.
pub(super) fn preflight_promotion(proof: &Proof) -> Option<PromotionPreflight> {
    let step_count = proof.steps.len();
    if step_count > MAX_PROMOTION_STEPS
        || proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::Anchor { .. }))
    {
        return None;
    }

    // Count the `steps` allocation itself in addition to every owned child
    // vector. Text is bounded separately because it is measured in bytes.
    let mut input_volume = step_count;
    let mut text_bytes = 0usize;
    for step in &proof.steps {
        let admitted = match step {
            ProofStep::Assume(_) => Some(()),
            ProofStep::Resolution { clause, .. } => spend_bounded(
                &mut input_volume,
                clause.len(),
                MAX_PROMOTION_VECTOR_ENTRIES,
            ),
            ProofStep::Step {
                rule,
                clause,
                premises,
                args,
            } => {
                spend_bounded(
                    &mut input_volume,
                    clause.len(),
                    MAX_PROMOTION_VECTOR_ENTRIES,
                )?;
                spend_bounded(
                    &mut input_volume,
                    premises.len(),
                    MAX_PROMOTION_VECTOR_ENTRIES,
                )?;
                spend_bounded(&mut input_volume, args.len(), MAX_PROMOTION_VECTOR_ENTRIES)?;
                if let AletheRule::Custom(name) = rule {
                    spend_bounded(&mut text_bytes, name.len(), MAX_PROMOTION_TEXT_BYTES)?;
                }
                Some(())
            }
            ProofStep::TheoryLemma {
                theory,
                clause,
                farkas,
                lia,
                ..
            } => {
                spend_bounded(
                    &mut input_volume,
                    clause.len(),
                    MAX_PROMOTION_VECTOR_ENTRIES,
                )?;
                if let Some(certificate) = farkas {
                    spend_bounded(
                        &mut input_volume,
                        certificate.coefficients.len(),
                        MAX_PROMOTION_VECTOR_ENTRIES,
                    )?;
                }
                if let Some(LiaAnnotation::CuttingPlane(cut)) = lia {
                    spend_bounded(
                        &mut input_volume,
                        cut.farkas.coefficients.len(),
                        MAX_PROMOTION_VECTOR_ENTRIES,
                    )?;
                }
                spend_bounded(&mut text_bytes, theory.len(), MAX_PROMOTION_TEXT_BYTES)
            }
            ProofStep::Anchor { .. } => None,
            _ => None,
        };
        admitted?;
    }
    for name in proof.named_steps.keys() {
        // Invalid/non-Assume ids are intentionally admitted here: the
        // promoter's post-rebuild retain pass has always sanitized them.
        // Preflight owns only their allocation/work bound, not their proof
        // authority.
        spend_bounded(&mut input_volume, 1, MAX_PROMOTION_VECTOR_ENTRIES)?;
        spend_bounded(&mut text_bytes, name.len(), MAX_PROMOTION_TEXT_BYTES)?;
    }

    let mut reachable = vec![false; step_count];
    let mut stack = Vec::new();
    for (index, step) in proof.steps.iter().enumerate() {
        let derives_empty = match step {
            ProofStep::Resolution { clause, .. }
            | ProofStep::TheoryLemma { clause, .. }
            | ProofStep::Step { clause, .. } => clause.is_empty(),
            ProofStep::Assume(_) | ProofStep::Anchor { .. } => false,
            _ => false,
        };
        if derives_empty {
            reachable[index] = true;
            stack.push(index);
        }
    }
    let mut edge_work = 0usize;
    while let Some(index) = stack.pop() {
        let mut mark = |premise: ProofId| -> Option<()> {
            let premise = premise.0 as usize;
            if premise >= step_count {
                return None;
            }
            if !reachable[premise] {
                reachable[premise] = true;
                stack.push(premise);
            }
            Some(())
        };
        match &proof.steps[index] {
            ProofStep::Resolution {
                clause1, clause2, ..
            } => {
                spend_bounded(&mut edge_work, 2, MAX_PROMOTION_EDGES)?;
                mark(*clause1)?;
                mark(*clause2)?;
            }
            ProofStep::Step { premises, .. } => {
                spend_bounded(&mut edge_work, premises.len(), MAX_PROMOTION_EDGES)?;
                for &premise in premises {
                    mark(premise)?;
                }
            }
            _ => {}
        }
    }
    Some(PromotionPreflight {
        reachable,
        input_volume,
    })
}

pub(super) fn promotion_output_within(
    preflight: &PromotionPreflight,
    plans: &[Option<EufLemmaPlan>],
    limit: usize,
) -> bool {
    if plans.len() != preflight.reachable.len() {
        return false;
    }
    let mut volume = preflight.input_volume;
    plans.iter().flatten().all(|plan| {
        plan.emitted_literal_volume()
            .is_some_and(|emitted| spend_bounded(&mut volume, emitted, limit).is_some())
    })
}

fn spend(total: &mut usize, amount: usize) -> Option<()> {
    *total = total.checked_add(amount)?;
    Some(())
}

fn taut_volume(
    prems: &[EufJust],
    tail_len: usize,
    emitted_lengths: &[usize],
    refls: &mut HashSet<TermId>,
    total: &mut usize,
) -> Option<usize> {
    let mut width = prems.len().checked_add(tail_len)?;
    spend(total, width)?;
    for premise in prems {
        match *premise {
            EufJust::Hyp(_) => continue,
            EufJust::Refl(side) => {
                if refls.insert(side) {
                    spend(total, 1)?;
                }
                width = width.checked_sub(1)?;
            }
            EufJust::Derived(index) => {
                let source_width = *emitted_lengths.get(index)?;
                width = width
                    .checked_sub(1)?
                    .checked_add(source_width.saturating_sub(1))?;
            }
        }
        spend(total, width)?;
    }
    // The real emitter adds this only when deduplication changes the clause;
    // charging it unconditionally is a safe upper bound.
    spend(total, width)?;
    Some(width)
}

impl EufLemmaPlan {
    pub(in crate::executor) fn emitted_literal_volume(&self) -> Option<usize> {
        let mut total = 0usize;
        let mut emitted_lengths = Vec::with_capacity(self.derivs.len());
        let mut refls = HashSet::default();
        for deriv in &self.derivs {
            let prems = match deriv {
                EufDeriv::Cong { prems, .. } => prems,
                EufDeriv::Chain { edges, .. } => edges,
            };
            emitted_lengths.push(taut_volume(
                prems,
                1,
                &emitted_lengths,
                &mut refls,
                &mut total,
            )?);
        }
        let final_width = match &self.concl {
            EufConcl::Eq { top } => *emitted_lengths.get(*top)?,
            EufConcl::EqRefl { .. } => {
                spend(&mut total, 1)?;
                1
            }
            EufConcl::Pred { prems, .. } => {
                taut_volume(prems, 2, &emitted_lengths, &mut refls, &mut total)?
            }
        };
        match &self.target {
            EufTarget::Bare { extras } if !extras.is_empty() => {
                spend(&mut total, final_width.checked_add(extras.len())?)?;
            }
            EufTarget::OrUnit { .. } => {
                let links = final_width.checked_mul(final_width.checked_add(2)?)?;
                spend(&mut total, links.checked_add(1)?)?;
            }
            EufTarget::Bare { .. } => {}
        }
        Some(total)
    }
}

#[cfg(test)]
mod tests {
    use ay_core::{AletheRule, Proof, ProofStep, Sort};

    use super::{
        preflight_promotion, promotion_output_within, PromotionPreflight, ProofId,
        MAX_PROMOTION_EDGES,
    };
    use crate::executor::Executor;

    fn clause_volume(proof: &Proof) -> usize {
        proof
            .steps
            .iter()
            .map(|step| match step {
                ProofStep::Step { clause, .. }
                | ProofStep::Resolution { clause, .. }
                | ProofStep::TheoryLemma { clause, .. } => clause.len(),
                ProofStep::Assume(_) | ProofStep::Anchor { .. } => 0,
                _ => 0,
            })
            .sum()
    }

    #[test]
    fn recipe_volume_dominates_bare_and_or_unit_emission() {
        let mut executor = Executor::new();
        let a = executor.ctx.terms.mk_var("volume_a", Sort::Int);
        let b = executor.ctx.terms.mk_var("volume_b", Sort::Int);
        let c = executor.ctx.terms.mk_var("volume_c", Sort::Int);
        let ab = executor.ctx.terms.mk_eq(a, b);
        let bc = executor.ctx.terms.mk_eq(b, c);
        let ac = executor.ctx.terms.mk_eq(a, c);
        let not_ab = executor.ctx.terms.mk_not_raw(ab);
        let not_bc = executor.ctx.terms.mk_not_raw(bc);
        let clause = [ac, not_ab, not_bc];
        let bare = executor
            .plan_euf_lemma(&clause)
            .expect("transitivity recipe");
        let mut proof = Proof::new();
        executor.emit_euf_lemma(&mut proof, &bare);
        assert!(clause_volume(&proof) <= bare.emitted_literal_volume().unwrap());

        let or_term = executor.ctx.terms.mk_or(clause.to_vec());
        let wrapped = executor.plan_euf_lemma(&[or_term]).expect("or-unit recipe");
        let mut proof = Proof::new();
        executor.emit_euf_lemma(&mut proof, &wrapped);
        assert!(clause_volume(&proof) <= wrapped.emitted_literal_volume().unwrap());
    }

    #[test]
    fn repeated_recipe_volume_is_charged_per_leaf() {
        let mut executor = Executor::new();
        let a = executor.ctx.terms.mk_var("repeat_volume_a", Sort::Int);
        let b = executor.ctx.terms.mk_var("repeat_volume_b", Sort::Int);
        let c = executor.ctx.terms.mk_var("repeat_volume_c", Sort::Int);
        let ab = executor.ctx.terms.mk_eq(a, b);
        let bc = executor.ctx.terms.mk_eq(b, c);
        let ac = executor.ctx.terms.mk_eq(a, c);
        let not_ab = executor.ctx.terms.mk_not_raw(ab);
        let not_bc = executor.ctx.terms.mk_not_raw(bc);
        let plan = executor
            .plan_euf_lemma(&[ac, not_ab, not_bc])
            .expect("transitivity recipe");
        let emitted = plan.emitted_literal_volume().expect("bounded recipe");
        let plans = vec![Some(plan.clone()), Some(plan)];
        let preflight = PromotionPreflight {
            reachable: vec![true; plans.len()],
            input_volume: 0,
        };
        assert!(promotion_output_within(&preflight, &plans, emitted * 2));
        assert!(!promotion_output_within(
            &preflight,
            &plans,
            emitted * 2 - 1
        ));
    }

    #[test]
    fn promotion_preflight_rejects_wide_repeated_premises() {
        let mut proof = Proof::new();
        let atom = ay_core::TermId(0);
        let assume = proof.add_assume(atom, None);
        proof.add_rule_step(
            AletheRule::Trust,
            Vec::new(),
            vec![assume; MAX_PROMOTION_EDGES + 1],
            Vec::new(),
        );
        assert!(preflight_promotion(&proof).is_none());
    }

    #[test]
    fn promotion_preflight_bounds_but_does_not_authorize_named_ids() {
        let mut proof = Proof::new();
        let atom = ay_core::TermId(0);
        let step = proof.add_rule_step(AletheRule::True, vec![atom], Vec::new(), Vec::new());
        proof.named_steps.insert("non_assume".to_string(), step);
        proof
            .named_steps
            .insert("dangling".to_string(), ProofId(u32::MAX));
        assert!(preflight_promotion(&proof).is_some());
    }
}
