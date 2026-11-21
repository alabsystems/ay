// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Compose checked arithmetic leaves within the exact authored scope.

use super::*;
use crate::theory_inference::intrinsic_integer::IntrinsicIntegerClause;
use ay_core::proof_validation::{
    farkas_conflict_lits_linear_holds_with_progress, FarkasValidationError,
};
use ay_core::{FarkasAnnotation, TheoryLit};

const MAX_INTEGER_ATTEMPTS: usize = 12;

struct IntegerLeaf<'a> {
    clause: &'a [TermId],
    retained: Option<&'a FarkasAnnotation>,
}

fn integer_leaf(step: &ProofStep) -> Option<IntegerLeaf<'_>> {
    match step {
        ProofStep::Step {
            rule: AletheRule::Trust,
            clause,
            premises,
            args,
        } if premises.is_empty() && args.is_empty() => Some(IntegerLeaf {
            clause,
            retained: None,
        }),
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::Generic,
            clause,
            farkas: None,
            lia: None,
            ..
        } => Some(IntegerLeaf {
            clause,
            retained: None,
        }),
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::LiaGeneric | TheoryLemmaKind::LraFarkas,
            clause,
            farkas: Some(retained),
            lia: None,
            ..
        } => Some(IntegerLeaf {
            clause,
            retained: Some(retained),
        }),
        _ => None,
    }
}

/// Called only after the intrinsic plan has admitted the complete clause/DAG.
/// Bound-only leaves have neither equality-span nor congruence premises, so
/// checking their recorded positional coefficients needs no stronger lane.
/// Other annotated fragments retain their original checker/annotation intact.
fn rejected_retained_bounds(
    terms: &ay_core::TermStore,
    leaf: &IntegerLeaf<'_>,
    budget: &RepairBudget,
) -> Option<bool> {
    let Some(annotation) = leaf.retained else {
        return Some(true);
    };
    let mut conflict = Vec::new();
    budget.reserve(&mut conflict, leaf.clause.len())?;
    for &literal in leaf.clause {
        budget.pay(1, 0).then_some(())?;
        let (atom, value) = match terms.get(literal) {
            TermData::Not(inner) => (*inner, true),
            _ => (literal, false),
        };
        if !matches!(
            terms.get(atom),
            TermData::App(Symbol::Named(name), _) if matches!(name.as_str(), "<" | "<=" | ">" | ">=")
        ) {
            return Some(false);
        }
        conflict.push(TheoryLit::new(atom, value));
    }
    // Producer coefficients are canonical rationals. Leave forged raw ratios
    // outside this repair fragment instead of changing the older validator's
    // decision boundary or trying to normalize its metadata here.
    if annotation.coefficients.len() == conflict.len() {
        budget.pay(annotation.coefficients.len(), 0).then_some(())?;
        if annotation
            .coefficients
            .iter()
            .any(|value| *value.denom() <= 0)
        {
            return Some(false);
        }
    }
    let checked = farkas_conflict_lits_linear_holds_with_progress(
        terms,
        &conflict,
        annotation,
        &mut |work, bytes| budget.pay(work, bytes),
    );
    match checked {
        Ok(holds) => Some(!holds),
        Err(FarkasValidationError::ResourceLimit) => None,
        // A malformed coefficient count or non-arithmetic row is not a
        // certificate. It grants nothing: emission must independently derive
        // the exact unchanged clause, and the complete final gate still runs.
        Err(_) => budget.pay(0, 0).then_some(true),
    }
}

impl Executor {
    /// Compose independent leaf derivations in one candidate. Neither stage
    /// installs authority. Both callers retain their complete final gate.
    pub(super) fn stage_checked_integer_and_euf_leaves(
        &mut self,
        proof: &mut Proof,
        budget: &RepairBudget,
    ) -> Option<usize> {
        let repaired = self.stage_small_integer_leaves_with_budget(proof, budget)?;
        replay_note(|| format!("small-integer-clauses: staged replacements={repaired}"));
        if self.proof_assembly_stop_requested() {
            return None;
        }
        if proof.steps.iter().any(|step| {
            matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    ..
                } | ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::Generic,
                    ..
                }
            )
        }) {
            let owner = budget.clone();
            budget.pay(0, 0).then_some(())?;
            let disposable = std::mem::take(proof);
            // Failure consumes only this disposable candidate. Never continue
            // with the empty sentinel; both callers abort before their final
            // strict gate and leave the retained outer proof untouched.
            let candidate = self.build_generic_euf_leaf_candidate_owned_with_admission(
                disposable,
                MAX_NATIVE_PAYLOAD,
                move |work, bytes| owner.pay(work, bytes),
            )?;
            *proof = candidate;
            replay_note(|| "small-integer-clauses: staged owned EUF candidate".to_owned());
        }
        (!self.proof_assembly_stop_requested() && budget.pay(0, 0)).then_some(repaired)
    }

    #[cfg(test)]
    pub(super) fn stage_small_integer_leaves(&mut self, proof: &mut Proof) -> usize {
        let budget = RepairBudget::new(self);
        self.stage_small_integer_leaves_with_budget(proof, &budget)
            .unwrap_or(0)
    }

    fn stage_small_integer_leaves_with_budget(
        &mut self,
        proof: &mut Proof,
        budget: &RepairBudget,
    ) -> Option<usize> {
        let mut progress = |work, storage| budget.pay(work, storage);
        let mut remap = Vec::new();
        budget.reserve(&mut remap, proof.steps.len())?;
        let original = std::mem::take(&mut proof.steps);
        let mut attempts = 0;
        let mut derived = 0;
        for step in original {
            if !progress(1, 0) {
                return None;
            }
            if attempts < MAX_INTEGER_ATTEMPTS {
                if let Some((leaf, plan)) = integer_leaf(&step).and_then(|leaf| {
                    let plan =
                        IntrinsicIntegerClause::admit(&self.ctx.terms, leaf.clause, &mut progress)?;
                    Some((leaf, plan))
                }) {
                    if !rejected_retained_bounds(&self.ctx.terms, &leaf, budget)? {
                        let step = crate::executor::proof::remap_step_premises(step, &remap);
                        remap.push(proof.add_step(step));
                        continue;
                    }
                    attempts += 1;
                    let start = proof.steps.len();
                    if let Some(id) = plan.emit(&mut self.ctx.terms, proof, &mut progress) {
                        replay_note(|| {
                            format!(
                                "small-integer-clauses: source_step={} emitted_start={start} emitted_end={} target={}",
                                remap.len(),
                                proof.steps.len(),
                                id.0,
                            )
                        });
                        remap.push(id);
                        derived += 1;
                        continue;
                    }
                    if !progress(0, 0) {
                        return None;
                    }
                }
            }
            let step = crate::executor::proof::remap_step_premises(step, &remap);
            remap.push(proof.add_step(step));
        }
        budget
            .pay(proof.named_steps.capacity().checked_mul(2)?, 0)
            .then_some(())?;
        proof.named_steps.retain(|_, id| {
            let Some(rebound) = remap.get(id.0 as usize) else {
                return false;
            };
            *id = *rebound;
            true
        });
        budget.pay(0, 0).then_some(derived)
    }

    /// Repair arithmetic leaves when the whole exact authored proof checks.
    pub(in crate::executor::proof) fn replace_with_checked_small_integer_leaves(
        &mut self,
        proof: &mut Proof,
    ) -> bool {
        // Projection validates every row even when the first repairable leaf is early.
        // Leave the retained proof untouched if the caller cannot afford that pass.
        if proof.steps.len() > MAX_PROBE_PROOF_STEPS
            || !crate::executor::proof::assembly_observations::can_observe(proof.steps.len())
        {
            return false;
        }
        let stop = self.make_proof_assembly_should_stop();
        let budget = RepairBudget::new(self);
        if !proof
            .steps
            .iter()
            .take_while(|_| !stop() && budget.pay(1, 0))
            .filter_map(integer_leaf)
            .any(|leaf| IntrinsicIntegerClause::may_reconstruct(&self.ctx.terms, leaf.clause))
        {
            return false;
        }
        let Some((epoch, context, window)) = self.bounded_plain_unsat_query_scope(MAX_NATIVE_ROOTS)
        else {
            return false;
        };
        if window != self.proof_original_problem_assertions_slice() {
            return false;
        }
        let roots = window.to_vec();
        let prefix = self.ctx.terms.snapshot_stamp();
        let metadata = self.ctx.terms.checker_visible_metadata_generation();
        let Some(mut candidate) = projection::copy(self, proof, &roots, &budget) else {
            return false;
        };
        if self
            .stage_native_conjunct_leaves(&mut candidate, &roots, &budget)
            .is_none()
        {
            return false;
        }
        let Some(repaired) = self.stage_checked_integer_and_euf_leaves(&mut candidate, &budget)
        else {
            return false;
        };
        if repaired == 0
            || candidate.steps.len() > MAX_PROBE_PROOF_STEPS
            || admit_proof_copy(&candidate).is_none()
            || self.proof_assembly_stop_requested()
            || ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &roots).is_err()
            || !self
                .check_proof_strict_with_datatypes(&candidate)
                .is_ok_and(|quality| quality.is_complete())
        {
            return false;
        }
        let current = self
            .bounded_plain_unsat_query_scope(MAX_NATIVE_ROOTS)
            .is_some_and(|(now_epoch, now_context, now_roots)| {
                now_epoch.is_same_epoch(&epoch) && now_context == context && now_roots == roots
            });
        if !current
            || self.proof_assembly_stop_requested()
            || !prefix.is_append_only_prefix_of(&self.ctx.terms)
            || metadata != self.ctx.terms.checker_visible_metadata_generation()
        {
            return false;
        }
        *proof = candidate;
        replay_note(|| format!("small-integer-clauses: checked replacements={repaired}"));
        true
    }
}

#[cfg(test)]
#[path = "integer_leaves_tests.rs"]
mod tests;
