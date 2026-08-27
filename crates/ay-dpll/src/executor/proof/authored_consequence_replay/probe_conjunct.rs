// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact assertion/conjunct reconstruction for consequence-replay probes.

use super::*;

#[derive(Clone)]
struct ConjunctPlan {
    root: TermId,
    path: Vec<(TermId, u32, TermId)>,
}

impl Executor {
    /// Replace probe-local singleton `trust` leaves with exact assertion or
    /// conjunct derivations before the probe's mandatory strict check.
    ///
    /// Ground preprocessing flattens an asserted conjunction into unit
    /// clauses. Proof reconstruction can consequently surface a conjunct as a
    /// premiseless `trust` step even though the consequence-replay probe was
    /// given the enclosing conjunction as one of its exact assertions. That is
    /// the shape produced by a finite-expanded existential's recorded Skolem
    /// instance in array frame obligations.
    ///
    /// This pass grants no semantic authority. It recognizes only an exact
    /// probe assertion or a positional descendant through raw `and` nodes,
    /// then replaces the leaf with `assume` plus strictly validated `and_pos`
    /// and `resolution` steps. The caller immediately runs the unchanged
    /// whole-proof strict checker; an unrelated leaf, malformed path, or
    /// incomplete rebuild therefore still fails closed.
    pub(in crate::executor) fn promote_consequence_probe_conjunct_trust_leaves(
        &mut self,
        proof: &mut Proof,
        assertions: &[TermId],
    ) {
        if assertions.is_empty()
            || assertions.len() > MAX_CONSEQUENCES
            || proof.steps.len() > MAX_PROBE_PROOF_STEPS
        {
            return;
        }

        let Some(plans) = self.consequence_probe_conjunct_plans(proof, assertions) else {
            return;
        };

        let mut rebuilt = Proof::new();
        let mut root_units: ay_core::kani_compat::DetHashMap<TermId, ProofId> =
            ay_core::kani_compat::DetHashMap::default();
        let mut remap: Vec<ProofId> = Vec::with_capacity(proof.steps.len());
        for (index, step) in proof.steps.iter().cloned().enumerate() {
            if let Some(plan) = &plans[index] {
                let mut unit = *root_units
                    .entry(plan.root)
                    .or_insert_with(|| rebuilt.add_assume(plan.root, None));
                for &(parent, position, child) in &plan.path {
                    let not_parent = self.ctx.terms.mk_not_raw(parent);
                    let projection = rebuilt.add_rule_step(
                        AletheRule::AndPos(position),
                        vec![not_parent, child],
                        Vec::new(),
                        vec![parent],
                    );
                    unit = rebuilt.add_resolution(vec![child], parent, projection, unit);
                }
                remap.push(unit);
                continue;
            }

            let remap_id = |id: ProofId| remap.get(id.0 as usize).copied().unwrap_or(id);
            let step = match step {
                ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1,
                    clause2,
                } => ProofStep::Resolution {
                    clause,
                    pivot,
                    clause1: remap_id(clause1),
                    clause2: remap_id(clause2),
                },
                ProofStep::Step {
                    rule,
                    clause,
                    premises,
                    args,
                } => ProofStep::Step {
                    rule,
                    clause,
                    premises: premises.into_iter().map(remap_id).collect(),
                    args,
                },
                other => other,
            };
            remap.push(rebuilt.add_step(step));
        }

        let mut remapped_named = proof.named_steps.clone();
        remapped_named.retain(|_, id| {
            let old_index = id.0 as usize;
            let Some(new_id) = remap.get(old_index) else {
                return false;
            };
            *id = *new_id;
            true
        });
        rebuilt.named_steps = remapped_named;
        *proof = rebuilt;
    }

    fn consequence_probe_conjunct_plans(
        &self,
        proof: &Proof,
        assertions: &[TermId],
    ) -> Option<Vec<Option<ConjunctPlan>>> {
        let mut plans = vec![None; proof.steps.len()];
        let mut planned = 0usize;
        for (index, step) in proof.steps.iter().enumerate() {
            let ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                ..
            } = step
            else {
                continue;
            };
            let [target] = clause.as_slice() else {
                continue;
            };
            if !premises.is_empty() {
                continue;
            }
            let Some(plan) = assertions.iter().find_map(|&root| {
                if root == *target {
                    return Some(ConjunctPlan {
                        root,
                        path: Vec::new(),
                    });
                }
                self.and_path_to(root, *target)
                    .map(|path| ConjunctPlan { root, path })
            }) else {
                continue;
            };
            planned += 1;
            if planned > MAX_CONSEQUENCES {
                return None;
            }
            plans[index] = Some(plan);
        }
        if planned == 0 {
            None
        } else {
            Some(plans)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn probe_conjunct_trust_leaves_are_derived_and_strict_checked() {
        let mut exec = Executor::new();
        let p = exec.ctx.terms.mk_fresh_var("probe_conjunct_p", Sort::Bool);
        let not_p = exec.ctx.terms.mk_not_raw(p);
        let root = exec
            .ctx
            .terms
            .mk_app(Symbol::named("and"), [p, not_p], Sort::Bool);
        exec.ctx.assertions.push(root);

        let mut proof = Proof::new();
        let positive = proof.add_rule_step(AletheRule::Trust, vec![p], Vec::new(), Vec::new());
        let negative = proof.add_rule_step(AletheRule::Trust, vec![not_p], Vec::new(), Vec::new());
        proof.add_resolution(Vec::new(), p, positive, negative);

        exec.promote_consequence_probe_conjunct_trust_leaves(&mut proof, &[root]);

        assert!(proof.steps.iter().all(|step| !matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Trust,
                ..
            }
        )));
        assert!(proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::AndPos(_),
                ..
            }
        )));
        let strict = exec.check_proof_strict_with_datatypes(&proof);
        assert!(
            strict.as_ref().is_ok_and(|quality| quality.is_complete()),
            "rebuilt probe proof must be strict-complete: {strict:?}; proof={proof:?}"
        );
        assert!(
            ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &[root]).is_ok(),
            "the rebuilt proof may assume only the exact probe root"
        );
    }

    #[test]
    fn probe_conjunct_promotion_leaves_unrelated_trust_visible() {
        let mut exec = Executor::new();
        let p = exec.ctx.terms.mk_fresh_var("probe_conjunct_p", Sort::Bool);
        let q = exec.ctx.terms.mk_fresh_var("probe_conjunct_q", Sort::Bool);
        let root = exec.ctx.terms.mk_app(Symbol::named("and"), [p], Sort::Bool);
        let mut proof = Proof::new();
        proof.add_rule_step(AletheRule::Trust, vec![q], Vec::new(), Vec::new());

        exec.promote_consequence_probe_conjunct_trust_leaves(&mut proof, &[root]);

        assert!(matches!(
            proof.steps.as_slice(),
            [ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                ..
            }] if clause == &[q] && premises.is_empty()
        ));
    }
}
