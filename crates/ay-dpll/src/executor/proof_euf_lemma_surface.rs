// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surface-override roles for emitted EUF derivations.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{Proof, Symbol};

use super::super::proof_trust_surgery_provenance::ProvenanceSurfaceAudit;
use super::super::proof_trust_surgery_surface_audit::{
    copied_structural_roles_are_static, live_proof_rendering_is_static,
};
use super::{EufConcl, EufDeriv, EufJust, EufLemmaPlan, EufTarget};
use crate::executor::Executor;

fn protect_congruence_equality(
    audit: &mut ProvenanceSurfaceAudit,
    terms: &mut ay_core::TermStore,
    equality: ay_core::TermId,
) {
    let sides = match terms.get(equality).clone() {
        TermData::App(Symbol::Named(op), sides) if op == "=" && sides.len() == 2 => Some(sides),
        _ => None,
    };
    audit.protect_rigid_operand(terms, equality);
    if let Some(sides) = sides {
        // `eq_congruent` is positional and requires the two printed sides to
        // retain their canonical application heads. Equivalent implication,
        // reordered arithmetic, or let spellings are not interchangeable in
        // this rigid rule role.
        for side in sides {
            audit.protect_rigid_operand(terms, side);
        }
    }
}

fn protect_justification(
    audit: &mut ProvenanceSurfaceAudit,
    terms: &mut ay_core::TermStore,
    justification: &EufJust,
) {
    match justification {
        EufJust::Refl(side) => {
            let equality = terms.mk_eq(*side, *side);
            audit.protect_rigid_operand(terms, equality);
        }
        EufJust::Hyp(literal) => audit.protect_operand(terms, *literal),
        EufJust::Derived(_) => {}
    }
}

impl EufLemmaPlan {
    pub(in crate::executor) fn protect_surface_operands(
        &self,
        audit: &mut ProvenanceSurfaceAudit,
        terms: &mut ay_core::TermStore,
    ) {
        for deriv in &self.derivs {
            match deriv {
                EufDeriv::Cong { eq_term, prems } => {
                    protect_congruence_equality(audit, terms, *eq_term);
                    for premise in prems {
                        protect_justification(audit, terms, premise);
                    }
                }
                EufDeriv::Chain { eq_term, edges } => {
                    audit.protect_rigid_operand(terms, *eq_term);
                    for edge in edges {
                        protect_justification(audit, terms, edge);
                    }
                }
            }
        }
        match &self.concl {
            EufConcl::Eq { .. } => {}
            EufConcl::EqRefl { eq_term } => audit.protect_rigid_operand(terms, *eq_term),
            EufConcl::Pred {
                neg_lit,
                pos_lit,
                prems,
            } => {
                audit.protect_rigid_operand(terms, *neg_lit);
                audit.protect_rigid_operand(terms, *pos_lit);
                for premise in prems {
                    protect_justification(audit, terms, premise);
                }
            }
        }
        match &self.target {
            EufTarget::Bare { extras } => {
                for &extra in extras {
                    audit.protect_operand(terms, extra);
                }
            }
            EufTarget::OrUnit { term } => audit.protect_rigid_operand(terms, *term),
        }
    }
}

impl Executor {
    /// Validate every rule role introduced by standalone generic-EUF
    /// promotion against the already-active surface map. Unlike trust
    /// surgery, this pass has no authored-source authority with which to add
    /// or change an override, so any active spelling that reaches a promoted
    /// operand must already be compatible with its exact Alethe role.
    pub(in crate::executor) fn generic_euf_promotion_surface_is_safe(
        &mut self,
        proof: &Proof,
        plans: &[Option<EufLemmaPlan>],
    ) -> bool {
        let Some(effective) = self.last_proof_term_overrides.as_ref() else {
            return true;
        };
        if effective.is_empty() {
            return true;
        }
        if plans.len() != proof.steps.len() {
            return false;
        }

        let mut audit = ProvenanceSurfaceAudit::default();
        let mut replaced = HashSet::default();
        for (index, plan) in plans.iter().enumerate() {
            let Some(plan) = plan else {
                continue;
            };
            replaced.insert(index);
            plan.protect_surface_operands(&mut audit, &mut self.ctx.terms);
        }

        // Promotion copies every old step, including unreachable diagnostic
        // material, into the exported proof. Audit all of those copied roles,
        // not merely the source slice reachable from the final empty clause.
        let live = vec![true; proof.steps.len()];
        audit.active_map_is_bounded(effective)
            && audit.protect_copied_resolution_and_farkas_roles(
                proof,
                &live,
                &replaced,
                &mut self.ctx.terms,
            )
            && live_proof_rendering_is_static(proof, &live, &self.ctx.terms, effective)
            && copied_structural_roles_are_static(
                proof,
                &live,
                &replaced,
                &self.ctx.terms,
                effective,
            )
            && audit.validate_effective(&self.ctx.terms, effective)
    }
}

#[cfg(test)]
mod tests {
    use ay_core::kani_compat::DetHashMap as HashMap;
    use ay_core::Sort;

    use super::ProvenanceSurfaceAudit;
    use crate::executor::Executor;

    #[test]
    fn standalone_euf_plan_audits_boolean_equality_surface() {
        let mut executor = Executor::new();
        let a = executor.ctx.terms.mk_var("late_euf_a", Sort::Int);
        let b = executor.ctx.terms.mk_var("late_euf_b", Sort::Int);
        let c = executor.ctx.terms.mk_var("late_euf_c", Sort::Int);
        let ab = executor.ctx.terms.mk_eq(a, b);
        let bc = executor.ctx.terms.mk_eq(b, c);
        let ac = executor.ctx.terms.mk_eq(a, c);
        let not_ab = executor.ctx.terms.mk_not_raw(ab);
        let not_bc = executor.ctx.terms.mk_not_raw(bc);
        let plan = executor
            .plan_euf_lemma(&[ac, not_ab, not_bc])
            .expect("transitivity fixture must plan");
        let mut audit = ProvenanceSurfaceAudit::default();
        plan.protect_surface_operands(&mut audit, &mut executor.ctx.terms);
        let mut active = HashMap::default();
        active.insert(not_ab, "(= (= late_euf_a late_euf_b) false)".to_string());
        assert!(!audit.validate_effective(&executor.ctx.terms, &active));
    }
}
