use std::rc::Rc;

use malachite_bigint::BigInt;
use veripb_formula::{pb_constraint::constraint_from_terms_and_coeff_sum, prelude::*};
use veripb_rules::{ObjectiveUpdateRule, ObjectiveUpdateType};

use crate::prelude::*;
use num_traits::{Signed, Zero};

// use super::ScopeId;

#[inline]
fn get_proofgoals(
    obj_rule: &ObjectiveUpdateRule,
    context: &Context,
) -> (Rc<DBConstraint>, Rc<DBConstraint>) {
    match obj_rule.update_type {
        ObjectiveUpdateType::New => {
            // Compute f_new >= f_old first and for f_old >= f_new the degree and the coefficients are just negated.
            let old_objective = context.objective.as_ref().unwrap();
            let new_geq_old_degree = old_objective.constant.clone() - &obj_rule.objective.constant;
            let old_geq_new_degree = -new_geq_old_degree.clone();
            let mut new_geq_old_terms = obj_rule
                .objective
                .terms
                .values()
                .cloned()
                .collect::<Vec<_>>();
            new_geq_old_terms.extend(
                old_objective
                    .terms
                    .values()
                    .map(|term| GeneralPBTerm::new(-term.coeff.clone(), term.lit)),
            );
            let old_geq_new_terms = new_geq_old_terms
                .iter()
                .map(|term| GeneralPBTerm::new(-term.coeff.clone(), term.lit))
                .collect::<Vec<_>>();
            let coeff_sum = new_geq_old_terms
                .iter()
                .fold(Zero::zero(), |sum: BigInt, term| sum + &term.coeff.abs());
            let new_geq_old_constraint = constraint_from_terms_and_coeff_sum(
                new_geq_old_terms,
                new_geq_old_degree,
                coeff_sum.clone(),
            );
            let old_geq_new_constraint = constraint_from_terms_and_coeff_sum(
                old_geq_new_terms,
                old_geq_new_degree,
                coeff_sum,
            );

            (
                Rc::new(new_geq_old_constraint.into()),
                Rc::new(old_geq_new_constraint.into()),
            )
        }
        ObjectiveUpdateType::Diff => {
            let coeff_abs_sum = obj_rule
                .objective
                .terms
                .values()
                .fold(Zero::zero(), |sum: BigInt, term| sum + &term.coeff.abs());

            // The proofgoal f_new >= f_old is just `diff_terms >= -diff_constant`.
            let new_geq_old_constraint = constraint_from_terms_and_coeff_sum(
                obj_rule.objective.terms.values().cloned().collect(),
                -obj_rule.objective.constant.clone(),
                coeff_abs_sum.clone(),
            );

            // The proofgoal f_old >= f_new is just `-diff_terms >= diff_constant`.
            let old_geq_new_constraint = constraint_from_terms_and_coeff_sum(
                obj_rule
                    .objective
                    .terms
                    .values()
                    .map(|term| GeneralPBTerm::new(-term.coeff.clone(), term.lit))
                    .collect(),
                obj_rule.objective.constant.clone(),
                coeff_abs_sum,
            );

            (
                Rc::new(new_geq_old_constraint.into()),
                Rc::new(old_geq_new_constraint.into()),
            )
        }
    }
}

impl Checkable for ObjectiveUpdateRule {
    #[inline]
    fn kernel_slot_taint(&self) -> &'static str {
        // `obju` stores no constraint, so this is never consumed; it names the
        // rule rather than a claim about it.
        "obju-unmodelled"
    }

    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        if context.objective.is_none() {
            return Err(CheckingError::ObjectiveUpdateNoObjective);
        }

        // We need to elaborate the obju rule line here, as autoproving might generate extra lines.
        if let Some(elaborator) = context.elaborator.as_mut() {
            elaborator.write_objective_update(
                self.update_type,
                &self.objective,
                &context.var_names,
            );
        }

        // Set up subproof subcontext.
        let mut subproof_context = SubproofContext::new(database.len());
        context.only_core = true;

        let (new_geq_old_constraint, old_geq_new_constraint) = get_proofgoals(self, context);

        subproof_context.add_single_proofgoal(new_geq_old_constraint, None);
        if context.trace_enabled {
            println!("  ** proofgoal from new objective >= old objective **");
            subproof_context.trace_internal_proofgoal_back(&context.var_names);
        }

        subproof_context.add_single_proofgoal(old_geq_new_constraint, None);
        if context.trace_enabled {
            println!("  ** proofgoal from old objective >= new objective **");
            subproof_context.trace_internal_proofgoal_back(&context.var_names);
        }

        // Start subproof and change to new objective.
        if self.has_subproof {
            // The update is applied at the `qed`, inside `finalize_unchecked`,
            // so the reference objective has to be captured HERE -- afterwards
            // the objective this run started with is gone. Whether the update
            // was verified is recorded at the `qed`, where the goals discharge.
            if context.config.kernel_verify {
                crate::kernel_bridge::capture_reference_objective(context);
            }
            subproof_context.objective_update = Some(std::mem::take(&mut self.objective));
            subproof_context.objective_update_type = self.update_type;
            context
                .subcontexts
                .push(Subcontext::Subproof(subproof_context));
        } else {
            // The two goals ARE the agreement `VeriPbCore.DbOkF.improve` needs:
            // `f_new >= f_old` and `f_old >= f_new`, both proved FROM the
            // database, which is exactly "the objectives agree on every model
            // of it". They discharge through the ordinary path, so anything
            // the kernel could not justify is already a skip -- and an
            // unchanged skip census across `finalize` is what says the
            // agreement was kernel-established rather than merely accepted.
            let before = context.kernel_stats.total_skips();
            crate::kernel_bridge::capture_reference_objective(context);
            subproof_context.finalize(context, database, &[])?;
            if context.config.kernel_verify {
                let verified = context.kernel_stats.total_skips() == before;
                crate::kernel_bridge::note_objective_update(context, verified);
            }
            context.update_objective(std::mem::take(&mut self.objective), self.update_type);
            context.only_core = false;
        }

        Ok(vec![])
    }
}
