use std::rc::Rc;

use veripb_formula::prelude::*;
use veripb_rules::DominanceBasedStrengtheningRule;

use crate::prelude::*;

use super::ScopeId;

impl Checkable for DominanceBasedStrengtheningRule {
    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        context.check_witness(&self.witness)?;

        // We need to elaborate the dom rule line here, as autoproving might generate extra lines.
        if let Some(elaborator) = context.elaborator.as_mut() {
            elaborator.write_dom_header(&self.constraint, &self.witness, &context.var_names);
        }

        let mut subproof_context = SubproofContext::new(database.len());
        let mut subproof_context_strict = SubproofContext::new(database.len());

        if context.objective.is_none() && context.active_order.is_none() {
            return Err(CheckingError::DominanceNoObjectiveOrOrder);
        }

        // Dominance stores a constraint that is not input-entailed, by the
        // same licence `red` uses. There is no shortcut path here, so this is
        // unconditional.
        context.witnessed_strengthening_used = true;

        // The kernel DOES model this now
        // (`VeriPbCore.dbOkF_dom_from_preorder`), and the offer is made where
        // the constraint is stored -- at the `qed` for the subproof form,
        // below for the auto-proved one -- never here, because this branch
        // returns the NEGATION first and the pending queue is consumed in
        // storage order.

        // Proofgoals from order.
        if let Some(active_order) = &mut context.active_order {
            let mut order_proofgoals = active_order.get_proofgoals_strict(&self.witness);
            if active_order.order.specification.is_empty() {
                for proofgoal in order_proofgoals {
                    subproof_context.add_internal_proofgoal(proofgoal);
                }
                if context.trace_enabled {
                    println!("  ** proofgoals from order **");
                    for id in 1..subproof_context.internal_proofgoal_len() {
                        subproof_context.trace_internal_proofgoal(id, &context.var_names);
                    }
                }
            } else {
                if !self.has_subproof {
                    subproof_context_strict.resize_internal(order_proofgoals.len());
                    subproof_context_strict.add_internal_proofgoal(order_proofgoals.pop().unwrap());
                }
                for proofgoal in order_proofgoals {
                    subproof_context.add_internal_proofgoal(proofgoal);
                }
            }
        }

        // Proofgoal from the objective.
        if let Some(objective) = &context.objective {
            if context.active_order.is_none() {
                subproof_context
                    .add_single_proofgoal(objective.get_proofgoal_strict(&self.witness), None);
            } else {
                subproof_context.add_single_proofgoal(
                    objective.get_proofgoal(&self.witness),
                    Some(ScopeId::LessEqual),
                );
            }
            if context.trace_enabled {
                println!("  ** proofgoal from objective **");
                subproof_context.trace_internal_proofgoal_back(&context.var_names);
            }
        }

        // Get database proofgoals.
        subproof_context.declare_database_obligations(Some(ScopeId::LessEqual));
        database.update_unique_index(&mut context.propagation_engine)?;
        let (goals, autodischarged) = database.get_proofgoals(
            &self.witness,
            false,
            context.elaborator.is_some(),
            false,
            context.config.kernel_verify,
        );
        // The slot each goal is about, paired with the substituted constraint
        // it is -- the same recovery `red` does, through the live ids
        // `copy_ids` carries onto a substituted image. `dom` asks
        // `get_proofgoals` with `add_derived_goals = false`, so only core ids
        // count here.
        // `dom` asks `get_proofgoals` with `add_derived_goals = false`
        // unconditionally, so derived slots never raise an obligation here.
        let derived_slots = crate::kernel_bridge::derived_slot_ids(database, false);
        let mut goal_slots: Vec<(usize, veripb_formula::prelude::PBConstraintEnum)> = Vec::new();
        let note =
            |source: &Rc<DBConstraint>,
             image: &Rc<DBConstraint>,
             out: &mut Vec<(usize, veripb_formula::prelude::PBConstraintEnum)>| {
                for &id in source.header.borrow().core_ids.iter() {
                    out.push((id, image.constraint.clone()));
                }
            };
        // Obligations proofgoal generation discharged by itself are re-judged
        // through the same entry points their explicit counterparts use.
        for discharged in &autodischarged {
            use crate::database::AutoDischarge;
            match discharged {
                AutoDischarge::Trivial(source, image)
                | AutoDischarge::Implied(source, image)
                | AutoDischarge::DbLookup(source, image, _) => note(source, image, &mut goal_slots),
            }
            crate::kernel_bridge::consume_autodischarge(context, discharged)?;
        }
        for constraint in goals {
            note(&constraint, &constraint, &mut goal_slots);
            subproof_context.add_database_proofgoal(constraint, false, Some(ScopeId::LessEqual));
        }
        if context.trace_enabled {
            subproof_context.trace_database_proofgoals(&context.var_names);
        }

        let skips_before = context.kernel_stats.total_skips();
        let negated = Rc::new(self.constraint.negate());

        if self.has_subproof {
            subproof_context.additional_hint = Some(database.len());
            context.inside_strengthening_subproof = true;

            subproof_context.to_add.push(self.constraint.clone());
            subproof_context.offers_dom_justification = true;
            subproof_context.red_goal_slots = std::mem::take(&mut goal_slots);
            subproof_context.red_derived_slots = derived_slots.clone();
            subproof_context.witness = std::mem::take(&mut self.witness);
            subproof_context.add_to_core = context.is_strengthening_to_core;
            context
                .subcontexts
                .push(Subcontext::Subproof(subproof_context));

            Ok(vec![negated])
        } else {
            // No subproof, so we have to autoprove the proofgoals.
            if let Some(elaborator) = context.elaborator.as_mut() {
                negated.set_out_id(0, elaborator.inc_id());
            }
            if context.active_order.is_some()
                && !context
                    .active_order
                    .as_ref()
                    .unwrap()
                    .order
                    .specification
                    .is_empty()
            {
                // Two contexts, one `dom` block: the `leq` scope and the
                // strict `geq` one both owe goals when the order carries a
                // specification. Only the second closes the block; see
                // `SubproofContext::suppress_closing_qed`.
                subproof_context.suppress_closing_qed = true;
                subproof_context.finalize(context, database, std::slice::from_ref(&negated))?;

                subproof_context_strict.finalize(context, database, &[negated])?;
            } else {
                subproof_context.finalize(context, database, &[negated])?;
            }

            // After every goal has discharged -- database side AND the strict
            // order side -- so an unchanged skip census says all of them were
            // kernel-justified.
            if context.config.kernel_verify {
                let discharged_cleanly = context.kernel_stats.total_skips() == skips_before;
                crate::kernel_bridge::offer_dom(
                    context,
                    &self.witness,
                    &self.constraint.constraint,
                    &goal_slots,
                    discharged_cleanly,
                    &derived_slots,
                );
            }

            Ok(vec![self.constraint.clone()])
        }
    }

    #[inline]
    fn kernel_slot_taint(&self) -> &'static str {
        // The NEGATED constraint this rule stores when it opens a subproof:
        // an ASSUMPTION the subproof discharges, not something the kernel
        // failed to justify. The rule's own constraint is offered and
        // justified separately, as in `red`.
        "dom-negation-premise"
    }

    #[inline]
    fn add_constraints_to_core(&self, context: &Context) -> bool {
        context.is_strengthening_to_core
    }
}
