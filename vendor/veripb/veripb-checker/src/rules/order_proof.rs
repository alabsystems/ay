use std::rc::Rc;

use veripb_formula::prelude::DBConstraint;
use veripb_rules::OrderProofRule;

use crate::prelude::*;

impl Checkable for OrderProofRule {
    #[inline]
    fn kernel_slot_taint(&self) -> &'static str {
        // The order's transitivity/reflexivity premises, assumed inside the
        // order-definition sub-database. The kernel has no order model.
        "order-proof-premise"
    }

    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        let mut subproof_context = SubproofContext::new(database.len());
        let (last_subcontext, subcontexts) = match context.subcontexts.split_last_mut() {
            Some((last, subcontexts)) => (last, subcontexts),
            None => return Err(CheckingError::ProofOnlyInReflexivityOrTransitivity),
        };
        let order_context = match subcontexts.last() {
            Some(Subcontext::Order(order)) => order,
            _ => return Err(CheckingError::ProofOnlyInReflexivityOrTransitivity),
        };
        let mut premises = Vec::new();

        match last_subcontext {
            Subcontext::Reflexivity(reflexivity) => {
                if reflexivity.is_proven {
                    return Err(CheckingError::ReflexivityAlreadyProven);
                }
                reflexivity.is_proven = true;
                let reflexivity_substitution = order_context.get_reflexivity_substitution();

                // Get the additional premises for reflexivity.
                for constraint in order_context.constructed_order.specification.iter() {
                    premises.push(Rc::new(constraint.substitute(&reflexivity_substitution)));
                }

                // Get the proofgoals for reflexivity.
                for constraint in order_context.constructed_order.definition.iter() {
                    let proofgoal = Rc::new(constraint.substitute(&reflexivity_substitution));
                    subproof_context.add_single_proofgoal(proofgoal, None);
                }
                if context.trace_enabled {
                    println!("  ** proofgoals for reflexivity **");
                    subproof_context.trace_all_internal_proofgoals(&context.var_names);
                }
            }
            Subcontext::Transitivity(transitivity) => {
                if transitivity.is_proven {
                    return Err(CheckingError::TransitivityAlreadyProven);
                }
                transitivity.is_proven = true;
                // The fresh variable lists are what makes the goals below the
                // *transitivity* statement rather than a tautology; nothing
                // else validates them, and `get_transitivity_substitution`
                // truncates silently when they are too short.
                order_context.check_transitivity_variables(transitivity, &context.var_names)?;
                let (transitivity_substitution_y_z, transitivity_substitution_x_z) =
                    order_context.get_transitivity_substitution(transitivity);

                // Get additional premises from the specification.
                for constraint in order_context.constructed_order.specification.iter() {
                    premises.push(Rc::new(DBConstraint::from(constraint.constraint.clone())));
                }
                for constraint in order_context.constructed_order.specification.iter() {
                    premises.push(Rc::new(
                        constraint.substitute(&transitivity_substitution_y_z),
                    ));
                }
                for constraint in order_context.constructed_order.specification.iter() {
                    premises.push(Rc::new(
                        constraint.substitute(&transitivity_substitution_x_z),
                    ));
                }

                // Get additional premises and proofgoals from definition constraints.
                for constraint in order_context.constructed_order.definition.iter() {
                    premises.push(constraint.clone());
                    let proofgoal = Rc::new(constraint.substitute(&transitivity_substitution_x_z));
                    subproof_context.add_single_proofgoal(proofgoal, None);
                }
                for constraint in order_context.constructed_order.definition.iter() {
                    premises.push(Rc::new(
                        constraint.substitute(&transitivity_substitution_y_z),
                    ));
                }
                if context.trace_enabled {
                    println!("  ** proofgoals for transitivity **");
                    subproof_context.trace_all_internal_proofgoals(&context.var_names);
                }
            }
            _ => return Err(CheckingError::ProofOnlyInReflexivityOrTransitivity),
        }

        context
            .subcontexts
            .push(Subcontext::Subproof(subproof_context));

        // Add premise constraints
        Ok(premises)
    }
}
