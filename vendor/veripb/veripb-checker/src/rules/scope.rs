use std::rc::Rc;

use veripb_formula::prelude::{DBConstraint, ToPrettyString};
use veripb_rules::{ScopeId, ScopeRule};

use crate::prelude::*;

impl Checkable for ScopeRule {
    #[inline]
    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        // The constraints a scope introduces are the order's *specification*,
        // derived inside `def_order` from the EMPTY formula. They are premises
        // about the order's auxiliary variables, and they are only a
        // conservative extension of the current database while those auxiliary
        // variables are unconstrained in it. Nothing else establishes that:
        // `$`-prefixed names are checked against the active order by
        // `checker::validate_aux_var`, but that check passes vacuously before
        // any `load_order` and passes by construction afterwards, so a plain
        // `red +1 ~$a >= 1 : $a -> 0` can put a constraint on an auxiliary
        // variable into the database either side of the `load_order`. The
        // specification then contradicts the database, and every proofgoal
        // inside the scope is discharged by RUP against a contradiction that
        // has nothing to do with the goal -- which refutes satisfiable
        // formulas.
        if let Some(active_order) = &context.active_order {
            if !active_order.order.specification.is_empty() {
                if let Some(&clashing) = active_order
                    .order
                    .aux_vars
                    .iter()
                    .find(|&&aux| database.var_occurs(aux))
                {
                    return Err(CheckingError::ScopeAuxVarNotFresh(
                        clashing.to_pretty_string(&context.var_names),
                    ));
                }
            }
        }

        if let Some(Subcontext::Subproof(subproof_context)) = context.subcontexts.last_mut() {
            let premises = if let Some(active_order) = &mut context.active_order {
                match self.id {
                    ScopeId::LessEqual => {
                        active_order.get_specification_less_equal(&subproof_context.witness)
                    }
                    ScopeId::GreaterEqual => {
                        active_order.get_specification_greater_equal(&subproof_context.witness)
                    }
                }
            } else {
                vec![]
            };

            if subproof_context.current_scope.is_some() {
                return Err(CheckingError::StartScopeWhileOtherScopeOpen);
            }
            subproof_context.scope_start_id = database.len();
            subproof_context.current_scope = Some(self.id);

            Ok(premises)
        } else {
            Err(CheckingError::ScopeOutsideSubproof)
        }
    }

    #[inline]
    fn kernel_slot_taint(&self) -> &'static str {
        // A scope introduces the dominance subproof's premises: assumptions
        // for the duration of the subproof, not constraints entailed by the
        // formula, and the dominance meta-step that discharges them is
        // outside the proved kernel (the development design notes section 5, item 5).
        "scope-premise"
    }

    #[inline]
    fn is_subproof_friendly(&self) -> bool {
        true
    }
}
