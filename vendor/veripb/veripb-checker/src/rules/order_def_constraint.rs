use std::rc::Rc;

use veripb_formula::prelude::*;
use veripb_rules::OrderDefConstraintRule;

use crate::prelude::*;

impl Checkable for OrderDefConstraintRule {
    #[inline]
    fn compute(
        &mut self,
        context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        if let Some(Subcontext::Order(order_context)) = context.subcontexts.last_mut() {
            let contains_only_order_vars = match &self.constraint.constraint {
                PBConstraintEnum::Clause(clause) => clause.get_lits().all(|lit| {
                    order_context
                        .constructed_order
                        .is_order_variable(lit.get_var())
                }),
                PBConstraintEnum::Cardinality(cardinality) => cardinality.get_lits().all(|lit| {
                    order_context
                        .constructed_order
                        .is_order_variable(lit.get_var())
                }),
                PBConstraintEnum::GeneralPBI64(constraint) => constraint.get_lits().all(|lit| {
                    order_context
                        .constructed_order
                        .is_order_variable(lit.get_var())
                }),
                PBConstraintEnum::GeneralPBI128(constraint) => constraint.get_lits().all(|lit| {
                    order_context
                        .constructed_order
                        .is_order_variable(lit.get_var())
                }),
                PBConstraintEnum::GeneralPBBigInt(constraint) => constraint.get_lits().all(|lit| {
                    order_context
                        .constructed_order
                        .is_order_variable(lit.get_var())
                }),
            };
            if contains_only_order_vars {
                order_context
                    .constructed_order
                    .definition
                    .push(self.constraint.clone());
                Ok(vec![])
            } else {
                Err(CheckingError::UndeclaredVariablesInOrder)
            }
        } else {
            Err(CheckingError::OnlyAllowedInOrderDef)
        }
    }
}
