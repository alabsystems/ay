use std::rc::Rc;

use veripb_formula::prelude::*;
use veripb_rules::OrderVariablesRule;

use crate::{order_context::OrderPhase, prelude::*};

impl Checkable for OrderVariablesRule {
    #[inline]
    fn compute(
        &mut self,
        context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        match context.subcontexts.last_mut() {
            Some(Subcontext::Order(order_context)) => {
                // Only at the very start: re-opening `vars` after `def` would
                // re-pair `left` and `right` with names the definition
                // constraints do not mention. See `OrderPhase`.
                order_context.open_block("vars", &[OrderPhase::BeforeVars])?;
                order_context.inside_vars = true;
                Ok(vec![])
            }
            Some(Subcontext::Transitivity(transitivity_context)) => {
                transitivity_context.inside_vars = true;
                Ok(vec![])
            }
            _ => Err(CheckingError::VarsNotAllowedHere),
        }
    }
}
