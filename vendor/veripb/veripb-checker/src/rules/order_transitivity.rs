use std::rc::Rc;

use veripb_formula::prelude::*;
use veripb_rules::OrderTransitivityRule;

use crate::{
    order_context::{OrderPhase, TransitivityContext},
    prelude::*,
};

impl Checkable for OrderTransitivityRule {
    #[inline]
    fn compute(
        &mut self,
        context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        // After `def`, and once. `OrderProofRule` builds the transitivity
        // obligations by iterating the definition as it stands when `proof`
        // runs, so a `transitivity` block before `def` proves transitivity of
        // the empty relation -- and the order's `end` then trusts the flag it
        // set. See `OrderPhase`.
        let Some(Subcontext::Order(order_context)) = context.subcontexts.last() else {
            return Err(CheckingError::OrderBlockOutOfSequence {
                block: "transitivity",
                expected: "a `def_order` or `pre_order` context",
            });
        };
        order_context.open_block("transitivity", &[OrderPhase::Definition])?;
        context
            .subcontexts
            .push(Subcontext::Transitivity(TransitivityContext::default()));
        Ok(vec![])
    }
}
