use std::rc::Rc;

use veripb_formula::prelude::*;
use veripb_rules::OrderReflexivityRule;

use crate::{
    order_context::{OrderPhase, ReflexivityContext},
    prelude::*,
};

impl Checkable for OrderReflexivityRule {
    #[inline]
    fn compute(
        &mut self,
        context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        // After `def` (and after `transitivity` if there is one), for the same
        // reason: the reflexivity obligations are the definition constraints
        // as they stand when the block opens. See `OrderPhase`.
        let Some(Subcontext::Order(order_context)) = context.subcontexts.last() else {
            return Err(CheckingError::OrderBlockOutOfSequence {
                block: "reflexivity",
                expected: "a `def_order` or `pre_order` context",
            });
        };
        order_context.open_block(
            "reflexivity",
            &[OrderPhase::Definition, OrderPhase::Transitivity],
        )?;
        context
            .subcontexts
            .push(Subcontext::Reflexivity(ReflexivityContext::default()));
        Ok(vec![])
    }
}
