use std::rc::Rc;

use veripb_formula::prelude::*;
use veripb_rules::OrderDefRule;

use crate::{order_context::OrderPhase, prelude::*};

impl Checkable for OrderDefRule {
    #[inline]
    fn compute(
        &mut self,
        context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        if let Some(Subcontext::Order(order_context)) = context.subcontexts.last_mut() {
            order_context.open_block("def", &[OrderPhase::Variables, OrderPhase::Specification])?;
            order_context.inside_def = true;
            Ok(vec![])
        } else {
            Err(CheckingError::DefNotAllowedHere)
        }
    }
}
