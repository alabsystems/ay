use std::rc::Rc;

use veripb_formula::prelude::*;
use veripb_propagator::propagation_engine::PropagationEngine;
use veripb_rules::OrderSpecificationRule;

use crate::{
    order_context::{OrderPhase, SpecificationContext},
    prelude::*,
};

impl Checkable for OrderSpecificationRule {
    #[inline]
    fn compute(
        &mut self,
        context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        // Check that we are inside the order definition, at the one point in
        // its block sequence where a specification belongs: after `vars` and
        // before `def`. Written later, the specification would enter the order
        // without having been a premise of the proofs that are supposed to
        // hold under it.
        let Some(Subcontext::Order(order_context)) = context.subcontexts.last() else {
            return Err(CheckingError::SpecNotAllowedHere);
        };
        order_context.open_block("spec", &[OrderPhase::Variables])?;
        Ok(vec![])
    }

    #[inline]
    fn swaps_database(&self) -> bool {
        true
    }

    #[inline]
    fn get_new_database(&mut self) -> (Database, PropagationEngine) {
        (Database::new(), new_veripb_propagation_engine())
    }

    #[inline]
    fn handle_old_database(
        &mut self,
        context: &mut Context,
        database: Database,
        prop_engine: PropagationEngine,
    ) {
        // Same stacking as `def_order`: the specification runs on a fresh
        // empty database (see `crate::kernel_bridge`).
        crate::kernel_bridge::shadow_save(context);
        let mut specification_context = SpecificationContext::new(database, prop_engine);
        if let Some(elaborator) = context.elaborator.as_mut() {
            specification_context.stored_elaborator_id = elaborator.current_id;
            elaborator.current_id = 0;
        }
        context
            .subcontexts
            .push(Subcontext::Specification(specification_context));
    }
}
