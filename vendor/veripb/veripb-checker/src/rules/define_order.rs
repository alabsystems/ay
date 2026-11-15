use std::rc::Rc;

use veripb_formula::prelude::*;
use veripb_propagator::propagation_engine::PropagationEngine;
use veripb_rules::DefineOrderRule;

use crate::{order_context::OrderContext, prelude::*};

impl Checkable for DefineOrderRule {
    #[inline]
    fn compute(
        &mut self,
        _context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
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
        // The order definition runs on a fresh empty database, so the kernel
        // shadow stacks the outer slots and mirrors the sub-database from
        // empty; `end subproof` restores it (see `crate::kernel_bridge`).
        crate::kernel_bridge::shadow_save(context);
        let mut order_context = OrderContext::new(
            std::mem::take(&mut self.name),
            database,
            prop_engine,
            std::mem::take(&mut context.active_order),
        );
        order_context.kernel_skips_at_open = context.kernel_stats.total_skips();
        if let Some(elaborator) = context.elaborator.as_mut() {
            order_context.stored_elaborator_id = elaborator.current_id;
            elaborator.current_id = 0;
        }
        context.subcontexts.push(Subcontext::Order(order_context));
    }
}
