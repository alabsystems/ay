use std::rc::Rc;

use veripb_formula::prelude::*;
use veripb_rules::ImpliesRule;

use crate::prelude::*;

impl Checkable for ImpliesRule {
    #[inline]
    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        self.hint = Some(check_implication(
            context.only_core,
            &mut context.propagation_engine,
            database,
            &self.constraint,
            self.hint,
        )?);
        if context.config.kernel_verify {
            if let Some(id) = self.hint {
                if self.add_result {
                    // The conclusion is stored, so the proved reconstruction
                    // chain is run from the source's shadow slot and feeds
                    // the new slot (see `crate::kernel_bridge`).
                    crate::kernel_bridge::consume_implication_derivation(
                        context,
                        database,
                        id,
                        &self.constraint.constraint,
                    )?;
                } else {
                    let source = database.get_entry(id)?.constraint.clone();
                    match crate::kernel_bridge::verify_implication(
                        &source,
                        &self.constraint.constraint,
                    ) {
                        Ok(None) => context.kernel_stats.implication_verified += 1,
                        Ok(Some(reason)) => context.kernel_stats.skip(reason),
                        Err(err) => return Err(err),
                    }
                }
            }
        }

        if self.add_result {
            Ok(vec![self.constraint.clone()])
        } else {
            Ok(vec![])
        }
    }

    #[inline]
    fn get_returned_id(&self) -> Option<isize> {
        if self.add_result { None } else { self.hint }
    }

    #[inline]
    fn is_subproof_friendly(&self) -> bool {
        true
    }
}
