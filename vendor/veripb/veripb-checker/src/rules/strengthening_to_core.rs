use std::rc::Rc;

use veripb_formula::prelude::DBConstraint;
use veripb_rules::StrengtheningToCoreRule;

use crate::prelude::*;

impl Checkable for StrengtheningToCoreRule {
    #[inline]
    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        // Check if strengthening to core mode is actually changed.
        if self.enable {
            if context.is_strengthening_to_core {
                log::warn!(
                    "Enabling strengthening to core mode, which was already enabled. Maybe this is not intentional and hints towards an error."
                );
            }
            database.move_to_core_all(&mut context.propagation_engine)?;
        } else if !context.is_strengthening_to_core {
            log::warn!(
                "Disabling strengthening to core mode, which was already disabled. Maybe this is not intentional and hints towards an error."
            );
        }

        // Change the strengthening to core mode.
        context.is_strengthening_to_core = self.enable;

        Ok(vec![])
    }
}
