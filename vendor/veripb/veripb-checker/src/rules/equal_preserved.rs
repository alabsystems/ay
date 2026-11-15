use std::rc::Rc;

use ahash::AHashSet;
use veripb_formula::prelude::*;
use veripb_rules::PreservedEqualsRule;

use crate::prelude::*;

impl Checkable for PreservedEqualsRule {
    fn compute(
        &mut self,
        context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        if let Some(preserved_vars) = &context.preserved_variables {
            let vars_set = AHashSet::from_iter(self.vars.iter().cloned());
            if vars_set == *preserved_vars {
                // The rule asserts an equality between the checker's own
                // preserved set and a listed one. The proved kernel has no
                // preserved-set model (the development design notes section 5, item 5),
                // so there is nothing to re-derive — counted rather than
                // passed over in silence.
                if context.config.kernel_verify {
                    context.kernel_stats.skip("preserved-set-unmodelled");
                }
                Ok(vec![])
            } else {
                // Both lists are sorted by `missing_vars_message`; taking
                // either set in hash order made this refusal name its
                // variables in a different order on every run.
                let missing_vars = crate::utils::missing_vars_message(
                    preserved_vars,
                    &vars_set,
                    &context.var_names,
                );
                let additional_vars = crate::utils::missing_vars_message(
                    &vars_set,
                    preserved_vars,
                    &context.var_names,
                );
                Err(CheckingError::PreservedEqualsSetMismatch(
                    missing_vars,
                    additional_vars,
                ))
            }
        } else {
            Err(CheckingError::PreservedEqualsNoPreservedSetKnown)
        }
    }
}
