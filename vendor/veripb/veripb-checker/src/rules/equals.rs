use std::rc::Rc;

use veripb_formula::prelude::DBConstraint;
use veripb_rules::EqualsRule;

use crate::prelude::*;

impl Checkable for EqualsRule {
    #[inline]
    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        // The found database constraint, kept so the kernel bridge can reach
        // its shadow slot when `ea` stores a copy of it.
        let found: Rc<DBConstraint>;
        match self.hint.as_mut() {
            None => {
                database.update_unique_index(&mut context.propagation_engine)?;
                if let Some(constraint) = database.lookup(&self.constraint) {
                    if !context.only_core || constraint.is_core_constraint() {
                        found = Rc::clone(constraint);
                        self.hint = Some(found.get_some_id() as isize);
                    } else {
                        return Err(CheckingError::not_found(&self.constraint, true));
                    }
                } else {
                    return Err(CheckingError::not_found(&self.constraint, false));
                }
            }
            Some(index) => {
                *index = database.normalize_id(*index);
                let constraint = database.get_entry_usize(*index as usize)?;
                if context.only_core && !constraint.is_core_constraint_id(*index as usize) {
                    return Err(CheckingError::CoreSubproofUsingNonCoreConstraint(*index));
                }
                if *constraint != self.constraint {
                    return Err(CheckingError::not_equal(&self.constraint, constraint));
                }
                found = Rc::clone(constraint);
            }
        }
        if self.add_result {
            // `ea` stores a copy of the found constraint, so the accept also
            // feeds the shadow database with that id's slot.
            crate::kernel_bridge::consume_db_lookup_derivation(
                context,
                database,
                &self.constraint.constraint,
                &found,
            )?;
        } else {
            crate::kernel_bridge::consume_db_lookup(
                context,
                &self.constraint.constraint,
                &found.constraint,
            )?;
        }
        if self.add_result {
            Ok(vec![self.constraint.clone()])
        } else {
            Ok(vec![])
        }
    }

    #[inline]
    fn get_returned_id(&self) -> Option<isize> {
        self.hint
    }

    #[inline]
    fn is_subproof_friendly(&self) -> bool {
        true
    }
}
