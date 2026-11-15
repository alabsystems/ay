use std::rc::Rc;

use veripb_formula::prelude::DBConstraint;
use veripb_rules::{IdentifierOption, MoveToCoreRule};

use crate::prelude::*;

impl Checkable for MoveToCoreRule {
    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        match self.identifier_option {
            IdentifierOption::Id => {
                for index in self.constraint_ids.iter_mut() {
                    *index = database.normalize_id(*index);
                    database.move_to_core(&mut context.propagation_engine, *index as usize)?;
                }
            }
            IdentifierOption::Range => {
                // Normalize constraint IDs to get rid of negative IDs.
                let range = {
                    let lower_bound = database.normalize_id(self.constraint_ids[0]) as usize;
                    let upper_bound = database.normalize_id(self.constraint_ids[1]) as usize;
                    lower_bound..upper_bound
                };

                self.constraint_ids = database
                    .get_undeleted(range)
                    .map(|result_id| result_id.map(|id| id as isize))
                    .collect::<Result<_, CheckingError>>()?;

                // Actually move the constraints between first and second ID in the vector to core.
                for &index in self.constraint_ids.iter() {
                    database.move_to_core(&mut context.propagation_engine, index as usize)?;
                }
            }
            IdentifierOption::Specification => unreachable!(),
        }

        Ok(vec![])
    }
}
