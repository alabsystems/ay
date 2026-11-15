use std::rc::Rc;

use veripb_formula::prelude::*;
use veripb_rules::IsDeletedCheck;

use crate::prelude::*;

impl Checkable for IsDeletedCheck {
    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        database.update_unique_index(&mut context.propagation_engine)?;
        if database.lookup(&self.constraint).is_some() {
            Err(CheckingError::DeletedConstraintInDB)
        } else {
            Ok(vec![])
        }
    }
}
