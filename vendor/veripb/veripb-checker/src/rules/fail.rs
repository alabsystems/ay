use std::rc::Rc;

use veripb_formula::prelude::DBConstraint;
use veripb_rules::FailRule;

use crate::prelude::*;

impl Checkable for FailRule {
    fn compute(
        &mut self,
        _context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        Err(CheckingError::FailProofUsed)
    }
}
