use std::rc::Rc;

use veripb_formula::prelude::DBConstraint;
use veripb_rules::UnimplementedRule;

use crate::prelude::*;

impl Checkable for UnimplementedRule {
    fn compute(
        &mut self,
        _context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        Err(CheckingError::not_implemented(&self.feature))
    }

    #[inline]
    fn is_subproof_friendly(&self) -> bool {
        true
    }
}
