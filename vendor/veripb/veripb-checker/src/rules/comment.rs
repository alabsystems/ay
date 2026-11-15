use std::rc::Rc;

use veripb_formula::prelude::DBConstraint;
use veripb_rules::Comment;

use crate::prelude::*;

impl Checkable for Comment {
    #[inline]
    fn compute(
        &mut self,
        _context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        Ok(vec![])
    }

    #[inline]
    fn is_subproof_friendly(&self) -> bool {
        true
    }
}
