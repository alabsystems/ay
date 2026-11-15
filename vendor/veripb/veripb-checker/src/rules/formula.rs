use std::rc::Rc;

use veripb_formula::prelude::DBConstraint;
use veripb_rules::FormulaCheck;

use crate::prelude::*;

impl Checkable for FormulaCheck {
    #[inline]
    fn compute(
        &mut self,
        _context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        if database.size() != self.size {
            return Err(CheckingError::formula_size_mismatch(
                database.size(),
                self.size,
            ));
        }
        Ok(vec![])
    }
}
