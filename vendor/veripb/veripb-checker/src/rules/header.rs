use std::rc::Rc;

use veripb_formula::prelude::DBConstraint;
use veripb_rules::HeaderRule;

use crate::prelude::*;

impl Checkable for HeaderRule {
    #[inline]
    fn compute(
        &mut self,
        context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        if context.major_version.unwrap() < 2 {
            return Err(CheckingError::UnsupportedProofVersion);
        }
        Ok(vec![])
    }
}
