use veripb_rules::EqualsObjectiveRule;

use crate::prelude::*;

impl Checkable for EqualsObjectiveRule {
    fn compute(
        &mut self,
        context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<std::rc::Rc<veripb_formula::prelude::DBConstraint>>, CheckingError> {
        if let Some(objective) = &context.objective {
            if *objective == self.objective {
                Ok(vec![])
            } else {
                Err(CheckingError::ObjectivesNotEqual)
            }
        } else {
            Err(CheckingError::EqualObjectiveWithoutObjective)
        }
    }
}
