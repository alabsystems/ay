use veripb_formula::prelude::*;
use veripb_rules::OrderFreshRightVariablesRule;

use crate::prelude::*;

impl Checkable for OrderFreshRightVariablesRule {
    #[inline]
    fn compute(
        &mut self,
        context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<std::rc::Rc<DBConstraint>>, CheckingError> {
        // Refuse a name an earlier `aux` list renamed for elaboration; version 3
        // does not admit the auxiliary spelling here. Checked before the
        // subcontext borrow, and before the `inside_vars` guard, because both
        // outcomes are refusals and this one needs `&Context`.
        crate::checker::refuse_renamed_auxiliary_name(context, &self.vars)?;
        // The list-declaration rules are legal only *inside* a `vars` block,
        // which is what `CheckingError::RuleOnlyAllowedInOrderVars` has always
        // said and what nothing checked: the guard was on the enclosing
        // subcontext alone, and a `vars ... end` leaves that subcontext open.
        // Every one of these rules overwrites its list outright, so a second
        // declaration written after `end vars` replaced a validated list with
        // an unvalidated one -- stepping around the symmetry check that
        // `end vars` performs, and the one `right` performs, by moving a line
        // one position. `load_order` then admitted an argument list as long as
        // the poisoned `left`, and every consumer zipped the two sides with
        // `izip!` and truncated to the shorter.
        if let Some(Subcontext::Transitivity(transitivity_context)) = context.subcontexts.last_mut()
        {
            if !transitivity_context.inside_vars {
                return Err(CheckingError::RuleOnlyAllowedInOrderVars);
            }

            transitivity_context.fresh_right = self.vars.clone();
            Ok(vec![])
        } else {
            Err(CheckingError::RuleOnlyAllowedInOrderVars)
        }
    }
}
