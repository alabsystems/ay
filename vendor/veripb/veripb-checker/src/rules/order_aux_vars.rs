use veripb_formula::prelude::*;
use veripb_rules::OrderAuxVariablesRule;

use crate::prelude::*;

impl Checkable for OrderAuxVariablesRule {
    #[inline]
    fn compute(
        &mut self,
        context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<std::rc::Rc<DBConstraint>>, CheckingError> {
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
        if let Some(Subcontext::Order(order_context)) = context.subcontexts.last_mut() {
            if !order_context.inside_vars {
                return Err(CheckingError::RuleOnlyAllowedInOrderVars);
            }

            order_context.aux_vars_defined = true;
            order_context.constructed_order.aux_vars = self.vars.clone();

            if order_context.constructed_order.set_variables(
                crate::order_context::OrderVariableKind::Auxiliary,
                self.vars.as_slice(),
            ) {
                return Err(CheckingError::OrderVariablesNonDistinct);
            }
        } else {
            return Err(CheckingError::RuleOnlyAllowedInOrderVars);
        }

        // Version 2.0 cannot spell an auxiliary variable the way version 3.0
        // requires, and elaboration emits version 3.0. Runs after the checks
        // above so that a misplaced or non-distinct `aux` still reports itself
        // rather than a naming problem.
        crate::checker::give_version3_auxiliary_names(context, &self.vars)?;
        Ok(vec![])
    }
}
