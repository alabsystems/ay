use veripb_formula::prelude::*;
use veripb_rules::OrderFreshAux1Rule;

use crate::prelude::*;

impl Checkable for OrderFreshAux1Rule {
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
        if let Some(Subcontext::Transitivity(transitivity_context)) = context.subcontexts.last_mut()
        {
            if !transitivity_context.inside_vars {
                return Err(CheckingError::RuleOnlyAllowedInOrderVars);
            }

            transitivity_context.fresh_aux_1 = self.vars.clone();
        } else {
            return Err(CheckingError::RuleOnlyAllowedInOrderVars);
        }

        // `fresh_aux_1` is read by the version-3 grammar with the same
        // "auxiliary variables only" rule as `aux`, so it needs the same
        // version-3 spelling in the elaborated proof.
        crate::checker::give_version3_auxiliary_names(context, &self.vars)?;
        Ok(vec![])
    }
}
