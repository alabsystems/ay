use std::rc::Rc;

use veripb_formula::prelude::*;
use veripb_rules::{
    LoadOrderRule,
    elaboration::{ConstraintLookup, Elaboratable, ElaborationError, Elaborator},
};

use crate::{order::ActiveOrder, prelude::*};

#[derive(Debug)]
pub struct LoadOrderChecker {
    pub inner: LoadOrderRule,
    pub elaboration_required: bool,
}

impl LoadOrderChecker {
    pub fn new(inner: LoadOrderRule) -> Self {
        Self {
            inner,
            elaboration_required: true,
        }
    }
}

impl Checkable for LoadOrderChecker {
    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        // The argument list is read by version 3 with `is_aux_allowed = false`;
        // a variable an earlier `aux` list renamed cannot appear here. See
        // `checker::refuse_renamed_auxiliary_name_in_lits`.
        crate::checker::refuse_renamed_auxiliary_name_in_lits(context, &self.inner.lits)?;
        match &self.inner.name {
            Some(name) => match context.orders.get(name) {
                Some(order) => {
                    // Load order.
                    if order.left_vars.len() != self.inner.lits.len() {
                        return Err(CheckingError::OrderWrongNumberVariables(
                            order.left_vars.len(),
                            self.inner.lits.len(),
                        ));
                    }
                    database.move_to_core_all(&mut context.propagation_engine)?;

                    context.active_order = Some(ActiveOrder::new(order, self.inner.lits.clone()));
                    crate::kernel_bridge::note_order_loaded(context, Some(name));
                }
                None => return Err(CheckingError::OrderNotDefined(name.to_owned())),
            },
            None => {
                // Unload order.
                if context.active_order.is_none() {
                    self.elaboration_required = false;
                }
                context.active_order = None;
                crate::kernel_bridge::note_order_loaded(context, None);
            }
        }
        Ok(vec![])
    }
}

impl From<LoadOrderRule> for LoadOrderChecker {
    fn from(inner: LoadOrderRule) -> Self {
        Self::new(inner)
    }
}

impl Elaboratable for LoadOrderChecker {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        if self.elaboration_required {
            elaborator.write_load_order(self.inner.name.as_deref(), &self.inner.lits, var_lookup);
        }
        Ok(())
    }
}
