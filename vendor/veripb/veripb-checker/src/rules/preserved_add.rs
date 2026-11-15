use std::rc::Rc;

use ahash::AHashSet;
use colored::Colorize;
use veripb_formula::prelude::*;
use veripb_rules::PreservedAddRule;

use crate::prelude::*;

/// Check if the constraint justifying the addition of the variable does not contain the added variable and if it only contains prserved variables.
fn check_constraint_vars(
    pres_add_rule: &PreservedAddRule,
    var_names: &VarNameManager,
    preserved_vars: &AHashSet<VarIdx>,
) -> Result<(), CheckingError> {
    match &pres_add_rule.constraint.constraint {
        PBConstraintEnum::Clause(clause) => {
            for lit in clause.get_lits() {
                let var = lit.get_var();
                if var == pres_add_rule.var {
                    return Err(CheckingError::PreservedAddVariableInConstraint);
                }
                if !preserved_vars.contains(&var) {
                    return Err(CheckingError::PreservedAddConstraintVariableNotPreserved(
                        var.to_pretty_string(var_names).bold(),
                    ));
                }
            }
        }
        PBConstraintEnum::Cardinality(cardinality) => {
            for lit in cardinality.get_lits() {
                let var = lit.get_var();
                if var == pres_add_rule.var {
                    return Err(CheckingError::PreservedAddVariableInConstraint);
                }
                if !preserved_vars.contains(&var) {
                    return Err(CheckingError::PreservedAddConstraintVariableNotPreserved(
                        var.to_pretty_string(var_names).bold(),
                    ));
                }
            }
        }
        PBConstraintEnum::GeneralPBI64(constraint) => {
            for lit in constraint.get_lits() {
                let var = lit.get_var();
                if var == pres_add_rule.var {
                    return Err(CheckingError::PreservedAddVariableInConstraint);
                }
                if !preserved_vars.contains(&var) {
                    return Err(CheckingError::PreservedAddConstraintVariableNotPreserved(
                        var.to_pretty_string(var_names).bold(),
                    ));
                }
            }
        }
        PBConstraintEnum::GeneralPBI128(constraint) => {
            for lit in constraint.get_lits() {
                let var = lit.get_var();
                if var == pres_add_rule.var {
                    return Err(CheckingError::PreservedAddVariableInConstraint);
                }
                if !preserved_vars.contains(&var) {
                    return Err(CheckingError::PreservedAddConstraintVariableNotPreserved(
                        var.to_pretty_string(var_names).bold(),
                    ));
                }
            }
        }
        PBConstraintEnum::GeneralPBBigInt(constraint) => {
            for lit in constraint.get_lits() {
                let var = lit.get_var();
                if var == pres_add_rule.var {
                    return Err(CheckingError::PreservedAddVariableInConstraint);
                }
                if !preserved_vars.contains(&var) {
                    return Err(CheckingError::PreservedAddConstraintVariableNotPreserved(
                        var.to_pretty_string(var_names).bold(),
                    ));
                }
            }
        }
    }
    Ok(())
}

impl Checkable for PreservedAddRule {
    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        context.preserved_set_changed = true;
        if let Some(preserved_vars) = &mut context.preserved_variables {
            // Check preconditions.
            if preserved_vars.contains(&self.var) {
                return Err(CheckingError::PreservedAddVariableAlreadyInSet);
            }
            check_constraint_vars(self, &context.var_names, preserved_vars)?;

            // Elaborate proof here, since autoproving adds elaborated proof directly.
            if let Some(elaborator) = &mut context.elaborator {
                elaborator.write_preserved_add(self.var, &self.constraint, &context.var_names);
            }

            // Add proofgoals.
            let mut subproof_context = SubproofContext::new(database.len());
            context.only_core = true;

            let var_impl_constraint = self
                .constraint
                .get_reification(self.var, ReificationDir::VarImplIneq);
            subproof_context.add_single_proofgoal(Rc::new(var_impl_constraint.into()), None);
            if context.trace_enabled {
                println!("  ** proofgoal for variable ==> constraint **");
                subproof_context.trace_internal_proofgoal_back(&context.var_names);
            }

            let constraint_impl_var = self
                .constraint
                .get_reification(self.var, ReificationDir::IneqImplVar);
            subproof_context.add_single_proofgoal(Rc::new(constraint_impl_var.into()), None);
            if context.trace_enabled {
                println!("  ** proofgoal for variable <== constraint **");
                subproof_context.trace_internal_proofgoal_back(&context.var_names);
            }

            // The reification proofgoals below are kernel-checked one by one
            // like any other proofgoal, but the *licence* they buy — that a
            // variable reified by an entailed equivalence may be added to the
            // preserved set without changing what the proof enumerates — is a
            // claim about preserved-set semantics, which the proved kernel
            // does not model at all (the development design notes section 5, item 5).
            // Counted so the summary cannot report full coverage on a run
            // this rule decided.
            if context.config.kernel_verify {
                context.kernel_stats.skip("preserved-set-unmodelled");
            }

            // Update preserved set.
            preserved_vars.insert(self.var);

            // Start subproof.
            if self.has_subproof {
                context
                    .subcontexts
                    .push(Subcontext::Subproof(subproof_context));
            } else {
                subproof_context.finalize(context, database, &[])?;
                context.only_core = false;
            }

            // Trace updated preserved set.
            if context.trace_enabled {
                context.print_preserved_set();
            }

            Ok(vec![])
        } else {
            Err(CheckingError::PreservedAddNoPreserved)
        }
    }
}
