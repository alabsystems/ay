use std::{num::NonZeroUsize, rc::Rc};

use colored::Colorize;
use veripb_formula::{prelude::*, propagation::RUPHint};
use veripb_rules::RUPRule;

use crate::prelude::*;

fn trace_failed_with_hints(
    rup_rule: &RUPRule,
    database: &Database,
    context: &mut Context,
    negated: DBConstraint,
) {
    context.annotated_rup_assignment.reset();

    println!("Propagation check failed! The propagation had the following trail:");
    println!("  propagations in format: <assignment> (<reason constraint>)");

    let mut any_propagation = false;
    loop {
        let mut unchanged = true;
        for id in rup_rule.hint.as_ref().unwrap().iter() {
            let id = database.normalize_id(*id);
            if id == 0 {
                for lit in negated.traced_propagate(&mut context.annotated_rup_assignment) {
                    unchanged = false;
                    any_propagation = true;
                    println!(
                        "    {} ({})",
                        lit.to_pretty_string(&context.var_names).purple(),
                        negated.to_pretty_string(&context.var_names).cyan(),
                    )
                }
            } else {
                let constraint = database.get_entry_usize(id as usize).unwrap();
                for lit in constraint.traced_propagate(&mut context.annotated_rup_assignment) {
                    unchanged = false;
                    any_propagation = true;
                    println!(
                        "    {} ({})",
                        lit.to_pretty_string(&context.var_names).purple(),
                        constraint.to_pretty_string(&context.var_names).cyan(),
                    )
                }
            };
        }
        if unchanged {
            if !any_propagation {
                // See the matching note in `PropagationEngine::trace_failed`: an empty trail
                // is the diagnosis, so state it rather than printing a bare header.
                println!(
                    "    {}",
                    "(no propagations: asserting the negation of this constraint left every \
                     hinted constraint with slack >= 1, so unit propagation had nothing to \
                     derive and stopped immediately)"
                        .yellow()
                );
                println!(
                    "    {}",
                    "hint: a single 'rup' step cannot justify this constraint; derive it \
                     explicitly with 'pol' instead"
                        .yellow()
                );
            }
            return;
        }
    }
}

impl Checkable for RUPRule {
    #[inline]
    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        match &self.hint {
            None => {
                // Do unit propagation check to see if constraint is implied.
                // Subproofs run on freshly swapped-in engines, so the
                // certificate-collection flag is (re)asserted here rather
                // than trusted from engine construction.
                context.propagation_engine.collect_kernel_certificate =
                    context.config.kernel_verify;
                database.update_propagation_index(&mut context.propagation_engine)?;
                if context
                    .propagation_engine
                    .reverse_unit_propagation_check(
                        &context.var_names,
                        &[],
                        Some(&self.constraint),
                        context.only_core,
                        context.elaborator.is_some(),
                        context.config.trace_failed,
                    )?
                    .is_conflict()
                {
                    crate::kernel_bridge::consume_rup_derivation(
                        context,
                        database,
                        &self.constraint.constraint,
                    )?;
                    if let Some(elaborator) = context.elaborator.as_mut() {
                        elaborator.write_rup_step(
                            &self.constraint.constraint,
                            &context.propagation_engine.rup_hints,
                            &context.var_names,
                        );
                    }
                    Ok(vec![self.constraint.clone()])
                } else {
                    Err(CheckingError::NotRUP(context.only_core))
                }
            }
            Some(hint) => {
                // Do propagation based on the constraint IDs given as hint.
                context.annotated_rup_assignment.reset();
                context
                    .annotated_rup_assignment
                    .resize(context.var_names.len());
                context.annotated_rup_hints.clear();
                let negated = self.constraint.negate();

                loop {
                    let mut unchanged = true;
                    for id in hint {
                        let id = database.normalize_id(*id);
                        if id == 0 {
                            match negated.propagate(&mut context.annotated_rup_assignment) {
                                ConstraintPropagationResult::Conflict => {
                                    kernel_verify_hinted(
                                        context,
                                        database,
                                        hint,
                                        &self.constraint,
                                    )?;
                                    if let Some(elaborator) = context.elaborator.as_mut() {
                                        context.annotated_rup_hints.push(RUPHint::NegatedPremise);
                                        elaborator.write_rup_step(
                                            &self.constraint.constraint,
                                            &context.annotated_rup_hints,
                                            &context.var_names,
                                        );
                                    }
                                    return Ok(vec![self.constraint.clone()]);
                                }
                                ConstraintPropagationResult::NoPropagation => {}
                                ConstraintPropagationResult::Propagated => {
                                    unchanged = false;
                                    if context.elaborator.is_some() {
                                        context.annotated_rup_hints.push(RUPHint::NegatedPremise);
                                    }
                                }
                            }
                        } else {
                            let constraint = database.get_entry_usize(id as usize)?;
                            if context.only_core && !constraint.is_core_constraint_id(id as usize) {
                                return Err(CheckingError::CoreSubproofUsingNonCoreConstraint(id));
                            }
                            match constraint.propagate(&mut context.annotated_rup_assignment) {
                                ConstraintPropagationResult::Conflict => {
                                    kernel_verify_hinted(
                                        context,
                                        database,
                                        hint,
                                        &self.constraint,
                                    )?;
                                    if let Some(elaborator) = context.elaborator.as_mut() {
                                        context.annotated_rup_hints.push(RUPHint::ConstraintId(
                                            NonZeroUsize::new(
                                                constraint
                                                    .get_out_id(constraint.get_some_id())
                                                    .expect("should have output ID"),
                                            )
                                            .expect("should be non-zero"),
                                        ));
                                        elaborator.write_rup_step(
                                            &self.constraint.constraint,
                                            &context.annotated_rup_hints,
                                            &context.var_names,
                                        );
                                    }
                                    return Ok(vec![self.constraint.clone()]);
                                }
                                ConstraintPropagationResult::NoPropagation => {}
                                ConstraintPropagationResult::Propagated => {
                                    unchanged = false;
                                    if context.elaborator.is_some() {
                                        context.annotated_rup_hints.push(RUPHint::ConstraintId(
                                            NonZeroUsize::new(
                                                constraint
                                                    .get_out_id(constraint.get_some_id())
                                                    .expect("should have output ID"),
                                            )
                                            .expect("should be non-zero"),
                                        ))
                                    }
                                }
                            }
                        };
                    }
                    if unchanged {
                        if context.config.trace_failed {
                            trace_failed_with_hints(self, database, context, negated);
                        }
                        return Err(CheckingError::NotRUP(context.only_core));
                    }
                }
            }
        }
    }

    #[inline]
    fn is_subproof_friendly(&self) -> bool {
        true
    }
}

/// Kernel-verify a hinted RUP acceptance: replay propagation over exactly the
/// hinted constraints through the proved kernel (see `crate::kernel_bridge`).
fn kernel_verify_hinted(
    context: &mut Context,
    database: &Database,
    hint: &[isize],
    target: &Rc<DBConstraint>,
) -> Result<(), CheckingError> {
    if !context.config.kernel_verify {
        return Ok(());
    }
    let mut hinted = Vec::new();
    for id in hint {
        let id = database.normalize_id(*id);
        if id == 0 {
            continue;
        }
        match database.get_entry_usize(id as usize) {
            // The id travels with the constraint so the bridge can find its
            // shadow slot without going back through the header.
            Ok(rc) => hinted.push((id as usize, rc.clone())),
            // The live loop resolves hint ids lazily and returns at the
            // first conflict, so a trailing id may be deleted or out of
            // range without ever having been used. Everything the live loop
            // actually consumed precedes the first unresolvable id, so the
            // replay simply stops the list here.
            Err(_) => break,
        }
    }
    crate::kernel_bridge::consume_hinted_rup(context, database, &hinted, &target.constraint)
}
