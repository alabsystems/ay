//! This submodule contains useful helper functions that can be used in multiple places for the checker.

use std::rc::Rc;

use ahash::AHashSet;
use itertools::Itertools;
use veripb_formula::prelude::*;
use veripb_propagator::propagation_engine::{
    CORE_CLAUSES_CARD, CORE_GENERAL, DERIVED_CLAUSES_CARD, DERIVED_GENERAL, PropagationEngine,
};
use veripb_rules::SolutionRuleOutput;

use crate::prelude::*;

/// The variables of `left` that are missing from `right`, named and listed in
/// ascending variable order.
///
/// Sorted rather than taken in hash order, because the sets this is called on
/// (`Context::preserved_variables` and the sets a rule or an output file
/// lists) are `AHashSet`s, and `ahash`'s default `RandomState` seeds itself
/// from runtime randomness once per process. Iterating one straight into the
/// message made the *reason a proof was refused* vary from run to run:
/// measured before this, a `epreserved` whose set disagrees on six variables
/// printed twelve distinct messages over twelve runs, and an `output` whose
/// preserved set disagrees printed ten distinct messages over ten runs. The
/// refusal itself, its error variant and the exit code were always the same —
/// only the order the variables were named in moved.
///
/// That is not a wrong verdict, but a diagnostic that is not a function of its
/// input cannot be diffed or regression-tested, and these are the least
/// travelled paths in the checker: a defect that shows up under one hash order
/// and not another is flaky rather than absent. Ascending order is also what a
/// reader wants, and what the `preserved:` line of an OPB file is written in.
///
/// See `tests/observable_output_deterministic.rs`.
#[inline]
pub fn missing_vars_message<V: VarNameLookup>(
    left: &AHashSet<VarIdx>,
    right: &AHashSet<VarIdx>,
    var_names: &V,
) -> String {
    left.difference(right)
        .copied()
        .sorted_unstable()
        .map(|v| v.to_pretty_string(var_names))
        .join(", ")
}

/// Set up a new propagation engine for VeriPB.
#[inline]
pub fn new_veripb_propagation_engine() -> PropagationEngine {
    let mut propagation_engine = PropagationEngine::default();
    propagation_engine.add_set();
    propagation_engine.add_set();
    propagation_engine.add_set();
    propagation_engine.add_set();
    propagation_engine.add_set();
    propagation_engine.enable_back(CORE_CLAUSES_CARD);
    propagation_engine.enable_back(CORE_GENERAL);
    propagation_engine.enable_back(DERIVED_CLAUSES_CARD);
    propagation_engine.enable_back(DERIVED_GENERAL);
    propagation_engine
}

/// Check if the given solution or the propagated solution satisfies all core constraint and that all necessary variables are assigned. Return the solution as an [`Assignment`].
#[inline]
pub fn check_solution(
    context: &mut Context,
    database: &mut Database,
    solution: &Vec<Lit>,
    solution_output: &SolutionRuleOutput,
) -> Result<Assignment<BooleanVar>, CheckingError> {
    let mut assignment = Assignment::from(solution, context.var_names.len())
        .ok_or(CheckingError::SolutionIsConflicting)?;
    assignment.resize(context.var_names.len());

    // Heuristic check if given solution already satisfies all core constraints and assigns the necessary variables.
    database.update_unique_index(&mut context.propagation_engine)?;
    if get_unsatisfied_core_constraint(database, &assignment)?.is_none()
        && solution_assigns_necessary_variables(context, &assignment, solution_output).is_ok()
    {
        kernel_check_logged_solution(context, database, &assignment)?;
        return Ok(assignment);
    }

    // Propagate the solution.
    database.update_propagation_index(&mut context.propagation_engine)?;
    let assignment = context.propagation_engine.propagate_solution(
        solution,
        &context.var_names,
        context.config.trace_failed,
    )?;

    // Check if the propagated solution satisfies all constraints.
    if let Some(id) = get_unsatisfied_core_constraint(database, &assignment)? {
        Err(CheckingError::SolutionNotSatisfiedConstraint(id))
    } else {
        solution_assigns_necessary_variables(context, &assignment, solution_output)?;
        kernel_check_logged_solution(context, database, &assignment)?;
        Ok(assignment)
    }
}

/// Kernel-verify a mid-proof logged solution (see `crate::kernel_bridge`).
///
/// [`crate::kernel_bridge::verify_db_solution`] re-judges the assignment
/// against *every* database constraint, and reports a disagreement as a
/// [`CheckingError::KernelDivergence`]. That was exactly the live check's own
/// standard while [`check_solution`] demanded that all database constraints
/// hold; it no longer is. The live check now only requires the *core*
/// constraints to be satisfied (see [`get_unsatisfied_core_constraint`]), and
/// a derived constraint may be merely satisfiability-preserving — so a
/// legitimate logged solution can falsify one. Re-judging all of them on such
/// a solution would refuse a good proof.
///
/// When some non-core constraint is unsatisfied, the bridge therefore has
/// nothing to say about this solution: record a counted skip rather than force
/// a verdict, which is how every other gap in the proved fragment is handled.
fn kernel_check_logged_solution(
    context: &mut Context,
    database: &Database,
    assignment: &Assignment<BooleanVar>,
) -> Result<(), CheckingError> {
    if !context.config.kernel_verify {
        return Ok(());
    }
    if !all_db_constraints_satisfied(database, assignment) {
        context.kernel_stats.skip("solution-satisfies-core-only");
        return Ok(());
    }
    match crate::kernel_bridge::verify_db_solution(database, assignment) {
        Ok(None) => {
            context.kernel_stats.solution_verified += 1;
            Ok(())
        }
        Ok(Some(reason)) => {
            context.kernel_stats.skip(reason);
            Ok(())
        }
        Err(err) => Err(err),
    }
}

/// Whether every database constraint — core and derived alike — is satisfied
/// by `assignment`.
///
/// This is the precondition [`crate::kernel_bridge::verify_db_solution`]
/// re-judges under; see [`kernel_check_logged_solution`].
#[inline]
fn all_db_constraints_satisfied(database: &Database, assignment: &Assignment<BooleanVar>) -> bool {
    database
        .unique_constraints
        .iter()
        .all(|constraint| constraint.is_satisfied(assignment))
}

/// Check if the requirements for the solution rule output are met.
///
/// Specifically, this means that all variables in the preserved set are assigned if we want an excluding constraint and that all variables in the objective function are assigned if we want a solution-improving constraint.
#[inline]
fn solution_assigns_necessary_variables(
    context: &mut Context,
    assignment: &Assignment<BooleanVar>,
    solution_output: &SolutionRuleOutput,
) -> Result<(), CheckingError> {
    match solution_output {
        SolutionRuleOutput::None => Ok(()),
        SolutionRuleOutput::Improving => {
            let Some(objective) = &context.objective else {
                return Err(CheckingError::SolutionImprovingRequiresObjective);
            };
            for &var in objective.terms.iter().map(|t| t.0) {
                if assignment.get_value(var) == BoolValue::Unassigned {
                    return Err(CheckingError::SolutionVarUnassignedImproving(
                        var.to_pretty_string(&context.var_names),
                    ));
                }
            }
            Ok(())
        }
        SolutionRuleOutput::Excluding => {
            let Some(preserved) = &context.preserved_variables else {
                return Err(CheckingError::NoPreservedForSolutionExcluding);
            };
            // `preserved` is an `AHashSet`, whose iteration order is the
            // randomly-seeded hash order and so is NOT a function of the input.
            // Reporting the first unassigned variable found in that order made
            // the refusal name a different variable from run to run
            // (`tests/observable_output_deterministic.rs` catches exactly this).
            // Report the SMALLEST unassigned variable instead: same refusal,
            // same condition, but a stable choice of witness. The `Improving`
            // arm above is already stable because it walks the objective's
            // term vector.
            if let Some(var) = preserved
                .iter()
                .copied()
                .filter(|&var| assignment.get_value(var) == BoolValue::Unassigned)
                .min()
            {
                return Err(CheckingError::SolutionVarUnassignedExcluding(
                    var.to_pretty_string(&context.var_names),
                ));
            }
            Ok(())
        }
    }
}

/// Check that the given solution satisfies all core constraints.
///
/// Returns the constraint ID of an unsatisfied constraints or `None` if all constraints are satisfied.
#[inline]
fn get_unsatisfied_core_constraint(
    database: &mut Database,
    assignment: &Assignment<BooleanVar>,
) -> Result<Option<usize>, CheckingError> {
    for constraint in database.unique_constraints.iter() {
        if constraint.is_core_constraint() && !constraint.is_satisfied(assignment) {
            // Core constraint is not satisfied.
            if constraint.is_falsified(assignment) {
                // Core constraint is falsified.
                return Err(CheckingError::SolutionFalsifyingConstraint(
                    constraint.get_some_id(),
                ));
            } else {
                // Core constraint is neither satisfied nor falsified.
                return Ok(Some(constraint.get_some_id()));
            }
        }
    }
    Ok(None)
}

/// Do the syntactic implication check with saturation.
///
/// This check can derive a constraint `target` from another constraint `source` by adding literal axioms to it, performing saturation and another round of adding literal axioms.
///
/// Already takes care to check if the `source` constraint is a core constraint in a core only subproof.
#[inline]
pub fn check_implication(
    only_core: bool,
    propagation_engine: &mut PropagationEngine,
    database: &mut Database,
    target: &Rc<DBConstraint>,
    hint: Option<isize>,
) -> Result<isize, CheckingError> {
    match hint {
        Some(hint) => {
            let index = database.normalize_id(hint);
            let entry = database.get_entry_usize(index as usize)?;
            if only_core && !entry.is_core_constraint_id(index as usize) {
                return Err(CheckingError::CoreSubproofUsingNonCoreConstraint(hint));
            }
            if !entry.implies(target) {
                return Err(CheckingError::not_implied(target, entry));
            }
            Ok(index)
        }
        None => {
            database.update_unique_index(propagation_engine)?;
            if let Some(constraint) = database.lookup(target)
                && (!only_core || constraint.is_core_constraint())
            {
                return Ok(constraint.get_some_id() as isize);
            }

            for constraint in database.unique_constraints.iter() {
                if (!only_core || constraint.is_core_constraint()) && constraint.implies(target) {
                    return Ok(constraint.get_some_id() as isize);
                }
            }

            Err(CheckingError::not_implied_db(target, only_core))
        }
    }
}

/// Do the syntactic implication check with saturation for the substituted database.
///
/// This check is stronger than the syntactic implication check, since it substitutes `source` and `target` constraints using the current unit propagation before checking if the `source` implies `target`.
///
/// Already takes care to check if the `source` constraint is a core constraint in a core only subproof.
#[inline]
pub fn check_substituted_implication(
    context: &mut Context,
    database: &mut Database,
    target: &Rc<DBConstraint>,
    hint: Option<isize>,
) -> Result<isize, CheckingError> {
    match hint {
        Some(hint) => {
            let propagated_assignment = context
                .propagation_engine
                .get_propagated_assignment(context.var_names.len(), context.only_core);
            let sub_target = &Rc::new(target.substitute(propagated_assignment));
            let index = database.normalize_id(hint);
            let entry = database.get_entry_usize(index as usize)?;
            let sub_source = &Rc::new(entry.substitute(propagated_assignment));
            if context.only_core && !entry.is_core_constraint_id(index as usize) {
                return Err(CheckingError::CoreSubproofUsingNonCoreConstraint(hint));
            }
            if !sub_source.implies(sub_target) {
                return Err(CheckingError::not_implied_substituted(sub_target, entry));
            }
            Ok(index)
        }
        None => {
            database.update_unique_index(&mut context.propagation_engine)?;
            let propagated_assignment = context
                .propagation_engine
                .get_propagated_assignment(context.var_names.len(), context.only_core);
            let sub_target = &Rc::new(target.substitute(propagated_assignment));
            if let Some(constraint) = database.lookup(target)
                && (!context.only_core || constraint.is_core_constraint())
            {
                return Ok(constraint.get_some_id() as isize);
            }
            if let Some(constraint) = database.lookup(sub_target)
                && (!context.only_core || constraint.is_core_constraint())
            {
                return Ok(constraint.get_some_id() as isize);
            }

            for constraint in database.unique_constraints.iter() {
                if !context.only_core || constraint.is_core_constraint() {
                    let sub_constraint = constraint.substitute(propagated_assignment);
                    if sub_constraint.implies(sub_target) {
                        return Ok(constraint.get_some_id() as isize);
                    }
                }
            }

            Err(CheckingError::not_implied_substituted_db(
                sub_target,
                context.only_core,
            ))
        }
    }
}
