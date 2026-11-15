use std::rc::Rc;

use malachite_bigint::BigInt;
use veripb_formula::{pb_constraint::constraint_from_terms, prelude::*};
use veripb_rules::{
    Bound, ConclusionResult, ConclusionRule,
    elaboration::{ConstraintLookup, Elaboratable, ElaborationError, Elaborator},
};

use crate::prelude::*;

#[derive(Debug)]
pub struct ConclusionChecker {
    inner: ConclusionRule,
    propagated_solution: Option<Assignment<BooleanVar>>,
}

impl ConclusionChecker {
    pub fn new(inner: ConclusionRule) -> Self {
        Self {
            inner,
            propagated_solution: None,
        }
    }
}

impl From<ConclusionRule> for ConclusionChecker {
    fn from(inner: ConclusionRule) -> Self {
        Self::new(inner)
    }
}

impl Checkable for ConclusionChecker {
    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        // Same rule for a solution hint; see `load_order`.
        if let Some(hint) = self.inner.solution_hint.as_ref() {
            crate::checker::refuse_renamed_auxiliary_name_in_lits(context, hint)?;
        }
        validate_conclusion_rule_usage(
            context.has_conclusion,
            context.has_output,
            context.has_end_proof,
        )?;

        // Perform the necessary checks for each conclusion.
        match self.inner.result {
            ConclusionResult::None => {}
            ConclusionResult::Unsatisfiable => {
                self.inner.constraint_id_hint = Some(validate_unsat_conclusion(
                    self.inner.constraint_id_hint,
                    database,
                    context.best_objective_value.as_ref(),
                    context.objective.as_ref(),
                )?);
                if let Some(id) = self.inner.constraint_id_hint {
                    crate::kernel_bridge::kernel_certify_refutation(context, database, id)?;
                }
            }
            ConclusionResult::Satisfiable => {
                if context.objective.is_some() {
                    return Err(CheckingError::ConclusionSatWithObjective);
                }

                // NOTE: `best_valid_objective_value`, not `best_objective_value`.
                // Without a solution hint this value is the *only* evidence for
                // the conclusion, and only solutions logged while checked
                // deletion was still in effect are solutions of the original
                // problem. Using `best_objective_value` here accepted
                // `conclusion SAT;` for an unsatisfiable formula after a single
                // unchecked deletion, matching what the `BOUNDS` branch below
                // has always done.
                self.propagated_solution = check_solution(
                    &self.inner.result,
                    self.inner.solution_hint.as_ref(),
                    context.var_names.len(),
                    &context.original_constraints,
                    context.best_valid_objective_value.as_ref(),
                )?;
                if let Some(assignment) = self.propagated_solution.take() {
                    kernel_check_solution(context, &assignment)?;
                    self.propagated_solution = Some(assignment);
                }
            }
            ConclusionResult::Bounds => {
                if context.objective.is_none() {
                    return Err(CheckingError::ConclusionBoundsNoObjective);
                }

                // Check lower bound.
                match self.inner.lower_bound_or_count.as_ref().unwrap() {
                    Bound::Unbounded => {
                        if self.inner.upper_bound != Some(Bound::Unbounded) {
                            return Err(CheckingError::ConclusionBoundsInfeasibleAndUpper);
                        }
                        if context.best_objective_value.is_some() {
                            return Err(CheckingError::ConclusionBoundsInfeasibleAndSolutionLogged);
                        }

                        self.inner.constraint_id_hint = Some(check_contradiction(
                            self.inner.constraint_id_hint,
                            database,
                        )?);
                        if let Some(id) = self.inner.constraint_id_hint {
                            crate::kernel_bridge::kernel_certify_refutation(context, database, id)?;
                        }
                    }
                    Bound::Bounded(bound) => {
                        // Check that the lower bound is not better than the best
                        // logged solution, and not better than anything solution
                        // logging removed from the database.
                        validate_lower_bound(
                            bound,
                            context.best_objective_value.as_ref(),
                            context.excluded_objective_lower_bound.as_ref(),
                        )?;
                        // Construct lower bounding constraint.
                        let constraint = constraint_from_terms::<BigInt>(
                            context
                                .objective
                                .as_ref()
                                .unwrap()
                                .terms
                                .values()
                                .cloned()
                                .collect(),
                            bound.to_owned() - &context.objective.as_ref().unwrap().constant,
                        );
                        let db_constraint = Rc::new(DBConstraint::from(constraint));

                        if let Some(contradicting_id) = database.contains_contradiction() {
                            self.inner.constraint_id_hint = Some(contradicting_id as isize);
                            crate::kernel_bridge::kernel_certify_refutation(
                                context,
                                database,
                                contradicting_id as isize,
                            )?;
                        } else {
                            self.inner.constraint_id_hint = Some(check_implication(
                                context.only_core,
                                &mut context.propagation_engine,
                                database,
                                &db_constraint,
                                self.inner.constraint_id_hint,
                            )?);
                            if context.config.kernel_verify {
                                if let Some(id) = self.inner.constraint_id_hint {
                                    let source = database.get_entry(id)?.constraint.clone();
                                    kernel_check_implication(
                                        context,
                                        &source,
                                        &db_constraint.constraint,
                                    )?;
                                }
                            }
                        }
                    }
                }

                // Check upper bound.
                match self.inner.upper_bound.as_ref().unwrap() {
                    Bound::Unbounded => {}
                    Bound::Bounded(bound) => {
                        if self.inner.lower_bound_or_count > self.inner.upper_bound {
                            return Err(CheckingError::ConclusionBoundsLowerGreaterUpper(
                                self.inner.lower_bound_or_count.to_owned().unwrap().unwrap(),
                                self.inner.upper_bound.to_owned().unwrap().unwrap(),
                            ));
                        }

                        match check_solution(
                            &self.inner.result,
                            self.inner.solution_hint.as_ref(),
                            context.var_names.len(),
                            &context.original_constraints,
                            context.best_valid_objective_value.as_ref(),
                        )? {
                            Some(assignment) => {
                                let value = context
                                    .original_objective
                                    .as_ref()
                                    .unwrap()
                                    .evaluate(&assignment)
                                    .ok_or(CheckingError::ObjectiveUnassigned)?;
                                if *bound != value {
                                    return Err(
                                        CheckingError::ConclusionBoundsUpperBoundMismatchHint(
                                            bound.to_owned(),
                                            value,
                                        ),
                                    );
                                }
                                // Shadow-recompute the accepted objective
                                // value in exact arithmetic (see
                                // `crate::kernel_bridge::verify_objective_value`;
                                // a cross-check, not a kernel theorem).
                                if context.config.kernel_verify {
                                    let outcome = crate::kernel_bridge::verify_objective_value(
                                        context.original_objective.as_ref().unwrap(),
                                        &assignment,
                                        &value,
                                    );
                                    match outcome {
                                        Ok(None) => context.kernel_stats.objective_verified += 1,
                                        Ok(Some(reason)) => context.kernel_stats.skip(reason),
                                        Err(err) => return Err(err),
                                    }
                                }
                                kernel_check_solution(context, &assignment)?;
                                self.propagated_solution = Some(assignment);
                            }
                            None => {
                                if bound != context.best_valid_objective_value.as_ref().unwrap() {
                                    return Err(
                                        CheckingError::ConclusionBoundsUpperBoundMismatchRecorded(
                                            bound.to_owned(),
                                            context.best_valid_objective_value.clone().unwrap(),
                                        ),
                                    );
                                }
                            }
                        }
                    }
                }
            }
            ConclusionResult::EnumerationComplete => {
                // `solx` is the only rule that removes a solution *and* counts
                // it. An objective-improving `soli`/`obji` stores `obj <= v - 1`,
                // which removes every assignment with objective value at least
                // `v` and leaves `num_excluded_solutions` untouched, so the
                // contradiction this arm requires can have been manufactured by
                // that constraint alone. It then establishes neither the count
                // nor "there are no further solutions", and a satisfiable
                // formula gets certified as `COMPLETE ENUMERATION OF 0
                // SOLUTIONS`. `output EQUIENUMERABLE` refuses after any solution
                // logging for the same reason (see `rules::output`); `output
                // NONE` reaches this arm without passing that check.
                //
                // `EnumerationPartial` below is deliberately *not* guarded: it
                // claims only that at least `n` projected solutions were
                // witnessed, and since no rule ever adds models, every `solx`
                // that passed still witnessed a distinct projected solution of
                // the original problem. Guarding it would reject sound proofs.
                if context.objective_improving_used {
                    return Err(CheckingError::ConclusionEnumerationObjectiveImproving);
                }
                let expected_sol = self
                    .inner
                    .lower_bound_or_count
                    .as_ref()
                    .unwrap()
                    .clone()
                    .unwrap();
                let actual_sol = BigInt::from(context.num_excluded_solutions);
                if expected_sol != actual_sol {
                    return Err(CheckingError::MismatchEnumeratedSolutions(
                        expected_sol,
                        actual_sol,
                    ));
                }
                self.inner.constraint_id_hint = Some(check_contradiction(
                    self.inner.constraint_id_hint,
                    database,
                )?);
                if let Some(id) = self.inner.constraint_id_hint {
                    crate::kernel_bridge::kernel_certify_refutation(context, database, id)?;
                }
            }
            ConclusionResult::EnumerationPartial => {
                let expected_sol = self
                    .inner
                    .lower_bound_or_count
                    .as_ref()
                    .unwrap()
                    .clone()
                    .unwrap();
                let actual_sol = BigInt::from(context.num_excluded_solutions);
                if expected_sol != actual_sol {
                    return Err(CheckingError::MismatchEnumeratedSolutions(
                        expected_sol,
                        actual_sol,
                    ));
                }
            }
        }

        // A conclusion that talks about solutions of the original problem only
        // holds under the weaker guarantee once unchecked deletion has been
        // used, so the verdict has to say so instead of claiming a plain
        // `s VERIFIED ...`.
        if !context.strong_solution_guarantees && depends_on_solutions(&self.inner.result) {
            context.weakened_verdict = true;
        }

        // Record the verification statement for each conclusion. It is printed
        // once the whole run has completed (see
        // `Context::take_verification_results`), so that a proof rejected after
        // its conclusion never leaves a verdict on stdout.
        context.pending_verification_results.push(
            crate::checked_result::CheckedStatement::conclusion(
                self.inner.result,
                self.inner.lower_bound_or_count.clone(),
                self.inner.upper_bound.clone(),
                context.assertion_used,
                context.weakened_verdict,
                context.config.print_verification_result,
            ),
        );

        context.has_conclusion = true;
        Ok(vec![])
    }
}

/// Return an error when the given bool flags indicate an
/// invalid state at the point where a [`ConclusionRule`] is encountered.
pub fn validate_conclusion_rule_usage(
    second_conclusion: bool,
    output_before_conclusion: bool,
    end_before_conclusion: bool,
) -> Result<(), CheckingError> {
    if second_conclusion {
        return Err(CheckingError::DoubleConclusion);
    }
    if !output_before_conclusion || end_before_conclusion {
        return Err(CheckingError::WrongFooterOrder("conclusion"));
    }
    Ok(())
}

/// Reject a `conclusion BOUNDS` lower bound the proof has not established.
///
/// The bound claims that *every* solution of the original problem has objective
/// value at least `bound`, but it is derived from a database that solution
/// logging may already have removed solutions from. So it may exceed neither
///
/// * `best_objective_value` — the best logged solution is a witness that the
///   optimum is no larger than its value, nor
/// * `excluded_objective_lower_bound` — a lower bound on the objective value of
///   everything solution logging removed, off which the derived lower-bounding
///   constraint says nothing at all.
///
/// The second is what `solx` needs. It removes the whole preserved class around
/// the logged solution, not just the representative whose value
/// `best_objective_value` records, and that class' minimum lies below the
/// representative's as soon as the objective mentions a variable outside the
/// preserved set. Checking only the first accepted
/// `conclusion BOUNDS 100 100` for a problem whose optimum is 0.
pub fn validate_lower_bound(
    bound: &BigInt,
    best_objective_value: Option<&BigInt>,
    excluded_objective_lower_bound: Option<&BigInt>,
) -> Result<(), CheckingError> {
    if best_objective_value.is_some_and(|best| bound > best) {
        return Err(CheckingError::ConclusionBoundsLBLargerBestSolution);
    }
    if excluded_objective_lower_bound.is_some_and(|excluded| bound > excluded) {
        return Err(CheckingError::ConclusionBoundsLBLargerExcludedSolutions);
    }
    Ok(())
}

/// Checks if the database contains a contradiction.
pub fn check_contradiction(
    constraint_id_hint: Option<isize>,
    database: &Database,
) -> Result<isize, CheckingError> {
    match constraint_id_hint {
        None => {
            if let Some(contradicting_id) = database.contains_contradiction() {
                Ok(contradicting_id as isize)
            } else {
                Err(CheckingError::NoContradicitionInDB)
            }
        }
        Some(hint) => {
            let constraint = database.get_entry(hint)?;
            if constraint.is_contradicting() {
                return Ok(database.normalize_id(hint));
            }
            Err(CheckingError::HintNoContradiction(hint))
        }
    }
}

/// Check if the proof contains a solution or the hint is a correct solution.
///
/// `num_vars` is the number of variables known to the checker; the assignment
/// built from the hint covers at least that many variables before it is used.
///
/// Returns the propagated solution if a solution was given as a hint.
#[inline]
fn check_solution(
    conclusion_result: &ConclusionResult,
    solution_hint: Option<&Vec<Lit>>,
    num_vars: usize,
    original_constraints: &[PBConstraintEnum],
    best_valid_objective_value: Option<&BigInt>,
) -> Result<Option<Assignment<BooleanVar>>, CheckingError> {
    match solution_hint {
        Some(solution) => {
            // Do not propagate the assignment, as the hint given in the conclusion has to be a full assignment.
            //
            // `Assignment::from` sizes the assignment to exactly the capacity it
            // is given and then writes every hint literal with the *unchecked*
            // accessor, and `is_satisfied` below reads it the same way; the
            // safety contract of both is `lit.get_var() < assignment.len()`. So
            // the capacity has to cover the variables of *both* sides: a hint
            // that does not mention the highest-numbered variable of the problem
            // would otherwise cause an out-of-bounds read for every original
            // constraint that does, and a hint mentioning a variable the checker
            // does not know would write out of bounds. Take the maximum of the
            // two, never less; the variables the hint leaves out stay
            // unassigned, which makes any constraint needing them count as
            // unsatisfied.
            let capacity = solution
                .iter()
                .map(|lit| lit.get_var() + 1)
                .max()
                .unwrap_or(0)
                .max(num_vars);
            let assignment = Assignment::from(solution, capacity)
                .ok_or(CheckingError::ConclusionSolutionConflicting)?;
            for constraint in original_constraints.iter() {
                if !constraint.is_satisfied(&assignment) {
                    return Err(CheckingError::OriginalConstraintNotSatisfied);
                }
            }
            Ok(Some(assignment))
        }
        None => {
            if best_valid_objective_value.is_none() {
                return Err(CheckingError::SolutionMissing(
                    conclusion_result.to_string(),
                ));
            }
            Ok(None)
        }
    }
}

/// Ensure an UNSAT conclusion is allowed: return an error if either `best_objective_value` or
/// `objective` is [`Some`].
///
/// Otherwise check the database for contradiction, returning the contradicting constraint id.
pub fn validate_unsat_conclusion(
    constraint_id_hint: Option<isize>,
    database: &mut Database,
    best_objective_value: Option<&BigInt>,
    objective: Option<&PBObjective>,
) -> Result<isize, CheckingError> {
    if best_objective_value.is_some() {
        return Err(CheckingError::ConclusionUnsatSolutionLogged);
    }
    if objective.is_some() {
        return Err(CheckingError::ConclusionUnsatObjective);
    }
    check_contradiction(constraint_id_hint, database)
}

/// Whether the meaning of `result` depends on solutions of the *original*
/// problem, and is therefore affected when unchecked deletion has weakened the
/// solution guarantees.
///
/// `UNSATISFIABLE` is not: deletion only ever weakens the current constraint
/// set, so a contradiction derived after an unchecked deletion still refutes
/// the original formula. Neither is `NO CONCLUSION`.
#[inline]
fn depends_on_solutions(result: &ConclusionResult) -> bool {
    match result {
        ConclusionResult::None | ConclusionResult::Unsatisfiable => false,
        ConclusionResult::Satisfiable
        | ConclusionResult::Bounds
        | ConclusionResult::EnumerationComplete
        | ConclusionResult::EnumerationPartial => true,
    }
}

/// Build the final `s VERIFIED ...` line summarising a completed conclusion.
///
/// The `s VERIFIED` prefix is qualified when the run could not give the full
/// guarantee: `s UNDER ASSERTIONS ...` when an unchecked assertion was used and
/// `s UNDER WEAKENED GUARANTEES ...` when unchecked deletion means the verdict
/// rests on solutions logged before the guarantee was dropped. Callers grep
/// stdout, so a weakened run must not print a bare `s VERIFIED`.
pub fn conclusion_status_line(
    result: &ConclusionResult,
    lower_bound: Option<&Bound>,
    upper_bound: Option<&Bound>,
    assertion_used: bool,
    weakened_guarantees: bool,
) -> String {
    let conclusion_status = match result {
        ConclusionResult::None => "NO CONCLUSION".to_string(),
        ConclusionResult::Unsatisfiable => "UNSATISFIABLE".to_string(),
        ConclusionResult::Satisfiable => "SATISFIABLE".to_string(),
        ConclusionResult::EnumerationComplete => {
            format!("COMPLETE ENUMERATION OF {} SOLUTIONS", lower_bound.unwrap())
        }
        ConclusionResult::EnumerationPartial => {
            format!("PARTIAL ENUMERATION OF {} SOLUTIONS", lower_bound.unwrap())
        }
        ConclusionResult::Bounds => format!(
            "BOUNDS {} <= obj <= {}",
            lower_bound.unwrap(),
            upper_bound.unwrap()
        ),
    };

    format!(
        "{} {conclusion_status}",
        verdict_prefix(assertion_used, weakened_guarantees)
    )
}

/// The prefix of an `s ...` verification result line.
///
/// `s VERIFIED` claims that everything the verdict rests on was checked, so it
/// is only used when that is true.
pub fn verdict_prefix(assertion_used: bool, weakened_guarantees: bool) -> &'static str {
    match (assertion_used, weakened_guarantees) {
        (false, false) => "s VERIFIED",
        (true, false) => "s UNDER ASSERTIONS",
        (false, true) => "s UNDER WEAKENED GUARANTEES",
        (true, true) => "s UNDER ASSERTIONS AND WEAKENED GUARANTEES",
    }
}

impl Elaboratable for ConclusionChecker {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        database: &C,
        var_names: &V,
    ) -> Result<(), ElaborationError> {
        let inner = &self.inner;
        match inner.result {
            ConclusionResult::None => elaborator.write_conclusion_none(),
            ConclusionResult::Satisfiable => {
                elaborator.write_conclusion_sat(var_names, self.propagated_solution.as_ref())
            }
            ConclusionResult::Unsatisfiable => elaborator
                .write_conclusion_unsat(database, inner.constraint_id_hint.unwrap() as usize),
            ConclusionResult::Bounds => elaborator.write_conclusion_bounds(
                database,
                var_names,
                inner.lower_bound_or_count.as_ref().unwrap(),
                inner.upper_bound.as_ref().unwrap(),
                inner.constraint_id_hint.unwrap() as usize,
                self.propagated_solution.as_ref(),
            ),
            ConclusionResult::EnumerationComplete => elaborator
                .write_conclusion_enumeration_complete(
                    database,
                    inner.lower_bound_or_count.as_ref().unwrap(),
                    inner.constraint_id_hint.unwrap() as usize,
                ),
            ConclusionResult::EnumerationPartial => elaborator
                .write_conclusion_enumeration_partial(inner.lower_bound_or_count.as_ref().unwrap()),
        }
        Ok(())
    }
}

// The contradiction re-judge lives in the bridge
// (`crate::kernel_bridge::kernel_check_contradiction_id`): it is shared with
// the mid-proof `qed` discharges in `end_subproof.rs`.

/// Kernel-verify an accepted solution against every original constraint
/// (see `crate::kernel_bridge`).
fn kernel_check_solution(
    context: &mut Context,
    assignment: &Assignment<BooleanVar>,
) -> Result<(), CheckingError> {
    if !context.config.kernel_verify {
        return Ok(());
    }
    match crate::kernel_bridge::verify_solution(&context.original_constraints, assignment) {
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

/// Kernel-verify a syntactic implication accept (see `crate::kernel_bridge`).
fn kernel_check_implication(
    context: &mut Context,
    source: &PBConstraintEnum,
    target: &PBConstraintEnum,
) -> Result<(), CheckingError> {
    match crate::kernel_bridge::verify_implication(source, target) {
        Ok(None) => {
            context.kernel_stats.implication_verified += 1;
            Ok(())
        }
        Ok(Some(reason)) => {
            context.kernel_stats.skip(reason);
            Ok(())
        }
        Err(err) => Err(err),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use veripb_formula::clause::Clause;

    /// The unit constraint `x<var> >= 1`.
    fn unit(var: VarIdx) -> PBConstraintEnum {
        Clause::from_lits(vec![Lit::from_var(var, false)]).into()
    }

    /// `is_satisfied` reads the assignment with `get_lit_value_unchecked`, whose
    /// safety contract is `lit.get_var() < assignment.len()`. A capacity taken
    /// from the hint alone leaves a hint that does not mention the
    /// highest-numbered variable of the problem making every original constraint
    /// that does read out of bounds.
    #[test]
    fn a_solution_hint_is_grown_to_cover_every_variable() {
        let num_vars = 200;
        let hint = vec![Lit::from_var(1, false)];

        let assignment = check_solution(
            &ConclusionResult::Satisfiable,
            Some(&hint),
            num_vars,
            &[unit(1)],
            None,
        )
        .expect("the hint satisfies the only constraint")
        .expect("a hint was given, so an assignment is returned");

        assert!(
            assignment.len() >= num_vars,
            "the assignment covers only {} of {num_vars} variables, so checking a \
             constraint over a higher-numbered variable reads out of bounds",
            assignment.len()
        );
    }

    /// The other direction of the same safety contract: `Assignment::from`
    /// writes the hint literals unchecked, so a hint mentioning a variable
    /// beyond the checker's count must still fit.
    #[test]
    fn a_solution_hint_beyond_the_known_variables_still_fits() {
        let hint = vec![Lit::from_var(199, false)];

        let assignment = check_solution(
            &ConclusionResult::Satisfiable,
            Some(&hint),
            2,
            &[unit(199)],
            None,
        )
        .expect("the hint satisfies the only constraint")
        .expect("a hint was given, so an assignment is returned");

        assert!(
            assignment.len() > 199,
            "the assignment covers only {} variables, so writing x199 from the hint is \
             out of bounds",
            assignment.len()
        );
    }

    /// The variables the hint left out stay unassigned, so a constraint that
    /// needs them is not satisfied and the conclusion is rejected.
    #[test]
    fn a_hint_that_leaves_a_constraint_unsatisfied_is_rejected() {
        let hint = vec![Lit::from_var(1, false)];

        let error = check_solution(
            &ConclusionResult::Satisfiable,
            Some(&hint),
            200,
            &[unit(1), unit(199)],
            None,
        )
        .expect_err("x199 is not assigned by the hint");

        assert!(matches!(
            error,
            CheckingError::OriginalConstraintNotSatisfied
        ));
    }

    /// Without a hint the conclusion rests entirely on a solution logged while
    /// the guarantees were still strong; there is nothing else to check.
    #[test]
    fn a_hintless_conclusion_needs_a_solution_logged_under_strong_guarantees() {
        let error = check_solution(&ConclusionResult::Satisfiable, None, 200, &[unit(1)], None)
            .expect_err("no solution was logged while checked deletion was enabled");

        assert!(matches!(error, CheckingError::SolutionMissing(_)));
    }

    /// Nothing has been logged and nothing has been removed, so there is no
    /// ceiling on what the lower bound may claim.
    #[test]
    fn a_lower_bound_is_unconstrained_before_any_solution_logging() {
        assert!(validate_lower_bound(&BigInt::from(1_000), None, None).is_ok());
    }

    /// The pre-existing check: a logged solution witnesses that the optimum is
    /// no larger than its value.
    #[test]
    fn a_lower_bound_above_the_best_logged_solution_is_rejected() {
        let best = BigInt::from(7);

        assert!(validate_lower_bound(&BigInt::from(7), Some(&best), None).is_ok());
        assert!(matches!(
            validate_lower_bound(&BigInt::from(8), Some(&best), None)
                .expect_err("8 is better than the logged 7"),
            CheckingError::ConclusionBoundsLBLargerBestSolution
        ));
    }

    /// The defect: `solx` removes the whole preserved class around the logged
    /// solution, so a bound may exceed neither the representative's value nor
    /// the class minimum — and the class minimum can be far below it.
    #[test]
    fn a_lower_bound_above_what_solution_logging_removed_is_rejected() {
        let best = BigInt::from(100);
        let excluded = BigInt::from(0);

        assert!(validate_lower_bound(&BigInt::from(0), Some(&best), Some(&excluded)).is_ok());
        assert!(matches!(
            validate_lower_bound(&BigInt::from(100), Some(&best), Some(&excluded)).expect_err(
                "the excluded class contains solutions of objective value 0, so a lower \
                 bound of 100 does not hold for the original problem"
            ),
            CheckingError::ConclusionBoundsLBLargerExcludedSolutions
        ));
    }

    /// `soli`/`obji` remove exactly `{ obj >= value }`, so for them the two
    /// records coincide and the added check changes nothing.
    #[test]
    fn an_improving_rule_leaves_the_lower_bound_check_unchanged() {
        let value = BigInt::from(42);

        assert!(validate_lower_bound(&BigInt::from(42), Some(&value), Some(&value)).is_ok());
        assert!(validate_lower_bound(&BigInt::from(43), Some(&value), Some(&value)).is_err());
    }
}
