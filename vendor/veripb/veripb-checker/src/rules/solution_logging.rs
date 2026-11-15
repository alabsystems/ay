use std::rc::Rc;

use ahash::AHashSet;
use colored::Colorize;
use malachite_bigint::BigInt;
use num_traits::{Signed, Zero};
use veripb_formula::{
    pb_constraint::{constraint_from_terms, constraint_from_terms_and_coeff_sum},
    prelude::*,
};
use veripb_rules::{
    ObjectiveValueRule, SolutionRule, SolutionRuleOutput,
    elaboration::{ConstraintLookup, Elaboratable, ElaborationError, Elaborator},
};

use crate::prelude::*;

#[derive(Debug)]
pub struct SolutionChecker {
    pub inner: SolutionRule,
    pub propagated_solution: Assignment<BooleanVar>,
}

impl SolutionChecker {
    fn new(inner: SolutionRule) -> Self {
        Self {
            inner,
            propagated_solution: Assignment::default(),
        }
    }
}

impl Checkable for SolutionChecker {
    fn compute(
        &mut self,
        context: &mut Context,
        database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        // Same rule for the logged solution; see `load_order`.
        crate::checker::refuse_renamed_auxiliary_name_in_lits(context, &self.inner.solution)?;
        // Set the flags that record that we introduced a solution-improving or
        // solution-excluding constraint. Set before any fallible work below, so
        // that a rule which errors out later can never leave the flags clear on
        // a path that already decided what this rule is.
        match self.inner.rule_output {
            SolutionRuleOutput::Improving => {
                context.solution_logged = true;
                context.objective_improving_used = true;
            }
            SolutionRuleOutput::Excluding => context.solution_logged = true,
            SolutionRuleOutput::None => {}
        }
        if self.inner.rule_output == SolutionRuleOutput::Improving && context.objective.is_none() {
            return Err(CheckingError::SolutionImprovingRequiresObjective);
        }

        let assignment = check_solution(
            context,
            database,
            &self.inner.solution,
            &self.inner.rule_output,
        )?;

        // Keep track of currently best solution.
        let value = if let Some(objective) = &context.objective {
            objective
                .evaluate(&assignment)
                .ok_or(CheckingError::ObjectiveUnassigned)?
        } else {
            BigInt::zero()
        };

        // Shadow-recompute the objective value in exact arithmetic (see
        // `crate::kernel_bridge::verify_objective_value`; a cross-check, not
        // a kernel theorem). Everything downstream — the claimed-value
        // comparison, `best_objective_value`, the improving constraint's
        // degree — consumes this value.
        if context.config.kernel_verify {
            if let Some(objective) = context.objective.as_ref() {
                let outcome =
                    crate::kernel_bridge::verify_objective_value(objective, &assignment, &value);
                match outcome {
                    Ok(None) => context.kernel_stats.objective_verified += 1,
                    Ok(Some(reason)) => context.kernel_stats.skip(reason),
                    Err(err) => return Err(err),
                }
            }
        }

        // Check if claimed objective value matches computed objective value.
        if context.objective.is_none() && self.inner.objective_value.is_some() {
            return Err(CheckingError::SolutionValueHintNoObjective);
        }
        if self
            .inner
            .objective_value
            .as_ref()
            .is_some_and(|claimed_value| *claimed_value != value)
        {
            return Err(CheckingError::SolutionIncorrectValue(
                self.inner.objective_value.clone().unwrap(),
                value,
            ));
        }
        if context
            .best_objective_value
            .as_ref()
            .is_none_or(|best_value| value < *best_value)
        {
            context.best_objective_value = Some(value.clone());
            if context.strong_solution_guarantees {
                context.best_valid_objective_value = Some(value.clone())
            }
        }

        // Store propagated solution for potential elaboration.
        self.propagated_solution = assignment;

        // Record a lower bound on the objective value of everything this rule
        // removes from the database. Off that set the rest of the proof says
        // nothing about the original problem, so `conclusion BOUNDS` may not
        // claim a lower bound above it and `output EQUIOPTIMAL` may not claim
        // agreement above it (see `Context::objective_guarantee_ceiling`).
        match self.inner.rule_output {
            // Removes nothing: the solution is only logged.
            SolutionRuleOutput::None => {}
            // Stores `obj <= value - 1`, removing exactly `{ obj >= value }`.
            SolutionRuleOutput::Improving => context.note_excluded_objective_bound(value.clone()),
            // Removes the whole preserved class around the logged solution,
            // whose minimum can lie below `value`.
            SolutionRuleOutput::Excluding => {
                let bound = excluded_class_lower_bound(
                    context.objective.as_ref(),
                    context.preserved_variables.as_ref(),
                    &self.propagated_solution,
                );
                context.note_excluded_objective_bound(bound);
            }
        }

        // A `sol` that only logs a solution is fully covered: the assignment
        // itself is re-judged against the database by the proved semantics
        // (`kernel_bridge::verify_db_solution`). An *excluding* or
        // *improving* `sol` additionally stores a constraint that rules the
        // exhibited solution out; that constraint is satisfiability-preserving,
        // NOT entailed by the formula, so it breaks the `DbEntailed` invariant
        // `checker_sound` rests on and the kernel has no model of it (nor of
        // the objective the improving form uses). The shadow slot is already a
        // named hole (`kernel_slot_taint` below); this makes the coverage line
        // say so too, instead of reporting "nothing outside the proved
        // fragment" on a run those constraints decided.
        // The EXCLUDING form is now modelled: its constraint is the blocking
        // clause, and `offer_solution_exclusion` below justifies the slot. The
        // IMPROVING form is not -- it bounds the OBJECTIVE, and the kernel has
        // no objective at all -- so it keeps the named hole.
        // Both storing forms are modelled now: the EXCLUDING form's constraint
        // is the blocking clause (`DbOkE.exclude`) and the IMPROVING form's is
        // the negated objective at a shifted degree (`DbOkB.improve`). Each is
        // offered where it is built, below.

        // Return constraint according to the output type of the rule.
        match self.inner.rule_output {
            SolutionRuleOutput::None => Ok(vec![]),
            SolutionRuleOutput::Excluding => {
                if context.preserved_set_changed {
                    return Err(CheckingError::SolutionExcludingPreservedVarChanged);
                }
                if context.strong_solution_guarantees {
                    context.num_excluded_solutions += 1;
                }
                let terms = if let Some(preserved_vars) = &context.preserved_variables {
                    let mut terms = Vec::with_capacity(preserved_vars.len());
                    // Ascending variable order, not hash order. The constraint
                    // built below is normalized, so its *terms* would come out
                    // sorted either way -- but the loop also refuses, and the
                    // refusal names the first unassigned preserved variable it
                    // reaches. `preserved_variables` is an `AHashSet`, whose
                    // `RandomState` seeds itself from runtime randomness once
                    // per process, so with more than one variable unassigned
                    // the refusal named a different one on different runs:
                    // measured before this, a `solx` leaving seven preserved
                    // variables unassigned named six distinct variables over
                    // fifteen runs. Same refusal, same exit code, different
                    // reason. See `tests/observable_output_deterministic.rs`.
                    let mut ordered: Vec<VarIdx> = preserved_vars.iter().copied().collect();
                    ordered.sort_unstable();
                    for var in ordered {
                        match self.propagated_solution.get_value(var) {
                            BoolValue::Unassigned => {
                                return Err(
                                    CheckingError::SolutionExcludingPreservedVarUnassigned(
                                        var.to_pretty_string(&context.var_names).bold(),
                                    ),
                                );
                            }
                            BoolValue::Assigned(true) => {
                                terms.push(GeneralPBTerm::new(1, Lit::from_var(var, true)));
                            }
                            BoolValue::Assigned(false) => {
                                terms.push(GeneralPBTerm::new(1, Lit::from_var(var, false)));
                            }
                        }
                    }
                    terms
                } else {
                    return Err(CheckingError::NoPreservedForSolutionExcluding);
                };
                let coeff_sum = terms.len() as i64;
                let constraint = constraint_from_terms_and_coeff_sum(terms, 1_i64, coeff_sum);
                // The blocking clause of the exhibited solution, which the
                // kernel DOES model (`VeriPbCore.DbOkE.exclude`, resting on
                // `agrees_of_not_holds_blockC`). Offered here, where the
                // constraint is built, so the shadow slot carries the
                // justification instead of a named hole.
                if context.config.kernel_verify {
                    crate::kernel_bridge::offer_solution_exclusion(context, &constraint);
                }
                Ok(vec![Rc::new(DBConstraint::from(constraint))])
            }
            SolutionRuleOutput::Improving => {
                let mut negated_terms: Vec<_> = context
                    .objective
                    .as_ref()
                    .unwrap()
                    .terms
                    .values()
                    .cloned()
                    .collect();
                for term in negated_terms.iter_mut() {
                    term.coeff = -term.coeff.clone();
                }

                let constraint = constraint_from_terms(
                    negated_terms,
                    BigInt::from(1) + &context.objective.as_ref().unwrap().constant - &value,
                )
                .into_smallest_type();
                // `VeriPbCore.improveC` for this run's objective, which the
                // kernel now models (`DbOkB.improve`, resting on
                // `bound_of_not_holds_improveC`).
                if context.config.kernel_verify {
                    crate::kernel_bridge::offer_solution_improving(context, &constraint, &value);
                }
                Ok(vec![Rc::new(DBConstraint::from(constraint))])
            }
        }
    }

    #[inline]
    fn kernel_slot_taint(&self) -> &'static str {
        // The excluding/improving constraint rules out a solution the run
        // just exhibited; it is satisfiability-preserving, not entailed by
        // the formula, and the kernel has no objective model at all
        // (the development design notes section 5, item 5).
        "solution-exclusion-unmodelled"
    }

    #[inline]
    fn add_constraints_to_core(&self, _context: &Context) -> bool {
        true
    }
}

/// A lower bound on the objective value of every assignment that the excluding
/// constraint of `solx` removes from the database.
///
/// `solx` stores "differ from the logged solution on at least one preserved
/// variable", so the set it removes is the whole *class* of assignments that
/// agree with `solution` on the preserved variables — not just `solution`
/// itself. The objective is linear and unconstrained on the variables outside
/// that agreement, so its exact minimum over the class is obtained by keeping
/// the contribution `solution` gives every preserved literal and taking the
/// minimising contribution for every other one. Ignoring the formula's
/// constraints only enlarges the class, which can only lower the result, so it
/// stays a lower bound on the objective value of every *solution* removed —
/// which is what `conclusion BOUNDS` needs.
///
/// `preserved_variables` is [`None`] only on the path where `solx` is about to
/// be rejected outright (`NoPreservedForSolutionExcluding`); reading it as the
/// empty set is the conservative choice, i.e. nothing is pinned down.
pub fn excluded_class_lower_bound(
    objective: Option<&PBObjective>,
    preserved_variables: Option<&AHashSet<VarIdx>>,
    solution: &Assignment<BooleanVar>,
) -> BigInt {
    let Some(objective) = objective else {
        return BigInt::zero();
    };
    let mut bound = objective.constant.clone();
    for (var, term) in objective.terms.iter() {
        let pinned = preserved_variables.is_some_and(|preserved| preserved.contains(var));
        match (pinned, solution.get_lit_value(term.lit)) {
            // Pinned by the logged solution across the whole class.
            (true, BoolValue::Assigned(true)) => bound += &term.coeff,
            (true, BoolValue::Assigned(false)) => {}
            // Free across the class — and an unassigned preserved variable is
            // not actually pinned either (`solx` rejects that case a few lines
            // later, but the minimising reading is the safe one here). Take
            // whichever value of the literal contributes least.
            _ => {
                if term.coeff.is_negative() {
                    bound += &term.coeff;
                }
            }
        }
    }
    bound
}

impl Checkable for ObjectiveValueRule {
    fn compute(
        &mut self,
        context: &mut Context,
        _database: &mut Database,
    ) -> Result<Vec<Rc<DBConstraint>>, CheckingError> {
        // Set before any fallible work below: `obji` stores the same
        // objective-improving constraint an improving `sol` does, so it removes
        // solutions without counting them (see
        // `Context::objective_improving_used`).
        context.objective_improving_used = true;
        if context.objective.is_none() {
            return Err(CheckingError::ObjectiveImprovingRequiresObjective);
        }
        if context
            .best_objective_value
            .as_ref()
            .is_none_or(|best_value| self.value < *best_value)
        {
            context.best_objective_value = Some(self.value.clone());
        }
        // The stored constraint is `obj <= value - 1`, so it removes exactly
        // `{ obj >= value }`.
        context.note_excluded_objective_bound(self.value.clone());
        let mut negated_terms: Vec<_> = context
            .objective
            .as_ref()
            .unwrap()
            .terms
            .values()
            .cloned()
            .collect();
        for term in negated_terms.iter_mut() {
            term.coeff = -term.coeff.clone();
        }

        let constraint = constraint_from_terms(
            negated_terms,
            BigInt::from(1) + &context.objective.as_ref().unwrap().constant - &self.value,
        )
        .into_smallest_type();
        // The SAME `VeriPbCore.improveC` an improving `sol` stores, so it takes
        // the same leg: `DbOkB.improve`, resting on
        // `bound_of_not_holds_improveC`. That leg's one non-free hypothesis is
        // `Int.le v bound` -- NOT "a solution was exhibited" -- which is
        // exactly why `obji`, which exhibits none, is covered by it. Refuting
        // `F` together with `obj < v` proves `obj >= v` over `F` whether or not
        // anything achieving `v` was ever shown.
        //
        // This rule is a SEPARATE `Checkable` from `SolutionChecker` and was
        // simply never routed when the improving `sol` was; it kept a blanket
        // skip that named the kernel's old lack of an objective as the reason.
        if context.config.kernel_verify {
            crate::kernel_bridge::offer_solution_improving(context, &constraint, &self.value);
        }
        Ok(vec![Rc::new(DBConstraint::from(constraint))])
    }

    #[inline]
    fn kernel_slot_taint(&self) -> &'static str {
        // Unreachable under `--kernel-verify`: `compute` always offers, so the
        // pending queue is never empty for this rule. Named apart from the
        // excluding form rather than shared with it, so a future path that
        // skips the offer is reported as itself instead of borrowing a reason
        // that would then be a lie.
        "objective-improving-unmodelled"
    }

    #[inline]
    fn add_constraints_to_core(&self, _context: &Context) -> bool {
        true
    }
}

impl From<SolutionRule> for SolutionChecker {
    fn from(inner: SolutionRule) -> Self {
        Self::new(inner)
    }
}

impl Elaboratable for SolutionChecker {
    fn elaborate<C: ConstraintLookup, V: VarNameLookup>(
        &self,
        elaborator: &mut Elaborator,
        _database: &C,
        var_lookup: &V,
    ) -> Result<(), ElaborationError> {
        elaborator.write_solution(
            &self.inner.rule_output,
            &self.propagated_solution,
            self.inner.objective_value.as_ref(),
            var_lookup,
        );
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    /// `x<var>` if `!negated`, `~x<var>` otherwise.
    fn lit(var: VarIdx, negated: bool) -> Lit {
        Lit::from_var(var, negated)
    }

    /// An objective built term by term, without the sign normalisation of
    /// [`PBObjective::from_terms`] — an `obju` diff can leave a negative
    /// coefficient behind, so the helper has to cope with one.
    fn objective(terms: Vec<(i64, Lit)>, constant: i64) -> PBObjective {
        let mut map: BTreeMap<VarIdx, GeneralPBTerm<BigInt>> = BTreeMap::new();
        for (coeff, lit) in terms {
            map.insert(lit.get_var(), GeneralPBTerm::new(BigInt::from(coeff), lit));
        }
        PBObjective {
            terms: map,
            constant: BigInt::from(constant),
        }
    }

    fn preserved(vars: &[VarIdx]) -> AHashSet<VarIdx> {
        vars.iter().copied().collect()
    }

    fn assignment(lits: &[Lit]) -> Assignment<BooleanVar> {
        // Upstream's `Assignment::from` now takes an explicit capacity and
        // writes through `set_lit_value_unchecked`, so the capacity MUST cover
        // every variable index used or the write is out of bounds. Size it from
        // the literals themselves rather than a guess.
        let capacity = lits
            .iter()
            .map(|l| l.get_var() as usize + 1)
            .max()
            .unwrap_or(0);
        Assignment::from(&lits.to_vec(), capacity).expect("the literals do not conflict")
    }

    /// With every objective variable preserved, the excluded class is pinned
    /// down to the logged solution, so the bound is exactly its objective value
    /// and the new `conclusion BOUNDS` guard costs nothing.
    #[test]
    fn a_fully_preserved_objective_is_pinned_to_the_logged_value() {
        let objective = objective(vec![(1, lit(0, false)), (1, lit(1, false))], 0);
        let solution = assignment(&[lit(0, false), lit(1, true)]);

        assert_eq!(
            excluded_class_lower_bound(Some(&objective), Some(&preserved(&[0, 1])), &solution),
            BigInt::from(1),
            "x1 is true and x2 is false, so the class minimum is the logged value 1"
        );
    }

    /// The defect: the objective is over a variable outside the preserved set,
    /// so the class `solx` removes contains assignments better than the logged
    /// representative and the bound has to drop to the class minimum.
    #[test]
    fn an_unpreserved_objective_variable_is_free_across_the_class() {
        let objective = objective(vec![(100, lit(1, false))], 0);
        // The logged solution has x2 true, i.e. objective value 100 ...
        let solution = assignment(&[lit(0, true), lit(1, false)]);

        assert_eq!(
            excluded_class_lower_bound(Some(&objective), Some(&preserved(&[0])), &solution),
            BigInt::zero(),
            "... but x2 is not preserved, so the excluded class also contains \
             assignments with x2 false, of objective value 0"
        );
    }

    /// A negative coefficient minimises by making its literal *true*, so the
    /// free choice contributes the coefficient rather than nothing.
    #[test]
    fn a_free_negative_coefficient_contributes_its_value() {
        let objective = objective(vec![(-7, lit(1, false))], 5);
        let solution = assignment(&[lit(0, false), lit(1, true)]);

        assert_eq!(
            excluded_class_lower_bound(Some(&objective), Some(&preserved(&[0])), &solution),
            BigInt::from(-2),
            "the constant 5 plus the minimising choice -7 for the free x2"
        );
    }

    /// A preserved literal the logged solution leaves unassigned is not really
    /// pinned; `solx` rejects that case, but the bound must not assume a value.
    #[test]
    fn an_unassigned_preserved_variable_is_treated_as_free() {
        let objective = objective(vec![(-3, lit(5, false))], 0);
        let solution = assignment(&[lit(0, false)]);

        assert_eq!(
            excluded_class_lower_bound(Some(&objective), Some(&preserved(&[5])), &solution),
            BigInt::from(-3),
        );
    }

    /// Without a preserved set nothing is pinned down at all. `solx` is rejected
    /// on that path anyway (`NoPreservedForSolutionExcluding`); the conservative
    /// reading keeps the helper total.
    #[test]
    fn without_a_preserved_set_every_variable_is_free() {
        let objective = objective(vec![(4, lit(0, false)), (-9, lit(1, false))], 1);
        let solution = assignment(&[lit(0, false), lit(1, false)]);

        assert_eq!(
            excluded_class_lower_bound(Some(&objective), None, &solution),
            BigInt::from(-8),
        );
        assert_eq!(
            excluded_class_lower_bound(None, Some(&preserved(&[0])), &solution),
            BigInt::zero(),
            "with no objective there is nothing to bound"
        );
    }
}
