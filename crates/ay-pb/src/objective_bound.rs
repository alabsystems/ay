// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared pseudo-Boolean objective-bound encoders.

use crate::types::{PbConstraint, PbObjective, PbRel, PbTerm};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ObjectiveBoundError {
    Bound,
    Coefficient,
}

pub(crate) fn objective_at_most_constraint(
    objective: &PbObjective,
    upper_bound: i128,
) -> Result<PbConstraint, ObjectiveBoundError> {
    let rhs = upper_bound
        .checked_neg()
        .ok_or(ObjectiveBoundError::Bound)?;
    let mut terms = Vec::with_capacity(objective.terms.len());
    for term in &objective.terms {
        terms.push(PbTerm {
            coeff: term
                .coeff
                .checked_neg()
                .ok_or(ObjectiveBoundError::Coefficient)?,
            lits: term.lits.clone(),
        });
    }

    Ok(PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs,
    })
}

pub(crate) fn strictly_better_than_incumbent_constraint(
    objective: &PbObjective,
    incumbent: i128,
) -> Result<PbConstraint, ObjectiveBoundError> {
    let upper_bound = incumbent.checked_sub(1).ok_or(ObjectiveBoundError::Bound)?;
    objective_at_most_constraint(objective, upper_bound)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::PbLit;

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }

    fn term(coeff: i128, var: u32) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![lit(var)],
        }
    }

    fn objective() -> PbObjective {
        PbObjective {
            terms: vec![term(3, 1), term(-2, 2)],
        }
    }

    #[test]
    fn objective_at_most_constraint_negates_objective_row() {
        let constraint = objective_at_most_constraint(&objective(), 7).expect("bound encodes");

        assert_eq!(constraint.rel, PbRel::Ge);
        assert_eq!(constraint.rhs, -7);
        assert_eq!(constraint.terms, vec![term(-3, 1), term(2, 2)]);
    }

    #[test]
    fn strictly_better_than_incumbent_uses_incumbent_minus_one() {
        let constraint =
            strictly_better_than_incumbent_constraint(&objective(), 5).expect("bound encodes");

        assert_eq!(constraint.rel, PbRel::Ge);
        assert_eq!(constraint.rhs, -4);
        assert_eq!(constraint.terms, vec![term(-3, 1), term(2, 2)]);
    }

    #[test]
    fn objective_bound_rejects_arithmetic_overflow() {
        let overflow_objective = PbObjective {
            terms: vec![term(i128::MIN, 1)],
        };

        assert_eq!(
            objective_at_most_constraint(&overflow_objective, 0),
            Err(ObjectiveBoundError::Coefficient)
        );
        assert_eq!(
            objective_at_most_constraint(&objective(), i128::MIN),
            Err(ObjectiveBoundError::Bound)
        );
        assert_eq!(
            strictly_better_than_incumbent_constraint(&objective(), i128::MIN),
            Err(ObjectiveBoundError::Bound)
        );
    }
}
