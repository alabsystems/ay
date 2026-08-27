// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::{PbConstraint, PbLit, PbObjective, PbRel, PbTerm};
use num_bigint::BigInt;
use num_traits::ToPrimitive;

/// Failure while exactly evaluating a pseudo-Boolean objective.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObjectiveEvalError {
    /// The final mathematical objective sum is outside the `i128` range.
    Overflow,
}

/// Evaluates a pseudo-Boolean constraint under a total Boolean assignment.
///
/// The common path accumulates with checked `i128` arithmetic. If an extreme
/// public or parsed constraint exceeds that range, evaluation falls back to
/// [`BigInt`] rather than panicking or wrapping. Returns `false` when a literal
/// has variable index zero or falls outside `assignment`; an incomplete model
/// must not pass an incumbent check because a missing negated literal happened
/// to look true.
#[must_use]
pub fn eval_constraint(constraint: &PbConstraint, assignment: &[bool]) -> bool {
    if !assignment_covers_constraint(constraint, assignment.len()) {
        return false;
    }

    match eval_terms_checked(&constraint.terms, assignment) {
        Ok(lhs) => match constraint.rel {
            PbRel::Ge => lhs >= constraint.rhs,
            PbRel::Eq => lhs == constraint.rhs,
        },
        Err(ObjectiveEvalError::Overflow) => eval_constraint_bigint(constraint, assignment),
    }
}

fn assignment_covers_constraint(constraint: &PbConstraint, assignment_len: usize) -> bool {
    constraint.terms.iter().all(|term| {
        term.lits.iter().all(|lit| {
            lit.var
                .checked_sub(1)
                .and_then(|index| usize::try_from(index).ok())
                .is_some_and(|index| index < assignment_len)
        })
    })
}

fn eval_constraint_bigint(constraint: &PbConstraint, assignment: &[bool]) -> bool {
    let lhs = eval_terms_bigint(&constraint.terms, assignment);
    let rhs = BigInt::from(constraint.rhs);
    match constraint.rel {
        PbRel::Ge => lhs >= rhs,
        PbRel::Eq => lhs == rhs,
    }
}

/// Evaluates a pseudo-Boolean objective under a total Boolean assignment.
pub fn eval_objective(objective: &PbObjective, assignment: &[bool]) -> i128 {
    if let Some(value) = eval_objective_checked(objective, assignment) {
        return value;
    }

    match eval_objective_exact(objective, assignment) {
        Ok(value) => saturating_i128_to_i64(value),
        Err(ObjectiveEvalError::Overflow) => {
            saturating_i128_to_i64(eval_terms_saturating(&objective.terms, assignment))
        }
    }
}

/// Evaluates a pseudo-Boolean objective exactly in `i128`.
///
/// The common path uses checked `i128` accumulation. If an intermediate sum
/// overflows, evaluation falls back to [`BigInt`] so later cancellation remains
/// exact. Returns [`ObjectiveEvalError::Overflow`] only when the final
/// mathematical sum is outside the `i128` range.
pub fn eval_objective_exact(
    objective: &PbObjective,
    assignment: &[bool],
) -> Result<i128, ObjectiveEvalError> {
    match eval_terms_checked(&objective.terms, assignment) {
        Ok(value) => Ok(value),
        Err(ObjectiveEvalError::Overflow) => eval_terms_bigint(&objective.terms, assignment)
            .to_i128()
            .ok_or(ObjectiveEvalError::Overflow),
    }
}

/// Evaluates an objective and returns `None` if the exact value does not fit `i128`.
pub(crate) fn eval_objective_checked(objective: &PbObjective, assignment: &[bool]) -> Option<i128> {
    checked_i128_to_i64(eval_objective_exact(objective, assignment).ok()?)
}

/// Returns true if every possible objective value fits in `i128`.
pub fn objective_range_fits_i64(objective: &PbObjective) -> bool {
    let mut lower = 0i128;
    let mut upper = 0i128;

    for term in &objective.terms {
        let coeff = term.coeff;
        if coeff < 0 {
            let Some(next) = lower.checked_add(coeff) else {
                return false;
            };
            lower = next;
        } else if coeff > 0 {
            let Some(next) = upper.checked_add(coeff) else {
                return false;
            };
            upper = next;
        }
    }

    // Reaching here means neither accumulator overflowed (the `checked_add`s
    // above return early otherwise), so the objective range fits in i128.
    true
}

fn eval_terms_checked(terms: &[PbTerm], assignment: &[bool]) -> Result<i128, ObjectiveEvalError> {
    terms
        .iter()
        .filter(|term| eval_term(term, assignment))
        .try_fold(0i128, |sum, term| {
            sum.checked_add(term.coeff)
                .ok_or(ObjectiveEvalError::Overflow)
        })
}

fn eval_terms_bigint(terms: &[PbTerm], assignment: &[bool]) -> BigInt {
    let mut sum = BigInt::from(0);
    for term in terms.iter().filter(|term| eval_term(term, assignment)) {
        sum += BigInt::from(term.coeff);
    }
    sum
}

fn eval_terms_saturating(terms: &[PbTerm], assignment: &[bool]) -> i128 {
    terms
        .iter()
        .filter(|term| eval_term(term, assignment))
        .fold(0i128, |sum, term| sum.saturating_add(term.coeff))
}

fn eval_term(term: &PbTerm, assignment: &[bool]) -> bool {
    term.lits
        .iter()
        .copied()
        .all(|lit| eval_lit(lit, assignment))
}

fn eval_lit(lit: PbLit, assignment: &[bool]) -> bool {
    let value = lit
        .var
        .checked_sub(1)
        .and_then(|index| usize::try_from(index).ok())
        .and_then(|index| assignment.get(index))
        .copied()
        .unwrap_or(false);

    if lit.negated {
        !value
    } else {
        value
    }
}

// Inert i64-era helpers: objectives are now `i128`, so there is nothing to clamp
// or range-check (the real overflow protection is the `checked_add` in
// `eval_terms_checked` / `objective_range_fits_i64`). Kept as explicit no-ops to
// avoid churning ~20 call sites; the bodies no longer trip clippy's
// absurd-comparison lint.
fn saturating_i128_to_i64(value: i128) -> i128 {
    value
}

fn checked_i128_to_i64(value: i128) -> Option<i128> {
    Some(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }

    fn not(var: u32) -> PbLit {
        PbLit { var, negated: true }
    }

    fn term(coeff: i128, lits: Vec<PbLit>) -> PbTerm {
        PbTerm { coeff, lits }
    }

    #[test]
    fn test_eval_constraint_ge_with_linear_terms() {
        let constraint = PbConstraint {
            terms: vec![term(2, vec![lit(1)]), term(3, vec![lit(2)])],
            rel: PbRel::Ge,
            rhs: 3,
        };

        assert!(!eval_constraint(&constraint, &[true, false]));
        assert!(eval_constraint(&constraint, &[false, true]));
    }

    #[test]
    fn test_eval_constraint_eq_with_negated_literal() {
        let constraint = PbConstraint {
            terms: vec![term(1, vec![not(1)]), term(1, vec![lit(2)])],
            rel: PbRel::Eq,
            rhs: 2,
        };

        assert!(eval_constraint(&constraint, &[false, true]));
        assert!(!eval_constraint(&constraint, &[true, true]));
    }

    #[test]
    fn test_eval_constraint_with_nonlinear_term() {
        let constraint = PbConstraint {
            terms: vec![term(5, vec![lit(1), lit(2)]), term(-2, vec![lit(3)])],
            rel: PbRel::Ge,
            rhs: 3,
        };

        assert!(eval_constraint(&constraint, &[true, true, false]));
        assert!(!eval_constraint(&constraint, &[true, false, false]));
    }

    #[test]
    fn test_eval_constraint_rejects_missing_variables() {
        let constraint = PbConstraint {
            terms: vec![term(1, vec![lit(2)])],
            rel: PbRel::Ge,
            rhs: 1,
        };

        assert!(!eval_constraint(&constraint, &[true]));
    }

    #[test]
    fn test_eval_constraint_rejects_missing_negated_variables() {
        let constraint = PbConstraint {
            terms: vec![term(1, vec![not(2)])],
            rel: PbRel::Ge,
            rhs: 1,
        };

        assert!(!eval_constraint(&constraint, &[true]));
    }

    #[test]
    fn test_eval_constraint_rejects_variable_zero() {
        let constraint = PbConstraint {
            terms: vec![term(1, vec![not(0)])],
            rel: PbRel::Ge,
            rhs: 1,
        };

        assert!(!eval_constraint(&constraint, &[true]));
    }

    #[test]
    fn test_eval_constraint_positive_overflow_is_exact() {
        let constraint = PbConstraint {
            terms: vec![term(i128::MAX, vec![lit(1)]), term(1, vec![lit(2)])],
            rel: PbRel::Ge,
            rhs: i128::MAX,
        };

        assert!(eval_constraint(&constraint, &[true, true]));
    }

    #[test]
    fn test_eval_constraint_negative_overflow_is_exact() {
        let constraint = PbConstraint {
            terms: vec![term(i128::MIN, vec![lit(1)]), term(-1, vec![lit(2)])],
            rel: PbRel::Ge,
            rhs: i128::MIN,
        };

        assert!(!eval_constraint(&constraint, &[true, true]));
    }

    #[test]
    fn test_eval_constraint_transient_overflow_with_cancellation_is_exact() {
        let constraint = PbConstraint {
            terms: vec![
                term(i128::MAX, vec![lit(1)]),
                term(1, vec![lit(2)]),
                term(-1, vec![lit(3)]),
            ],
            rel: PbRel::Eq,
            rhs: i128::MAX,
        };

        assert!(eval_constraint(&constraint, &[true, true, true]));
    }

    #[test]
    fn test_eval_objective_sums_true_terms() {
        let objective = PbObjective {
            terms: vec![
                term(10, vec![lit(1)]),
                term(-4, vec![not(2)]),
                term(7, vec![lit(1), lit(3)]),
            ],
        };

        assert_eq!(eval_objective(&objective, &[true, false, true]), 13);
        assert_eq!(eval_objective(&objective, &[false, false, true]), -4);
    }

    #[test]
    fn test_eval_objective_saturates_on_overflow() {
        let objective = PbObjective {
            terms: vec![term(i128::MAX, vec![lit(1)]), term(1, vec![lit(2)])],
        };

        assert_eq!(eval_objective(&objective, &[true, true]), i128::MAX);
        assert_eq!(
            eval_objective_exact(&objective, &[true, true]),
            Err(ObjectiveEvalError::Overflow)
        );
    }

    #[test]
    fn test_eval_objective_exact_recovers_positive_overflow_with_cancellation() {
        let objective = PbObjective {
            terms: vec![
                term(i128::MAX, vec![lit(1)]),
                term(1, vec![lit(2)]),
                term(-1, vec![lit(3)]),
            ],
        };

        assert_eq!(
            eval_objective_exact(&objective, &[true, true, true]),
            Ok(i128::MAX)
        );
    }

    #[test]
    fn test_eval_objective_exact_diverges_from_checked_fold_on_recoverable_overflow() {
        // WITNESS for the deductive-checks TARGET 2 contract. The BigInt fallback makes
        // `eval_objective_exact` STRICTLY MORE DEFINED than the checked fold it
        // starts from: here the fold's INTERMEDIATE `i128::MAX + 1` overflows
        // (so `eval_terms_checked` fails closed) while the exact mathematical
        // sum `i128::MAX` fits, so the function recovers `Ok(i128::MAX)`.
        //
        // The two therefore DISAGREE on this input, which is why the fixture may
        // NOT pin `result == eval_terms_checked(&objective.terms, assignment)`:
        // that contract is FALSE of the shipped body exactly here. The honest
        // contract is the two-armed one the body implements (Ok-passthrough plus
        // the exact-BigInt narrowing on the Err arm).
        let objective = PbObjective {
            terms: vec![
                term(i128::MAX, vec![lit(1)]),
                term(1, vec![lit(2)]),
                term(-1, vec![lit(3)]),
            ],
        };
        let assignment = [true, true, true];

        assert_eq!(
            eval_terms_checked(&objective.terms, &assignment),
            Err(ObjectiveEvalError::Overflow),
            "the checked fold must fail closed on the intermediate overflow"
        );
        assert_eq!(
            eval_objective_exact(&objective, &assignment),
            Ok(i128::MAX),
            "the live body must recover the exact in-range sum"
        );
        assert_ne!(
            eval_objective_exact(&objective, &assignment),
            eval_terms_checked(&objective.terms, &assignment),
            "the live body is NOT the checked fold — the divergence the overflow \
             fallback exists for"
        );
    }

    #[test]
    fn test_eval_objective_exact_recovers_negative_overflow_with_cancellation() {
        let objective = PbObjective {
            terms: vec![
                term(i128::MIN, vec![lit(1)]),
                term(-1, vec![lit(2)]),
                term(1, vec![lit(3)]),
            ],
        };

        assert_eq!(
            eval_objective_exact(&objective, &[true, true, true]),
            Ok(i128::MIN)
        );
    }

    #[test]
    fn test_eval_objective_exact_keeps_positive_i64_overflow() {
        // A sum that is far beyond the old i64 range but still fits the
        // supported i128 range must be preserved EXACTLY (not saturated and
        // not rejected). `i128::MAX - 1` + `1` lands exactly on `i128::MAX`.
        let objective = PbObjective {
            terms: vec![term(i128::MAX - 1, vec![lit(1)]), term(1, vec![lit(2)])],
        };

        assert_eq!(
            eval_objective_exact(&objective, &[true, true]),
            Ok(i128::MAX)
        );
        // It fits i128, so the saturating and checked paths keep it exact too.
        assert_eq!(eval_objective(&objective, &[true, true]), i128::MAX);
        assert_eq!(
            eval_objective_checked(&objective, &[true, true]),
            Some(i128::MAX)
        );
    }

    #[test]
    fn test_eval_objective_exact_keeps_negative_i64_overflow() {
        // A sum far below the old i64 range that still fits i128 must be kept
        // exact. `(i128::MIN + 1)` + `(-1)` lands exactly on `i128::MIN`.
        let objective = PbObjective {
            terms: vec![term(i128::MIN + 1, vec![lit(1)]), term(-1, vec![lit(2)])],
        };

        assert_eq!(
            eval_objective_exact(&objective, &[true, true]),
            Ok(i128::MIN)
        );
        assert_eq!(eval_objective(&objective, &[true, true]), i128::MIN);
        assert_eq!(
            eval_objective_checked(&objective, &[true, true]),
            Some(i128::MIN)
        );
    }

    #[test]
    fn test_eval_objective_checked_accepts_i64_boundary_values() {
        let objective = PbObjective {
            terms: vec![term(i128::MAX, vec![lit(1)]), term(i128::MIN, vec![lit(2)])],
        };

        assert_eq!(
            eval_objective_checked(&objective, &[true, false]),
            Some(i128::MAX)
        );
        assert_eq!(
            eval_objective_checked(&objective, &[false, true]),
            Some(i128::MIN)
        );
        assert_eq!(eval_objective_checked(&objective, &[true, true]), Some(-1));
    }

    #[test]
    fn test_objective_range_fits_i64_accepts_mixed_safe_range() {
        let objective = PbObjective {
            terms: vec![term(10, vec![lit(1)]), term(-4, vec![not(2)])],
        };
        assert!(objective_range_fits_i64(&objective));
    }

    #[test]
    fn test_objective_range_fits_i64_rejects_positive_overflow() {
        let objective = PbObjective {
            terms: vec![term(i128::MAX, vec![lit(1)]), term(1, vec![lit(2)])],
        };

        assert!(!objective_range_fits_i64(&objective));
    }

    #[test]
    fn test_objective_range_fits_i64_rejects_negative_underflow() {
        let objective = PbObjective {
            terms: vec![term(i128::MIN, vec![lit(1)]), term(-1, vec![lit(2)])],
        };

        assert!(!objective_range_fits_i64(&objective));
    }
}
