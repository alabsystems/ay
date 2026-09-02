// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Evaluation compatibility helpers for PB constraints and objectives.

use crate::solver::eval_constraint;
use crate::types::{PbConstraint, WboInstance};

// `verify_all_constraints` carries a native Trust `ensures` clause. A clause is RAW
// GRAMMAR — cfg-stripping runs after parsing — so it cannot be hidden from a
// compiler that lacks the extension, and it would make this whole file unreadable
// to one. It therefore lives alone in a fragment: the verifier reads
// `eval/vig_core.rs`, everyone else reads `eval/vig_core_stock.rs`, and the two are
// pinned together by `tests/native_contract_twins.rs`. Both are `include!`d rather
// than made a submodule so the function keeps this module, its `crate::`
// re-export and its doc links.
#[cfg(deductive_verify)]
include!("eval/vig_core.rs");
#[cfg(not(deductive_verify))]
include!("eval/vig_core_stock.rs");

/// The WBO Verified Incumbent Gate (campaign M0: WBO-VIG consolidation): the
/// SINGLE audited chokepoint deciding whether an assignment is an admissible
/// WBO model and what its true cost is.
///
/// Returns `Some(cost)` iff ALL of:
/// 1. the assignment covers the WBO variable space (`num_vars` prefix exists);
/// 2. every HARD constraint is satisfied ([`verify_all_constraints`]);
/// 3. the total cost of falsified soft constraints is computable without
///    overflow; and
/// 4. that cost is STRICTLY LESS than the `soft:` top cost when one is given
///    (official WBO semantics: an assignment reaching the top is NOT a model).
///
/// `None` is fail-closed: callers must not emit the assignment as a model or
/// print its cost. Every WBO emission/caching path routes through this gate
/// (both driver binaries; future WBO arms MUST use it rather than re-deriving
/// the checks — the 2026 PARTIAL-LIN wrong answers came from exactly such a
/// scattered re-derivation missing rule 4).
#[must_use]
pub fn wbo_admissible_cost(wbo: &WboInstance, assignment: &[bool]) -> Option<i128> {
    let num_vars = usize::try_from(wbo.num_vars).ok()?;
    let projected = assignment.get(..num_vars)?;
    if !verify_all_constraints(&wbo.hard_constraints, projected) {
        return None;
    }
    let mut total = 0_i128;
    for (cost, constraint) in &wbo.soft_constraints {
        if eval_constraint(constraint, projected) {
            continue;
        }
        total = total.checked_add(*cost)?;
    }
    if wbo.top_cost.is_some_and(|top| total >= top) {
        return None;
    }
    Some(total)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::{eval_constraint, eval_objective};
    use crate::types::{PbLit, PbObjective, PbRel, PbTerm};

    fn lit(var: u32, negated: bool) -> PbLit {
        PbLit { var, negated }
    }

    fn linear_term(coeff: i128, var: u32) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![lit(var, false)],
        }
    }

    fn negated_term(coeff: i128, var: u32) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![lit(var, true)],
        }
    }

    #[test]
    fn test_eval_constraint_ge_satisfied() {
        // +1 x1 +1 x2 >= 1 with x1=true, x2=false => 1 >= 1 => true
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1), linear_term(1, 2)],
            rel: PbRel::Ge,
            rhs: 1,
        };
        assert!(eval_constraint(&constraint, &[true, false]));
    }

    #[test]
    fn test_eval_constraint_ge_not_satisfied() {
        // +1 x1 +1 x2 >= 2 with x1=true, x2=false => 1 >= 2 => false
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1), linear_term(1, 2)],
            rel: PbRel::Ge,
            rhs: 2,
        };
        assert!(!eval_constraint(&constraint, &[true, false]));
    }

    #[test]
    fn test_eval_constraint_eq_satisfied() {
        // +1 x1 -1 x2 = 0 with x1=true, x2=true => 1 - 1 = 0 => true
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1), linear_term(-1, 2)],
            rel: PbRel::Eq,
            rhs: 0,
        };
        assert!(eval_constraint(&constraint, &[true, true]));
    }

    #[test]
    fn test_eval_constraint_eq_not_satisfied() {
        // +1 x1 -1 x2 = 0 with x1=true, x2=false => 1 - 0 = 1 != 0 => false
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1), linear_term(-1, 2)],
            rel: PbRel::Eq,
            rhs: 0,
        };
        assert!(!eval_constraint(&constraint, &[true, false]));
    }

    #[test]
    fn test_eval_constraint_negated_literal() {
        // +1 ~x1 >= 1 with x1=false => ~false=true => 1 >= 1 => true
        let constraint = PbConstraint {
            terms: vec![negated_term(1, 1)],
            rel: PbRel::Ge,
            rhs: 1,
        };
        assert!(eval_constraint(&constraint, &[false]));
    }

    #[test]
    fn test_eval_constraint_negated_literal_not_satisfied() {
        // +1 ~x1 >= 1 with x1=true => ~true=false => 0 >= 1 => false
        let constraint = PbConstraint {
            terms: vec![negated_term(1, 1)],
            rel: PbRel::Ge,
            rhs: 1,
        };
        assert!(!eval_constraint(&constraint, &[true]));
    }

    #[test]
    fn test_eval_constraint_nonlinear() {
        // +1 x1 x2 >= 1 with x1=true, x2=true => 1*1*1=1 >= 1 => true
        let constraint = PbConstraint {
            terms: vec![PbTerm {
                coeff: 1,
                lits: vec![lit(1, false), lit(2, false)],
            }],
            rel: PbRel::Ge,
            rhs: 1,
        };
        assert!(eval_constraint(&constraint, &[true, true]));
    }

    #[test]
    fn test_eval_constraint_nonlinear_false() {
        // +1 x1 x2 >= 1 with x1=true, x2=false => 1*1*0=0 >= 1 => false
        let constraint = PbConstraint {
            terms: vec![PbTerm {
                coeff: 1,
                lits: vec![lit(1, false), lit(2, false)],
            }],
            rel: PbRel::Ge,
            rhs: 1,
        };
        assert!(!eval_constraint(&constraint, &[true, false]));
    }

    #[test]
    fn test_eval_objective() {
        // min: +1 x1 +2 x2 with x1=true, x2=false => 1 + 0 = 1
        let objective = PbObjective {
            terms: vec![linear_term(1, 1), linear_term(2, 2)],
        };
        assert_eq!(eval_objective(&objective, &[true, false]), 1);
    }

    #[test]
    fn test_eval_objective_all_true() {
        // min: +1 x1 +2 x2 with x1=true, x2=true => 1 + 2 = 3
        let objective = PbObjective {
            terms: vec![linear_term(1, 1), linear_term(2, 2)],
        };
        assert_eq!(eval_objective(&objective, &[true, true]), 3);
    }

    #[test]
    fn test_eval_objective_all_false() {
        // min: +1 x1 +2 x2 with all false => 0
        let objective = PbObjective {
            terms: vec![linear_term(1, 1), linear_term(2, 2)],
        };
        assert_eq!(eval_objective(&objective, &[false, false]), 0);
    }

    #[test]
    fn test_verify_all_constraints_satisfied() {
        let constraints = vec![
            PbConstraint {
                terms: vec![linear_term(1, 1)],
                rel: PbRel::Ge,
                rhs: 1,
            },
            PbConstraint {
                terms: vec![linear_term(1, 2)],
                rel: PbRel::Ge,
                rhs: 1,
            },
        ];
        assert!(verify_all_constraints(&constraints, &[true, true]));
    }

    #[test]
    fn test_verify_all_constraints_one_fails() {
        let constraints = vec![
            PbConstraint {
                terms: vec![linear_term(1, 1)],
                rel: PbRel::Ge,
                rhs: 1,
            },
            PbConstraint {
                terms: vec![linear_term(1, 2)],
                rel: PbRel::Ge,
                rhs: 1,
            },
        ];
        assert!(!verify_all_constraints(&constraints, &[true, false]));
    }

    #[test]
    fn test_verify_all_constraints_handles_i128_overflow_exactly() {
        let constraints = vec![PbConstraint {
            terms: vec![linear_term(i128::MAX, 1), linear_term(1, 2)],
            rel: PbRel::Ge,
            rhs: i128::MAX,
        }];

        assert!(verify_all_constraints(&constraints, &[true, true]));
    }

    #[test]
    fn test_eval_constraint_large_coefficients() {
        // +1000000 x1 +2000000 x2 >= 3000000 with both true
        let constraint = PbConstraint {
            terms: vec![linear_term(1_000_000, 1), linear_term(2_000_000, 2)],
            rel: PbRel::Ge,
            rhs: 3_000_000,
        };
        assert!(eval_constraint(&constraint, &[true, true]));
    }

    #[test]
    fn test_eval_constraint_negative_rhs() {
        // +1 x1 >= -5 with x1=false => 0 >= -5 => true
        let constraint = PbConstraint {
            terms: vec![linear_term(1, 1)],
            rel: PbRel::Ge,
            rhs: -5,
        };
        assert!(eval_constraint(&constraint, &[false]));
    }
}

#[cfg(test)]
mod wbo_vig_tests {
    use super::*;
    use crate::types::{PbLit, PbRel, PbTerm};

    fn unit(coeff: i128, var: u32) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![PbLit {
                var,
                negated: false,
            }],
        }
    }

    fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }
    }

    fn wbo(top: Option<i128>) -> WboInstance {
        // hard: x1 + x2 <= 1; softs: [2] x1, [2] x2 — min cost 2.
        WboInstance {
            top_cost: top,
            num_vars: 2,
            hard_constraints: vec![ge(vec![unit(-1, 1), unit(-1, 2)], -1)],
            soft_constraints: vec![(2, ge(vec![unit(1, 1)], 1)), (2, ge(vec![unit(1, 2)], 1))],
            objective: None,
        }
    }

    #[test]
    fn admits_model_strictly_below_top() {
        assert_eq!(wbo_admissible_cost(&wbo(Some(3)), &[true, false]), Some(2));
    }

    #[test]
    fn rejects_model_at_top() {
        assert_eq!(wbo_admissible_cost(&wbo(Some(2)), &[true, false]), None);
    }

    #[test]
    fn rejects_hard_violation_even_with_admissible_cost() {
        // x1 = x2 = true violates the hard row; cost would be 0 (< top).
        assert_eq!(wbo_admissible_cost(&wbo(Some(3)), &[true, true]), None);
    }

    #[test]
    fn rejects_short_assignment() {
        assert_eq!(wbo_admissible_cost(&wbo(Some(3)), &[true]), None);
    }

    #[test]
    fn omitted_top_is_unbounded() {
        assert_eq!(wbo_admissible_cost(&wbo(None), &[false, false]), Some(4));
    }

    #[test]
    fn fails_closed_on_cost_overflow() {
        let mut instance = wbo(None);
        instance.soft_constraints = vec![
            (i128::MAX, ge(vec![unit(1, 1)], 1)),
            (i128::MAX, ge(vec![unit(1, 2)], 1)),
        ];
        assert_eq!(wbo_admissible_cost(&instance, &[false, false]), None);
    }
}
