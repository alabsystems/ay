// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Linearization of non-linear pseudo-Boolean terms.

use crate::types::{PbConstraint, PbInstance, PbLit, PbObjective, PbRel, PbTerm};

/// Returns `true` when every constraint and objective term is already linear.
pub fn is_linear(instance: &PbInstance) -> bool {
    instance
        .constraints
        .iter()
        .all(|constraint| constraint.terms.iter().all(|term| term.lits.len() <= 1))
        && instance
            .objective
            .as_ref()
            .map(|objective| objective.terms.iter().all(|term| term.lits.len() <= 1))
            .unwrap_or(true)
}

/// Replaces every non-linear term with a fresh auxiliary variable and AND constraints.
pub fn linearize(instance: &PbInstance) -> PbInstance {
    if is_linear(instance) {
        return instance.clone();
    }

    let mut next_var = instance.num_vars;
    let mut constraints = Vec::new();

    for constraint in &instance.constraints {
        let mut aux_constraints = Vec::new();
        let terms = linearize_terms(&constraint.terms, &mut next_var, &mut aux_constraints);
        constraints.extend(aux_constraints);
        constraints.push(PbConstraint {
            terms,
            rel: constraint.rel,
            rhs: constraint.rhs,
        });
    }

    let objective = if let Some(objective) = &instance.objective {
        let mut aux_constraints = Vec::new();
        let terms = linearize_terms(&objective.terms, &mut next_var, &mut aux_constraints);
        constraints.extend(aux_constraints);
        Some(PbObjective { terms })
    } else {
        None
    };

    PbInstance {
        num_vars: next_var,
        num_constraints: u32::try_from(constraints.len())
            .expect("linearized instance must fit within u32 constraint counts"),
        constraints,
        objective,
    }
}

fn linearize_terms(
    terms: &[PbTerm],
    next_var: &mut u32,
    aux_constraints: &mut Vec<PbConstraint>,
) -> Vec<PbTerm> {
    terms
        .iter()
        .map(|term| linearize_term(term, next_var, aux_constraints))
        .collect()
}

fn linearize_term(
    term: &PbTerm,
    next_var: &mut u32,
    aux_constraints: &mut Vec<PbConstraint>,
) -> PbTerm {
    if term.lits.len() <= 1 {
        return term.clone();
    }

    let aux_var = fresh_var(next_var);
    let aux_pos = PbLit {
        var: aux_var,
        negated: false,
    };
    let aux_neg = PbLit {
        var: aux_var,
        negated: true,
    };

    for factor in &term.lits {
        aux_constraints.push(PbConstraint {
            terms: vec![
                PbTerm {
                    coeff: 1,
                    lits: vec![aux_neg],
                },
                PbTerm {
                    coeff: 1,
                    lits: vec![*factor],
                },
            ],
            rel: PbRel::Ge,
            rhs: 1,
        });
    }

    let mut lower_bound_terms = Vec::with_capacity(term.lits.len() + 1);
    lower_bound_terms.push(PbTerm {
        coeff: 1,
        lits: vec![aux_pos],
    });
    for factor in &term.lits {
        lower_bound_terms.push(PbTerm {
            coeff: -1,
            lits: vec![*factor],
        });
    }

    let lit_count =
        i128::try_from(term.lits.len()).expect("term literal count must fit within i128");
    aux_constraints.push(PbConstraint {
        terms: lower_bound_terms,
        rel: PbRel::Ge,
        rhs: 1 - lit_count,
    });

    PbTerm {
        coeff: term.coeff,
        lits: vec![aux_pos],
    }
}

fn fresh_var(next_var: &mut u32) -> u32 {
    *next_var = next_var
        .checked_add(1)
        .expect("linearization variable count must fit within u32");
    *next_var
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::{eval_constraint, eval_objective};

    fn lit(var: u32, negated: bool) -> PbLit {
        PbLit { var, negated }
    }

    fn term(coeff: i128, lits: Vec<PbLit>) -> PbTerm {
        PbTerm { coeff, lits }
    }

    fn linear_term(coeff: i128, var: u32) -> PbTerm {
        term(coeff, vec![lit(var, false)])
    }

    fn negated_term(coeff: i128, var: u32) -> PbTerm {
        term(coeff, vec![lit(var, true)])
    }

    fn assignments(num_vars: u32) -> Vec<Vec<bool>> {
        let total = 1usize
            .checked_shl(num_vars)
            .expect("test assignment space must fit in usize");

        (0..total)
            .map(|mask| {
                (0..num_vars)
                    .map(|index| ((mask >> index) & 1) == 1)
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    fn satisfying_extensions(
        instance: &PbInstance,
        original_assignment: &[bool],
        original_num_vars: u32,
    ) -> Vec<Vec<bool>> {
        let extra_vars = instance
            .num_vars
            .checked_sub(original_num_vars)
            .expect("linearized instance cannot reduce the variable count");
        let total = 1usize
            .checked_shl(extra_vars)
            .expect("test extension space must fit in usize");

        (0..total)
            .filter_map(|mask| {
                let mut assignment = original_assignment.to_vec();
                for index in 0..extra_vars {
                    assignment.push(((mask >> index) & 1) == 1);
                }

                if instance
                    .constraints
                    .iter()
                    .all(|constraint| eval_constraint(constraint, &assignment))
                {
                    Some(assignment)
                } else {
                    None
                }
            })
            .collect()
    }

    fn assert_equivalent(original: &PbInstance, linearized: &PbInstance) {
        assert!(is_linear(linearized));

        for original_assignment in assignments(original.num_vars) {
            let original_satisfied = original
                .constraints
                .iter()
                .all(|constraint| eval_constraint(constraint, &original_assignment));
            let extensions =
                satisfying_extensions(linearized, &original_assignment, original.num_vars);

            assert_eq!(
                !extensions.is_empty(),
                original_satisfied,
                "feasibility mismatch for assignment {original_assignment:?}"
            );

            match (&original.objective, &linearized.objective) {
                (Some(original_objective), Some(linearized_objective)) => {
                    let expected = eval_objective(original_objective, &original_assignment);
                    for extension in &extensions {
                        assert_eq!(
                            eval_objective(linearized_objective, extension),
                            expected,
                            "objective mismatch for assignment {original_assignment:?}"
                        );
                    }
                }
                (None, None) => {}
                _ => panic!("objective presence must be preserved"),
            }
        }
    }

    #[test]
    fn linear_instance_passes_through_unchanged() {
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 2,
            constraints: vec![
                PbConstraint {
                    terms: vec![linear_term(2, 1), negated_term(-3, 2)],
                    rel: PbRel::Ge,
                    rhs: 0,
                },
                PbConstraint {
                    terms: vec![linear_term(1, 3)],
                    rel: PbRel::Eq,
                    rhs: 1,
                },
            ],
            objective: Some(PbObjective {
                terms: vec![linear_term(5, 1), negated_term(-2, 2)],
            }),
        };

        assert!(is_linear(&instance));
        assert_eq!(linearize(&instance), instance);
    }

    #[test]
    fn single_nonlinear_term_gets_linearized() {
        let instance = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![PbConstraint {
                terms: vec![term(3, vec![lit(1, false), lit(2, false)])],
                rel: PbRel::Ge,
                rhs: 2,
            }],
            objective: None,
        };

        let linearized = linearize(&instance);

        assert_eq!(linearized.num_vars, 3);
        assert_eq!(linearized.num_constraints, 4);
        assert_eq!(linearized.constraints.len(), 4);
        assert_eq!(
            linearized.constraints[0],
            PbConstraint {
                terms: vec![negated_term(1, 3), linear_term(1, 1)],
                rel: PbRel::Ge,
                rhs: 1,
            }
        );
        assert_eq!(
            linearized.constraints[1],
            PbConstraint {
                terms: vec![negated_term(1, 3), linear_term(1, 2)],
                rel: PbRel::Ge,
                rhs: 1,
            }
        );
        assert_eq!(
            linearized.constraints[2],
            PbConstraint {
                terms: vec![linear_term(1, 3), linear_term(-1, 1), linear_term(-1, 2)],
                rel: PbRel::Ge,
                rhs: -1,
            }
        );
        assert_eq!(
            linearized.constraints[3],
            PbConstraint {
                terms: vec![linear_term(3, 3)],
                rel: PbRel::Ge,
                rhs: 2,
            }
        );

        assert_equivalent(&instance, &linearized);
    }

    #[test]
    fn multiple_nonlinear_terms_are_linearized() {
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 2,
            constraints: vec![
                PbConstraint {
                    terms: vec![
                        term(2, vec![lit(1, false), lit(2, false)]),
                        linear_term(1, 3),
                    ],
                    rel: PbRel::Ge,
                    rhs: 1,
                },
                PbConstraint {
                    terms: vec![term(-4, vec![lit(2, false), lit(3, false)])],
                    rel: PbRel::Ge,
                    rhs: -2,
                },
            ],
            objective: None,
        };

        let linearized = linearize(&instance);

        assert_eq!(linearized.num_vars, 5);
        assert_eq!(linearized.constraints.len(), 8);
        assert!(linearized.constraints.iter().all(|constraint| constraint
            .terms
            .iter()
            .all(|pb_term| pb_term.lits.len() <= 1)));
        assert_eq!(
            linearized.constraints[3],
            PbConstraint {
                terms: vec![linear_term(2, 4), linear_term(1, 3)],
                rel: PbRel::Ge,
                rhs: 1,
            }
        );
        assert_eq!(
            linearized.constraints[7],
            PbConstraint {
                terms: vec![linear_term(-4, 5)],
                rel: PbRel::Ge,
                rhs: -2,
            }
        );

        assert_equivalent(&instance, &linearized);
    }

    #[test]
    fn nonlinear_term_with_negated_literals_is_linearized() {
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints: vec![PbConstraint {
                terms: vec![term(1, vec![lit(1, false), lit(2, true), lit(3, false)])],
                rel: PbRel::Ge,
                rhs: 1,
            }],
            objective: None,
        };

        let linearized = linearize(&instance);

        assert_eq!(linearized.num_vars, 4);
        assert_eq!(
            linearized.constraints[1],
            PbConstraint {
                terms: vec![negated_term(1, 4), negated_term(1, 2)],
                rel: PbRel::Ge,
                rhs: 1,
            }
        );
        assert_eq!(
            linearized.constraints[3],
            PbConstraint {
                terms: vec![
                    linear_term(1, 4),
                    linear_term(-1, 1),
                    negated_term(-1, 2),
                    linear_term(-1, 3),
                ],
                rel: PbRel::Ge,
                rhs: -2,
            }
        );

        assert_equivalent(&instance, &linearized);
    }

    #[test]
    fn objective_is_linearized() {
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints: vec![PbConstraint {
                terms: vec![linear_term(1, 1)],
                rel: PbRel::Ge,
                rhs: 0,
            }],
            objective: Some(PbObjective {
                terms: vec![
                    term(7, vec![lit(1, false), lit(2, false)]),
                    term(-2, vec![lit(2, true), lit(3, false)]),
                ],
            }),
        };

        let linearized = linearize(&instance);
        let objective = linearized
            .objective
            .as_ref()
            .expect("linearized instance must keep its objective");

        assert_eq!(linearized.num_vars, 5);
        assert_eq!(linearized.constraints.len(), 7);
        assert_eq!(
            objective,
            &PbObjective {
                terms: vec![linear_term(7, 4), linear_term(-2, 5)],
            }
        );

        assert_equivalent(&instance, &linearized);
    }

    #[test]
    fn equality_constraints_with_nonlinear_terms_are_linearized() {
        let instance = PbInstance {
            num_vars: 3,
            num_constraints: 1,
            constraints: vec![PbConstraint {
                terms: vec![
                    term(1, vec![lit(1, false), lit(2, false)]),
                    negated_term(1, 3),
                ],
                rel: PbRel::Eq,
                rhs: 1,
            }],
            objective: None,
        };

        let linearized = linearize(&instance);

        assert_eq!(linearized.constraints.len(), 4);
        assert_eq!(linearized.constraints[3].rel, PbRel::Eq);
        assert_eq!(
            linearized.constraints[3],
            PbConstraint {
                terms: vec![linear_term(1, 4), negated_term(1, 3)],
                rel: PbRel::Eq,
                rhs: 1,
            }
        );

        assert_equivalent(&instance, &linearized);
    }

    #[test]
    fn is_linear_reports_constraint_and_objective_cases() {
        let linear = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![PbConstraint {
                terms: vec![linear_term(1, 1), negated_term(-1, 2)],
                rel: PbRel::Ge,
                rhs: 0,
            }],
            objective: Some(PbObjective {
                terms: vec![linear_term(1, 1)],
            }),
        };
        let nonlinear_constraint = PbInstance {
            num_vars: 2,
            num_constraints: 1,
            constraints: vec![PbConstraint {
                terms: vec![term(1, vec![lit(1, false), lit(2, false)])],
                rel: PbRel::Ge,
                rhs: 1,
            }],
            objective: None,
        };
        let nonlinear_objective = PbInstance {
            num_vars: 2,
            num_constraints: 0,
            constraints: Vec::new(),
            objective: Some(PbObjective {
                terms: vec![term(1, vec![lit(1, false), lit(2, false)])],
            }),
        };

        assert!(is_linear(&linear));
        assert!(!is_linear(&nonlinear_constraint));
        assert!(!is_linear(&nonlinear_objective));
    }

    #[test]
    fn brute_force_equivalence_holds_for_mixed_instance() {
        let instance = PbInstance {
            num_vars: 4,
            num_constraints: 2,
            constraints: vec![
                PbConstraint {
                    terms: vec![
                        term(2, vec![lit(1, false), lit(2, false)]),
                        negated_term(-1, 3),
                    ],
                    rel: PbRel::Ge,
                    rhs: 0,
                },
                PbConstraint {
                    terms: vec![
                        term(1, vec![lit(1, true), lit(4, false)]),
                        linear_term(1, 2),
                    ],
                    rel: PbRel::Eq,
                    rhs: 1,
                },
            ],
            objective: Some(PbObjective {
                terms: vec![
                    term(3, vec![lit(1, false), lit(2, false), lit(3, false)]),
                    term(-2, vec![lit(2, true), lit(4, false)]),
                    linear_term(5, 1),
                ],
            }),
        };

        let linearized = linearize(&instance);

        assert_equivalent(&instance, &linearized);
    }
}
