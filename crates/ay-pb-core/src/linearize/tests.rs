// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

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
