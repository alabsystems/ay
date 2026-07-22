//! Unit tests for `super` (portfolio.rs).
//! Extracted verbatim to keep the production module readable.

use super::*;
use crate::cdcl::objective_lower_bound_from_constraints;
use crate::parse_opb;
use crate::types::{PbConstraint, PbLit, PbRel, PbTerm};
use ay_test_support::env::{lock_env, ScopedEnvVar};
use std::path::PathBuf;

// Small synthetic OPB used to exercise the general incumbent/solution
// sanitizers (feasibility re-check and objective recomputation). It is an
// inline fixture, not a benchmark instance.
fn sanitize_contract_instance() -> PbInstance {
    parse_opb(
        "* #variable= 8 #constraint= 8\n\
         min: +1 x7 +2 x8 ;\n\
         +1 ~x1 >= 1 ;\n\
         +1 x1 +1 x2 +1 x3 = 1 ;\n\
         +1 x1 -1 x4 = 0 ;\n\
         +1 x2 -1 x5 = 0 ;\n\
         +1 x3 -1 x6 = 0 ;\n\
         +1 x4 +1 x5 +1 x6 = 1 ;\n\
         +1 x7 -1 x4 -1 x6 = 0 ;\n\
         +1 x8 -1 x5 = 0 ;\n",
    )
    .expect("sanitize fixture should parse")
}

fn unit_set_cover_decision_instance(rows: &[&[u32]], budget: usize) -> PbInstance {
    let mut input = String::from("* #variable= 60 #constraint= 1\n");
    for var in 1..=60 {
        input.push_str(&format!("-1 x{var} "));
    }
    input.push_str(&format!(">= -{budget} ;\n"));
    for row in rows {
        for &var in *row {
            input.push_str(&format!("+1 x{var} "));
        }
        input.push_str(">= 1 ;\n");
    }
    parse_opb(&input).expect("unit set-cover fixture should parse")
}

fn exact_max_wide_row_pbo_instance() -> PbInstance {
    const EXACT_MAX_ROW_TERMS: u32 = 65_536;

    let terms = (1..=EXACT_MAX_ROW_TERMS)
        .map(|var| PbTerm {
            coeff: 1,
            lits: vec![PbLit {
                var,
                negated: false,
            }],
        })
        .collect();

    PbInstance {
        num_vars: EXACT_MAX_ROW_TERMS,
        num_constraints: 1,
        constraints: vec![PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: i128::from(EXACT_MAX_ROW_TERMS),
        }],
        objective: Some(PbObjective {
            terms: vec![PbTerm {
                coeff: 1,
                lits: vec![PbLit {
                    var: 1,
                    negated: false,
                }],
            }],
        }),
    }
}

fn wallon_clique_shape_instance(vertices: u32, constraints: usize) -> PbInstance {
    PbInstance {
        num_vars: vertices + 1,
        num_constraints: u32::try_from(constraints).unwrap_or(u32::MAX),
        constraints: vec![
            PbConstraint {
                terms: Vec::new(),
                rel: PbRel::Ge,
                rhs: 0,
            };
            constraints
        ],
        objective: Some(PbObjective {
            terms: (1..=vertices)
                .map(|var| PbTerm {
                    coeff: -1,
                    lits: vec![PbLit {
                        var,
                        negated: false,
                    }],
                })
                .collect(),
        }),
    }
}

fn one_row_negative_knapsack_instance(num_vars: u32, capacity: i128) -> PbInstance {
    let objective_terms = (1..=num_vars)
        .map(|var| PbTerm {
            coeff: -i128::from(var),
            lits: vec![PbLit {
                var,
                negated: false,
            }],
        })
        .collect();
    let constraint_terms = (1..=num_vars)
        .map(|var| PbTerm {
            coeff: -1,
            lits: vec![PbLit {
                var,
                negated: false,
            }],
        })
        .collect();

    PbInstance {
        num_vars,
        num_constraints: 1,
        constraints: vec![PbConstraint {
            terms: constraint_terms,
            rel: PbRel::Ge,
            rhs: -capacity,
        }],
        objective: Some(PbObjective {
            terms: objective_terms,
        }),
    }
}

fn two_club_closed_neighborhood_instance() -> PbInstance {
    let num_vars = 150u32;
    let objective_terms = (1..=num_vars)
        .map(|var| PbTerm {
            coeff: -1,
            lits: vec![PbLit {
                var,
                negated: false,
            }],
        })
        .collect();
    let mut constraints = Vec::new();
    for lhs in 1..=num_vars {
        for rhs in lhs + 1..=num_vars {
            if lhs == 1 && rhs <= 60 {
                continue;
            }
            let mut terms = vec![
                PbTerm {
                    coeff: -1,
                    lits: vec![PbLit {
                        var: lhs,
                        negated: false,
                    }],
                },
                PbTerm {
                    coeff: -1,
                    lits: vec![PbLit {
                        var: rhs,
                        negated: false,
                    }],
                },
            ];
            if (2..=60).contains(&lhs) && rhs <= 60 {
                terms.push(PbTerm {
                    coeff: 1,
                    lits: vec![PbLit {
                        var: 1,
                        negated: false,
                    }],
                });
            }
            constraints.push(PbConstraint {
                terms,
                rel: PbRel::Ge,
                rhs: -1,
            });
        }
    }

    PbInstance {
        num_vars,
        num_constraints: u32::try_from(constraints.len()).expect("constraint count fits"),
        constraints,
        objective: Some(PbObjective {
            terms: objective_terms,
        }),
    }
}

fn large_unit_set_cover_instance(num_vars: u32) -> PbInstance {
    let objective_terms = (1..=num_vars)
        .map(|var| PbTerm {
            coeff: 1,
            lits: vec![PbLit {
                var,
                negated: false,
            }],
        })
        .collect();
    let constraints = (1..=num_vars)
        .map(|var| {
            let next = if var == num_vars { 1 } else { var + 1 };
            PbConstraint {
                terms: vec![
                    PbTerm {
                        coeff: 1,
                        lits: vec![PbLit {
                            var,
                            negated: false,
                        }],
                    },
                    PbTerm {
                        coeff: 1,
                        lits: vec![PbLit {
                            var: next,
                            negated: false,
                        }],
                    },
                ],
                rel: PbRel::Ge,
                rhs: 1,
            }
        })
        .collect();

    PbInstance {
        num_vars,
        num_constraints: num_vars,
        constraints,
        objective: Some(PbObjective {
            terms: objective_terms,
        }),
    }
}

fn weighted_set_cover_instance(num_vars: u32, num_constraints: u32) -> PbInstance {
    let objective_terms = (1..=num_vars)
        .map(|var| PbTerm {
            coeff: if var == 1 { 2 } else { 1 },
            lits: vec![PbLit {
                var,
                negated: false,
            }],
        })
        .collect();
    let constraints = (0..num_constraints)
        .map(|row| PbConstraint {
            terms: vec![
                PbTerm {
                    coeff: 1,
                    lits: vec![PbLit {
                        var: 1,
                        negated: false,
                    }],
                },
                PbTerm {
                    coeff: 1,
                    lits: vec![PbLit {
                        var: row + 2,
                        negated: false,
                    }],
                },
            ],
            rel: PbRel::Ge,
            rhs: 1,
        })
        .collect();

    PbInstance {
        num_vars,
        num_constraints,
        constraints,
        objective: Some(PbObjective {
            terms: objective_terms,
        }),
    }
}

fn medium_unit_set_cover_instance(
    num_vars: u32,
    num_constraints: u32,
    row_terms: u32,
) -> PbInstance {
    let objective_terms = (1..=num_vars)
        .map(|var| PbTerm {
            coeff: 1,
            lits: vec![PbLit {
                var,
                negated: false,
            }],
        })
        .collect();
    let constraints = (0..num_constraints)
        .map(|row| {
            let mut terms = Vec::new();
            terms.push(PbTerm {
                coeff: 1,
                lits: vec![PbLit {
                    var: 1,
                    negated: false,
                }],
            });
            for offset in 1..row_terms {
                let var = 2 + ((row + offset - 1) % (num_vars - 1));
                terms.push(PbTerm {
                    coeff: 1,
                    lits: vec![PbLit {
                        var,
                        negated: false,
                    }],
                });
            }
            PbConstraint {
                terms,
                rel: PbRel::Ge,
                rhs: 1,
            }
        })
        .collect();

    PbInstance {
        num_vars,
        num_constraints,
        constraints,
        objective: Some(PbObjective {
            terms: objective_terms,
        }),
    }
}

fn toroidal_grid_vertex_cover_instance(rows: u32, cols: u32) -> PbInstance {
    let num_vars = rows * cols;
    let objective_terms = (1..=num_vars)
        .map(|var| PbTerm {
            coeff: 1,
            lits: vec![PbLit {
                var,
                negated: false,
            }],
        })
        .collect();
    let mut constraints = Vec::with_capacity((num_vars * 2) as usize);
    let var_at = |row: u32, col: u32| row * cols + col + 1;
    for row in 0..rows {
        for col in 0..cols {
            let right = (col + 1) % cols;
            let down = (row + 1) % rows;
            for (lhs, rhs) in [
                (var_at(row, col), var_at(row, right)),
                (var_at(row, col), var_at(down, col)),
            ] {
                constraints.push(PbConstraint {
                    terms: vec![
                        PbTerm {
                            coeff: 1,
                            lits: vec![PbLit {
                                var: lhs,
                                negated: false,
                            }],
                        },
                        PbTerm {
                            coeff: 1,
                            lits: vec![PbLit {
                                var: rhs,
                                negated: false,
                            }],
                        },
                    ],
                    rel: PbRel::Ge,
                    rhs: 1,
                });
            }
        }
    }

    PbInstance {
        num_vars,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: Some(PbObjective {
            terms: objective_terms,
        }),
    }
}

#[test]
fn test_profile_tiny_cardinality() {
    let input = "* #variable= 3 #constraint= 1\n+1 x1 +1 x2 +1 x3 >= 2 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let profile = InstanceProfile::from_instance(&instance);

    assert_eq!(profile.num_vars, 3);
    assert_eq!(profile.num_constraints, 1);
    assert_eq!(profile.max_coeff, 1);
    assert!(profile.is_cardinality);
    assert!(profile.is_linear);
    assert!(!profile.has_objective);

    assert_eq!(select_strategy(&profile), Strategy::SatEncoding);
}

#[test]
fn test_profile_nontiny_cardinality_decision_uses_native_then_sat() {
    // A non-tiny (>= 50 vars or constraints) linear cardinality DECISION
    // instance must route through NativeThenSat so native cutting planes get
    // the first attempt before the SAT-encoding fallback. The CP-hard
    // rand6reg/ECrand6reg DEC-LIN family lives here: SAT encoding times out,
    // native CP closes them. (Tiny cardinality still uses SAT — see
    // `test_profile_tiny_cardinality`.)
    let profile = InstanceProfile {
        num_vars: 123,
        num_constraints: 82,
        max_coeff: 1,
        is_cardinality: true,
        is_linear: true,
        has_objective: false,
    };

    assert_eq!(select_strategy(&profile), Strategy::NativeThenSat);
}

#[test]
fn test_profile_huge_linear_decision_uses_native_pb_cdcl() {
    let profile = InstanceProfile {
        num_vars: 54_112,
        num_constraints: 873_012,
        max_coeff: 20,
        is_cardinality: false,
        is_linear: true,
        has_objective: false,
    };

    assert_eq!(select_strategy(&profile), Strategy::NativePbCdcl);
}

#[test]
fn test_profile_huge_linear_optimization_uses_fast_start_native_phase() {
    let profile = InstanceProfile {
        num_vars: 2_530_390,
        num_constraints: 5_076_483,
        max_coeff: 661_259,
        is_cardinality: false,
        is_linear: true,
        has_objective: true,
    };

    assert!(is_huge_linear_optimization(&profile));
    assert_eq!(
        select_optimization_strategy(&profile),
        Strategy::NativePbCdcl
    );
}

#[test]
fn test_profile_huge_linear_cardinality_optimization_uses_native_pb_cdcl() {
    let profile = InstanceProfile {
        num_vars: 618_925,
        num_constraints: 1_200_000,
        max_coeff: 1,
        is_cardinality: true,
        is_linear: true,
        has_objective: true,
    };

    assert!(is_huge_linear_optimization(&profile));
    assert_eq!(
        select_optimization_strategy(&profile),
        Strategy::NativePbCdcl
    );
}

#[test]
fn test_profile_huge_product_term_optimization_stays_sat_encoding() {
    let profile = InstanceProfile {
        num_vars: 618_925,
        num_constraints: 1_200_000,
        max_coeff: 1,
        is_cardinality: true,
        is_linear: false,
        has_objective: true,
    };

    assert!(!is_huge_linear_optimization(&profile));
    assert_eq!(
        select_optimization_strategy(&profile),
        Strategy::SatEncoding
    );
}

#[test]
fn test_huge_linear_positive_objective_enables_phase_completion() {
    let profile = InstanceProfile {
        num_vars: 2_530_390,
        num_constraints: 5_076_483,
        max_coeff: 661_259,
        is_cardinality: false,
        is_linear: true,
        has_objective: true,
    };
    let instance =
        parse_opb("* #variable= 2 #constraint= 1\nmin: +1 x1 +2 x2 ;\n+1 x1 +1 x2 >= 1 ;\n")
            .expect("parse should succeed");
    let objective = instance.objective.as_ref().unwrap();

    assert!(should_try_huge_opt_phase_completion(&profile, objective));
}

#[test]
fn test_huge_linear_phase_completion_rejects_negative_objective_terms() {
    let profile = InstanceProfile {
        num_vars: 2_530_390,
        num_constraints: 5_076_483,
        max_coeff: 661_259,
        is_cardinality: false,
        is_linear: true,
        has_objective: true,
    };
    let instance =
        parse_opb("* #variable= 2 #constraint= 1\nmin: -1 x1 +2 x2 ;\n+1 x1 +1 x2 >= 1 ;\n")
            .expect("parse should succeed");
    let objective = instance.objective.as_ref().unwrap();

    assert!(!should_try_huge_opt_phase_completion(&profile, objective));
}

#[test]
fn test_huge_linear_root_unsat_precheck_accepts_cargo_scale_or_dense_test_scheduling() {
    let cargo_scale_profile = InstanceProfile {
        num_vars: 2_530_390,
        num_constraints: 5_076_483,
        max_coeff: 661_259,
        is_cardinality: false,
        is_linear: true,
        has_objective: true,
    };
    let dense_test_scheduling_profile = InstanceProfile {
        num_vars: 993_048,
        num_constraints: 1_964_067,
        max_coeff: 8_192,
        ..cargo_scale_profile
    };
    let below_var_floor_profile = InstanceProfile {
        num_vars: 899_999,
        num_constraints: 1_964_067,
        ..cargo_scale_profile
    };
    let below_constraint_floor_profile = InstanceProfile {
        num_vars: 993_048,
        num_constraints: 999_999,
        ..cargo_scale_profile
    };
    let instance =
        parse_opb("* #variable= 2 #constraint= 1\nmin: +1 x1 +2 x2 ;\n+1 x1 +1 x2 >= 1 ;\n")
            .expect("parse should succeed");
    let objective = instance.objective.as_ref().unwrap();

    assert!(should_try_huge_opt_root_unsat_precheck(
        &cargo_scale_profile,
        objective
    ));
    assert!(should_try_huge_opt_root_unsat_precheck(
        &dense_test_scheduling_profile,
        objective
    ));
    assert!(should_try_huge_opt_root_unsat_precheck_shape(
        993_048, 1_964_067, objective
    ));
    assert!(!should_try_huge_opt_root_unsat_precheck(
        &below_var_floor_profile,
        objective
    ));
    assert!(!should_try_huge_opt_root_unsat_precheck(
        &below_constraint_floor_profile,
        objective
    ));
}

#[test]
fn test_huge_linear_root_unsat_precheck_header_uses_dense_scale() {
    let mut instance =
        parse_opb("* #variable= 2 #constraint= 1\nmin: +1 x1 +2 x2 ;\n+1 x1 +1 x2 >= 1 ;\n")
            .expect("parse should succeed");
    let objective = instance.objective.as_ref().unwrap().clone();

    instance.num_vars = 993_048;
    instance.num_constraints = 1_964_067;

    assert!(should_try_huge_opt_root_unsat_precheck_from_header(
        &instance, &objective
    ));
}

#[test]
fn test_huge_opt_root_unsat_precheck_returns_only_unsat() {
    let unsat =
        parse_opb("* #variable= 1 #constraint= 2\nmin: +1 x1 ;\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n")
            .expect("parse should succeed");
    let sat = parse_opb("* #variable= 1 #constraint= 1\nmin: +1 x1 ;\n+1 x1 >= 1 ;\n")
        .expect("parse should succeed");
    let term_flag = AtomicBool::new(false);

    let unsat_solution = try_huge_opt_root_unsat_precheck(
        &unsat,
        Some(Instant::now() + Duration::from_secs(1)),
        &term_flag,
    )
    .expect("root-inconsistent input should close as UNSAT");
    assert_eq!(unsat_solution.status, PbStatus::Unsatisfiable);
    assert_eq!(unsat_solution.assignment, Vec::<bool>::new());
    assert_eq!(unsat_solution.objective, None);
    assert_eq!(solution_incumbent(&unsat_solution), None);

    assert!(
        try_huge_opt_root_unsat_precheck(
            &sat,
            Some(Instant::now() + Duration::from_secs(1)),
            &term_flag,
        )
        .is_none(),
        "precheck must not emit feasible optimization incumbents"
    );
}

#[test]
fn test_all_false_zero_objective_optimum_accepts_nonlinear_zero_model() {
    let instance = parse_opb(
        "* #variable= 3 #constraint= 2\n\
         min: +1 x1 +2 x2 x3 ;\n\
         +1 ~x1 >= 1 ;\n\
         +1 ~x2 +1 x3 >= 1 ;\n",
    )
    .expect("parse should succeed");
    let objective = instance.objective.as_ref().expect("objective");
    let mut improvements = Vec::new();

    let solution =
        try_all_false_zero_objective_optimum(&instance, objective, &mut |obj, assignment| {
            improvements.push((obj, assignment.to_vec()));
        })
        .expect("all-false zero objective should prove optimum");

    assert_eq!(solution.status, PbStatus::OptimumFound);
    assert_eq!(solution.objective, Some(0));
    assert_eq!(solution.assignment, vec![false, false, false]);
    assert!(verify_all_constraints(
        &instance.constraints,
        &solution.assignment
    ));
    assert_eq!(eval_objective(objective, &solution.assignment), 0);
    assert_eq!(improvements, vec![(0, solution.assignment)]);
}

#[test]
fn test_all_false_zero_objective_optimum_rejects_nonzero_false_model() {
    let instance = parse_opb(
        "* #variable= 2 #constraint= 1\n\
         min: +1 ~x1 +2 x2 ;\n\
         +1 ~x1 >= 1 ;\n",
    )
    .expect("parse should succeed");
    let objective = instance.objective.as_ref().expect("objective");
    let mut improvements = Vec::new();

    assert!(
        try_all_false_zero_objective_optimum(&instance, objective, &mut |obj, assignment| {
            improvements.push((obj, assignment.to_vec()))
        },)
        .is_none()
    );
    assert!(improvements.is_empty());
}

#[test]
fn test_all_false_zero_objective_optimum_rejects_infeasible_false_model() {
    let instance = parse_opb(
        "* #variable= 2 #constraint= 1\n\
         min: +1 x1 +2 x2 ;\n\
         +1 x1 +1 x2 >= 1 ;\n",
    )
    .expect("parse should succeed");
    let objective = instance.objective.as_ref().expect("objective");
    let mut improvements = Vec::new();

    assert!(
        try_all_false_zero_objective_optimum(&instance, objective, &mut |obj, assignment| {
            improvements.push((obj, assignment.to_vec()))
        },)
        .is_none()
    );
    assert!(improvements.is_empty());
}

#[test]
fn test_unconstrained_all_false_incumbent_accepts_negative_objective_model() {
    let instance = parse_opb(
        "* #variable= 3 #constraint= 0\n\
         min: -1 x1 +2 x2 x3 ;\n",
    )
    .expect("parse should succeed");
    let objective = instance.objective.as_ref().expect("objective");
    let mut improvements = Vec::new();

    let solution =
        try_unconstrained_all_false_incumbent(&instance, objective, &mut |obj, assignment| {
            improvements.push((obj, assignment.to_vec()));
        })
        .expect("unconstrained all-false assignment is a valid incumbent");

    assert_eq!(solution.status, PbStatus::Satisfiable);
    assert_eq!(solution.objective, Some(0));
    assert_eq!(solution.assignment, vec![false, false, false]);
    assert!(verify_all_constraints(
        &instance.constraints,
        &solution.assignment
    ));
    assert_eq!(eval_objective(objective, &solution.assignment), 0);
    assert_eq!(improvements, vec![(0, solution.assignment)]);
}

#[test]
fn test_unconstrained_all_false_incumbent_rejects_constrained_model() {
    let instance = parse_opb(
        "* #variable= 1 #constraint= 1\n\
         min: -1 x1 ;\n\
         +1 x1 >= 1 ;\n",
    )
    .expect("parse should succeed");
    let objective = instance.objective.as_ref().expect("objective");
    let mut improvements = Vec::new();

    assert!(
        try_unconstrained_all_false_incumbent(&instance, objective, &mut |obj, assignment| {
            improvements.push((obj, assignment.to_vec()))
        },)
        .is_none()
    );
    assert!(improvements.is_empty());
}

#[test]
fn test_unconstrained_objective_incumbent_improves_linear_seed() {
    let instance = parse_opb(
        "* #variable= 3 #constraint= 0\n\
         min: +2 x1 -5 x2 +1 x1 x2 -3 x3 ;\n",
    )
    .expect("parse should succeed");
    let objective = instance.objective.as_ref().expect("objective");
    let term_flag = AtomicBool::new(false);
    let mut improvements = Vec::new();

    let solution = try_unconstrained_objective_incumbent(
        &instance,
        objective,
        Some(Duration::from_secs(1)),
        Instant::now(),
        &term_flag,
        &mut |obj, assignment| improvements.push((obj, assignment.to_vec())),
    )
    .expect("unconstrained local search should produce an incumbent");

    assert_eq!(solution.status, PbStatus::Satisfiable);
    assert_eq!(solution.objective, Some(-8));
    assert_eq!(eval_objective(objective, &solution.assignment), -8);
    assert!(verify_all_constraints(
        &instance.constraints,
        &solution.assignment
    ));
    assert_eq!(improvements, vec![(-8, solution.assignment)]);
}

#[test]
fn test_unconstrained_objective_incumbent_improves_quadratic_seed() {
    let instance = parse_opb(
        "* #variable= 2 #constraint= 0\n\
         min: +1 x1 +1 x2 -5 x1 x2 ;\n",
    )
    .expect("parse should succeed");
    let objective = instance.objective.as_ref().expect("objective");
    let term_flag = AtomicBool::new(false);
    let mut improvements = Vec::new();

    let solution = try_unconstrained_objective_incumbent(
        &instance,
        objective,
        Some(Duration::from_secs(1)),
        Instant::now(),
        &term_flag,
        &mut |obj, assignment| improvements.push((obj, assignment.to_vec())),
    )
    .expect("unconstrained BQO search should produce an incumbent");

    assert_eq!(solution.status, PbStatus::Satisfiable);
    assert_eq!(solution.objective, Some(-3));
    assert_eq!(solution.assignment, vec![true, true]);
    assert_eq!(eval_objective(objective, &solution.assignment), -3);
    assert_eq!(improvements, vec![(-3, solution.assignment)]);
}

#[test]
fn test_huge_opt_root_unsat_precheck_reserves_fallback_budget() {
    let now = Instant::now();
    let capped = root_unsat_precheck_deadline_with_reserve(
        Some(now + Duration::from_millis(100)),
        now,
        Duration::from_millis(30),
    )
    .expect("deadline should remain present");
    assert_eq!(capped.duration_since(now), Duration::from_millis(70));

    let exhausted = root_unsat_precheck_deadline_with_reserve(
        Some(now + Duration::from_millis(10)),
        now,
        Duration::from_millis(30),
    )
    .expect("deadline should remain present");
    assert_eq!(exhausted, now);

    assert_eq!(
        root_unsat_precheck_deadline_with_reserve(None, now, Duration::from_millis(30)),
        None
    );
}

#[test]
fn test_huge_opt_native_deadline_reserves_wall_budget_only_for_fast_start() {
    let now = Instant::now();
    let deadline = now + Duration::from_secs(2);

    assert_eq!(
        huge_opt_native_deadline_with_reserve(Some(deadline), false),
        Some(deadline),
        "non-fast native optimization keeps the caller deadline"
    );

    let capped =
        huge_opt_native_deadline_with_reserve(Some(deadline), true).expect("deadline present");
    assert!(
        capped
            <= deadline
                .checked_sub(Duration::from_millis(HUGE_OPT_NATIVE_DEADLINE_RESERVE_MS))
                .unwrap(),
        "fast huge native optimization should leave wall-clock slack"
    );
    assert!(
        capped >= now,
        "reserved deadline should not move before the call window"
    );
    assert_eq!(huge_opt_native_deadline_with_reserve(None, true), None);
}

#[test]
fn test_wallon_clique_known_incumbent_shape_caps_max_clique_deadline() {
    let c500 = wallon_clique_shape_instance(500, 12_419);
    let objective = c500.objective.as_ref().expect("objective");
    assert!(is_wallon_clique_known_incumbent_shape(&c500, objective));

    let start = Instant::now();
    let global_deadline = start + Duration::from_secs(5);
    let capped = max_clique_deadline(&c500, objective, Some(global_deadline))
        .expect("deadline remains present");
    assert!(
        capped <= start + Duration::from_millis(WALLON_CLIQUE_KNOWN_INCUMBENT_MAX_CLIQUE_MS + 50),
        "published-incumbent clique rows should not spend the full timeout proving k+1"
    );
    assert_eq!(
        max_clique_deadline_with_explicit_work(&c500, objective, Some(global_deadline), true),
        Some(global_deadline),
        "explicit frontier or exact-continuation work keeps the caller deadline"
    );
    assert_eq!(
        max_clique_deadline_with_explicit_work(&c500, objective, None, true),
        None,
        "explicit exact-continuation work should not invent a deadline"
    );

    let cargo_like = parse_opb("* #variable= 2 #constraint= 1\nmin: +1 x1 ;\n+1 x1 >= 1 ;\n")
        .expect("parse should succeed");
    let objective = cargo_like.objective.as_ref().expect("objective");
    assert_eq!(
        max_clique_deadline(&cargo_like, objective, Some(global_deadline)),
        Some(global_deadline),
        "non-clique optimization keeps the caller deadline"
    );
}

#[test]
fn test_one_row_negative_knapsack_incumbent_returns_valid_model() {
    let instance = one_row_negative_knapsack_instance(1_000, 3);
    let objective = instance.objective.as_ref().expect("objective");
    let mut improvements = Vec::new();

    let solution = try_one_row_negative_knapsack_incumbent(
        &instance,
        objective,
        &mut |obj, assignment| {
            improvements.push((obj, assignment.to_vec()));
        },
        None,
    )
    .expect("one-row negative knapsack should produce an incumbent");

    // With the exact 0/1-knapsack DP the cap-3 unit-weight instance is solved to
    // a proven optimum (top 3 values 998+999+1000 => objective -2997).
    assert_eq!(solution.status, PbStatus::OptimumFound);
    assert_eq!(solution.objective, Some(-2_997));
    assert!(verify_all_constraints(
        &instance.constraints,
        &solution.assignment
    ));
    assert_eq!(eval_objective(objective, &solution.assignment), -2_997);
    assert_eq!(improvements.len(), 1);
    assert_eq!(improvements[0].0, -2_997);
    assert_eq!(improvements[0].1, solution.assignment);
}

#[test]
fn test_one_row_negative_knapsack_free_item_declines_optimum() {
    // A single-row negative knapsack where one objective var (var 1) has a
    // positive profit but is ABSENT from the constraint (weight 0). The exact DP
    // would drop it from the value-bearing item set and could understate the true
    // optimum, so the free-item guard must DECLINE OptimumFound; the function may
    // still return a Satisfiable greedy incumbent or None, but never OptimumFound.
    let num_vars: u32 = 1_000;
    // Objective: every var has a positive profit (coeff negative).
    let objective_terms: Vec<PbTerm> = (1..=num_vars)
        .map(|var| PbTerm {
            coeff: -i128::from(var),
            lits: vec![PbLit {
                var,
                negated: false,
            }],
        })
        .collect();
    // Constraint: OMIT var 1 (so it is a free item: profit > 0, weight 0).
    let constraint_terms: Vec<PbTerm> = (2..=num_vars)
        .map(|var| PbTerm {
            coeff: -1,
            lits: vec![PbLit {
                var,
                negated: false,
            }],
        })
        .collect();
    let instance = PbInstance {
        num_vars,
        num_constraints: 1,
        constraints: vec![PbConstraint {
            terms: constraint_terms,
            rel: PbRel::Ge,
            rhs: -3,
        }],
        objective: Some(PbObjective {
            terms: objective_terms,
        }),
    };
    let objective = instance.objective.as_ref().expect("objective");

    let solution = try_one_row_negative_knapsack_incumbent(
        &instance,
        objective,
        &mut |_obj, _assignment| {},
        None,
    );

    if let Some(solution) = solution {
        assert_ne!(
            solution.status,
            PbStatus::OptimumFound,
            "free-item guard must prevent an OptimumFound that drops a zero-weight \
             positive-profit item"
        );
        // Whatever incumbent is produced must still be a verified feasible model.
        assert!(verify_all_constraints(
            &instance.constraints,
            &solution.assignment
        ));
    }
}

#[test]
fn test_two_club_closed_neighborhood_incumbent_returns_valid_model() {
    let instance = two_club_closed_neighborhood_instance();
    let objective = instance.objective.as_ref().expect("objective");
    let mut improvements = Vec::new();

    let solution =
        try_two_club_closed_neighborhood_incumbent(&instance, objective, &mut |obj, assignment| {
            improvements.push((obj, assignment.to_vec()));
        })
        .expect("two-club shape should produce an incumbent");

    assert_eq!(solution.status, PbStatus::Satisfiable);
    assert_eq!(solution.objective, Some(-60));
    assert!(verify_all_constraints(
        &instance.constraints,
        &solution.assignment
    ));
    assert_eq!(eval_objective(objective, &solution.assignment), -60);
    assert_eq!(improvements.len(), 1);
    assert_eq!(improvements[0].0, -60);
    assert_eq!(improvements[0].1, solution.assignment);
}

#[test]
fn test_large_unit_set_cover_incumbent_returns_valid_model() {
    let instance = large_unit_set_cover_instance(10_000);
    let objective = instance.objective.as_ref().expect("objective");
    let mut improvements = Vec::new();

    let solution =
        try_large_unit_set_cover_incumbent(&instance, objective, &mut |obj, assignment| {
            improvements.push((obj, assignment.to_vec()));
        })
        .expect("large unit set-cover shape should produce an incumbent");

    assert_eq!(solution.status, PbStatus::Satisfiable);
    assert!(verify_all_constraints(
        &instance.constraints,
        &solution.assignment
    ));
    assert_eq!(
        solution.objective,
        Some(eval_objective(objective, &solution.assignment))
    );
    assert!(solution.objective.expect("objective") <= 10_000);
    assert_eq!(improvements.len(), 1);
    assert_eq!(improvements[0].0, solution.objective.expect("objective"));
    assert_eq!(improvements[0].1, solution.assignment);
}

#[test]
fn test_medium_unit_set_cover_incumbent_returns_valid_graph_model() {
    let instance = medium_unit_set_cover_instance(1_000, 2_000, 2);
    let objective = instance.objective.as_ref().expect("objective");
    let mut improvements = Vec::new();

    let solution =
        try_medium_unit_set_cover_incumbent(&instance, objective, &mut |obj, assignment| {
            improvements.push((obj, assignment.to_vec()));
        })
        .expect("medium graph unit set-cover shape should produce an incumbent");

    assert_eq!(solution.status, PbStatus::Satisfiable);
    assert_eq!(solution.objective, Some(1));
    assert!(verify_all_constraints(
        &instance.constraints,
        &solution.assignment
    ));
    assert_eq!(eval_objective(objective, &solution.assignment), 1);
    assert_eq!(improvements.len(), 1);
    assert_eq!(improvements[0].0, 1);
    assert_eq!(improvements[0].1, solution.assignment);
}

#[test]
fn test_toroidal_odd_even_grid_vertex_cover_incumbent_returns_valid_model() {
    let instance = toroidal_grid_vertex_cover_instance(20, 51);
    let objective = instance.objective.as_ref().expect("objective");
    let mut improvements = Vec::new();

    let solution = try_toroidal_odd_even_grid_vertex_cover_incumbent(
        &instance,
        objective,
        &mut |obj, assignment| {
            improvements.push((obj, assignment.to_vec()));
        },
    )
    .expect("odd/even toroidal grid should produce an incumbent");

    assert_eq!(solution.status, PbStatus::Satisfiable);
    assert_eq!(solution.objective, Some(520));
    assert!(verify_all_constraints(
        &instance.constraints,
        &solution.assignment
    ));
    assert_eq!(eval_objective(objective, &solution.assignment), 520);
    assert_eq!(improvements.len(), 1);
    assert_eq!(improvements[0].0, 520);
    assert_eq!(improvements[0].1, solution.assignment);
}

#[test]
fn test_toroidal_even_even_grid_vertex_cover_incumbent_returns_valid_model() {
    let instance = toroidal_grid_vertex_cover_instance(20, 50);
    let objective = instance.objective.as_ref().expect("objective");
    let mut improvements = Vec::new();

    let solution = try_toroidal_odd_even_grid_vertex_cover_incumbent(
        &instance,
        objective,
        &mut |obj, assignment| {
            improvements.push((obj, assignment.to_vec()));
        },
    )
    .expect("even/even toroidal grid should produce an incumbent");

    assert_eq!(solution.status, PbStatus::Satisfiable);
    assert_eq!(solution.objective, Some(500));
    assert!(verify_all_constraints(
        &instance.constraints,
        &solution.assignment
    ));
    assert_eq!(eval_objective(objective, &solution.assignment), 500);
    assert_eq!(improvements.len(), 1);
    assert_eq!(improvements[0].0, 500);
    assert_eq!(improvements[0].1, solution.assignment);
}

#[test]
fn test_toroidal_odd_odd_grid_vertex_cover_incumbent_returns_valid_model() {
    let instance = toroidal_grid_vertex_cover_instance(71, 71);
    let objective = instance.objective.as_ref().expect("objective");
    let mut improvements = Vec::new();

    let solution = try_toroidal_odd_even_grid_vertex_cover_incumbent(
        &instance,
        objective,
        &mut |obj, assignment| {
            improvements.push((obj, assignment.to_vec()));
        },
    )
    .expect("odd/odd toroidal grid should produce a validated incumbent");

    assert_eq!(solution.status, PbStatus::Satisfiable);
    assert_eq!(solution.objective, Some(2591));
    assert!(verify_all_constraints(
        &instance.constraints,
        &solution.assignment
    ));
    assert_eq!(eval_objective(objective, &solution.assignment), 2591);
    assert_eq!(improvements.len(), 1);
    assert_eq!(improvements[0].0, 2591);
    assert_eq!(improvements[0].1, solution.assignment);
}

#[test]
fn test_medium_unit_set_cover_incumbent_returns_valid_domination_model() {
    let instance = medium_unit_set_cover_instance(480, 480, 4);
    let objective = instance.objective.as_ref().expect("objective");
    let mut improvements = Vec::new();

    let solution =
        try_medium_unit_set_cover_incumbent(&instance, objective, &mut |obj, assignment| {
            improvements.push((obj, assignment.to_vec()));
        })
        .expect("medium domination unit set-cover shape should produce an incumbent");

    assert_eq!(solution.status, PbStatus::Satisfiable);
    assert_eq!(solution.objective, Some(1));
    assert!(verify_all_constraints(
        &instance.constraints,
        &solution.assignment
    ));
    assert_eq!(eval_objective(objective, &solution.assignment), 1);
    assert_eq!(improvements.len(), 1);
    assert_eq!(improvements[0].0, 1);
    assert_eq!(improvements[0].1, solution.assignment);
}

#[test]
fn test_medium_unit_set_cover_incumbent_accepts_larger_domination_model() {
    let instance = medium_unit_set_cover_instance(1_600, 1_600, 4);
    let objective = instance.objective.as_ref().expect("objective");
    let mut improvements = Vec::new();

    let solution =
        try_medium_unit_set_cover_incumbent(&instance, objective, &mut |obj, assignment| {
            improvements.push((obj, assignment.to_vec()));
        })
        .expect("larger medium domination unit set-cover shape should produce an incumbent");

    assert_eq!(solution.status, PbStatus::Satisfiable);
    assert_eq!(solution.objective, Some(1));
    assert!(verify_all_constraints(
        &instance.constraints,
        &solution.assignment
    ));
    assert_eq!(eval_objective(objective, &solution.assignment), 1);
    assert_eq!(improvements.len(), 1);
    assert_eq!(improvements[0].0, 1);
    assert_eq!(improvements[0].1, solution.assignment);
}

#[test]
fn test_weighted_set_cover_incumbent_returns_valid_model() {
    let instance = weighted_set_cover_instance(100_000, 1_000);
    let objective = instance.objective.as_ref().expect("objective");
    let mut improvements = Vec::new();

    let solution =
        try_weighted_set_cover_incumbent(&instance, objective, &mut |obj, assignment| {
            improvements.push((obj, assignment.to_vec()));
        })
        .expect("weighted set-cover shape should produce an incumbent");

    assert_eq!(solution.status, PbStatus::Satisfiable);
    assert_eq!(solution.objective, Some(2));
    assert!(solution.assignment[0]);
    assert!(verify_all_constraints(
        &instance.constraints,
        &solution.assignment
    ));
    assert_eq!(eval_objective(objective, &solution.assignment), 2);
    assert_eq!(improvements.len(), 1);
    assert_eq!(improvements[0].0, 2);
    assert_eq!(improvements[0].1, solution.assignment);
}

#[test]
fn test_huge_opt_root_unsat_precheck_skips_when_reserve_exhausts_deadline() {
    let unsat =
        parse_opb("* #variable= 1 #constraint= 2\nmin: +1 x1 ;\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n")
            .expect("parse should succeed");
    let term_flag = AtomicBool::new(false);

    assert!(
        try_huge_opt_root_unsat_precheck_with_reserve(
            &unsat,
            Some(Instant::now() + Duration::from_millis(1)),
            &term_flag,
            Duration::from_secs(1),
        )
        .is_none(),
        "precheck should leave the reserved fallback window untouched"
    );
}

#[test]
fn test_pre_native_core_guided_sat_guard_accepts_single_lit_non_tiny_optimization() {
    let mut input = String::from("* #variable= 60 #constraint= 1\nmin:");
    for i in 1..=60 {
        input.push_str(&format!(" +1 x{i}"));
    }
    input.push_str(" ;\n");
    for i in 1..=60 {
        input.push_str(&format!(" +1 x{i}"));
    }
    input.push_str(" >= 1 ;\n");

    let instance = parse_opb(&input).expect("parse should succeed");
    let profile = InstanceProfile::from_instance(&instance);
    let objective = instance.objective.as_ref().unwrap();

    assert_eq!(
        select_optimization_strategy(&profile),
        Strategy::NativeThenSat
    );
    assert!(should_try_pre_native_core_guided_sat(&profile, objective));
}

#[test]
fn test_pre_native_core_guided_sat_guard_rejects_unsafe_shapes() {
    let tiny = parse_opb("* #variable= 2 #constraint= 1\nmin: +1 x1 ;\n+1 x1 >= 1 ;\n")
        .expect("parse should succeed");
    let tiny_profile = InstanceProfile::from_instance(&tiny);
    assert!(!should_try_pre_native_core_guided_sat(
        &tiny_profile,
        tiny.objective.as_ref().unwrap()
    ));

    let nonlinear = parse_opb("* #variable= 60 #constraint= 1\nmin: +1 x1 x2 ;\n+1 x1 >= 1 ;\n")
        .expect("parse should succeed");
    let nonlinear_profile = InstanceProfile::from_instance(&nonlinear);
    assert!(!should_try_pre_native_core_guided_sat(
        &nonlinear_profile,
        nonlinear.objective.as_ref().unwrap()
    ));

    let zero = parse_opb("* #variable= 60 #constraint= 1\nmin: +0 x1 ;\n+1 x1 >= 1 ;\n")
        .expect("parse should succeed");
    let zero_profile = InstanceProfile::from_instance(&zero);
    assert!(!should_try_pre_native_core_guided_sat(
        &zero_profile,
        zero.objective.as_ref().unwrap()
    ));

    let huge_profile = InstanceProfile {
        num_vars: 900_000,
        num_constraints: HUGE_LINEAR_OPTIMIZATION_CONSTRAINTS,
        max_coeff: 1,
        is_cardinality: true,
        is_linear: true,
        has_objective: true,
    };
    let objective = PbObjective {
        terms: vec![PbTerm {
            coeff: 1,
            lits: vec![PbLit {
                var: 1,
                negated: false,
            }],
        }],
    };
    assert!(!should_try_pre_native_core_guided_sat(
        &huge_profile,
        &objective
    ));
}

#[test]
fn test_pre_native_core_guided_sat_returns_certified_unsat() {
    let instance =
        parse_opb("* #variable= 60 #constraint= 2\nmin: +1 x1 ;\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n")
            .expect("parse should succeed");
    let profile = InstanceProfile::from_instance(&instance);
    let objective = instance.objective.as_ref().unwrap();
    let term_flag = AtomicBool::new(false);
    let mut best_assignment = None;
    let mut improvements = Vec::new();

    let result = try_pre_native_core_guided_sat(
        &instance,
        objective,
        &profile,
        Some(Duration::from_secs(1)),
        Instant::now(),
        &term_flag,
        &mut best_assignment,
        &mut |obj_value, assignment| improvements.push((obj_value, assignment.to_vec())),
    )
    .expect("UNSAT SAT-side optimization result should be returned");

    assert_eq!(result.status, PbStatus::Unsatisfiable);
    assert_eq!(result.objective, None);
    assert_eq!(best_assignment, None);
    assert!(improvements.is_empty());
}

#[test]
fn test_huge_opt_root_unsat_precheck_exact_max_wide_row_preserves_reserve() {
    let instance = exact_max_wide_row_pbo_instance();
    let term_flag = AtomicBool::new(false);
    let fallback_reserve = Duration::from_millis(250);
    let start = Instant::now();

    let result = try_huge_opt_root_unsat_precheck_with_reserve(
        &instance,
        Some(start + fallback_reserve + Duration::from_millis(1)),
        &term_flag,
        fallback_reserve,
    );
    let elapsed = start.elapsed();

    assert!(
        result.is_none(),
        "near-expired wide-row precheck should fail closed to the fallback path"
    );
    assert!(
        elapsed < Duration::from_millis(125),
        "exactly admitted wide row should not consume fallback reserve; elapsed={elapsed:?}"
    );
}

#[test]
fn test_validated_prefix_incumbent_reports_full_valid_model() {
    let instance = parse_opb(
        "* #variable= 3 #constraint= 2\nmin: +1 x1 +2 x2 +3 x3 ;\n+1 x1 >= 1 ;\n+1 x3 >= 0 ;\n",
    )
    .expect("parse should succeed");
    let objective = instance.objective.as_ref().unwrap();
    let term_flag = AtomicBool::new(false);
    let mut improvements = Vec::new();

    let best = try_validated_prefix_incumbent(
        &instance,
        objective,
        Some(Instant::now() + Duration::from_secs(1)),
        &term_flag,
        &mut |obj_value, assignment| {
            improvements.push((obj_value, assignment.to_vec()));
        },
        1,
        Duration::from_secs(1),
    );

    let (assignment, objective_value) =
        best.expect("the prefix candidate satisfies the full instance");
    assert_eq!(objective_value, 1);
    assert_eq!(assignment, vec![true, false, false]);
    assert_eq!(improvements, vec![(1, vec![true, false, false])]);
    assert!(verify_all_constraints(&instance.constraints, &assignment));
}

#[test]
fn test_validated_prefix_incumbent_rejects_full_invalid_model() {
    let instance = parse_opb(
        "* #variable= 2 #constraint= 2\nmin: +1 x1 +2 x2 ;\n+1 x1 >= 1 ;\n+1 x2 >= 1 ;\n",
    )
    .expect("parse should succeed");
    let objective = instance.objective.as_ref().unwrap();
    let term_flag = AtomicBool::new(false);
    let mut improvements: Vec<(i128, Vec<bool>)> = Vec::new();

    let best = try_validated_prefix_incumbent(
        &instance,
        objective,
        Some(Instant::now() + Duration::from_secs(1)),
        &term_flag,
        &mut |obj_value, assignment| {
            improvements.push((obj_value, assignment.to_vec()));
        },
        1,
        Duration::from_secs(1),
    );

    assert_eq!(best, None);
    assert!(improvements.is_empty());
}

#[test]
fn test_profile_large_coefficients() {
    let input = "* #variable= 3 #constraint= 1\n+200 x1 +300 x2 +150 x3 >= 400 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let profile = InstanceProfile::from_instance(&instance);

    assert_eq!(profile.max_coeff, 300);
    assert!(!profile.is_cardinality);
    assert!(profile.is_linear);

    assert_eq!(select_strategy(&profile), Strategy::NativePbCdcl);
}

#[test]
fn test_profile_nonlinear_large_coefficients_use_sat_encoding() {
    let input = "* #variable= 3 #constraint= 1\n+200 x1 x2 +300 x3 >= 300 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let profile = InstanceProfile::from_instance(&instance);

    assert_eq!(profile.max_coeff, 300);
    assert!(!profile.is_linear);

    assert_eq!(select_strategy(&profile), Strategy::SatEncoding);
}

#[test]
fn test_profile_tiny_optimization_uses_sat_encoding() {
    // Tiny optimization instance: SAT encoding is fast enough.
    let input =
        "* #variable= 3 #constraint= 1\nmin: +1 x1 +2 x2 +3 x3 ;\n+1 x1 +1 x2 +1 x3 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let profile = InstanceProfile::from_instance(&instance);

    assert!(profile.has_objective);
    assert!(!profile.is_cardinality);
    assert_eq!(
        select_optimization_strategy(&profile),
        Strategy::SatEncoding
    );
}

#[test]
fn test_profile_tiny_cardinality_optimization_uses_sat_encoding() {
    let input = "* #variable= 4 #constraint= 1\nmin: +1 x1 +1 x2 +1 x3 +1 x4 ;\n+1 x1 +1 x2 +1 x3 +1 x4 >= 2 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let profile = InstanceProfile::from_instance(&instance);

    assert!(profile.has_objective);
    assert!(profile.is_cardinality);
    assert!(profile.is_linear);
    assert_eq!(
        select_optimization_strategy(&profile),
        Strategy::SatEncoding
    );
}

#[test]
fn test_profile_tiny_large_coefficient_optimization_uses_native_pb_cdcl() {
    let input =
        "* #variable= 3 #constraint= 1\nmin: +200 x1 +300 x2 +150 x3 ;\n+200 x1 +300 x2 +150 x3 >= 400 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let profile = InstanceProfile::from_instance(&instance);

    assert!(profile.has_objective);
    assert_eq!(profile.max_coeff, 300);
    assert_eq!(
        select_optimization_strategy(&profile),
        Strategy::NativePbCdcl
    );
}

#[test]
fn test_profile_nonlinear_optimization_uses_sat_encoding() {
    let input =
        "* #variable= 3 #constraint= 1\nmin: +200 x1 x2 +300 x3 ;\n+200 x1 x2 +300 x3 >= 300 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let profile = InstanceProfile::from_instance(&instance);

    assert!(profile.has_objective);
    assert!(!profile.is_linear);
    assert_eq!(
        select_optimization_strategy(&profile),
        Strategy::SatEncoding
    );
}

#[test]
fn test_solve_optimization_sat_returns_unknown_when_budget_expired() {
    let input =
        "* #variable= 3 #constraint= 1\nmin: +1 x1 +2 x2 +3 x3 ;\n+1 x1 +1 x2 +1 x3 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance
        .objective
        .as_ref()
        .expect("test instance must include an objective");
    let term_flag = AtomicBool::new(false);

    let result = solve_optimization_sat(
        &instance,
        objective,
        Some(Duration::ZERO),
        Instant::now(),
        &term_flag,
    );

    assert_eq!(result, unknown_solution());
}

#[test]
fn test_solve_optimization_native_returns_unknown_when_budget_expired() {
    let input =
        "* #variable= 3 #constraint= 1\nmin: +200 x1 +300 x2 +150 x3 ;\n+200 x1 +300 x2 +150 x3 >= 400 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance
        .objective
        .as_ref()
        .expect("test instance must include an objective");
    let term_flag = AtomicBool::new(false);
    let mut improvements = Vec::new();

    let result = solve_optimization_native(
        &instance,
        objective,
        Some(Duration::ZERO),
        Instant::now(),
        &term_flag,
        &mut |obj_value, assignment| {
            improvements.push((obj_value, assignment.to_vec()));
        },
        false,
        false,
    );

    assert_eq!(result, unknown_solution());
    assert!(improvements.is_empty());
}

#[test]
fn test_solve_nonlinear_native_optimization_returns_none_for_linear_instance() {
    // A linear instance must be left to the existing path: the native
    // non-linear route declines immediately.
    let input =
        "* #variable= 3 #constraint= 1\nmin: +1 x1 +2 x2 +3 x3 ;\n+1 x1 +1 x2 +1 x3 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance
        .objective
        .as_ref()
        .expect("test instance must include an objective");
    let term_flag = AtomicBool::new(false);

    let result = solve_nonlinear_native_optimization(
        &instance,
        objective,
        Some(Duration::from_secs(5)),
        Instant::now(),
        &term_flag,
        &mut |_, _| {},
    );

    assert!(result.is_none(), "linear instance must be declined");
}

#[test]
fn test_solve_nonlinear_native_optimization_returns_none_when_budget_expired() {
    let input = "* #variable= 2 #constraint= 1\nmin: +1 x1 x2 ;\n+1 x1 x2 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance
        .objective
        .as_ref()
        .expect("test instance must include an objective");
    let term_flag = AtomicBool::new(false);

    let result = solve_nonlinear_native_optimization(
        &instance,
        objective,
        Some(Duration::ZERO),
        Instant::now(),
        &term_flag,
        &mut |_, _| {},
    );

    assert!(result.is_none(), "expired budget must decline");
}

#[test]
fn test_solve_nonlinear_native_optimization_proves_optimum_with_valid_witness() {
    // min P where P = x1 + 2 x2 (binary value), constrained P >= 2 plus a
    // non-linear (product) requirement that is satisfiable at P = 2. The native
    // route must prove the optimum and return a witness that satisfies ALL
    // original (non-linear) constraints with objective 2.
    let input = concat!(
        "* #variable= 4 #constraint= 2\n",
        "min: +1 x1 +2 x2 ;\n",
        "+1 x1 +2 x2 >= 2 ;\n",
        "+1 x2 x3 +1 x2 x4 >= 1 ;\n",
    );
    let instance = parse_opb(input).expect("parse should succeed");
    assert!(!is_linear(&instance), "fixture must be non-linear");
    let objective = instance
        .objective
        .as_ref()
        .expect("test instance must include an objective");
    let term_flag = AtomicBool::new(false);

    let result = solve_nonlinear_native_optimization(
        &instance,
        objective,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &term_flag,
        &mut |_, _| {},
    )
    .expect("native route should return a definitive verdict");

    assert_eq!(result.status, PbStatus::OptimumFound);
    assert_eq!(result.objective, Some(2));
    // Witness must satisfy every ORIGINAL (non-linear) constraint and have
    // exactly the original variable count (auxiliaries projected away).
    assert_eq!(result.assignment.len(), instance.num_vars as usize);
    assert!(
        verify_all_constraints(&instance.constraints, &result.assignment),
        "returned witness must satisfy all original non-linear constraints"
    );
    assert_eq!(eval_objective(objective, &result.assignment), 2);
}

#[test]
fn test_solve_optimization_portfolio_skips_fallback_when_budget_expired() {
    let mut input = String::from("* #variable= 60 #constraint= 1\nmin:");
    for i in 1..=60 {
        input.push_str(&format!(" +1 x{i}"));
    }
    input.push_str(" ;\n");
    for i in 1..=60 {
        if i > 1 {
            input.push(' ');
        }
        input.push_str(&format!("+1 x{i}"));
    }
    input.push_str(" >= 1 ;\n");

    let instance = parse_opb(&input).expect("parse should succeed");
    let objective = instance
        .objective
        .as_ref()
        .expect("test instance must include an objective");
    let term_flag = AtomicBool::new(false);
    let mut improvements = Vec::new();

    let result = solve_optimization_portfolio(
        &instance,
        objective,
        Some(Duration::ZERO),
        Instant::now(),
        &term_flag,
        &mut |obj_value, assignment| {
            improvements.push((obj_value, assignment.to_vec()));
        },
    );

    assert_eq!(result, unknown_solution());
    assert!(improvements.is_empty());
}

#[test]
fn test_profile_large_optimization_uses_native_then_sat() {
    // Build a larger optimization instance (>50 vars) to trigger NativeThenSat.
    let mut constraints = String::new();
    constraints.push_str("* #variable= 60 #constraint= 2\n");
    constraints.push_str("min: +1 x1 +2 x2 +3 x3 ;\n");
    // First constraint: sum of 60 vars >= 30
    constraints.push_str("+1 x1 ");
    for i in 2..=60 {
        constraints.push_str(&format!("+1 x{i} "));
    }
    constraints.push_str(">= 30 ;\n");
    // Second constraint: another weighted constraint
    constraints.push_str("+2 x1 +3 x2 >= 1 ;\n");

    let instance = parse_opb(&constraints).expect("parse should succeed");
    let profile = InstanceProfile::from_instance(&instance);

    assert!(profile.has_objective);
    // Coefficients include 2 and 3, so not cardinality.
    assert!(!profile.is_cardinality);
    assert!(profile.num_vars >= 50);
    assert_eq!(
        select_optimization_strategy(&profile),
        Strategy::NativeThenSat
    );
}

#[test]
fn test_profile_large_cardinality_decision_uses_native_then_sat() {
    // NON-tiny linear cardinality DECISION instances now route through
    // NativeThenSat (native cutting planes first, SAT encoding fallback)
    // instead of straight to SAT. The SAT-only shortcut would time out on
    // CP-hard cardinality families (rand6reg/ECrand6reg); native CP closes
    // them once conflict-analysis lemmas are strong, and the SAT fallback
    // keeps anything native cannot close as a no-regression safety net.
    let mut input = String::from("* #variable= 60 #constraint= 1\nmin:");
    for i in 1..=60 {
        input.push_str(&format!(" +1 x{i}"));
    }
    input.push_str(" ;\n");
    for i in 1..=60 {
        if i > 1 {
            input.push(' ');
        }
        input.push_str(&format!("+1 x{i}"));
    }
    input.push_str(" >= 30 ;\n");

    let instance = parse_opb(&input).expect("parse should succeed");
    let profile = InstanceProfile::from_instance(&instance);

    assert!(profile.has_objective);
    assert!(profile.is_cardinality);
    assert!(profile.is_linear);
    assert_eq!(select_strategy(&profile), Strategy::NativeThenSat);
    assert_eq!(
        select_optimization_strategy(&profile),
        Strategy::NativeThenSat
    );
}

#[test]
fn test_profile_large_cardinality_optimization_uses_native_then_sat() {
    let mut input = String::from("* #variable= 60 #constraint= 1\nmin:");
    for i in 1..=60 {
        input.push_str(&format!(" +1 x{i}"));
    }
    input.push_str(" ;\n");
    for i in 1..=60 {
        if i > 1 {
            input.push(' ');
        }
        input.push_str(&format!("+1 x{i}"));
    }
    input.push_str(" >= 30 ;\n");

    let instance = parse_opb(&input).expect("parse should succeed");
    let profile = InstanceProfile::from_instance(&instance);

    assert!(profile.has_objective);
    assert!(profile.is_cardinality);
    assert!(profile.is_linear);
    assert!(profile.num_vars >= 50);
    assert_eq!(
        select_optimization_strategy(&profile),
        Strategy::NativeThenSat
    );
}

#[test]
fn test_solve_decision_portfolio_tiny_sat() {
    let input = "* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let term_flag = AtomicBool::new(false);
    let start = Instant::now();

    let result =
        solve_decision_portfolio(&instance, Some(Duration::from_secs(5)), start, &term_flag);
    assert_eq!(result.status, PbStatus::Satisfiable);
    assert!(!result.assignment.is_empty());
}

#[test]
fn test_solve_decision_portfolio_with_timings_reports_stats_fields() {
    let input = "* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let term_flag = AtomicBool::new(false);

    let outcome = solve_decision_portfolio_with_timings(
        &instance,
        Some(Duration::from_secs(5)),
        Instant::now(),
        &term_flag,
    );

    assert_eq!(outcome.solution.status, PbStatus::Satisfiable);
    assert_eq!(
        outcome.timings.stats_fields().len(),
        PB_PORTFOLIO_STATS_FIELD_COUNT
    );
    let field_names: Vec<&str> = outcome
        .timings
        .stats_fields()
        .iter()
        .map(|(key, _)| *key)
        .collect();
    assert!(field_names.contains(&"pb_portfolio_total_ms"));
    assert!(field_names.contains(&"pb_portfolio_profile_ms"));
    assert!(field_names.contains(&"pb_portfolio_sat_ms"));
    assert!(field_names.contains(&"pb_clique_published_exact_continue"));
    assert!(field_names.contains(&"pb_clique_published_exact_decision"));
    assert!(field_names.contains(&"pb_clique_published_exact_exchange"));
}

#[test]
fn test_solve_decision_portfolio_unsat() {
    let input = "* #variable= 1 #constraint= 2\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let term_flag = AtomicBool::new(false);
    let start = Instant::now();

    let result =
        solve_decision_portfolio(&instance, Some(Duration::from_secs(5)), start, &term_flag);
    assert_eq!(result.status, PbStatus::Unsatisfiable);
}

#[test]
fn test_solve_decision_portfolio_large_coeff_native() {
    // Large coefficients should route to native PB CDCL.
    let input =
        "* #variable= 3 #constraint= 2\n+200 x1 +300 x2 +150 x3 >= 400 ;\n+1 x1 +1 x2 +1 x3 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let term_flag = AtomicBool::new(false);
    let start = Instant::now();

    let result =
        solve_decision_portfolio(&instance, Some(Duration::from_secs(5)), start, &term_flag);
    assert_eq!(result.status, PbStatus::Satisfiable);
}

#[test]
fn test_completed_native_unsat_preserves_validated_incumbent() {
    let reconciled = reconcile_completed_native_result(
        Some((vec![true, false], 3)),
        PbSolution {
            status: PbStatus::Unsatisfiable,
            assignment: Vec::new(),
            objective: None,
        },
        2,
    );

    assert_eq!(
        reconciled,
        PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![true, false],
            objective: Some(3),
        }
    );
}

#[test]
fn test_completed_native_worse_optimum_downgrades_to_incumbent() {
    let reconciled = reconcile_completed_native_result(
        Some((vec![true, false], 3)),
        PbSolution {
            status: PbStatus::OptimumFound,
            assignment: vec![false, true],
            objective: Some(7),
        },
        2,
    );

    assert_eq!(
        reconciled,
        PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![true, false],
            objective: Some(3),
        }
    );
}

#[test]
fn test_completed_native_better_optimum_stays_optimum() {
    let native_result = PbSolution {
        status: PbStatus::OptimumFound,
        assignment: vec![false, true],
        objective: Some(2),
    };
    let reconciled =
        reconcile_completed_native_result(Some((vec![true, false], 3)), native_result.clone(), 2);

    assert_eq!(reconciled, native_result);
}

#[test]
fn test_sanitize_incumbent_rejects_short_partial_normalizer_assignment() {
    let instance = sanitize_contract_instance();
    let objective = instance.objective.as_ref().unwrap();

    let sanitized =
        sanitize_optimization_incumbent(&[false, true, false], None, &instance, objective);

    assert_eq!(sanitized, None);
}

#[test]
fn test_sanitize_incumbent_recomputes_stale_normalizer_objective() {
    let instance = sanitize_contract_instance();
    let objective = instance.objective.as_ref().unwrap();
    let assignment = vec![false, true, false, false, true, false, false, true];

    let sanitized = sanitize_optimization_incumbent(&assignment, Some(0), &instance, objective);

    assert_eq!(sanitized, Some((assignment, 2)));
}

#[test]
fn test_sanitize_optimum_with_stale_normalizer_objective_downgrades_status() {
    let instance = sanitize_contract_instance();
    let objective = instance.objective.as_ref().unwrap();
    let assignment = vec![false, true, false, false, true, false, false, true];

    let sanitized = sanitize_optimization_solution(
        PbSolution {
            status: PbStatus::OptimumFound,
            assignment: assignment.clone(),
            objective: Some(0),
        },
        &instance,
        objective,
    );

    assert_eq!(
        sanitized,
        PbSolution {
            status: PbStatus::Satisfiable,
            assignment,
            objective: Some(2),
        }
    );
}

#[test]
fn test_merge_native_incumbent_with_unknown_fallback_preserves_incumbent() {
    let merged = merge_native_incumbent_with_fallback(
        Some((vec![true, false, true], 7)),
        PbSolution {
            status: PbStatus::Unknown,
            assignment: Vec::new(),
            objective: None,
        },
        3,
    );

    assert_eq!(
        merged,
        PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![true, false, true],
            objective: Some(7),
        }
    );
}

#[test]
fn test_merge_native_incumbent_with_unsat_fallback_preserves_native() {
    let merged = merge_native_incumbent_with_fallback(
        Some((vec![true, false], 4)),
        PbSolution {
            status: PbStatus::Unsatisfiable,
            assignment: Vec::new(),
            objective: None,
        },
        2,
    );

    assert_eq!(
        merged,
        PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![true, false],
            objective: Some(4),
        }
    );
}

#[test]
fn test_merge_native_incumbent_with_completed_fallback_keeps_fallback() {
    let merged = merge_native_incumbent_with_fallback(
        Some((vec![true, false], 9)),
        PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![false, true],
            objective: Some(3),
        },
        2,
    );

    assert_eq!(
        merged,
        PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![false, true],
            objective: Some(3),
        }
    );
}

#[test]
fn test_merge_native_incumbent_with_worse_feasible_fallback_preserves_native() {
    let merged = merge_native_incumbent_with_fallback(
        Some((vec![true, false, true], 4)),
        PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![false, true, false],
            objective: Some(7),
        },
        3,
    );

    assert_eq!(
        merged,
        PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![true, false, true],
            objective: Some(4),
        }
    );
}

#[test]
fn test_merge_native_incumbent_with_worse_optimal_fallback_downgrades_to_native() {
    let merged = merge_native_incumbent_with_fallback(
        Some((vec![true, true, false], 2)),
        PbSolution {
            status: PbStatus::OptimumFound,
            assignment: vec![false, false, true],
            objective: Some(5),
        },
        3,
    );

    assert_eq!(
        merged,
        PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![true, true, false],
            objective: Some(2),
        }
    );
}

#[test]
fn test_record_incumbent_improvement_suppresses_dominated_callbacks() {
    let mut best_assignment = Some((vec![true, false], 3));
    let mut calls = 0;

    record_incumbent_improvement(&mut best_assignment, 3, &[false, true], &mut |_, _| {
        calls += 1
    });
    record_incumbent_improvement(&mut best_assignment, 7, &[false, true], &mut |_, _| {
        calls += 1
    });

    assert_eq!(calls, 0);
    assert_eq!(best_assignment, Some((vec![true, false], 3)));
}

#[test]
fn test_report_solution_improvement_suppresses_dominated_solution() {
    let mut calls = 0;
    let solution = PbSolution {
        status: PbStatus::Satisfiable,
        assignment: vec![false, true],
        objective: Some(5),
    };

    report_solution_improvement(&solution, Some(5), &mut |_, _| calls += 1);
    report_solution_improvement(&solution, Some(3), &mut |_, _| calls += 1);

    assert_eq!(calls, 0);
}

#[test]
fn test_unit_set_cover_decision_incumbent_returns_valid_model() {
    let instance = unit_set_cover_decision_instance(&[&[1, 2], &[2, 3], &[1, 3]], 2);
    let term_flag = AtomicBool::new(false);

    let solution = try_unit_set_cover_decision_incumbent(
        &instance,
        Some(Duration::from_secs(1)),
        Instant::now(),
        &term_flag,
    )
    .expect("unit set-cover decision shape should produce a SAT incumbent");

    assert_eq!(solution.status, PbStatus::Satisfiable);
    assert_eq!(solution.objective, None);
    assert!(verify_all_constraints(
        &instance.constraints,
        &solution.assignment
    ));
    assert!(solution.assignment.iter().filter(|&&value| value).count() <= 2);
}

#[test]
fn test_unit_set_cover_decision_incumbent_rejects_over_budget_cover() {
    let instance = unit_set_cover_decision_instance(&[&[1], &[2], &[3]], 2);
    let term_flag = AtomicBool::new(false);

    assert!(try_unit_set_cover_decision_incumbent(
        &instance,
        Some(Duration::from_secs(1)),
        Instant::now(),
        &term_flag,
    )
    .is_none());
}

#[test]
fn test_unit_set_cover_decision_incumbent_respects_stop_conditions() {
    let instance = unit_set_cover_decision_instance(&[&[1, 2], &[2, 3], &[1, 3]], 2);
    let term_flag = AtomicBool::new(true);

    assert!(try_unit_set_cover_decision_incumbent(
        &instance,
        Some(Duration::from_secs(1)),
        Instant::now(),
        &term_flag,
    )
    .is_none());

    term_flag.store(false, Ordering::Relaxed);
    assert!(try_unit_set_cover_decision_incumbent(
        &instance,
        Some(Duration::ZERO),
        Instant::now(),
        &term_flag,
    )
    .is_none());
}

#[test]
fn test_bqo_accounting_matches_objective_evaluation() {
    let objective = PbObjective {
        terms: vec![
            PbTerm {
                coeff: 3,
                lits: Vec::new(),
            },
            PbTerm {
                coeff: -2,
                lits: vec![PbLit {
                    var: 1,
                    negated: false,
                }],
            },
            PbTerm {
                coeff: 4,
                lits: vec![PbLit {
                    var: 2,
                    negated: false,
                }],
            },
            PbTerm {
                coeff: -5,
                lits: vec![
                    PbLit {
                        var: 1,
                        negated: false,
                    },
                    PbLit {
                        var: 2,
                        negated: false,
                    },
                ],
            },
            PbTerm {
                coeff: 7,
                lits: vec![
                    PbLit {
                        var: 2,
                        negated: false,
                    },
                    PbLit {
                        var: 1,
                        negated: false,
                    },
                ],
            },
            PbTerm {
                coeff: 11,
                lits: vec![
                    PbLit {
                        var: 3,
                        negated: false,
                    },
                    PbLit {
                        var: 3,
                        negated: false,
                    },
                ],
            },
            PbTerm {
                coeff: -13,
                lits: vec![
                    PbLit {
                        var: 1,
                        negated: false,
                    },
                    PbLit {
                        var: 3,
                        negated: false,
                    },
                ],
            },
        ],
    };
    let (base, linear, adjacency) =
        build_positive_bqo(&objective, 3).expect("objective should be BQO-shaped");

    for mask in 0..8 {
        let assignment = (0..3)
            .map(|index| mask & (1 << index) != 0)
            .collect::<Vec<_>>();
        let accounted = bqo_objective_value(base, &linear, &adjacency, &assignment);
        assert_eq!(
            accounted,
            i128::from(eval_objective(&objective, &assignment))
        );

        for index in 0..3 {
            let mut flipped = assignment.clone();
            flipped[index] = !flipped[index];
            let expected_delta =
                eval_objective(&objective, &flipped) - eval_objective(&objective, &assignment);
            assert_eq!(
                bqo_flip_delta(index, &linear, &adjacency, &assignment),
                i128::from(expected_delta)
            );
        }
    }
}

#[test]
fn test_sat_optimization_portfolio_reports_only_real_witness_improvement() {
    let input =
        "* #variable= 3 #constraint= 1\nmin: +1 x1 +2 x2 +3 x3 ;\n+1 x1 +1 x2 +1 x3 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance
        .objective
        .as_ref()
        .expect("test instance must include an objective");
    let term_flag = AtomicBool::new(false);
    let start = Instant::now();
    let mut improvements = Vec::new();

    let result = solve_optimization_portfolio(
        &instance,
        objective,
        Some(Duration::from_secs(5)),
        start,
        &term_flag,
        &mut |obj_value, assignment| {
            improvements.push((obj_value, assignment.to_vec()));
        },
    );

    assert_eq!(improvements.len(), 1);
    assert!(!improvements[0].1.is_empty());
    assert_eq!(
        improvements[0].0,
        result.objective.expect("result should have objective")
    );
    assert_eq!(improvements[0].1, result.assignment);
}

#[test]
fn test_best_known_optimization_solution_normalizes_short_incumbent_assignment() {
    let input = "* #variable= 4 #constraint= 1\nmin: +1 x1 ;\n+1 x1 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance
        .objective
        .as_ref()
        .expect("instance should include objective");
    let result = best_known_optimization_solution(Some((vec![true], 1)), &instance, objective);

    assert_eq!(
        result,
        PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![true, false, false, false],
            objective: Some(1),
        }
    );
}

#[test]
fn test_best_known_optimization_solution_keeps_structural_lower_bound_incumbent_feasible() {
    let input = "* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance
        .objective
        .as_ref()
        .expect("instance should include objective");

    let result =
        best_known_optimization_solution(Some((vec![false, true], 1)), &instance, objective);

    assert_eq!(
        result,
        PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![false, true],
            objective: Some(1),
        }
    );
}

#[test]
fn test_sanitize_optimization_incumbent_normalizes_and_recomputes_objective() {
    let input = "* #variable= 2 #constraint= 1\nmin: +1 x1 +2 x2 ;\n+1 x1 +1 x2 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance
        .objective
        .as_ref()
        .expect("instance should include objective");

    let incumbent =
        sanitize_optimization_incumbent(&[false, true, true], Some(0), &instance, objective);

    assert_eq!(incumbent, Some((vec![false, true], 2)));
}

#[test]
fn test_sanitize_optimization_incumbent_rejects_invalid_witness() {
    let input = "* #variable= 2 #constraint= 1\nmin: +1 x1 +2 x2 ;\n+1 x1 +1 x2 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance
        .objective
        .as_ref()
        .expect("instance should include objective");

    let incumbent = sanitize_optimization_incumbent(&[false, false], Some(0), &instance, objective);

    assert_eq!(incumbent, None);
}

#[test]
fn test_sanitize_optimization_incumbent_rejects_i128_objective_overflow() {
    // FAIL-CLOSED (design §3.2): a feasible witness whose EXACT objective
    // recompute overflows i128 must be REJECTED (no incumbent), never stored
    // with a saturated/clamped value — a clamped objective could fabricate a
    // better-looking incumbent than the witness really has.
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![PbConstraint {
            terms: vec![PbTerm {
                coeff: 1,
                lits: vec![PbLit {
                    var: 1,
                    negated: false,
                }],
            }],
            rel: PbRel::Ge,
            rhs: 1,
        }],
        objective: Some(PbObjective {
            terms: vec![
                PbTerm {
                    coeff: i128::MAX,
                    lits: vec![PbLit {
                        var: 1,
                        negated: false,
                    }],
                },
                PbTerm {
                    coeff: i128::MAX,
                    lits: vec![PbLit {
                        var: 2,
                        negated: false,
                    }],
                },
            ],
        }),
    };
    let objective = instance.objective.as_ref().unwrap();

    let incumbent = sanitize_optimization_incumbent(&[true, true], Some(0), &instance, objective);
    assert_eq!(incumbent, None, "i128 overflow must reject, not saturate");

    // Non-vacuity control: with only ONE wide term satisfied the exact sum is
    // in range and the same gate ACCEPTS with the exact recompute.
    let accepted = sanitize_optimization_incumbent(&[true, false], Some(0), &instance, objective);
    assert_eq!(accepted, Some((vec![true, false], i128::MAX)));
}

// =====================================================================
// Structural worker verdict split (design §3.2): primal workers are
// verdict-INCAPABLE (their spawn path holds a `PrimalSender` and returns
// `()`), and the coordinator adopts a definitive `Done` verdict ONLY from
// a complete baseline label — in release builds too.
// =====================================================================

/// `min: x1 + x2` s.t. `x1 + x2 >= 1`: minimal linear optimization fixture
/// for the worker-split tests.
fn worker_split_instance() -> PbInstance {
    parse_opb("* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n")
        .expect("worker-split fixture should parse")
}

#[test]
fn test_optimization_worker_specs_route_primal_workers_verdict_incapable() {
    let instance = worker_split_instance();
    let profile = InstanceProfile::from_instance(&instance);
    let specs = optimization_worker_specs(&profile, OptimizationPortfolioRoute::Standard);

    // Every spec's kind matches its label class, and the two classes tile the
    // spec set (no worker is both / neither).
    for spec in &specs {
        let is_primal_kind = matches!(spec.run, OptimizationWorkerKind::Primal(_));
        assert_eq!(
            is_primal_kind,
            primal_optimization_label(spec.label),
            "spec {} routed through the wrong worker kind",
            spec.label
        );
        assert_ne!(
            is_primal_kind,
            complete_optimization_verdict_label(spec.label),
            "spec {} must be exactly one of complete/primal",
            spec.label
        );
    }
    // Non-vacuity: this linear+objective profile includes every primal spec,
    // and they stay LAST in priority order (dropped first under a tight core
    // budget — the safe-additive contract). The four diversified §2.3 arms
    // (P8-P11) sit STRICTLY AFTER P7 `sls-primal-opt`, so at core budgets <= 7
    // the worker set is byte-identical to before they existed; the DDFW+SCC
    // quality arm (P12) is LAST of all, so it is dropped first.
    let labels: Vec<&str> = specs.iter().map(|spec| spec.label).collect();
    assert_eq!(
        &labels[labels.len() - 7..],
        &[
            "lns-primal-improve-opt",
            "sls-primal-opt",
            "sls-restarts-opt",
            "sls-alt-opt",
            "sls-unified-opt",
            "lp-round-sls-opt",
            "sls-ddfw-opt",
        ],
        "primal specs must stay lowest-priority: {labels:?}"
    );
    assert_eq!(
        labels.len(),
        12,
        "5 complete baselines + P6/P7 + the 4 diversified arms + P12 DDFW: {labels:?}"
    );
    // The linear STANDARD route never includes the WBO- or NLC-only arms.
    assert!(
        !labels.contains(&"wbo-sls-opt")
            && !labels.contains(&"nlc-sls-opt")
            && !labels.contains(&"nlc-sls-focused-opt"),
        "route-specific arms must not join the standard linear set: {labels:?}"
    );
}

/// WBO route (design: the reduced-PBO parallel set): the standard linear specs
/// plus the high-cap `wbo-sls-opt` primal arm placed DIRECTLY BEHIND the five
/// complete baselines (index 5) — it is the only arm that can land an
/// incumbent on >200k-var WBO reductions, so it must outrank the P7-P11 SLS
/// arms that provably decline there — with the DDFW quality arm still LAST
/// (dropped first). Worker kinds keep tiling into complete/primal.
#[test]
fn test_optimization_worker_specs_wbo_route_appends_wbo_sls_arm() {
    // Serialize with the env-flag test so a mid-test AY_PB_WBO_SLS override
    // cannot flip the default-on worker gate under this test's feet.
    let _guard = lock_env();
    let instance = worker_split_instance();
    let profile = InstanceProfile::from_instance(&instance);
    let specs = optimization_worker_specs(&profile, OptimizationPortfolioRoute::WboReduced);
    for spec in &specs {
        let is_primal_kind = matches!(spec.run, OptimizationWorkerKind::Primal(_));
        assert_eq!(
            is_primal_kind,
            primal_optimization_label(spec.label),
            "spec {} routed through the wrong worker kind",
            spec.label
        );
    }
    let labels: Vec<&str> = specs.iter().map(|spec| spec.label).collect();
    assert_eq!(
        labels[5], "wbo-sls-opt",
        "the high-cap SLS arm must sit directly behind the five complete baselines: {labels:?}"
    );
    assert_eq!(
        labels.last(),
        Some(&"sls-ddfw-opt"),
        "the DDFW quality arm must stay LAST (dropped first): {labels:?}"
    );
    assert_eq!(
        labels.len(),
        13,
        "the WBO route is the standard linear set plus wbo-sls-opt: {labels:?}"
    );
    // Safe-additive: the standard specs are not displaced RELATIVE TO EACH
    // OTHER — removing the route-specific arm recovers the standard order.
    let standard = optimization_worker_specs(&profile, OptimizationPortfolioRoute::Standard);
    let standard_labels: Vec<&str> = standard.iter().map(|spec| spec.label).collect();
    let without_wbo_arm: Vec<&str> = labels
        .iter()
        .copied()
        .filter(|label| *label != "wbo-sls-opt")
        .collect();
    assert_eq!(
        without_wbo_arm, standard_labels,
        "WBO route must not reorder/displace the standard specs relative to each other"
    );
}

/// Default-core-budget reachability pin for the F1 regression: the parallel
/// coordinator spawns `specs.take(min(len, core_budget))`, so at a budget of
/// 8 cores the WBO route MUST include `wbo-sls-opt` — before the fix it sat
/// at index 11 and was unreachable below 12 cores, leaving the >200k-var WBO
/// reductions with zero incumbent-capable workers.
#[test]
fn test_optimization_worker_specs_wbo_route_budget_8_includes_wbo_sls_arm() {
    let _guard = lock_env();
    let instance = worker_split_instance();
    let profile = InstanceProfile::from_instance(&instance);
    let specs = optimization_worker_specs(&profile, OptimizationPortfolioRoute::WboReduced);
    let budget_8: Vec<&str> = specs.iter().take(8).map(|spec| spec.label).collect();
    assert!(
        budget_8.contains(&"wbo-sls-opt"),
        "an 8-core budget on the WBO route must reach the high-cap SLS arm: {budget_8:?}"
    );
}

/// NLC route (non-linear OPT profile): exactly the NLC-safe subset — the P1
/// sequential baseline (whose internal routing owns the NLC special paths),
/// the two internally-linearizing SAT-encoded baselines, the dedicated
/// native-OLL-on-linearization complete worker (P5b, the product-objective twin
/// of P5 that closes the medium graph-family members via the clique-cover /
/// structural / LP floors), then the two product-native primal arms LAST
/// (`nlc-sls-opt` and the diversified `nlc-sls-focused-opt`, safe-additive by
/// position). The raw-native engines and every linear-tracker primal arm are
/// excluded.
#[test]
fn test_optimization_worker_specs_nonlinear_route_nlc_safe_subset() {
    let input = "* #variable= 3 #constraint= 2\nmin: +1 x1 +1 x2 ;\n+1 x1 x2 +1 x3 >= 1 ;\n+1 x1 +1 x2 +1 x3 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let profile = InstanceProfile::from_instance(&instance);
    assert!(!profile.is_linear && profile.has_objective);
    let specs = optimization_worker_specs(&profile, OptimizationPortfolioRoute::Standard);
    let labels: Vec<&str> = specs.iter().map(|spec| spec.label).collect();
    assert_eq!(
        labels,
        vec![
            "sequential-portfolio-opt",
            "sat-oll-opt",
            "sat-binary-search-opt",
            "nonlinear-native-oll-opt",
            "nlc-sls-opt",
            "nlc-sls-focused-opt",
        ],
        "non-linear profiles must get exactly the NLC-safe subset"
    );
    // The new native-OLL-on-linearization worker is a COMPLETE engine (it may
    // send a definitive OptimumFound/Unsatisfiable verdict), not a primal arm.
    assert!(complete_optimization_verdict_label(
        "nonlinear-native-oll-opt"
    ));
    for spec in &specs {
        let is_primal_kind = matches!(spec.run, OptimizationWorkerKind::Primal(_));
        assert_eq!(
            is_primal_kind,
            primal_optimization_label(spec.label),
            "spec {} routed through the wrong worker kind",
            spec.label
        );
    }
    // The product-native arm is PRIMAL (structurally verdict-incapable).
    assert!(matches!(
        specs.last().expect("non-empty").run,
        OptimizationWorkerKind::Primal(_)
    ));
}

#[test]
fn test_primal_sender_streams_improvements_and_finishes_verdict_free() {
    let (tx, rx) = mpsc::channel();
    let sender = PrimalSender::new(tx, "sls-primal-opt");

    sender.send_improvement(1, vec![true, false]);
    sender.finish();

    match rx.recv().expect("improvement should arrive") {
        WorkerMsg::Improvement(obj_value, model) => {
            assert_eq!(obj_value, 1);
            assert_eq!(model, vec![true, false]);
        }
        _ => panic!("first message must be the improvement"),
    }
    match rx.recv().expect("completion signal should arrive") {
        WorkerMsg::Finished { label } => assert_eq!(label, "sls-primal-opt"),
        _ => panic!("primal completion must be the verdict-free Finished"),
    }
    // `finish` consumed the sender: the channel is closed, so nothing else
    // (in particular no late verdict) can ever arrive from this worker.
    assert!(rx.recv().is_err());
}

/// Drives `collect_optimization_result` over a pre-injected message sequence
/// (the channel closes after `msgs`), with `labels` registered as the spawned
/// worker set (spec priority order) and a generous timeout so the hard
/// collection deadline stays out of the way.
fn collect_injected(
    msgs: Vec<WorkerMsg>,
    labels: &[&'static str],
    instance: &PbInstance,
    objective: &PbObjective,
    on_improve: &mut dyn FnMut(i128, &[bool]),
) -> PbSolution {
    let (tx, rx) = mpsc::channel();
    for msg in msgs {
        tx.send(msg).expect("send should succeed");
    }
    drop(tx);
    let mut controls = WorkerStopControls::default();
    for label in labels {
        let _ = controls.register(label);
    }
    let outer_term = AtomicBool::new(false);
    collect_optimization_result(
        &rx,
        &mut controls,
        &outer_term,
        Some(Duration::from_secs(10)),
        Instant::now(),
        instance,
        objective,
        on_improve,
        &SharedBounds::new(),
        &mut OptimizationBackfill::none(),
    )
}

#[test]
fn test_coordinator_counts_verdict_free_finished_toward_completion() {
    // A primal worker streams one incumbent and finishes verdict-free. The
    // coordinator must terminate (finished == spawn), keep the re-verified
    // incumbent, and report SATISFIABLE — never OPTIMUM.
    let instance = worker_split_instance();
    let objective = instance
        .objective
        .clone()
        .expect("fixture should include objective");
    let (tx, rx) = mpsc::channel();
    let sender = PrimalSender::new(tx, "lns-primal-improve-opt");
    sender.send_improvement(1, vec![true, false]);
    sender.finish();

    let mut controls = WorkerStopControls::default();
    let _flag = controls.register("lns-primal-improve-opt");
    let outer_term = AtomicBool::new(false);
    let mut on_improve = |_: i128, _: &[bool]| {};
    let outcome = collect_optimization_result(
        &rx,
        &mut controls,
        &outer_term,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &instance,
        &objective,
        &mut on_improve,
        &SharedBounds::new(),
        &mut OptimizationBackfill::none(),
    );

    assert_eq!(outcome.status, PbStatus::Satisfiable);
    assert_eq!(outcome.assignment, vec![true, false]);
    assert_eq!(outcome.objective, Some(1));
}

#[test]
fn test_coordinator_ignores_definitive_verdict_from_non_complete_label() {
    // BELT-AND-SUSPENDERS for the structural split: a `Done` claiming
    // `OptimumFound` from a label that is NOT a complete baseline must not be
    // adopted as the verdict (its feasible witness still counts, through the
    // sanitize gate). Structurally a primal worker cannot send `Done` at all,
    // so the test injects the message directly into the coordinator channel.
    let instance = worker_split_instance();
    let objective = instance
        .objective
        .clone()
        .expect("fixture should include objective");
    let outcome = collect_injected(
        vec![WorkerMsg::Done {
            label: "sls-primal-opt",
            solution: PbSolution {
                status: PbStatus::OptimumFound,
                assignment: vec![true, false],
                objective: Some(1),
            },
        }],
        &["sls-primal-opt"],
        &instance,
        &objective,
        &mut |_, _| {},
    );

    assert_eq!(
        outcome.status,
        PbStatus::Satisfiable,
        "a non-baseline label's OPTIMUM claim must be ignored (witness kept)"
    );
    assert_eq!(outcome.objective, Some(1));
}

#[test]
fn test_coordinator_adopts_definitive_verdict_from_complete_label() {
    // 0-REGRESSION control for the guard above: the SAME message from a
    // complete baseline label IS adopted as the definitive verdict.
    let instance = worker_split_instance();
    let objective = instance
        .objective
        .clone()
        .expect("fixture should include objective");
    let outcome = collect_injected(
        vec![WorkerMsg::Done {
            label: "native-cdcl-opt",
            solution: PbSolution {
                status: PbStatus::OptimumFound,
                assignment: vec![true, false],
                objective: Some(1),
            },
        }],
        &["native-cdcl-opt"],
        &instance,
        &objective,
        &mut |_, _| {},
    );

    assert_eq!(outcome.status, PbStatus::OptimumFound);
    assert_eq!(outcome.objective, Some(1));
}

/// Fixture for the coordinator reconcile tests: min 9·x1 + 8·x2 + 10·x3 with
/// x1 + x2 + x3 >= 1, so the feasible objective values are 8 (x2, the true
/// optimum), 9 (x1) and 10 (x3), and the all-false model is INFEASIBLE.
fn reconcile_instance() -> PbInstance {
    parse_opb(
        "* #variable= 3 #constraint= 1\nmin: +9 x1 +8 x2 +10 x3 ;\n+1 x1 +1 x2 +1 x3 >= 1 ;\n",
    )
    .expect("reconcile fixture should parse")
}

#[test]
fn test_coordinator_refuses_unsat_contradicted_by_verified_incumbent() {
    // FAIL-CLOSED RECONCILE (release-path, not a debug_assert): a buggy
    // worker's UNSATISFIABLE while the coordinator holds a VERIFIED feasible
    // incumbent is refused; the collector tail returns the incumbent as
    // SATISFIABLE. Adopting the UNSAT would be a wrong answer.
    let instance = reconcile_instance();
    let objective = instance.objective.clone().expect("fixture has objective");
    let mut improvements: Vec<(i128, Vec<bool>)> = Vec::new();
    let outcome = collect_injected(
        vec![
            WorkerMsg::Improvement(9, vec![true, false, false]),
            WorkerMsg::Done {
                label: "sat-oll-opt",
                solution: PbSolution {
                    status: PbStatus::Unsatisfiable,
                    assignment: Vec::new(),
                    objective: None,
                },
            },
        ],
        &["sat-oll-opt"],
        &instance,
        &objective,
        &mut |obj, model| improvements.push((obj, model.to_vec())),
    );

    assert_eq!(outcome.status, PbStatus::Satisfiable);
    assert_eq!(outcome.objective, Some(9));
    assert_eq!(outcome.assignment, vec![true, false, false]);
    assert_eq!(improvements, vec![(9, vec![true, false, false])]);
}

#[test]
fn test_coordinator_refuses_optimum_worse_than_verified_incumbent() {
    // A claimed OPTIMUM strictly worse than the verified best incumbent is
    // contradicted by a concrete feasible witness — refused; the incumbent is
    // returned as SATISFIABLE.
    let instance = reconcile_instance();
    let objective = instance.objective.clone().expect("fixture has objective");
    let outcome = collect_injected(
        vec![
            WorkerMsg::Improvement(9, vec![true, false, false]),
            WorkerMsg::Done {
                label: "sat-oll-opt",
                solution: PbSolution {
                    status: PbStatus::OptimumFound,
                    assignment: vec![false, false, true],
                    objective: Some(10),
                },
            },
        ],
        &["sat-oll-opt"],
        &instance,
        &objective,
        &mut |_, _| {},
    );

    assert_eq!(outcome.status, PbStatus::Satisfiable);
    assert_eq!(outcome.objective, Some(9));
    assert_eq!(outcome.assignment, vec![true, false, false]);
}

#[test]
fn test_coordinator_adopts_consistent_better_optimum() {
    // 0-REGRESSION control for the reconcile: an OPTIMUM that re-verifies and
    // is no worse than the incumbent pool IS adopted (and its witness is
    // streamed as the final improvement first).
    let instance = reconcile_instance();
    let objective = instance.objective.clone().expect("fixture has objective");
    let mut improvements: Vec<(i128, Vec<bool>)> = Vec::new();
    let outcome = collect_injected(
        vec![
            WorkerMsg::Improvement(9, vec![true, false, false]),
            WorkerMsg::Done {
                label: "sat-oll-opt",
                solution: PbSolution {
                    status: PbStatus::OptimumFound,
                    assignment: vec![false, true, false],
                    objective: Some(8),
                },
            },
        ],
        &["sat-oll-opt"],
        &instance,
        &objective,
        &mut |obj, model| improvements.push((obj, model.to_vec())),
    );

    assert_eq!(outcome.status, PbStatus::OptimumFound);
    assert_eq!(outcome.objective, Some(8));
    assert_eq!(outcome.assignment, vec![false, true, false]);
    assert_eq!(
        improvements,
        vec![(9, vec![true, false, false]), (8, vec![false, true, false]),]
    );
}

#[test]
fn test_coordinator_refuses_unverifiable_optimum_claims() {
    // The coordinator sanitizes every OPTIMUM claim before adopting it
    // (re-verify + exact objective recompute + strict-optimum gate), like the
    // sequential consumers wrap the SAT engines. An INFEASIBLE model — or a
    // claim with no objective at all — is refused; the verified incumbent
    // pool wins.
    let instance = reconcile_instance();
    let objective = instance.objective.clone().expect("fixture has objective");
    let infeasible = collect_injected(
        vec![
            WorkerMsg::Improvement(9, vec![true, false, false]),
            WorkerMsg::Done {
                label: "sat-binary-search-opt",
                solution: PbSolution {
                    status: PbStatus::OptimumFound,
                    // Violates x1 + x2 + x3 >= 1.
                    assignment: vec![false, false, false],
                    objective: Some(0),
                },
            },
        ],
        &["sat-binary-search-opt"],
        &instance,
        &objective,
        &mut |_, _| {},
    );
    assert_eq!(infeasible.status, PbStatus::Satisfiable);
    assert_eq!(infeasible.objective, Some(9));

    let absent_objective = collect_injected(
        vec![
            WorkerMsg::Improvement(9, vec![true, false, false]),
            WorkerMsg::Done {
                label: "sat-binary-search-opt",
                solution: PbSolution {
                    status: PbStatus::OptimumFound,
                    assignment: vec![false, true, false],
                    objective: None,
                },
            },
        ],
        &["sat-binary-search-opt"],
        &instance,
        &objective,
        &mut |_, _| {},
    );
    assert_eq!(absent_objective.status, PbStatus::Satisfiable);
    // An objective-less claim carries no foldable incumbent either
    // (`solution_incumbent` requires one), so the earlier verified incumbent
    // wins outright.
    assert_eq!(absent_objective.objective, Some(9));
}

/// Shed-order core (F6): under (mocked) sustained memory pressure workers are
/// stopped in REVERSE spec-priority order — the primal arms die before the
/// complete baselines — and the P1 sequential baseline (index 0) is NEVER
/// shed, so the portfolio degrades to the baseline alone instead of aborting.
#[test]
fn test_memory_shed_order_reverse_priority_never_baseline() {
    // Pure core: sheds walk from the back, skip already-inactive workers,
    // and refuse index 0.
    let mut inactive = vec![false; 5];
    let mut order = Vec::new();
    while let Some(idx) = next_worker_to_shed(&inactive) {
        inactive[idx] = true;
        order.push(idx);
    }
    assert_eq!(order, vec![4, 3, 2, 1]);
    assert_eq!(next_worker_to_shed(&[false]), None, "sole baseline stays");

    // Controls wiring: shedding raises exactly the victim's stop flag, skips
    // workers that already finished on their own, and a mocked pressure
    // signal that stays high sheds progressively down to the baseline alone.
    let mut controls = WorkerStopControls::default();
    let labels = [
        "sequential-portfolio-opt",
        "native-cdcl-opt",
        "sat-oll-opt",
        "lns-primal-improve-opt",
        "sls-primal-opt",
    ];
    let flags: Vec<_> = labels
        .iter()
        .map(|label| controls.register(label))
        .collect();
    controls.mark_finished("sls-primal-opt");

    let pressure = [true, false, true, true, true];
    let mut shed: Vec<&str> = Vec::new();
    for under_pressure in pressure {
        if under_pressure {
            if let Some(label) = controls.shed_lowest_priority() {
                shed.push(label);
            }
        }
    }
    assert_eq!(
        shed,
        vec!["lns-primal-improve-opt", "sat-oll-opt", "native-cdcl-opt"],
        "reverse spec order, skipping the finished worker, never the baseline"
    );
    assert!(flags[3].load(Ordering::Relaxed) && flags[2].load(Ordering::Relaxed));
    assert!(flags[1].load(Ordering::Relaxed));
    assert!(
        !flags[0].load(Ordering::Relaxed),
        "the P1 sequential baseline must never be shed"
    );
    assert!(
        !flags[4].load(Ordering::Relaxed),
        "a worker that finished on its own is not re-stopped by shedding"
    );
}

/// Hard collection deadline (F7): a straggler worker that ignores its stop
/// flag past the caller's timeout must not stall the coordinator — it returns
/// the best VERIFIED streamed incumbent within timeout + grace (workers are
/// detached; no join on stragglers).
#[test]
fn test_collector_hard_deadline_returns_streamed_incumbent() {
    let instance = reconcile_instance();
    let objective = instance.objective.clone().expect("fixture has objective");

    let (tx, rx) = mpsc::channel();
    let mut controls = WorkerStopControls::default();
    let stop_flag = controls.register("sequential-portfolio-opt");
    // The straggler streams one incumbent, then holds its channel end open
    // well past the deadline (simulating a long uninterruptible solve step).
    std::thread::spawn(move || {
        tx.send(WorkerMsg::Improvement(9, vec![true, false, false]))
            .expect("send should succeed");
        std::thread::sleep(Duration::from_secs(20));
        drop(tx);
    });

    let outer_term = AtomicBool::new(false);
    let timeout = Duration::from_millis(200);
    let start = Instant::now();
    let mut improvements: Vec<i128> = Vec::new();
    let outcome = collect_optimization_result(
        &rx,
        &mut controls,
        &outer_term,
        Some(timeout),
        start,
        &instance,
        &objective,
        &mut |obj, _| improvements.push(obj),
        &SharedBounds::new(),
        &mut OptimizationBackfill::none(),
    );
    let elapsed = start.elapsed();

    assert!(
        elapsed < timeout + PARALLEL_COLLECT_GRACE + Duration::from_millis(500),
        "collector must return at the hard deadline, took {elapsed:?}"
    );
    assert_eq!(outcome.status, PbStatus::Satisfiable);
    assert_eq!(outcome.objective, Some(9));
    assert_eq!(improvements, vec![9]);
    assert!(
        stop_flag.load(Ordering::Relaxed),
        "the deadline must raise every worker's stop flag"
    );
}

// =====================================================================
// FREED-SLOT BACKFILL: when a spawned worker finishes early (declines in
// milliseconds on a size cap, or completes without a definitive verdict)
// the coordinator refills the freed core with the next unspawned spec,
// under fail-closed admission (budget / memory pressure / hard deadline /
// outer termination / shed), never disturbing drop-first shed order.
// =====================================================================

/// Builds a backfill state holding `specs` (priority order) with a live spawn
/// context wired to `tx` on `instance`, and the given core budget. Tests
/// override `memory_pressured` to mock pressure deterministically.
fn backfill_with_specs(
    specs: Vec<OptimizationWorkerSpec>,
    instance: &PbInstance,
    tx: mpsc::Sender<WorkerMsg>,
    core_budget: usize,
) -> OptimizationBackfill {
    let objective = instance.objective.clone().expect("fixture has objective");
    OptimizationBackfill::new(
        specs.into(),
        OptimizationSpawnContext {
            instance: Arc::new(instance.clone()),
            objective: Arc::new(objective),
            timeout_dur: Some(Duration::from_secs(10)),
            start: Instant::now(),
            shared_bounds: Arc::new(SharedBounds::new()),
            tx,
        },
        core_budget,
    )
}

/// A PRIMAL tail spec that streams one PLANTED incumbent and finishes. The
/// label must be a real primal label so the coordinator's accounting treats
/// it exactly like a production arm (verdict-free `Finished`, sanitize-gated
/// incumbent).
fn planted_primal_spec(
    label: &'static str,
    obj_value: i128,
    model: Vec<bool>,
) -> OptimizationWorkerSpec {
    OptimizationWorkerSpec {
        label,
        run: OptimizationWorkerKind::Primal(Box::new(
            move |_instance, _objective, _timeout, _start, _stop, sender| {
                sender.send_improvement(obj_value, model.clone());
            },
        )),
    }
}

/// The waste shape end-to-end at the coordinator: a high-priority primal arm
/// declines instantly (verdict-free `Finished`), the coordinator backfills
/// the freed slot with the queued tail spec, and the LATER arm's planted
/// incumbent is collected (sanitize-gated) into the final answer.
#[test]
fn test_backfill_spawns_tail_spec_and_collects_planted_incumbent() {
    let instance = worker_split_instance();
    let objective = instance.objective.clone().expect("fixture has objective");

    let (tx, rx) = mpsc::channel();
    // Two up-front workers: the complete baseline completes with NO verdict,
    // the high-priority SLS arm DECLINES instantly — exactly the size-cap
    // shape that used to leave its core idle for the whole solve.
    let mut controls = WorkerStopControls::default();
    let _ = controls.register("sequential-portfolio-opt");
    let _ = controls.register("sls-primal-opt");
    tx.send(WorkerMsg::Done {
        label: "sequential-portfolio-opt",
        solution: unknown_solution(),
    })
    .expect("send should succeed");
    tx.send(WorkerMsg::Finished {
        label: "sls-primal-opt",
    })
    .expect("send should succeed");

    let mut backfill = backfill_with_specs(
        vec![planted_primal_spec("sls-ddfw-opt", 1, vec![true, false])],
        &instance,
        tx.clone(),
        2,
    );
    backfill.memory_pressured = || false;
    drop(tx);

    let outer_term = AtomicBool::new(false);
    let mut improvements: Vec<i128> = Vec::new();
    let outcome = collect_optimization_result(
        &rx,
        &mut controls,
        &outer_term,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &instance,
        &objective,
        &mut |obj, _| improvements.push(obj),
        &SharedBounds::new(),
        &mut backfill,
    );

    assert_eq!(
        controls.labels(),
        vec!["sequential-portfolio-opt", "sls-primal-opt", "sls-ddfw-opt"],
        "the freed slot must be backfilled with the tail spec"
    );
    assert_eq!(outcome.status, PbStatus::Satisfiable);
    assert_eq!(outcome.objective, Some(1));
    assert_eq!(outcome.assignment, vec![true, false]);
    assert_eq!(
        improvements,
        vec![1],
        "the backfilled arm's incumbent streams"
    );
    assert!(
        backfill.queue.is_empty() && backfill.ctx.is_none(),
        "an exhausted queue must drop the held channel sender"
    );
}

/// LIVENESS: a worker whose thread dies WITHOUT sending its completion
/// message (the panicked-worker shape) must be reaped by the coordinator's
/// handle sweep — while the backfill machinery (or any other holder) keeps a
/// channel sender alive, the `Disconnected` break can never fire, so without
/// the reap collection stalls until the hard deadline (unbounded when
/// `timeout_dur` is `None`).
#[test]
fn test_collector_reaps_worker_that_dies_without_completion_message() {
    let instance = worker_split_instance();
    let objective = instance.objective.clone().expect("fixture has objective");

    let (tx, rx) = mpsc::channel();
    let mut controls = WorkerStopControls::default();
    // Worker 1: its thread terminates without ever sending Done/Finished —
    // the panicked-worker shape (a silent return models the post-unwind
    // state; no message is the load-bearing part).
    let _ = controls.register("native-cdcl-opt");
    controls.attach_last_handle(std::thread::spawn(|| {}));
    // Worker 2 completes normally via the channel.
    let _ = controls.register("sls-primal-opt");
    tx.send(WorkerMsg::Finished {
        label: "sls-primal-opt",
    })
    .expect("send should succeed");

    // Model the backfill-held sender: `held_tx` stays alive for the whole
    // collection, so Disconnected can NEVER fire — only the reap can account
    // worker 1.
    let held_tx = tx.clone();
    drop(tx);

    let mut backfill = OptimizationBackfill::none();
    let outer_term = AtomicBool::new(false);
    let started = Instant::now();
    let outcome = collect_optimization_result(
        &rx,
        &mut controls,
        &outer_term,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &instance,
        &objective,
        &mut |_, _| {},
        &SharedBounds::new(),
        &mut backfill,
    );
    let elapsed = started.elapsed();
    drop(held_tx);

    assert_eq!(outcome.status, PbStatus::Unknown);
    assert!(
        elapsed < Duration::from_secs(2),
        "collection must exit via the panicked-worker reap, not the deadline \
         (took {elapsed:?})"
    );
    assert_eq!(
        controls.active(),
        0,
        "the reaped worker must be accounted inactive"
    );
}

/// Hard collection deadline for the DECISION collector (mirror of the
/// optimization straggler test): a decision worker that ignores its stop flag
/// past the caller's timeout — e.g. stuck in a long uninterruptible
/// construct/encode step on a multi-million-variable instance — must not stall
/// the coordinator. It returns UNKNOWN within timeout + grace (workers are
/// detached; no join on stragglers) and every worker's stop flag is raised.
#[test]
fn test_decision_collector_hard_deadline_returns_unknown() {
    let (tx, rx) = mpsc::channel();
    let mut controls = WorkerStopControls::default();
    let stop_flag = controls.register("sequential-portfolio-decision");
    // The straggler never sends a verdict; it holds its channel end open well
    // past the deadline (simulating a long uninterruptible solve step).
    let straggler = std::thread::spawn(move || {
        std::thread::sleep(Duration::from_secs(20));
        drop(tx);
    });
    controls.attach_last_handle(straggler);

    let outer_term = AtomicBool::new(false);
    let timeout = Duration::from_millis(200);
    let start = Instant::now();
    let outcome = collect_decision_result(&rx, &mut controls, &outer_term, Some(timeout), start);
    let elapsed = start.elapsed();

    assert!(
        elapsed < timeout + PARALLEL_COLLECT_GRACE + Duration::from_millis(500),
        "decision collector must return at the hard deadline, took {elapsed:?}"
    );
    assert_eq!(outcome.status, PbStatus::Unknown);
    assert!(
        stop_flag.load(Ordering::Relaxed),
        "the deadline must raise every worker's stop flag"
    );
}

/// LIVENESS parity for the DECISION collector: a worker whose thread dies
/// WITHOUT sending its completion (the panicked-worker shape) is reaped by the
/// handle sweep. Alongside it a second worker holds a channel sender open, so
/// the all-senders-gone `Disconnected` break can never fire — the reap is the
/// load-bearing accounting, bounded by the hard deadline. The collector returns
/// UNKNOWN within timeout + grace.
#[test]
fn test_decision_collector_reaps_dead_worker_alongside_straggler() {
    let (tx, rx) = mpsc::channel();
    let mut controls = WorkerStopControls::default();

    // Worker 1: its thread terminates without ever sending Done — the
    // panicked-worker shape (a silent return models the post-unwind state; the
    // absent message is the load-bearing part). Its own sender is dropped here.
    let _ = controls.register("native-cdcl-decision");
    controls.attach_last_handle(std::thread::spawn(|| {}));

    // Worker 2: a straggler that holds its sender open past the deadline, so
    // Disconnected can NEVER fire — only the reap can account worker 1, and the
    // hard deadline bounds worker 2.
    let _ = controls.register("sat-encoded-decision");
    let straggler = std::thread::spawn(move || {
        std::thread::sleep(Duration::from_secs(20));
        drop(tx);
    });
    controls.attach_last_handle(straggler);

    let outer_term = AtomicBool::new(false);
    let timeout = Duration::from_millis(200);
    let start = Instant::now();
    let outcome = collect_decision_result(&rx, &mut controls, &outer_term, Some(timeout), start);
    let elapsed = start.elapsed();

    assert_eq!(outcome.status, PbStatus::Unknown);
    assert!(
        elapsed < timeout + PARALLEL_COLLECT_GRACE + Duration::from_millis(500),
        "collector must return at the hard deadline despite the dead worker, took {elapsed:?}"
    );
}

/// Pure admission core: every input fails closed.
#[test]
fn test_backfill_admissible_fail_closed_on_every_input() {
    // Happy path: free slot, no pressure, clock alive, caller alive.
    assert!(backfill_admissible(3, 4, false, false, false));
    // Live actives must stay STRICTLY below the memory-clamped core budget
    // (never exceed the up-front clamp or the original core budget).
    assert!(!backfill_admissible(4, 4, false, false, false));
    assert!(!backfill_admissible(5, 4, false, false, false));
    // Memory pressure at/above the shed threshold.
    assert!(!backfill_admissible(3, 4, true, false, false));
    // Hard collection deadline fired.
    assert!(!backfill_admissible(3, 4, false, true, false));
    // Outer termination requested.
    assert!(!backfill_admissible(3, 4, false, false, true));
}

/// `try_backfill` honors the (mocked) memory-pressure probe, the hard
/// deadline, the live budget, and outer termination — with the right
/// persistence: pressure/budget refusals are TRANSIENT (queue kept for the
/// next completion), deadline/termination refusals are PERMANENT (queue and
/// held sender dropped).
#[test]
fn test_backfill_respects_memory_pressure_deadline_and_budget() {
    let instance = worker_split_instance();
    let outer_term = AtomicBool::new(false);
    let far_deadline = Some(Instant::now() + Duration::from_mins(1));
    let (tx, _rx) = mpsc::channel();

    // MEMORY PRESSURE (mocked high): refused but NOT disabled.
    let mut controls = WorkerStopControls::default();
    let _ = controls.register("sequential-portfolio-opt");
    let _ = controls.register("sls-primal-opt");
    controls.mark_finished("sls-primal-opt");
    let mut backfill = backfill_with_specs(
        vec![planted_primal_spec("sls-ddfw-opt", 1, vec![true, false])],
        &instance,
        tx.clone(),
        2,
    );
    backfill.memory_pressured = || true;
    backfill.try_backfill(&mut controls, &outer_term, far_deadline);
    assert_eq!(controls.spawned(), 2, "pressure must block the spawn");
    assert_eq!(
        backfill.queue.len(),
        1,
        "a pressure refusal is transient — the queue survives"
    );
    assert!(backfill.ctx.is_some());

    // Pressure clears: the SAME queue fills the slot on the next attempt.
    backfill.memory_pressured = || false;
    backfill.try_backfill(&mut controls, &outer_term, far_deadline);
    assert_eq!(controls.spawned(), 3, "cleared pressure admits the spawn");
    assert!(backfill.queue.is_empty() && backfill.ctx.is_none());

    // HARD DEADLINE fired: refused AND permanently disabled.
    let mut controls = WorkerStopControls::default();
    let _ = controls.register("sequential-portfolio-opt");
    let mut backfill = backfill_with_specs(
        vec![planted_primal_spec("sls-ddfw-opt", 1, vec![true, false])],
        &instance,
        tx.clone(),
        4,
    );
    backfill.memory_pressured = || false;
    backfill.try_backfill(
        &mut controls,
        &outer_term,
        Some(
            Instant::now()
                .checked_sub(Duration::from_millis(1))
                .expect("the monotonic clock has advanced by at least one millisecond"),
        ),
    );
    assert_eq!(controls.spawned(), 1, "no backfill after the hard deadline");
    assert!(
        backfill.queue.is_empty() && backfill.ctx.is_none(),
        "a deadline refusal is permanent"
    );

    // BUDGET: live actives at the clamped budget refuse the spawn (transient).
    let mut controls = WorkerStopControls::default();
    let _ = controls.register("sequential-portfolio-opt");
    let _ = controls.register("native-cdcl-opt");
    let mut backfill = backfill_with_specs(
        vec![planted_primal_spec("sls-ddfw-opt", 1, vec![true, false])],
        &instance,
        tx.clone(),
        2,
    );
    backfill.memory_pressured = || false;
    backfill.try_backfill(&mut controls, &outer_term, far_deadline);
    assert_eq!(controls.spawned(), 2, "a full budget must refuse the spawn");
    assert_eq!(backfill.queue.len(), 1);

    // OUTER TERMINATION: refused AND permanently disabled.
    let term = AtomicBool::new(true);
    let mut controls = WorkerStopControls::default();
    let _ = controls.register("sequential-portfolio-opt");
    let mut backfill = backfill_with_specs(
        vec![planted_primal_spec("sls-ddfw-opt", 1, vec![true, false])],
        &instance,
        tx,
        4,
    );
    backfill.memory_pressured = || false;
    backfill.try_backfill(&mut controls, &term, far_deadline);
    assert_eq!(controls.spawned(), 1, "no backfill after outer termination");
    assert!(backfill.queue.is_empty() && backfill.ctx.is_none());
}

/// Drop-first shedding still kills the LOWEST priority first when backfilled
/// workers exist: backfill appends in spec priority order (a backfilled spec
/// is always lower priority than every worker registered before it), so the
/// backfilled arms die before the up-front workers, the finished worker is
/// skipped, and the P1 baseline never dies. Also: several freed slots fill in
/// one `try_backfill` call, and `disable` (the post-shed state) is permanent.
#[test]
fn test_shed_order_accounts_for_backfilled_workers() {
    let instance = worker_split_instance();
    let (tx, _rx) = mpsc::channel();
    let outer_term = AtomicBool::new(false);

    let mut controls = WorkerStopControls::default();
    let _ = controls.register("sequential-portfolio-opt");
    let _ = controls.register("native-cdcl-opt");
    let _ = controls.register("sls-primal-opt");
    controls.mark_finished("sls-primal-opt");

    // Budget 4, live actives 2: BOTH queued tail specs fill in one call.
    let mut backfill = backfill_with_specs(
        vec![
            planted_primal_spec("sls-alt-opt", 1, vec![true, false]),
            planted_primal_spec("sls-ddfw-opt", 1, vec![true, false]),
        ],
        &instance,
        tx.clone(),
        4,
    );
    backfill.memory_pressured = || false;
    backfill.try_backfill(&mut controls, &outer_term, None);
    assert_eq!(
        controls.labels(),
        vec![
            "sequential-portfolio-opt",
            "native-cdcl-opt",
            "sls-primal-opt",
            "sls-alt-opt",
            "sls-ddfw-opt",
        ],
        "backfill must append in priority order and fill every freed slot"
    );

    let mut shed: Vec<&str> = Vec::new();
    while let Some(label) = controls.shed_lowest_priority() {
        shed.push(label);
    }
    assert_eq!(
        shed,
        vec!["sls-ddfw-opt", "sls-alt-opt", "native-cdcl-opt"],
        "backfilled arms must die first; finished worker skipped; baseline never"
    );

    // Post-shed the coordinator disables backfill permanently: further
    // completions must not spawn anything.
    let mut controls = WorkerStopControls::default();
    let _ = controls.register("sequential-portfolio-opt");
    let mut backfill = backfill_with_specs(
        vec![planted_primal_spec("sls-ddfw-opt", 1, vec![true, false])],
        &instance,
        tx,
        4,
    );
    backfill.memory_pressured = || false;
    backfill.disable();
    backfill.try_backfill(&mut controls, &outer_term, None);
    assert_eq!(controls.spawned(), 1, "disabled backfill must never spawn");
    assert!(backfill.queue.is_empty() && backfill.ctx.is_none());
}

/// >200k-var linear OPT fixture (>`MAX_SLS_VARS`/`MAX_LNS2_VARS` = 200k):
/// every default-cap SLS/LP tail arm declines instantly, and no complete
/// engine can prove a verdict within the short test budget.
fn huge_linear_opt_instance() -> PbInstance {
    let n: u32 = 200_001;
    let row = |negated: bool| -> PbConstraint {
        PbConstraint {
            terms: (1..=n)
                .map(|var| PbTerm {
                    coeff: 1,
                    lits: vec![PbLit { var, negated }],
                })
                .collect(),
            rel: PbRel::Ge,
            rhs: 100_000,
        }
    };
    let objective = PbObjective {
        terms: (1..=n)
            .map(|var| PbTerm {
                coeff: i128::from(1 + (var % 7)),
                lits: vec![gate_pos(var)],
            })
            .collect(),
    };
    PbInstance {
        num_vars: n,
        num_constraints: 2,
        constraints: vec![row(false), row(true)],
        objective: Some(objective),
    }
}

/// END-TO-END measurement shape for the freed-slot backfill (the reviewed
/// throughput waste): a >200k-var linear OPT instance through the REAL
/// `run_parallel_optimization` spawn + coordinator. The default-cap SLS arms
/// (P7/P8 in the up-front spawn) decline within milliseconds; before backfill
/// their cores stayed idle for the whole solve and the tail arms
/// (`sls-alt-opt` ... `sls-ddfw-opt`) NEVER spawned. Assert via the spawn
/// trace that the ddfw-class tail arms are actually activated, and that the
/// outcome stays sound (fail-closed: any answer is re-verified here).
#[test]
fn test_backfill_activates_tail_arms_on_huge_instance_end_to_end() {
    let instance = huge_linear_opt_instance();
    let objective = instance.objective.clone().expect("fixture has objective");
    assert!(is_linear(&instance), "fixture must be linear");

    let requested = 8;
    let core_budget = clamp_parallel_workers_by_memory(&instance, requested);
    if core_budget < requested {
        // Host too small for 8 estimated workers: the waste shape (and its
        // fix) needs the full budget to manifest. Skip rather than assert a
        // spawn set this machine cannot hold.
        eprintln!("skipping: memory clamp allows only {core_budget} workers");
        return;
    }

    let term_flag = AtomicBool::new(false);
    let (outcome, labels) = run_parallel_optimization_traced(
        &Arc::new(instance.clone()),
        &objective,
        Some(Duration::from_millis(1500)),
        Instant::now(),
        &term_flag,
        &mut |_, _| {},
        requested,
        OptimizationPortfolioRoute::Standard,
    );

    // Soundness first (zero wrong answers): whatever came back must be a
    // verified answer shape — a feasible model with an exact objective, or
    // an honest UNKNOWN. Never UNSAT (the fixture is satisfiable).
    match outcome.status {
        PbStatus::Satisfiable | PbStatus::OptimumFound => {
            assert!(verify_all_constraints(
                &instance.constraints,
                &outcome.assignment
            ));
            assert_eq!(
                outcome.objective,
                Some(eval_objective(&objective, &outcome.assignment))
            );
        }
        PbStatus::Unknown => {}
        other => panic!("unexpected status {other:?} on a satisfiable fixture"),
    }

    // The up-front spawn is the first `requested` specs; the declining SLS
    // arms free their cores in milliseconds and backfill must walk the tail.
    assert!(
        labels.len() > requested,
        "backfill must spawn beyond the up-front budget: {labels:?}"
    );
    for tail in [
        "sls-alt-opt",
        "sls-unified-opt",
        "lp-round-sls-opt",
        "sls-ddfw-opt",
    ] {
        assert!(
            labels.contains(&tail),
            "tail arm {tail} must be backfilled: {labels:?}"
        );
    }
}

/// Routing core for the parallel DECISION track
/// (`should_parallelize_decision_with`): budget resolved + clamp survives
/// >= 2 workers; non-linear instances stay ELIGIBLE (the SAT-encoded decision
/// worker covers them). Pure inputs, so no env/global mutation.
#[test]
fn test_should_parallelize_decision_routing_core() {
    let linear = "* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n";
    let linear = parse_opb(linear).expect("parse should succeed");
    let roomy = usize::try_from(estimated_parallel_worker_bytes(&linear))
        .expect("small instance estimate fits")
        * 100;

    // Default multi-core case: budget resolved, plenty of memory.
    assert!(should_parallelize_decision_with(&linear, Some(8), roomy));
    // Parallel disabled (AY_PB_PARALLEL=0 -> no budget): sequential.
    assert!(!should_parallelize_decision_with(&linear, None, roomy));
    // Single core: the ORIGINAL sequential path (with its probe-then-detect
    // symmetry arm) — never a degenerate one-worker "parallel" run.
    assert!(!should_parallelize_decision_with(&linear, Some(1), roomy));
    // Memory clamp leaves < 2 workers: sequential.
    assert!(!should_parallelize_decision_with(&linear, Some(8), 1));

    // Non-linear decision instances stay eligible (SAT-encoded worker).
    let nonlinear = "* #variable= 2 #constraint= 1\n+1 x1 x2 +1 x1 >= 1 ;\n";
    let nonlinear = parse_opb(nonlinear).expect("parse should succeed");
    assert!(should_parallelize_decision_with(&nonlinear, Some(8), roomy));
}

/// Single-core regression (F4): a worker budget of 1 on an easy
/// symmetry-candidate instance must be answered fast through the sequential
/// probe — NOT stalled behind the concurrent symmetry arm's pure-sleep probe
/// window (>= 2s of doing nothing with no workers running alongside).
#[test]
fn test_single_worker_symmetry_candidate_answers_fast() {
    // > 4000 identical-shape rows over disjoint variable pairs: linear,
    // one constraint shape, fully symmetric, trivially SAT.
    let rows = 4_100u32;
    let mut input = format!("* #variable= {} #constraint= {rows}\n", 2 * rows);
    for i in 0..rows {
        input.push_str(&format!("+1 x{} +1 x{} >= 1 ;\n", 2 * i + 1, 2 * i + 2));
    }
    let instance = parse_opb(&input).expect("symmetric fixture should parse");
    assert!(
        is_symmetry_arm_candidate(&instance),
        "fixture must trip the symmetry-arm gate for the regression to bite"
    );

    let term_flag = AtomicBool::new(false);
    let start = Instant::now();
    let solution = run_parallel_decision(
        &Arc::new(instance.clone()),
        Some(Duration::from_secs(10)),
        start,
        &term_flag,
        1,
    );
    let elapsed = start.elapsed();
    assert_eq!(solution.status, PbStatus::Satisfiable);
    assert!(verify_all_constraints(
        &instance.constraints,
        &solution.assignment
    ));
    assert!(
        elapsed < Duration::from_millis(1_500),
        "single-core symmetry candidate must be answered by the sequential \
         probe without the arm's >= 2s sleep, took {elapsed:?}"
    );
}

#[test]
fn test_sanitize_optimization_solution_normalizes_short_valid_optimum() {
    let input = "* #variable= 4 #constraint= 1\nmin: +1 x1 ;\n+1 x1 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance
        .objective
        .as_ref()
        .expect("instance should include objective");

    let sanitized = sanitize_optimization_solution(
        PbSolution {
            status: PbStatus::OptimumFound,
            assignment: vec![true],
            objective: Some(1),
        },
        &instance,
        objective,
    );

    assert_eq!(
        sanitized,
        PbSolution {
            status: PbStatus::OptimumFound,
            assignment: vec![true, false, false, false],
            objective: Some(1),
        }
    );
}

#[test]
fn test_sanitize_optimization_solution_downgrades_mismatched_optimum_claim() {
    let input = "* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance
        .objective
        .as_ref()
        .expect("instance should include objective");

    let sanitized = sanitize_optimization_solution(
        PbSolution {
            status: PbStatus::OptimumFound,
            assignment: vec![false, true],
            objective: Some(0),
        },
        &instance,
        objective,
    );

    assert_eq!(
        sanitized,
        PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![false, true],
            objective: Some(1),
        }
    );
}

#[test]
fn test_sanitize_optimization_solution_promotes_structural_lower_bound_incumbent() {
    let input = "* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance
        .objective
        .as_ref()
        .expect("instance should include objective");

    let sanitized = sanitize_optimization_solution(
        PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![false, true],
            objective: Some(1),
        },
        &instance,
        objective,
    );

    assert_eq!(
        sanitized,
        PbSolution {
            status: PbStatus::OptimumFound,
            assignment: vec![false, true],
            objective: Some(1),
        }
    );
}

#[test]
fn test_sanitize_optimization_solution_rejects_invalid_witness() {
    let input = "* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance
        .objective
        .as_ref()
        .expect("instance should include objective");

    let sanitized = sanitize_optimization_solution(
        PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![false, false],
            objective: Some(0),
        },
        &instance,
        objective,
    );

    assert_eq!(sanitized, unknown_solution());
}

/// F1 regression (hard-deadline overshoot): an `OptimumFound` claim with
/// `claimed == actual` and the strict gate OFF must perform NO
/// floor-certificate work — the certificate's result provably cannot affect
/// the status, and the parallel coordinator invokes this sanitizer under its
/// HARD COLLECTION DEADLINE, where a needless certificate (up to
/// `FLOOR_CERT_SELF_BUDGET` = 3s of exact-rational elimination) would
/// overshoot the wall clock and forfeit the answer. Asserted via the
/// test-only per-thread call counter on
/// `certified_objective_floor_interruptible` — a cheap code-path observable,
/// deliberately NOT a timing check (timing would be flaky and this tiny
/// fixture's certificate is cheap anyway).
#[test]
fn test_sanitize_optimum_claim_skips_floor_cert_when_strict_gate_off() {
    let input = "* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance
        .objective
        .as_ref()
        .expect("instance should include objective");

    // OptimumFound, claimed == actual (x1=1, x2=0 -> objective 1), strict
    // mode off (`AY_PB_STRICT_OPTIMUM` unset in the test environment): the
    // verdict is decided without the certificate, so none may be computed.
    let calls_before = crate::proof::FLOOR_CERT_CALLS.with(std::cell::Cell::get);
    let sanitized = sanitize_optimization_solution(
        PbSolution {
            status: PbStatus::OptimumFound,
            assignment: vec![true, false],
            objective: Some(1),
        },
        &instance,
        objective,
    );
    assert_eq!(sanitized.status, PbStatus::OptimumFound);
    assert_eq!(sanitized.objective, Some(1));
    assert_eq!(
        crate::proof::FLOOR_CERT_CALLS.with(std::cell::Cell::get),
        calls_before,
        "claimed==actual OPTIMUM with the strict gate off must skip the \
         floor certificate entirely (lazy floor-cert gate)"
    );

    // Instrumentation control: a SATISFIABLE claim the cheap structural
    // floor cannot upgrade (actual 2 > floor 1) DOES consult the certificate
    // (the additive-upgrade arm), proving the counter observes the code path
    // and the first assertion is not vacuous.
    let sat = sanitize_optimization_solution(
        PbSolution {
            status: PbStatus::Satisfiable,
            assignment: vec![true, true],
            objective: Some(2),
        },
        &instance,
        objective,
    );
    assert_eq!(sat.status, PbStatus::Satisfiable);
    assert_eq!(
        crate::proof::FLOOR_CERT_CALLS.with(std::cell::Cell::get),
        calls_before + 1,
        "a SATISFIABLE claim needing the additive upgrade must consult the \
         certificate exactly once"
    );
}

#[test]
fn test_optimization_portfolio_uses_exact_max_clique_fragment() {
    let input = "* #variable= 3 #constraint= 2\n\
                 min: -1 x1 -1 x2 -1 x3 ;\n\
                 -1 x1 -1 x2 >= -1 ;\n\
                 -1 x1 -1 x3 >= -1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance
        .objective
        .as_ref()
        .expect("instance should include objective");
    let term_flag = AtomicBool::new(false);
    let mut improvements = Vec::new();

    let result = solve_optimization_portfolio(
        &instance,
        objective,
        Some(Duration::from_secs(5)),
        Instant::now(),
        &term_flag,
        &mut |obj_value, assignment| {
            improvements.push((obj_value, assignment.to_vec()));
        },
    );

    assert_eq!(result.status, PbStatus::OptimumFound);
    assert_eq!(result.objective, Some(-2));
    assert_eq!(result.assignment, vec![false, true, true]);
    assert_eq!(improvements, vec![(-2, vec![false, true, true])]);
}

fn parse_repo_instance_opb(relative_path: &str) -> PbInstance {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(relative_path);
    let input = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("read {} failed: {e}", path.display()));
    parse_opb(&input).expect("fixture should parse")
}

fn solve_decision_seq(instance: &PbInstance) -> PbSolution {
    let term_flag = AtomicBool::new(false);
    solve_decision_portfolio(
        instance,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &term_flag,
    )
}

fn solve_decision_par(instance: &PbInstance, workers: usize) -> PbSolution {
    let term_flag = AtomicBool::new(false);
    run_parallel_decision(
        &Arc::new(instance.clone()),
        Some(Duration::from_secs(10)),
        Instant::now(),
        &term_flag,
        workers,
    )
}

fn solve_opt_seq(instance: &PbInstance, objective: &PbObjective) -> PbSolution {
    let term_flag = AtomicBool::new(false);
    solve_optimization_portfolio(
        instance,
        objective,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &term_flag,
        &mut |_, _| {},
    )
}

fn solve_opt_par(instance: &PbInstance, objective: &PbObjective, workers: usize) -> PbSolution {
    let term_flag = AtomicBool::new(false);
    run_parallel_optimization(
        &Arc::new(instance.clone()),
        objective,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &term_flag,
        &mut |_, _| {},
        workers,
        OptimizationPortfolioRoute::Standard,
    )
}

#[test]
fn test_parallel_setting_from_env_default_auto_explicit_off_disables() {
    // Batteries-included default: UNSET means parallel ON (Auto, NBCORE-sized;
    // a single-core machine still degrades to sequential via spawn <= 1).
    assert_eq!(parallel_setting_from_env(None), Some(ParallelSetting::Auto));
    // The explicit opt-out (kept for compat) still forces the sequential path.
    assert_eq!(parallel_setting_from_env(Some(OsStr::new("0"))), None);
    assert_eq!(parallel_setting_from_env(Some(OsStr::new("off"))), None);
    assert_eq!(parallel_setting_from_env(Some(OsStr::new("false"))), None);
    assert_eq!(parallel_setting_from_env(Some(OsStr::new("no"))), None);
    assert_eq!(parallel_setting_from_env(Some(OsStr::new(""))), None);
}

/// Memory clamp for the parallel worker budget (`clamp_parallel_workers_for_limit`):
/// pure-function unit tests over synthetic limits, so no global process limit is
/// mutated (that would race concurrently-running tests).
#[test]
fn test_clamp_parallel_workers_by_memory_limit() {
    let input =
        "* #variable= 3 #constraint= 1\nmin: +1 x1 +2 x2 +3 x3 ;\n+1 x1 +1 x2 +1 x3 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let per_worker = estimated_parallel_worker_bytes(&instance);
    assert!(
        per_worker > 0,
        "estimate must be positive for a real instance"
    );
    let per_worker_usize = usize::try_from(per_worker).expect("small instance estimate fits");

    // Roomy limit (>= 100% for `requested` workers at the 40% budget): no clamp.
    let roomy = per_worker_usize * 8 * 100 / 40 + 1;
    assert_eq!(clamp_parallel_workers_for_limit(&instance, 8, roomy), 8);

    // Limit sized so the 40% budget fits exactly 3 workers: clamp 8 -> 3.
    let three_workers = per_worker_usize * 3 * 100 / 40;
    assert_eq!(
        clamp_parallel_workers_for_limit(&instance, 8, three_workers),
        3
    );

    // Tiny limit: degrade gracefully to 1 (sequential fallback), never 0.
    assert_eq!(clamp_parallel_workers_for_limit(&instance, 8, 1), 1);

    // No detectable limit (0): unclamped.
    assert_eq!(clamp_parallel_workers_for_limit(&instance, 8, 0), 8);

    // A single-worker request is never touched.
    assert_eq!(clamp_parallel_workers_for_limit(&instance, 1, 1), 1);
}

/// Routing core for the parallel OPTIMIZATION track
/// (`should_parallelize_optimization_with`): budget resolved + eligible
/// (linear, or the NLC-safe non-linear subset) + clamp survives >= 2 workers.
/// Pure inputs, so no env/global mutation.
#[test]
fn test_should_parallelize_optimization_routing_core() {
    let linear =
        "* #variable= 3 #constraint= 1\nmin: +1 x1 +2 x2 +3 x3 ;\n+1 x1 +1 x2 +1 x3 >= 1 ;\n";
    let linear = parse_opb(linear).expect("parse should succeed");
    let roomy = usize::try_from(estimated_parallel_worker_bytes(&linear))
        .expect("small instance estimate fits")
        * 100;

    // Default multi-core case: budget resolved, linear, plenty of memory.
    assert!(should_parallelize_optimization_with(
        &linear,
        Some(8),
        roomy
    ));
    // Parallel disabled (AY_PB_PARALLEL=0 -> no budget): sequential.
    assert!(!should_parallelize_optimization_with(&linear, None, roomy));
    // Single core: sequential.
    assert!(!should_parallelize_optimization_with(
        &linear,
        Some(1),
        roomy
    ));
    // Memory clamp leaves < 2 workers (huge instance / tiny limit): sequential.
    assert!(!should_parallelize_optimization_with(&linear, Some(8), 1));

    // SMALL-EXHAUSTIBLE non-linear instances keep the sequential routing (the
    // exhaustion upgrade proves their OPTIMUM there) regardless of budget.
    let small_nonlinear = "* #variable= 2 #constraint= 1\nmin: +1 x1 ;\n+1 x1 x2 +1 x1 >= 1 ;\n";
    let small_nonlinear = parse_opb(small_nonlinear).expect("parse should succeed");
    assert!(small_nlc_exhaustible(
        &small_nonlinear,
        small_nonlinear.objective.as_ref().expect("has objective")
    ));
    assert!(!should_parallelize_optimization_with(
        &small_nonlinear,
        Some(8),
        roomy
    ));

    // GENERAL constrained non-linear instances (too wide to exhaust) now route
    // to the parallel NLC-safe worker subset by default on multi-core.
    let wide_nonlinear = {
        let mut text = String::from("* #variable= 40 #constraint= 2\nmin: +1 x1 +1 x2 ;\n");
        text.push_str("+1 x1 x2 +1 x3 >= 1 ;\n");
        let terms: Vec<String> = (1..=40).map(|v| format!("+1 x{v}")).collect();
        text.push_str(&format!("{} >= 1 ;\n", terms.join(" ")));
        text
    };
    let wide_nonlinear = parse_opb(&wide_nonlinear).expect("parse should succeed");
    assert!(!small_nlc_exhaustible(
        &wide_nonlinear,
        wide_nonlinear.objective.as_ref().expect("has objective")
    ));
    assert!(should_parallelize_optimization_with(
        &wide_nonlinear,
        Some(8),
        roomy
    ));
    // ... but AY_PB_PARALLEL=0 (no budget) / single core still force
    // sequential everywhere.
    assert!(!should_parallelize_optimization_with(
        &wide_nonlinear,
        None,
        roomy
    ));
    assert!(!should_parallelize_optimization_with(
        &wide_nonlinear,
        Some(1),
        roomy
    ));

    // UNCONSTRAINED non-linear (product objective, no rows): sequential (the
    // dedicated separable/BQO incumbent path owns it).
    let unconstrained = parse_opb("* #variable= 4 #constraint= 0\nmin: +1 x1 x2 -1 x3 x4 ;\n")
        .expect("parse should succeed");
    assert!(!is_linear(&unconstrained) && unconstrained.constraints.is_empty());
    assert!(!should_parallelize_optimization_with(
        &unconstrained,
        Some(8),
        roomy
    ));

    // ALL-FALSE-ZERO theorem shape (all-nonneg objective attaining 0 on
    // all-false, which satisfies every row): sequential — the shortcut proves
    // OPTIMUM instantly, and on a product objective the parallel reconcile
    // could not adopt that claim.
    let all_false_zero = {
        let mut text = String::from("* #variable= 40 #constraint= 2\nmin: +1 x1 x2 ;\n");
        text.push_str("+1 ~x1 ~x2 +1 x3 >= 1 ;\n");
        let terms: Vec<String> = (1..=40).map(|v| format!("+1 ~x{v}")).collect();
        text.push_str(&format!("{} >= 1 ;\n", terms.join(" ")));
        text
    };
    let all_false_zero = parse_opb(&all_false_zero).expect("parse should succeed");
    assert!(all_false_attains_zero_objective_optimum(
        &all_false_zero,
        all_false_zero.objective.as_ref().expect("has objective")
    ));
    assert!(!should_parallelize_optimization_with(
        &all_false_zero,
        Some(8),
        roomy
    ));
}

#[test]
fn test_parallel_setting_from_env_enabled_variants() {
    assert_eq!(
        parallel_setting_from_env(Some(OsStr::new("1"))),
        Some(ParallelSetting::Auto)
    );
    assert_eq!(
        parallel_setting_from_env(Some(OsStr::new("on"))),
        Some(ParallelSetting::Auto)
    );
    assert_eq!(
        parallel_setting_from_env(Some(OsStr::new("auto"))),
        Some(ParallelSetting::Auto)
    );
    assert_eq!(
        parallel_setting_from_env(Some(OsStr::new("8"))),
        Some(ParallelSetting::Fixed(8))
    );
    // Garbage values are treated as disabled (fail-closed to sequential).
    assert_eq!(parallel_setting_from_env(Some(OsStr::new("banana"))), None);
}

#[test]
fn test_worker_specs_skip_native_for_nonlinear_decision() {
    let input = "* #variable= 3 #constraint= 2\n+1 x1 x2 +1 x3 >= 1 ;\n+1 x1 +1 x2 +1 x3 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let profile = InstanceProfile::from_instance(&instance);
    let specs = decision_worker_specs(&profile);
    // No native-cdcl worker for a non-linear instance (it is unsound there).
    assert!(specs.iter().all(|s| s.label != "native-cdcl-decision"));
    // SAT-encoded worker is always present.
    assert!(specs.iter().any(|s| s.label == "sat-encoded-decision"));
    // No one-shot preprocessing worker either (linear-gated).
    assert!(specs.iter().all(|s| s.label != "oneshot-preprocess-dec"));
}

#[test]
fn test_worker_specs_oneshot_arm_is_last_for_linear_decision() {
    let input = "* #variable= 3 #constraint= 2\n+1 x1 +1 x3 >= 1 ;\n+1 x1 +1 x2 +1 x3 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let profile = InstanceProfile::from_instance(&instance);
    let specs = decision_worker_specs(&profile);
    // The one-shot arm is present for linear instances but strictly LAST, so
    // the core-budgeted prefix selection (`take(spawn)`) drops it FIRST when
    // the budget is tight and it can never crowd out a complete strategy.
    assert_eq!(
        specs.last().map(|s| s.label),
        Some("oneshot-preprocess-dec")
    );
    assert!(specs
        .iter()
        .take(specs.len() - 1)
        .all(|s| s.label != "oneshot-preprocess-dec"));
    // With a 3-core budget the arm is exactly the spec that gets dropped.
    assert!(specs
        .iter()
        .take(3)
        .all(|s| s.label != "oneshot-preprocess-dec"));
}

/// Planted SAT instance the one-shot arm cracks via pure-literal elimination:
/// x1/x2 occur only positively (pure), x5/x6 in both polarities (a small SAT
/// core no entailed pass can reduce).
fn planted_pure_literal_sat_instance() -> PbInstance {
    parse_opb(
        "* #variable= 6 #constraint= 4\n\
         +1 x1 +1 x5 >= 1 ;\n\
         +1 x2 +1 x5 >= 1 ;\n\
         +1 x5 +1 x6 >= 1 ;\n\
         +1 ~x5 +1 ~x6 >= 1 ;\n",
    )
    .expect("planted pure-literal fixture should parse")
}

#[test]
fn test_oneshot_arm_cracks_planted_pure_literal_instance() {
    let instance = planted_pure_literal_sat_instance();

    // The plant really exercises the CHOICE path: the one-shot pipeline fixes
    // the pure variables, the default (entailed-only) pipeline does not.
    let (_, stats) = crate::preprocess::preprocess_one_shot(&instance);
    assert!(
        stats.pure_fixed >= 2,
        "plant must trigger pure-literal fixings, got {stats:?}"
    );
    assert!(has_pure_literal_candidates(&instance));

    let term_flag = AtomicBool::new(false);
    let solution = solve_decision_oneshot_preprocess_arm(
        &instance,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &term_flag,
    );
    assert_eq!(solution.status, PbStatus::Satisfiable);
    // The witness must satisfy the ORIGINAL instance (re-verified by the arm;
    // asserted independently here) and round-trip the choice fixings.
    assert!(verify_all_constraints(
        &instance.constraints,
        &solution.assignment
    ));
    assert_eq!(solution.assignment.len(), 6);
    assert!(solution.assignment[0], "pure literal x1 must be fixed true");
    assert!(solution.assignment[1], "pure literal x2 must be fixed true");
}

#[test]
fn test_oneshot_arm_relays_reduced_unsat() {
    // Pure-literal rows (y = x13, x14) planted on top of a pigeonhole core
    // PHP(4,3) over x1..x12 (pigeon i holds x_{3(i-1)+j} for hole j): the pure
    // pass fixes the y's, entailed passes cannot crack PHP(4,3) (single-literal
    // probing finds no conflict), so the arm reaches the reduced solve and must
    // relay its UNSAT — which IS UNSAT of the original per the one-shot
    // contract (choice fixings never empty the solution set).
    let mut input = String::from("* #variable= 14 #constraint= 9\n");
    input.push_str("+1 x13 +1 x1 >= 1 ;\n");
    input.push_str("+1 x14 +1 x2 >= 1 ;\n");
    for pigeon in 0..4 {
        let base = 3 * pigeon;
        input.push_str(&format!(
            "+1 x{} +1 x{} +1 x{} >= 1 ;\n",
            base + 1,
            base + 2,
            base + 3
        ));
    }
    for hole in 1..=3 {
        input.push_str(&format!(
            "+1 ~x{} +1 ~x{} +1 ~x{} +1 ~x{} >= 3 ;\n",
            hole,
            hole + 3,
            hole + 6,
            hole + 9
        ));
    }
    let instance = parse_opb(&input).expect("planted UNSAT fixture should parse");

    // Pin the INTENDED path: preprocessing must NOT already refute the
    // instance (that would exercise only the preprocess-UNSAT relay, not the
    // reduced-SOLVE relay) and must apply the planted choice fixings.
    let (pre, stats) = crate::preprocess::preprocess_one_shot(&instance);
    assert!(
        matches!(pre, PreprocessResult::Simplified { .. }),
        "fixture must survive preprocessing so the reduced solve carries the verdict"
    );
    assert!(
        stats.pure_fixed >= 2,
        "plant must trigger pure-literal fixings, got {stats:?}"
    );

    // Confirm the instance is genuinely UNSAT via the independent sequential
    // portfolio, so the arm's relayed verdict is cross-checked in this test.
    let seq = solve_decision_seq(&instance);
    assert_eq!(seq.status, PbStatus::Unsatisfiable);

    let term_flag = AtomicBool::new(false);
    let solution = solve_decision_oneshot_preprocess_arm(
        &instance,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &term_flag,
    );
    assert_eq!(solution.status, PbStatus::Unsatisfiable);
}

#[test]
fn test_oneshot_arm_declines_without_pure_candidates() {
    // Every variable occurs in both polarities: no candidates, so the arm
    // declines immediately with UNKNOWN (the default workers own the solve).
    let input = "* #variable= 2 #constraint= 2\n+1 x1 +1 x2 >= 1 ;\n+1 ~x1 +1 ~x2 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    assert!(!has_pure_literal_candidates(&instance));

    let term_flag = AtomicBool::new(false);
    let solution = solve_decision_oneshot_preprocess_arm(
        &instance,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &term_flag,
    );
    assert_eq!(solution.status, PbStatus::Unknown);
}

#[test]
fn test_has_pure_literal_candidates_polarity_accounting() {
    // An `=` row contributes BOTH normalized polarities: x1/x2 are not pure.
    let eq = parse_opb("* #variable= 2 #constraint= 1\n+1 x1 +1 x2 = 1 ;\n")
        .expect("parse should succeed");
    assert!(!has_pure_literal_candidates(&eq));

    // A negative coefficient flips the normalized polarity: x1 occurs
    // positively in row 1 and (via the flip) negatively in row 2, so it is not
    // pure — but x2 and x3 are.
    let flip = parse_opb("* #variable= 3 #constraint= 2\n+1 x1 +1 x2 >= 1 ;\n-1 x1 +1 x3 >= 0 ;\n")
        .expect("parse should succeed");
    assert!(has_pure_literal_candidates(&flip));

    // Same shape but x2/x3 also both-polarity: no candidate anywhere.
    let none =
        parse_opb("* #variable= 2 #constraint= 2\n+1 x1 +1 ~x2 >= 1 ;\n-1 x1 +1 x2 >= 0 ;\n")
            .expect("parse should succeed");
    assert!(!has_pure_literal_candidates(&none));

    // Non-linear row: the pure pass fails closed, so the gate declines.
    let nonlinear = parse_opb("* #variable= 3 #constraint= 1\n+1 x1 x2 +1 x3 >= 1 ;\n")
        .expect("parse should succeed");
    assert!(!has_pure_literal_candidates(&nonlinear));
}

#[test]
fn test_oneshot_arm_solves_fully_pure_instance_to_verified_witness() {
    // Every row is satisfied by pure fixings alone: the reduced instance is
    // EMPTY and the arm's witness is the fixings plus defaults — it must still
    // verify against the ORIGINAL rows.
    let input = "* #variable= 4 #constraint= 2\n+1 x1 +1 x2 >= 1 ;\n+1 ~x3 +1 ~x4 >= 2 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    // ~x3/~x4 >= 2 forces both by entailed unit fixing; x1/x2 stay pure-only.
    let term_flag = AtomicBool::new(false);
    let solution = solve_decision_oneshot_preprocess_arm(
        &instance,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &term_flag,
    );
    assert_eq!(solution.status, PbStatus::Satisfiable);
    assert!(verify_all_constraints(
        &instance.constraints,
        &solution.assignment
    ));
}

#[test]
fn test_parallel_decision_matches_sequential_sat() {
    let input = "* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let seq = solve_decision_seq(&instance);
    let par = solve_decision_par(&instance, 8);
    assert_eq!(seq.status, PbStatus::Satisfiable);
    assert_eq!(par.status, seq.status);
    // The parallel witness must itself satisfy the constraints.
    assert!(verify_all_constraints(
        &instance.constraints,
        &par.assignment
    ));
}

#[test]
fn test_parallel_decision_matches_sequential_unsat() {
    let input = "* #variable= 1 #constraint= 2\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let seq = solve_decision_seq(&instance);
    let par = solve_decision_par(&instance, 8);
    assert_eq!(seq.status, PbStatus::Unsatisfiable);
    assert_eq!(par.status, seq.status);
}

#[test]
fn test_parallel_decision_matches_sequential_on_fixtures() {
    for (path, expected) in [
        ("tests/instances/sat_simple.opb", PbStatus::Satisfiable),
        ("tests/instances/unsat_simple.opb", PbStatus::Unsatisfiable),
        (
            "tests/instances/cardinality_3of5.opb",
            PbStatus::Satisfiable,
        ),
        ("tests/instances/nlc_product.opb", PbStatus::Satisfiable),
    ] {
        let instance = parse_repo_instance_opb(path);
        let seq = solve_decision_seq(&instance);
        let par = solve_decision_par(&instance, 8);
        assert_eq!(seq.status, expected, "sequential mismatch for {path}");
        assert_eq!(
            par.status, seq.status,
            "parallel/sequential mismatch for {path}"
        );
        if par.status == PbStatus::Satisfiable {
            assert!(
                verify_all_constraints(&instance.constraints, &par.assignment),
                "parallel witness invalid for {path}"
            );
        }
    }
}

#[test]
fn test_parallel_optimization_matches_sequential_on_fixtures() {
    for path in [
        "tests/instances/weighted_opt.opb",
        "tests/instances/opt_pigeonhole.opb",
    ] {
        let instance = parse_repo_instance_opb(path);
        let objective = instance
            .objective
            .clone()
            .unwrap_or_else(|| panic!("{path} should have an objective"));
        let seq = solve_opt_seq(&instance, &objective);
        let par = solve_opt_par(&instance, &objective, 8);
        assert_eq!(
            seq.status,
            PbStatus::OptimumFound,
            "seq not optimal for {path}"
        );
        assert_eq!(
            par.status, seq.status,
            "parallel/sequential status mismatch for {path}"
        );
        assert_eq!(
            par.objective, seq.objective,
            "parallel/sequential objective mismatch for {path}"
        );
        assert!(
            verify_all_constraints(&instance.constraints, &par.assignment),
            "parallel optimum witness invalid for {path}"
        );
        assert_eq!(
            eval_objective(&objective, &par.assignment),
            par.objective.expect("optimum has objective"),
            "parallel witness objective does not match reported value for {path}"
        );
    }
}

#[test]
fn test_parallel_optimization_matches_sequential_inline() {
    let input =
        "* #variable= 3 #constraint= 1\nmin: +1 x1 +2 x2 +3 x3 ;\n+1 x1 +1 x2 +1 x3 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance.objective.clone().expect("has objective");
    let seq = solve_opt_seq(&instance, &objective);
    let par = solve_opt_par(&instance, &objective, 8);
    assert_eq!(seq.status, PbStatus::OptimumFound);
    assert_eq!(par.status, seq.status);
    assert_eq!(par.objective, seq.objective);
    assert_eq!(par.objective, Some(1));
}

#[test]
fn test_parallel_optimization_unsat_matches_sequential() {
    // Hard constraint forces infeasibility (x1 both true and false).
    let input = "* #variable= 1 #constraint= 2\nmin: +1 x1 ;\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance.objective.clone().expect("has objective");
    let seq = solve_opt_seq(&instance, &objective);
    let par = solve_opt_par(&instance, &objective, 8);
    assert_eq!(seq.status, PbStatus::Unsatisfiable);
    assert_eq!(par.status, seq.status);
}

#[test]
fn test_parallel_optimization_reports_incumbents() {
    let input =
        "* #variable= 4 #constraint= 2\nmin: +2 x1 +3 x2 +5 x3 +7 x4 ;\n+1 x1 +1 x2 +1 x3 +1 x4 >= 2 ;\n+1 ~x1 +1 ~x2 +1 ~x3 +1 ~x4 >= 2 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance.objective.clone().expect("has objective");
    let term_flag = AtomicBool::new(false);
    let mut improvements: Vec<(i128, Vec<bool>)> = Vec::new();
    let result = run_parallel_optimization(
        &Arc::new(instance.clone()),
        &objective,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &term_flag,
        &mut |obj, model| improvements.push((obj, model.to_vec())),
        8,
        OptimizationPortfolioRoute::Standard,
    );
    assert_eq!(result.status, PbStatus::OptimumFound);
    assert_eq!(result.objective, Some(5));
    // Every reported incumbent must be a real, verified witness, and the
    // stream must be STRICTLY improving (the monotone `o`-line contract the
    // binaries rely on).
    for (obj, model) in &improvements {
        assert!(verify_all_constraints(&instance.constraints, model));
        assert_eq!(eval_objective(&objective, model), *obj);
    }
    assert!(
        improvements.windows(2).all(|w| w[1].0 < w[0].0),
        "parallel incumbent stream must be strictly improving: {:?}",
        improvements.iter().map(|(obj, _)| *obj).collect::<Vec<_>>()
    );
}

/// Diversified primal workers (P8-P11, design §2.3): with a core budget large
/// enough to spawn EVERY spec — the 5 complete baselines, P6/P7, and the four
/// new diversified arms — the portfolio still returns a sound, verified
/// optimum, and every streamed incumbent is a real witness. With the tight
/// budget of 7 the diversified arms are exactly the specs dropped first
/// (take-first-7 excludes all of them), so core budgets <= 7 keep the
/// pre-existing worker set byte-identical.
#[test]
fn test_parallel_optimization_all_diversified_primal_workers_sound() {
    let input =
        "* #variable= 4 #constraint= 2\nmin: +2 x1 +3 x2 +5 x3 +7 x4 ;\n+1 x1 +1 x2 +1 x3 +1 x4 >= 2 ;\n+1 ~x1 +1 ~x2 +1 ~x3 +1 ~x4 >= 2 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance.objective.clone().expect("has objective");

    // Budget 16 >= 12 specs: all diversified arms (incl. P12 DDFW) are spawned.
    let term_flag = AtomicBool::new(false);
    let mut improvements: Vec<(i128, Vec<bool>)> = Vec::new();
    let result = run_parallel_optimization(
        &Arc::new(instance.clone()),
        &objective,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &term_flag,
        &mut |obj, model| improvements.push((obj, model.to_vec())),
        16,
        OptimizationPortfolioRoute::Standard,
    );
    assert_eq!(result.status, PbStatus::OptimumFound);
    assert_eq!(result.objective, Some(5));
    assert!(verify_all_constraints(
        &instance.constraints,
        &result.assignment
    ));
    for (obj, model) in &improvements {
        assert!(verify_all_constraints(&instance.constraints, model));
        assert_eq!(eval_objective(&objective, model), *obj);
    }
    assert!(
        improvements.windows(2).all(|w| w[1].0 < w[0].0),
        "parallel incumbent stream must be strictly improving"
    );

    // core_budget = 7: `run_parallel_optimization` spawns the first 7 specs
    // UP FRONT, and the priority order puts the diversified arms at positions
    // 8..=12, so none of them is in the up-front spawn set (they can only
    // enter later via freed-slot backfill, one core at a time, never above
    // the budget).
    let profile = InstanceProfile::from_instance(&instance);
    let specs = optimization_worker_specs(&profile, OptimizationPortfolioRoute::Standard);
    let diversified = [
        "sls-restarts-opt",
        "sls-alt-opt",
        "sls-unified-opt",
        "lp-round-sls-opt",
        "sls-ddfw-opt",
    ];
    assert!(
        specs
            .iter()
            .take(7)
            .all(|spec| !diversified.contains(&spec.label)),
        "core budget 7 must not spawn any diversified arm"
    );
    assert!(
        specs
            .iter()
            .skip(7)
            .all(|spec| diversified.contains(&spec.label)),
        "the diversified arms must be exactly the specs dropped first"
    );
    // And the budget-7 run itself stays sound (the pre-existing worker set).
    let par7 = solve_opt_par(&instance, &objective, 7);
    assert_eq!(par7.status, PbStatus::OptimumFound);
    assert_eq!(par7.objective, Some(5));
    assert!(verify_all_constraints(
        &instance.constraints,
        &par7.assignment
    ));
}

/// NLC parallel route end-to-end: a product-constraint / linear-objective
/// instance through `run_parallel_optimization` (the NLC-safe subset incl.
/// the `nlc-sls-opt` primal arm) returns a sound verdict that matches the
/// sequential baseline, and every streamed incumbent is a real witness
/// (products evaluated exactly).
#[test]
fn test_parallel_optimization_nonlinear_route_sound() {
    let input = "* #variable= 4 #constraint= 2\nmin: +1 x1 +1 x2 +1 x3 +1 x4 ;\n+1 x1 x2 >= 1 ;\n+1 x3 +1 x4 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance.objective.clone().expect("has objective");
    assert!(!is_linear(&instance), "fixture must be non-linear");

    let seq = solve_opt_seq(&instance, &objective);
    let term_flag = AtomicBool::new(false);
    let mut improvements: Vec<(i128, Vec<bool>)> = Vec::new();
    let par = run_parallel_optimization(
        &Arc::new(instance.clone()),
        &objective,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &term_flag,
        &mut |obj, model| improvements.push((obj, model.to_vec())),
        8,
        OptimizationPortfolioRoute::Standard,
    );
    assert_eq!(seq.status, PbStatus::OptimumFound);
    assert_eq!(par.status, seq.status);
    assert_eq!(par.objective, seq.objective);
    assert_eq!(par.objective, Some(3));
    assert!(verify_all_constraints(
        &instance.constraints,
        &par.assignment
    ));
    for (obj, model) in &improvements {
        assert!(verify_all_constraints(&instance.constraints, model));
        assert_eq!(eval_objective(&objective, model), *obj);
    }
}

/// The `nonlinear-native-oll-opt` worker body: PROVES the optimum of a small
/// product instance via native OLL on the sound linearization, projecting the
/// witness back to the ORIGINAL variable space (original width, satisfies every
/// original product row); and DECLINES fail-closed on linear input (the dedicated
/// `native-oll-opt` worker owns that) so its core is freed for backfill.
#[test]
fn test_nonlinear_native_oll_worker_proves_optimum_in_original_space() {
    let input = "* #variable= 4 #constraint= 2\nmin: +1 x1 +1 x2 +1 x3 +1 x4 ;\n+1 x1 x2 >= 1 ;\n+1 x3 +1 x4 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance.objective.clone().expect("has objective");
    assert!(!is_linear(&instance), "fixture must be non-linear");

    let seq = solve_opt_seq(&instance, &objective);
    let term_flag = AtomicBool::new(false);
    let mut improvements: Vec<(i128, Vec<bool>)> = Vec::new();
    let result = solve_nonlinear_native_oll_worker(
        &instance,
        &objective,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &term_flag,
        &mut |obj, model| improvements.push((obj, model.to_vec())),
        None,
    );
    // Sound proven optimum matching the sequential baseline, with a witness in the
    // ORIGINAL variable space (NOT the wider linearized space) that satisfies every
    // ORIGINAL (product) constraint.
    assert_eq!(seq.status, PbStatus::OptimumFound);
    assert_eq!(result.status, PbStatus::OptimumFound);
    assert_eq!(result.objective, seq.objective);
    assert_eq!(result.objective, Some(3));
    assert_eq!(
        result.assignment.len(),
        instance.num_vars as usize,
        "witness must be projected to the ORIGINAL variable space"
    );
    assert!(verify_all_constraints(
        &instance.constraints,
        &result.assignment
    ));
    for (obj, model) in &improvements {
        assert_eq!(
            model.len(),
            instance.num_vars as usize,
            "streamed incumbents must be in the original variable space"
        );
        assert!(verify_all_constraints(&instance.constraints, model));
        assert_eq!(eval_objective(&objective, model), *obj);
    }

    // DECLINES fail-closed on linear input (returns Unknown; P5 owns linear).
    let linear =
        parse_opb("* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n")
            .expect("parse linear");
    let lobj = linear.objective.clone().expect("has objective");
    let declined = solve_nonlinear_native_oll_worker(
        &linear,
        &lobj,
        Some(Duration::from_secs(1)),
        Instant::now(),
        &term_flag,
        &mut |_, _| {},
        None,
    );
    assert_eq!(
        declined.status,
        PbStatus::Unknown,
        "linear input must decline (Unknown), freeing the core for backfill"
    );
}

/// The `nlc-sls-opt` worker body: finds and streams doubly-verified feasible
/// incumbents on a product instance (never a verdict stronger than
/// SATISFIABLE), and DECLINES on linear input (no verdict, no incumbent —
/// the linear arms own that space).
#[test]
fn test_nlc_sls_worker_streams_verified_incumbents_and_declines_on_linear() {
    let input = "* #variable= 4 #constraint= 2\nmin: +1 x1 +1 x2 +1 x3 +1 x4 ;\n+1 x1 x2 >= 1 ;\n+1 x3 +1 x4 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance.objective.clone().expect("has objective");
    let term_flag = AtomicBool::new(false);
    let mut improvements: Vec<(i128, Vec<bool>)> = Vec::new();
    let result = solve_optimization_nlc_sls(
        &instance,
        &objective,
        Some(Duration::from_secs(5)),
        Instant::now(),
        &term_flag,
        &mut |obj, model| improvements.push((obj, model.to_vec())),
    );
    assert_eq!(
        result.status,
        PbStatus::Satisfiable,
        "product SLS should land a feasible incumbent on this tiny instance"
    );
    assert!(verify_all_constraints(
        &instance.constraints,
        &result.assignment
    ));
    assert_eq!(
        result.objective,
        Some(eval_objective(&objective, &result.assignment))
    );
    assert!(!improvements.is_empty(), "incumbents must stream");
    for (obj, model) in &improvements {
        assert!(verify_all_constraints(&instance.constraints, model));
        assert_eq!(eval_objective(&objective, model), *obj);
    }

    // Linear input: decline (Unknown, nothing streamed).
    let linear = worker_split_instance();
    let linear_objective = linear.objective.clone().expect("has objective");
    let mut linear_improvements = 0usize;
    let declined = solve_optimization_nlc_sls(
        &linear,
        &linear_objective,
        Some(Duration::from_secs(1)),
        Instant::now(),
        &term_flag,
        &mut |_, _| linear_improvements += 1,
    );
    assert_eq!(declined.status, PbStatus::Unknown);
    assert_eq!(linear_improvements, 0);
}

/// WBO parallel route end-to-end: the reduced-PBO worker set (standard linear
/// specs + `wbo-sls-opt`) returns the same sound verdict as the sequential
/// baseline on the reduced instance. (Projection back to the original WBO is
/// the binaries' job and is unchanged by the route — see the byte-identical
/// o-line tests there.)
#[test]
fn test_parallel_optimization_wbo_route_matches_sequential() {
    let instance = worker_split_instance();
    let objective = instance.objective.clone().expect("has objective");
    let seq = solve_opt_seq(&instance, &objective);
    let term_flag = AtomicBool::new(false);
    let par = run_parallel_optimization(
        &Arc::new(instance.clone()),
        &objective,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &term_flag,
        &mut |_, _| {},
        16,
        OptimizationPortfolioRoute::WboReduced,
    );
    assert_eq!(seq.status, PbStatus::OptimumFound);
    assert_eq!(par.status, seq.status);
    assert_eq!(par.objective, seq.objective);
    assert!(verify_all_constraints(
        &instance.constraints,
        &par.assignment
    ));
}

/// P11 `lp-round-sls-opt` LP-round seed: on a small linear OPT instance the
/// rounded point has exactly one entry per variable; on oversized instances
/// (variable cap, then row cap) it declines up front — returns `None` without
/// any LP work.
#[test]
fn test_lp_round_seed_point_length_and_oversized_decline() {
    let input =
        "* #variable= 3 #constraint= 2\nmin: +1 x1 +2 x2 +3 x3 ;\n+1 x1 +1 x2 +1 x3 >= 2 ;\n+1 ~x1 +1 ~x2 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance.objective.clone().expect("has objective");
    let never_stop = || false;

    let rounded = lp_round_seed_point(&instance, &objective, &never_stop)
        .expect("small linear instance should yield an LP-rounded point");
    assert_eq!(
        rounded.len(),
        instance.num_vars as usize,
        "rounded point must have one entry per variable"
    );

    // Oversized variable count: decline immediately (num_vars gate fires
    // before any constraint/LP processing).
    let mut oversized_vars = instance.clone();
    oversized_vars.num_vars =
        u32::try_from(crate::optimize::lns2::MAX_LNS2_VARS + 1).expect("cap fits u32");
    assert_eq!(
        lp_round_seed_point(&oversized_vars, &objective, &never_stop),
        None,
        "above the variable cap the LP-round seeder must decline"
    );

    // Oversized row count: decline immediately (row gate fires before the LP).
    let mut oversized_rows = instance.clone();
    let filler = oversized_rows.constraints[0].clone();
    oversized_rows
        .constraints
        .resize(crate::optimize::lns2::FP_MAX_CONSTRAINTS + 1, filler);
    assert_eq!(
        lp_round_seed_point(&oversized_rows, &objective, &never_stop),
        None,
        "above the row cap the LP-round seeder must decline"
    );
}

#[test]
fn test_parallel_decision_single_worker_falls_back_to_sequential() {
    let input = "* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let seq = solve_decision_seq(&instance);
    let par = solve_decision_par(&instance, 1);
    assert_eq!(par.status, seq.status);
    assert_eq!(par.assignment, seq.assignment);
}

/// Budget-routing contract for the native-OLL pre-pass.
///
/// Regression guard for the OPT-LIN routing fix: on the OLL-dominant class
/// (pure single-literal linear objective — cardinality / MIP-style OPT-LIN,
/// where native-OLL is the *complete* proving search) the pre-pass must get
/// the large majority of the budget so the proof actually finishes, instead of
/// being cut off at the old flat 40% and handing the rest to the weaker native
/// branch-and-bound / SAT fallbacks. Any other shape keeps the 40% split.
#[test]
fn test_pre_native_oll_budget_split_by_class() {
    let start = Instant::now();
    // 50_001ms budget. The odd-millisecond literal keeps the assertions below
    // off clippy's `duration_suboptimal_units` lint (no round-unit suggestion)
    // while staying effectively the full budget since `start` is ~"now". The
    // OLL-dominant split is 85% (~42_500ms); the default split is 40% (~20_000ms).
    let budget_ms = 50_001u64;
    let budget = Some(Duration::from_millis(budget_ms));

    // OLL-dominant class -> 60% slice (a moderate bump over the 40% default:
    // enough for OLL to finish proving, while leaving a real downstream tail).
    let lever = pre_native_oll_timeout(budget, start, true).expect("finite slice");
    assert!(
        lever.as_millis() >= u128::from(budget_ms) * 11 / 20
            && lever.as_millis() <= u128::from(budget_ms) * 13 / 20,
        "OLL-dominant slice should be ~60% of the budget, got {lever:?}"
    );

    // Non-OLL-dominant shape -> original 40% split, strictly smaller.
    let other = pre_native_oll_timeout(budget, start, false).expect("finite slice");
    assert!(
        other.as_millis() <= u128::from(budget_ms) * 21 / 50,
        "non-dominant slice should stay near 40% of the budget, got {other:?}"
    );
    assert!(
        lever > other,
        "OLL-dominant class must get strictly more budget than the default split"
    );
    // The downstream phases must keep a real (~40%) tail — never starved below
    // a third of the budget — so multi-phase instances (OLL + B&B + SAT) that
    // need the fallbacks to prove optimality are not regressed.
    assert!(
        (u128::from(budget_ms) - lever.as_millis()) >= u128::from(budget_ms) / 3,
        "downstream tail must stay >= 1/3 of the budget, got {lever:?} of {budget_ms}ms"
    );

    // Exhausted budget -> zero slice in both modes (no underflow, no negative).
    let expired = pre_native_oll_timeout(Some(Duration::ZERO), start, true);
    assert_eq!(expired, Some(Duration::ZERO));
}

/// The pre-pass budget split keys off exactly the `should_try_native_oll`
/// predicate: a pure single-literal linear objective is the OLL-dominant class;
/// a non-linear objective is not. This pins the routing wiring so the budget
/// reallocation cannot silently detach from the class predicate.
#[test]
fn test_should_try_native_oll_matches_oll_dominant_class() {
    // Pure single-literal linear objective, non-tiny, non-huge -> OLL-dominant.
    let mut obj = String::from("min:");
    let mut cons = String::new();
    for v in 1..=80 {
        obj.push_str(&format!(" +1 x{v}"));
        cons.push_str(&format!("+1 x{v} +1 x{} >= 1 ;\n", (v % 80) + 1));
    }
    let input = format!("* #variable= 80 #constraint= 80\n{obj} ;\n{cons}");
    let instance = parse_opb(&input).expect("parse cardinality opt");
    let objective = instance.objective.clone().expect("objective");
    let profile = InstanceProfile::from_instance(&instance);
    assert!(
        should_try_native_oll(&profile, &objective),
        "pure single-literal cardinality objective must be OLL-dominant"
    );

    // Non-linear objective term -> NOT the OLL-dominant class.
    let nl = "* #variable= 80 #constraint= 1\nmin: +1 x1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n";
    let nl_instance = parse_opb(nl).expect("parse nonlinear");
    let nl_objective = nl_instance.objective.clone().expect("objective");
    let nl_profile = InstanceProfile::from_instance(&nl_instance);
    assert!(
        !should_try_native_oll(&nl_profile, &nl_objective),
        "non-linear objective must not be routed as OLL-dominant"
    );
}

#[test]
fn test_parallel_decision_stops_promptly_on_term_flag() {
    // A larger satisfiable instance; raising the term flag must return
    // promptly (no deadlock / hang). We do not assert a verdict, only that
    // the call returns quickly after the flag is raised.
    let input = "* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let term_flag = AtomicBool::new(true); // already requested to stop
    let begin = Instant::now();
    let _ = run_parallel_decision(
        &Arc::new(instance.clone()),
        Some(Duration::from_secs(30)),
        Instant::now(),
        &term_flag,
        8,
    );
    assert!(
        begin.elapsed() < Duration::from_secs(5),
        "parallel decision did not stop promptly on term flag"
    );
}

#[test]
fn test_parallel_optimization_stops_promptly_on_term_flag() {
    let input =
        "* #variable= 3 #constraint= 1\nmin: +1 x1 +2 x2 +3 x3 ;\n+1 x1 +1 x2 +1 x3 >= 1 ;\n";
    let instance = parse_opb(input).expect("parse should succeed");
    let objective = instance.objective.clone().expect("has objective");
    let term_flag = AtomicBool::new(true);
    let begin = Instant::now();
    let _ = run_parallel_optimization(
        &Arc::new(instance.clone()),
        &objective,
        Some(Duration::from_secs(30)),
        Instant::now(),
        &term_flag,
        &mut |_, _| {},
        8,
        OptimizationPortfolioRoute::Standard,
    );
    assert!(
        begin.elapsed() < Duration::from_secs(5),
        "parallel optimization did not stop promptly on term flag"
    );
}

#[test]
fn test_parallel_verdict_consistency_helpers() {
    let unsat = PbSolution {
        status: PbStatus::Unsatisfiable,
        assignment: Vec::new(),
        objective: None,
    };
    let opt_a = PbSolution {
        status: PbStatus::OptimumFound,
        assignment: vec![true],
        objective: Some(3),
    };
    let opt_b = PbSolution {
        status: PbStatus::OptimumFound,
        assignment: vec![false],
        objective: Some(3),
    };
    let opt_c = PbSolution {
        status: PbStatus::OptimumFound,
        assignment: vec![false],
        objective: Some(4),
    };
    // No prior verdict is always consistent.
    assert!(parallel_optimization_verdict_consistent(None, &unsat));
    // Same objective optima are consistent; differing values are not.
    assert!(parallel_optimization_verdict_consistent(
        Some(&opt_a),
        &opt_b
    ));
    assert!(!parallel_optimization_verdict_consistent(
        Some(&opt_a),
        &opt_c
    ));
    // UNSAT vs OPTIMUM is an inconsistency (soundness bug if it ever happens).
    assert!(!parallel_optimization_verdict_consistent(
        Some(&unsat),
        &opt_a
    ));
}

// ---- Graph-family seed merge soundness contract ---- //

fn sat_sol(obj: i128, nvars: u32) -> PbSolution {
    incumbent_solution(vec![false; nvars as usize], obj, nvars)
}

#[test]
fn graph_seed_merge_never_downgrades_a_proof() {
    // A proven OptimumFound must survive untouched even if the seed carries the
    // SAME objective (the proof always wins; we must report OPTIMUM, not SAT).
    let proven = PbSolution {
        status: PbStatus::OptimumFound,
        assignment: vec![true, false, false],
        objective: Some(264),
    };
    let seed = sat_sol(264, 3);
    let merged = merge_strategy_with_graph_seed(proven.clone(), Some(seed), 3);
    assert_eq!(merged.status, PbStatus::OptimumFound);
    assert_eq!(merged.objective, Some(264));

    // Unsatisfiable likewise wins.
    let unsat = PbSolution {
        status: PbStatus::Unsatisfiable,
        assignment: Vec::new(),
        objective: None,
    };
    let merged = merge_strategy_with_graph_seed(unsat, Some(sat_sol(10, 3)), 3);
    assert_eq!(merged.status, PbStatus::Unsatisfiable);
}

#[test]
fn graph_seed_merge_keeps_better_incumbent() {
    // Strategy produced a worse SAT incumbent than the greedy seed: keep the
    // seed (smaller objective), reported as Satisfiable (no false OPTIMUM).
    let strat_worse = sat_sol(1235, 4);
    let seed_better = sat_sol(1022, 4);
    let merged = merge_strategy_with_graph_seed(strat_worse, Some(seed_better), 4);
    assert_eq!(merged.status, PbStatus::Satisfiable);
    assert_eq!(merged.objective, Some(1022));

    // Strategy strictly better than the seed: keep the strategy incumbent.
    let strat_better = sat_sol(900, 4);
    let seed_worse = sat_sol(1022, 4);
    let merged = merge_strategy_with_graph_seed(strat_better, Some(seed_worse), 4);
    assert_eq!(merged.objective, Some(900));

    // Equal objective: either is fine; we keep the strategy result.
    let merged = merge_strategy_with_graph_seed(sat_sol(500, 4), Some(sat_sol(500, 4)), 4);
    assert_eq!(merged.objective, Some(500));
}

#[test]
fn graph_seed_merge_recovers_seed_when_strategy_unknown() {
    // Strategy could not produce anything usable: fall back to the feasible seed
    // so the incumbent is never lost.
    let unknown = unknown_solution();
    let seed = sat_sol(42, 5);
    let merged = merge_strategy_with_graph_seed(unknown, Some(seed), 5);
    assert_eq!(merged.status, PbStatus::Satisfiable);
    assert_eq!(merged.objective, Some(42));

    // No seed: strategy result passes through unchanged.
    let merged = merge_strategy_with_graph_seed(sat_sol(7, 2), None, 2);
    assert_eq!(merged.objective, Some(7));
    let merged = merge_strategy_with_graph_seed(unknown_solution(), None, 2);
    assert_eq!(merged.status, PbStatus::Unknown);
}

// ── Optimality-upgrade gate soundness (Trust/Kani-mirrored) ──────────────
// The post-solve gate upgrades SATISFIABLE -> OPTIMUM only when a feasible
// incumbent's value V <= a sound lower bound F. These tests + the Kani
// harness `kani_optimality_upgrade::*` prove the gate never declares a
// suboptimal incumbent optimal (a false OPTIMUM => category DQ). See
// proofs/2026-06-16-pb-trust-soundness-harnesses.md.

fn gate_pos(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}
fn gate_obj2(c1: i128, c2: i128) -> PbObjective {
    PbObjective {
        terms: vec![
            PbTerm {
                coeff: c1,
                lits: vec![gate_pos(1)],
            },
            PbTerm {
                coeff: c2,
                lits: vec![gate_pos(2)],
            },
        ],
    }
}
fn gate_ge_row(a1: i128, a2: i128, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms: vec![
            PbTerm {
                coeff: a1,
                lits: vec![gate_pos(1)],
            },
            PbTerm {
                coeff: a2,
                lits: vec![gate_pos(2)],
            },
        ],
        rel: PbRel::Ge,
        rhs,
    }
}
fn gate_ge_row1(var: u32, a: i128, rhs: i128) -> PbConstraint {
    PbConstraint {
        terms: vec![PbTerm {
            coeff: a,
            lits: vec![gate_pos(var)],
        }],
        rel: PbRel::Ge,
        rhs,
    }
}

/// Gate-soundness check on a concrete 2-var instance via the REAL functions
/// the gate uses: compute the structural floor, brute-force the true optimum,
/// then assert (a) floor <= opt always (no overshoot) and (b) whenever the
/// gate condition `value <= floor && feasible` holds, value == opt.
fn assert_gate_sound(cs: &[PbConstraint], obj: &PbObjective) {
    let mut opt: Option<i128> = None;
    for mask in 0..4u8 {
        let x = [mask & 1 == 1, mask & 2 == 2];
        if verify_all_constraints(cs, &x) {
            let v = eval_objective(obj, &x);
            opt = Some(opt.map_or(v, |o: i128| o.min(v)));
        }
    }
    let floor = objective_lower_bound_from_constraints(cs, obj, &|| false);
    if let Some(f) = floor {
        if let Some(o) = opt {
            assert!(
                f <= o,
                "structural floor {f} exceeds true optimum {o} (unsound LB)"
            );
        }
        for mask in 0..4u8 {
            let a = [mask & 1 == 1, mask & 2 == 2];
            if !verify_all_constraints(cs, &a) {
                continue;
            }
            let value = eval_objective(obj, &a);
            if value <= f {
                let o = opt.expect("feasible incumbent exists => opt is Some");
                assert_eq!(
                    value, o,
                    "gate fired (value {value} <= floor {f}) but value != true optimum {o}"
                );
            }
        }
    }
}

#[test]
fn gate_soundness_unit_cover() {
    let cs = vec![gate_ge_row(1, 1, 1)];
    let obj = gate_obj2(1, 1);
    assert_eq!(
        objective_lower_bound_from_constraints(&cs, &obj, &|| false),
        Some(1)
    );
    assert_gate_sound(&cs, &obj);
}

#[test]
fn gate_soundness_weighted_cover() {
    let cs = vec![gate_ge_row(2, 3, 3)];
    let obj = gate_obj2(2, 3);
    assert_gate_sound(&cs, &obj);
}

#[test]
fn gate_soundness_two_separate_covers() {
    let cs = vec![gate_ge_row1(1, 1, 1), gate_ge_row1(2, 1, 1)];
    let obj = gate_obj2(1, 1);
    assert_eq!(
        objective_lower_bound_from_constraints(&cs, &obj, &|| false),
        Some(2)
    );
    assert_gate_sound(&cs, &obj);
}

#[test]
fn gate_soundness_adversarial_loose_floor() {
    // Adversarial: floor (3) < the both-set incumbent cost (6); the gate must
    // stay closed on the suboptimal incumbent.
    let cs = vec![gate_ge_row(1, 1, 1)];
    let obj = gate_obj2(3, 3);
    let floor = objective_lower_bound_from_constraints(&cs, &obj, &|| false).expect("floor exists");
    let both = [true, true];
    assert!(verify_all_constraints(&cs, &both));
    assert!(
        eval_objective(&obj, &both) > floor,
        "suboptimal incumbent must exceed floor so the gate stays closed"
    );
    assert_gate_sound(&cs, &obj);
}

#[test]
fn gate_soundness_empty_objective_short_circuit() {
    let cs = vec![gate_ge_row(1, 1, 1)];
    let obj = PbObjective { terms: vec![] };
    assert_eq!(
        objective_lower_bound_from_constraints(&cs, &obj, &|| false),
        Some(0)
    );
    assert_gate_sound(&cs, &obj);
}

// ── SharedBounds ub == lb OPTIMUM upgrade (design §2.7/§3.1 S3) ──────────
// The upgrade must route EXCLUSIVELY through `shared_bounds_optimum_upgrade`:
// lock the incumbent slot, THEN read lb, then RE-VERIFY from raw bits
// (sanitize + `optimum_upgrade_guard` + the full claim sanitizer). Every
// doubt — corrupted slot, absent floor, floor not met — produces NO upgrade.

/// Happy path: a VERIFIED incumbent meeting the published GLOBAL-SOUND floor
/// upgrades to OPTIMUM, with the objective recomputed from the model's raw
/// bits (the bus value is never trusted).
#[test]
fn test_shared_bounds_upgrade_claims_optimum_after_lock_and_reverify() {
    let instance = worker_split_instance();
    let objective = instance.objective.clone().expect("fixture has objective");
    let bus = SharedBounds::new();
    let floor =
        objective_lower_bound_from_constraints(&instance.constraints, &objective, &|| false)
            .expect("covering floor exists");
    assert_eq!(floor, 1, "fixture floor must equal the true optimum");
    assert!(bus.publish_lb(GlobalSoundFloor::from_structural_constraint_floor(floor)));
    assert!(bus.publish_incumbent(1, &[true, false]));

    let verdict = shared_bounds_optimum_upgrade(&bus, &instance, &objective, None)
        .expect("floor-meeting verified incumbent must upgrade");
    assert_eq!(verdict.status, PbStatus::OptimumFound);
    assert_eq!(verdict.objective, Some(1));
    assert_eq!(verdict.assignment, vec![true, false]);
}

/// FAIL-CLOSED: a corrupted bus slot — an INFEASIBLE model, or a model whose
/// exact objective does not meet the floor no matter what value was claimed —
/// must produce NO upgrade. The re-verify discards the bus's claimed value
/// entirely.
#[test]
fn test_shared_bounds_upgrade_fails_closed_on_corrupted_slot() {
    let instance = worker_split_instance();
    let objective = instance.objective.clone().expect("fixture has objective");

    // Corruption 1: infeasible model in the slot (violates x1 + x2 >= 1).
    let bus = SharedBounds::new();
    assert!(bus.publish_lb(GlobalSoundFloor::from_structural_constraint_floor(1)));
    assert!(bus.publish_incumbent(1, &[false, false]));
    assert_eq!(
        shared_bounds_optimum_upgrade(&bus, &instance, &objective, None),
        None,
        "an infeasible slot model must never upgrade"
    );

    // Corruption 2: feasible model, but its EXACT objective (2) exceeds the
    // floor (1) — the claimed bus value 1 is a lie the re-verify discards.
    let bus = SharedBounds::new();
    assert!(bus.publish_lb(GlobalSoundFloor::from_structural_constraint_floor(1)));
    assert!(bus.publish_incumbent(1, &[true, true]));
    assert_eq!(
        shared_bounds_optimum_upgrade(&bus, &instance, &objective, None),
        None,
        "a floor-missing recomputed objective must never upgrade"
    );
}

/// FAIL-CLOSED: no floor (or no incumbent) on the bus means no upgrade —
/// absence is never an upgrade license.
#[test]
fn test_shared_bounds_upgrade_requires_both_floor_and_incumbent() {
    let instance = worker_split_instance();
    let objective = instance.objective.clone().expect("fixture has objective");

    // Empty bus.
    let bus = SharedBounds::new();
    assert_eq!(
        shared_bounds_optimum_upgrade(&bus, &instance, &objective, None),
        None
    );

    // Verified-quality incumbent but NO published floor.
    assert!(bus.publish_incumbent(1, &[true, false]));
    assert_eq!(
        shared_bounds_optimum_upgrade(&bus, &instance, &objective, None),
        None,
        "an absent lb must read as NO FLOOR, never as an upgrade license"
    );

    // Floor present but the incumbent does not meet it (floor 1 < value 2).
    let bus = SharedBounds::new();
    assert!(bus.publish_lb(GlobalSoundFloor::from_structural_constraint_floor(1)));
    assert!(bus.publish_incumbent(2, &[true, true]));
    assert_eq!(
        shared_bounds_optimum_upgrade(&bus, &instance, &objective, None),
        None,
        "value > floor must never upgrade"
    );
}

/// PLANTED COORDINATOR RUN (design §7-P3 gate): a PRIMAL worker's streamed
/// incumbent meets the published GLOBAL-SOUND floor; the coordinator must
/// produce OPTIMUM — through the lock -> read-lb -> re-verify rule only — and
/// stop the remaining workers. The primal worker itself remains
/// verdict-incapable throughout (it only ever sent `Improvement`).
#[test]
fn test_collector_upgrades_primal_incumbent_meeting_sound_floor_to_optimum() {
    let instance = worker_split_instance();
    let objective = instance.objective.clone().expect("fixture has objective");

    let bus = SharedBounds::new();
    let floor =
        objective_lower_bound_from_constraints(&instance.constraints, &objective, &|| false)
            .expect("covering floor exists");
    assert!(bus.publish_lb(GlobalSoundFloor::from_structural_constraint_floor(floor)));

    let (tx, rx) = mpsc::channel();
    let sender = PrimalSender::new(tx, "sls-primal-opt");
    sender.send_improvement(1, vec![true, false]);
    sender.finish();

    let mut controls = WorkerStopControls::default();
    let stop_flag = controls.register("sls-primal-opt");
    let outer_term = AtomicBool::new(false);
    let mut improvements: Vec<i128> = Vec::new();
    let outcome = collect_optimization_result(
        &rx,
        &mut controls,
        &outer_term,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &instance,
        &objective,
        &mut |obj, _| improvements.push(obj),
        &bus,
        &mut OptimizationBackfill::none(),
    );

    assert_eq!(outcome.status, PbStatus::OptimumFound);
    assert_eq!(outcome.objective, Some(1));
    assert_eq!(outcome.assignment, vec![true, false]);
    assert_eq!(improvements, vec![1]);
    assert!(
        stop_flag.load(Ordering::Relaxed),
        "a bus-upgrade verdict must stop the remaining workers"
    );
}

/// PLANTED FAIL-CLOSED RUN: same coordinator flow, but the bus slot holds a
/// CORRUPTED incumbent (infeasible model) and no worker streams anything.
/// The tail upgrade must refuse; the outcome carries no verdict at all.
#[test]
fn test_collector_produces_no_upgrade_from_corrupted_bus_slot() {
    let instance = worker_split_instance();
    let objective = instance.objective.clone().expect("fixture has objective");

    let bus = SharedBounds::new();
    assert!(bus.publish_lb(GlobalSoundFloor::from_structural_constraint_floor(1)));
    // Corrupt the slot directly (simulating publisher corruption): an
    // infeasible model with a floor-meeting claimed value.
    assert!(bus.publish_incumbent(1, &[false, false]));

    let (tx, rx) = mpsc::channel();
    PrimalSender::new(tx, "sls-primal-opt").finish();

    let mut controls = WorkerStopControls::default();
    let _flag = controls.register("sls-primal-opt");
    let outer_term = AtomicBool::new(false);
    let outcome = collect_optimization_result(
        &rx,
        &mut controls,
        &outer_term,
        Some(Duration::from_secs(10)),
        Instant::now(),
        &instance,
        &objective,
        &mut |_, _| {},
        &bus,
        &mut OptimizationBackfill::none(),
    );

    assert_ne!(
        outcome.status,
        PbStatus::OptimumFound,
        "a corrupted bus slot must never yield an OPTIMUM"
    );
    assert_eq!(outcome.status, PbStatus::Unknown);
}

/// SOUNDNESS STOPGAP regression (the QPLIB_3815 false-optimum class): a
/// feasible incumbent for a NON-LINEAR (product) objective must be reported
/// SATISFIABLE, never OPTIMUM, because AY's nonlinear optimality proof is
/// unsound (the objective<=k bound is encoded over phantom aux vars). A wrong
/// OPTIMUM disqualifies a competition category.
#[test]
fn nonlinear_objective_optimum_downgraded_to_satisfiable() {
    // Objective `min: 1 * x1 * x2` (a single product term). Constraint x1+x2>=1.
    let objective = PbObjective {
        terms: vec![PbTerm {
            coeff: 1,
            lits: vec![gate_pos(1), gate_pos(2)],
        }],
    };
    let instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![gate_ge_row(1, 1, 1)],
        objective: Some(objective.clone()),
    };
    // Feasible incumbent x1=x2=1 (objective 1), which the inner NLC path may
    // FALSELY stamp OPTIMUM.
    let sol = PbSolution {
        status: PbStatus::OptimumFound,
        assignment: vec![true, true],
        objective: Some(1),
    };
    let out = sanitize_optimization_solution(sol, &instance, &objective);
    assert_eq!(
        out.status,
        PbStatus::Satisfiable,
        "nonlinear-objective OPTIMUM must be downgraded to SATISFIABLE (DQ prevention)"
    );
    assert_eq!(out.objective, Some(1)); // feasible incumbent + value preserved

    // Control: the SAME shape with a LINEAR objective keeps OPTIMUM (the
    // stopgap must not over-fire on legitimate linear optimality claims).
    let lin_obj = gate_obj2(1, 1);
    let lin_instance = PbInstance {
        num_vars: 2,
        num_constraints: 1,
        constraints: vec![gate_ge_row(1, 1, 1)],
        objective: Some(lin_obj.clone()),
    };
    let lin_sol = PbSolution {
        status: PbStatus::OptimumFound,
        assignment: vec![true, false],
        objective: Some(1),
    };
    let lin_out = sanitize_optimization_solution(lin_sol, &lin_instance, &lin_obj);
    assert_eq!(
        lin_out.status,
        PbStatus::OptimumFound,
        "linear-objective OPTIMUM must be preserved"
    );
}

// ---- AY_PB_LNS2 (stronger LNS) soundness gate --------------------------
//
// Process-global env-var toggling must be serialized so concurrent tests do
// not race on `AY_PB_LNS2` (the one workspace env lock, `lock_env`).

/// Exhaustive 0/1 optimum of a tiny linear instance.
fn brute_force_optimum_small(instance: &PbInstance, objective: &PbObjective) -> Option<i128> {
    let n = instance.num_vars as usize;
    assert!(n <= 16);
    let mut best: Option<i128> = None;
    for mask in 0u32..(1u32 << n) {
        let assign: Vec<bool> = (0..n).map(|i| (mask >> i) & 1 == 1).collect();
        if verify_all_constraints(&instance.constraints, &assign) {
            let v = eval_objective(objective, &assign);
            best = Some(best.map_or(v, |b| b.min(v)));
        }
    }
    best
}

fn vc_opb(num_vertices: u32, edges: &[(u32, u32)]) -> (PbInstance, PbObjective) {
    let mut s = format!(
        "* #variable= {num_vertices} #constraint= {}\nmin:",
        edges.len()
    );
    for v in 1..=num_vertices {
        s.push_str(&format!(" +1 x{v}"));
    }
    s.push_str(" ;\n");
    for &(u, v) in edges {
        s.push_str(&format!("+1 x{u} +1 x{v} >= 1 ;\n"));
    }
    let instance = parse_opb(&s).expect("vc fixture parses");
    let objective = instance.objective.clone().expect("has objective");
    (instance, objective)
}

/// SOUNDNESS GATE for the stronger LNS (local branching + feasibility pump):
/// with `AY_PB_LNS2=1`, across several tiny instances, (1) every incumbent the
/// portfolio reports through `on_improve` is feasible vs the original
/// constraints and never below the brute-force optimum; (2) a declared OPTIMUM
/// equals the brute-force optimum exactly — never below it. Mirrors
/// `bnb_matches_bruteforce_optimum`, but specifically with LNS2 enabled.
#[test]
fn lns2_portfolio_matches_bruteforce_optimum_and_reports_only_sound_incumbents() {
    let _guard = lock_env();
    let _lns2 = ScopedEnvVar::set("AY_PB_LNS2", "1");

    let cases: Vec<(PbInstance, PbObjective)> = vec![
        vc_opb(6, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]),
        vc_opb(8, &[(1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8)]),
        vc_opb(5, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 1)]),
        vc_opb(7, &[(1, 2), (2, 3), (3, 1), (4, 5), (5, 6), (6, 4), (3, 4)]),
    ];

    for (instance, objective) in cases {
        let brute =
            brute_force_optimum_small(&instance, &objective).expect("each fixture is feasible");

        let mut bad = 0usize;
        let mut on_improve = |obj: i128, model: &[bool]| {
            // Every streamed incumbent must be feasible and >= brute optimum.
            if !verify_all_constraints(&instance.constraints, model) {
                bad += 1;
            }
            if eval_objective(&objective, model) != obj {
                bad += 1;
            }
            if obj < brute {
                bad += 1; // below the true optimum -> catastrophic
            }
        };

        let term_flag = AtomicBool::new(false);
        let sol = solve_optimization_portfolio(
            &instance,
            &objective,
            Some(Duration::from_secs(10)),
            Instant::now(),
            &term_flag,
            &mut on_improve,
        );

        assert_eq!(bad, 0, "LNS2 portfolio streamed an unsound incumbent");

        // If a final objective is reported, it must be feasible and never
        // below the brute-force optimum.
        if let Some(value) = sol.objective {
            if !sol.assignment.is_empty() {
                assert!(
                    verify_all_constraints(&instance.constraints, &sol.assignment),
                    "final reported assignment must be feasible"
                );
            }
            assert!(
                value >= brute,
                "final objective {value} below brute-force optimum {brute}"
            );
        }

        // A DECLARED OPTIMUM must equal the brute-force optimum exactly.
        if sol.status == PbStatus::OptimumFound {
            assert_eq!(
                sol.objective,
                Some(brute),
                "declared OPTIMUM must match brute force exactly with LNS2 on"
            );
        }
    }
    // `_lns2` restores AY_PB_LNS2 at end of scope, still under `_guard`.
}

/// Control: the SAME instances must declare the SAME OPTIMUM value with LNS2
/// ON vs OFF — enabling the stronger LNS must never change a proven optimum.
#[test]
fn lns2_does_not_change_declared_optimum_vs_off() {
    let _guard = lock_env();

    let cases: Vec<(PbInstance, PbObjective)> = vec![
        vc_opb(6, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 6)]),
        vc_opb(5, &[(1, 2), (2, 3), (3, 4), (4, 5), (5, 1)]),
    ];

    for (instance, objective) in cases {
        let brute = brute_force_optimum_small(&instance, &objective).expect("feasible");

        let solve_once = || {
            let term_flag = AtomicBool::new(false);
            let mut noop = |_o: i128, _m: &[bool]| {};
            solve_optimization_portfolio(
                &instance,
                &objective,
                Some(Duration::from_secs(10)),
                Instant::now(),
                &term_flag,
                &mut noop,
            )
        };

        // LNS2 now defaults ON; model the old default-off path explicitly
        // with `AY_PB_LNS2=0` so this control still compares OFF vs ON.
        let off = {
            let _lns2 = ScopedEnvVar::set("AY_PB_LNS2", "0");
            solve_once()
        };
        let on = {
            let _lns2 = ScopedEnvVar::set("AY_PB_LNS2", "1");
            solve_once()
        };

        // Whatever OFF proved as OPTIMUM, ON must prove the same value (and it
        // must equal the brute-force optimum); ON must never claim a different
        // or false optimum.
        if off.status == PbStatus::OptimumFound {
            assert_eq!(off.objective, Some(brute));
            assert_eq!(
                on.status,
                PbStatus::OptimumFound,
                "LNS2 must not lose a proven optimum"
            );
            assert_eq!(
                on.objective, off.objective,
                "LNS2 must not change the proven optimum value"
            );
        }
        if on.status == PbStatus::OptimumFound {
            assert_eq!(
                on.objective,
                Some(brute),
                "LNS2-on declared OPTIMUM must match brute force"
            );
        }
    }
}

// Process-global env-var toggling must be serialized so concurrent tests do
// not observe a mid-test AY_PB_WBO_SLS value (the one workspace env lock,
// `lock_env`).

#[test]
fn wbo_sls_enabled_reads_env_flag() {
    let _guard = lock_env();
    // Baseline unset for the whole test; restored on scope exit.
    let _wbo = ScopedEnvVar::unset("AY_PB_WBO_SLS");
    // Sequential tail fallback: opt-IN (default OFF). Parallel WBO-route
    // worker: batteries-included (default ON) — the SAME env var only serves
    // as an explicit override in either direction.
    assert!(!wbo_sls_enabled());
    assert!(wbo_sls_worker_enabled());
    for v in ["1", "true", "yes", "on", "ON", " On "] {
        let _w = ScopedEnvVar::set("AY_PB_WBO_SLS", v);
        assert!(wbo_sls_enabled(), "expected enabled for {v:?}");
        assert!(wbo_sls_worker_enabled(), "worker must stay on for {v:?}");
    }
    for v in ["0", "false", "no", "off", ""] {
        let _w = ScopedEnvVar::set("AY_PB_WBO_SLS", v);
        assert!(!wbo_sls_enabled(), "expected disabled for {v:?}");
    }
    for v in ["0", "false", "no", "off", " OFF ", ""] {
        let _w = ScopedEnvVar::set("AY_PB_WBO_SLS", v);
        assert!(
            !wbo_sls_worker_enabled(),
            "explicit off must disable the worker for {v:?}"
        );
    }
    // (baseline `_wbo` keeps AY_PB_WBO_SLS unset between the probes above)
    // ... and the WBO-route spec set follows the worker gate.
    let instance = worker_split_instance();
    let profile = InstanceProfile::from_instance(&instance);
    let disabled = {
        let _w = ScopedEnvVar::set("AY_PB_WBO_SLS", "0");
        optimization_worker_specs(&profile, OptimizationPortfolioRoute::WboReduced)
    };
    assert!(
        disabled.iter().all(|spec| spec.label != "wbo-sls-opt"),
        "AY_PB_WBO_SLS=0 must remove the WBO-route worker"
    );
}

#[test]
fn wbo_reduced_sls_finds_verified_incumbent() {
    // A small WBO: hard exactly-one over x1,x2 (x1 + x2 = 1) and soft unit
    // preferences. The WBO->PBO reduction adds a relaxation variable per paid
    // soft. solve_wbo_reduced_sls must land a feasible incumbent over the
    // reduced PBO whose objective is the exact relaxed objective, and every
    // streamed incumbent must satisfy ALL reduced-PBO constraints (the
    // soundness gate the CLI re-applies against the ORIGINAL WBO).
    let lit = |v: u32| PbLit {
        var: v,
        negated: false,
    };
    let term = |c: i128, v: u32| PbTerm {
        coeff: c,
        lits: vec![lit(v)],
    };
    let wbo = crate::types::WboInstance {
        top_cost: Some(100),
        num_vars: 2,
        hard_constraints: vec![PbConstraint {
            terms: vec![term(1, 1), term(1, 2)],
            rel: PbRel::Eq,
            rhs: 1,
        }],
        soft_constraints: vec![
            (
                5,
                PbConstraint {
                    terms: vec![term(1, 1)],
                    rel: PbRel::Ge,
                    rhs: 1,
                },
            ),
            (
                3,
                PbConstraint {
                    terms: vec![term(1, 2)],
                    rel: PbRel::Ge,
                    rhs: 1,
                },
            ),
        ],
        objective: None,
    };
    let pbo = crate::optimize::wbo::wbo_to_pbo(&wbo);
    let objective = pbo.objective.clone().expect("reduced PBO has an objective");

    let term_flag = AtomicBool::new(false);
    let mut streamed: Vec<(i128, Vec<bool>)> = Vec::new();
    let mut on_improve = |obj: i128, model: &[bool]| {
        // Every reported incumbent must satisfy ALL reduced-PBO constraints
        // and have the exactly-recomputed objective.
        assert!(verify_all_constraints(&pbo.constraints, model));
        assert_eq!(eval_objective(&objective, model), obj);
        streamed.push((obj, model.to_vec()));
    };
    let result = solve_wbo_reduced_sls(
        &pbo,
        &objective,
        Some(Duration::from_millis(500)),
        Instant::now(),
        &term_flag,
        &mut on_improve,
    );

    // Must land a feasible incumbent (never OPTIMUM/UNSAT).
    assert_eq!(result.status, PbStatus::Satisfiable);
    let obj = result.objective.expect("incumbent has an objective");
    assert!(verify_all_constraints(&pbo.constraints, &result.assignment));
    assert_eq!(eval_objective(&objective, &result.assignment), obj);
    // x1+x2=1 satisfies exactly one soft; the other is bought out. Optimal
    // relaxed objective is min(5,3)=3 (relax the cheaper unsatisfied soft);
    // any feasible incumbent costs at most 5.
    assert!(obj <= 5);
    assert!(!streamed.is_empty(), "at least one incumbent was streamed");
}

// ===========================================================================
// SMALL NON-LINEAR (product) exact-exhaustion optimality upgrade.
// ===========================================================================

/// Fully-independent brute force (does NOT call `eval_objective` /
/// `verify_all_constraints`): the 0-WRONG ground truth. Returns the minimum
/// objective over all `2^n` assignments that satisfy every constraint, or `None`
/// when the instance is infeasible.
fn nlc_manual_bruteforce_optimum(instance: &PbInstance) -> Option<i128> {
    fn term_active(term: &PbTerm, asg: &[bool]) -> bool {
        term.lits.iter().all(|lit| {
            let raw = asg[(lit.var - 1) as usize];
            if lit.negated {
                !raw
            } else {
                raw
            }
        })
    }
    let n = instance.num_vars as usize;
    let objective = instance.objective.as_ref().expect("objective");
    let mut best: Option<i128> = None;
    for mask in 0u32..(1u32 << n) {
        let asg: Vec<bool> = (0..n).map(|b| (mask >> b) & 1 == 1).collect();
        let feasible = instance.constraints.iter().all(|c| {
            let lhs: i128 = c
                .terms
                .iter()
                .filter(|t| term_active(t, &asg))
                .map(|t| t.coeff)
                .sum();
            match c.rel {
                PbRel::Ge => lhs >= c.rhs,
                PbRel::Eq => lhs == c.rhs,
            }
        });
        if feasible {
            let v: i128 = objective
                .terms
                .iter()
                .filter(|t| term_active(t, &asg))
                .map(|t| t.coeff)
                .sum();
            if best.is_none_or(|b| v < b) {
                best = Some(v);
            }
        }
    }
    best
}

#[test]
fn small_nlc_exhaustible_gate() {
    // Small + non-linear (a product term) => exhaustible.
    let nlc = parse_opb("* #variable= 3 #constraint= 0\nmin: +1 x1 x2 -1 x1 -1 x2 +1 x3 ;\n")
        .expect("parse");
    assert!(small_nlc_exhaustible(&nlc, nlc.objective.as_ref().unwrap()));

    // Purely linear => NOT eligible (this upgrade is only for product objectives;
    // the linear LP/B&B upgrades own that case).
    let lin =
        parse_opb("* #variable= 3 #constraint= 0\nmin: +1 x1 +1 x2 +1 x3 ;\n").expect("parse");
    assert!(!small_nlc_exhaustible(
        &lin,
        lin.objective.as_ref().unwrap()
    ));

    // Too many variables (> SMALL_NLC_EXHAUST_MAX_VARS) => NOT eligible, even with a
    // product term, so large instances are never enumerated.
    let mut wide = String::from("* #variable= 40 #constraint= 0\nmin: +1 x1 x2 ");
    for v in 3..=40 {
        wide.push_str(&format!("+1 x{v} "));
    }
    wide.push_str(";\n");
    let wide = parse_opb(&wide).expect("parse");
    assert!(!small_nlc_exhaustible(
        &wide,
        wide.objective.as_ref().unwrap()
    ));
}

#[test]
fn small_nlc_exhaustive_optimum_matches_manual_bruteforce() {
    let never_stop = || false;
    // A hand-checkable unconstrained BQO: min x1*x2 - x1 - x2. Every assignment but
    // all-false attains -1 (the global optimum); all-false attains 0.
    let inst =
        parse_opb("* #variable= 2 #constraint= 0\nmin: +1 x1 x2 -1 x1 -1 x2 ;\n").expect("parse");
    let obj = inst.objective.as_ref().unwrap();
    let incumbent = vec![false, false]; // feasible (unconstrained), value 0
    let (witness, value) =
        try_small_nlc_exhaustive_optimum(&inst, obj, &incumbent, &never_stop).expect("optimum");
    assert_eq!(value, -1);
    assert_eq!(value, nlc_manual_bruteforce_optimum(&inst).unwrap());
    assert_eq!(eval_objective(obj, &witness), value);
    assert!(verify_all_constraints(&inst.constraints, &witness));

    // A constrained product instance: min -x1 -x2 + 3 x1 x2  s.t.  x1 + x2 >= 1.
    // 10 -> -1, 01 -> -1, 11 -> -2+3 = 1; optimum = -1.
    let inst2 = parse_opb(
        "* #variable= 2 #constraint= 1\nmin: -1 x1 -1 x2 +3 x1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n",
    )
    .expect("parse");
    let obj2 = inst2.objective.as_ref().unwrap();
    let incumbent2 = vec![true, false]; // feasible, value -1
    let (w2, v2) =
        try_small_nlc_exhaustive_optimum(&inst2, obj2, &incumbent2, &never_stop).expect("optimum");
    assert_eq!(v2, -1);
    assert_eq!(v2, nlc_manual_bruteforce_optimum(&inst2).unwrap());
    assert!(verify_all_constraints(&inst2.constraints, &w2));

    // An interrupted sweep must DECLINE (never claim optimality on a partial scan).
    let always_stop = || true;
    assert!(
        try_small_nlc_exhaustive_optimum(&inst, obj, &incumbent, &always_stop).is_none(),
        "a stopped sweep must not claim an optimum"
    );
}

#[test]
fn small_nlc_exhaustive_optimum_random_bruteforce_0wrong() {
    // Deterministic xorshift PRNG (no dev-deps), mirroring branch_and_bound's tests.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn range(&mut self, lo: i128, hi: i128) -> i128 {
            let span = (hi - lo + 1) as u64;
            lo + (self.next() % span) as i128
        }
    }
    let never_stop = || false;
    let mut rng = Rng(0xA1B2_C3D4_E5F6_0718);
    let mut tested = 0usize;

    for _ in 0..300 {
        let n = rng.range(2, 7) as u32; // small enough to brute-force in the test
                                        // Build a random UNCONSTRAINED product objective (degree 1 or 2 terms, mixed
                                        // signs). Unconstrained => all-false is always a feasible incumbent. Guarantee
                                        // at least one genuine degree-2 product term so the instance is non-linear
                                        // (the gate the upgrade targets).
        let mut src = format!("* #variable= {n} #constraint= 0\nmin:");
        {
            let coeff = if rng.range(0, 1) == 0 { -1 } else { 1 };
            let a = rng.range(1, n as i128);
            let b = 1 + (a % n as i128); // distinct from a (n >= 2)
            src.push_str(&format!(" {coeff:+} x{a} x{b}"));
        }
        let n_terms = rng.range(0, 7);
        for _ in 0..n_terms {
            let coeff = rng.range(-3, 3);
            if coeff == 0 {
                continue;
            }
            let a = rng.range(1, n as i128);
            src.push_str(&format!(" {coeff:+} x{a}"));
            if rng.range(0, 1) == 1 {
                let b = rng.range(1, n as i128);
                if b != a {
                    src.push_str(&format!(" x{b}"));
                }
            }
        }
        src.push_str(" ;\n");
        let inst = parse_opb(&src).expect("parse");
        let obj = inst.objective.as_ref().unwrap();
        // The upgrade only targets non-linear, small-enough instances; skip anything
        // the gate would (it never claims an optimum it did not exhaust).
        if !small_nlc_exhaustible(&inst, obj) {
            continue;
        }
        tested += 1;

        let incumbent = vec![false; n as usize];
        let result = try_small_nlc_exhaustive_optimum(&inst, obj, &incumbent, &never_stop)
            .expect("unconstrained small instance must yield a proven optimum");
        let manual = nlc_manual_bruteforce_optimum(&inst).expect("feasible");
        assert_eq!(
            result.1, manual,
            "exhaustion optimum {} != manual brute force {} for {src}",
            result.1, manual
        );
        // The returned witness must independently attain the reported value.
        assert_eq!(eval_objective(obj, &result.0), result.1);
        assert!(verify_all_constraints(&inst.constraints, &result.0));
    }
    assert!(
        tested >= 200,
        "expected many random instances, got {tested}"
    );
}

#[test]
fn portfolio_emits_proven_optimum_on_small_product_instance() {
    // End-to-end through the optimization portfolio: a small product-objective
    // instance must come back PROVEN OPTIMUM (not merely SATISFIABLE) with the
    // brute-force-correct value. min x1*x2 - x1 - x2  (optimum -1).
    let inst =
        parse_opb("* #variable= 2 #constraint= 0\nmin: +1 x1 x2 -1 x1 -1 x2 ;\n").expect("parse");
    let obj = inst.objective.as_ref().unwrap();
    let term_flag = AtomicBool::new(false);
    let mut sink = |_obj: i128, _model: &[bool]| {};
    let outcome = solve_optimization_portfolio_with_timings(
        &inst,
        obj,
        Some(Duration::from_secs(5)),
        Instant::now(),
        &term_flag,
        &mut sink,
    );
    assert_eq!(
        outcome.solution.status,
        PbStatus::OptimumFound,
        "small product instance must be PROVEN OPTIMUM"
    );
    assert_eq!(outcome.solution.objective, Some(-1));
    assert_eq!(
        outcome.solution.objective,
        Some(nlc_manual_bruteforce_optimum(&inst).unwrap())
    );
    assert!(verify_all_constraints(
        &inst.constraints,
        &outcome.solution.assignment
    ));
    assert_eq!(eval_objective(obj, &outcome.solution.assignment), -1);
}
