// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Comprehensive acceptance tests for the ay-pb solver.
//!
//! Ensures zero wrong answers across all PB competition categories:
//! - Satisfiable decision instances (PBS)
//! - Unsatisfiable decision instances (PBS)
//! - Optimization instances (PBO)
//! - Non-linear constraint instances (NLC)
//! - Weighted Boolean Optimization instances (WBO)
//!
//! Every SAT result is verified by evaluating ALL constraints against the model.
//! Cross-validation runs both native CDCL and SAT encoding paths to check agreement.
//! Optimization results are verified by brute-force enumeration on small instances.

use ay_pb::{
    eval_constraint, eval_objective, is_linear, linearize, parse_opb, parse_wbo,
    verify_all_constraints, wbo_to_pbo, CnfEncoder, ParseError, PbCdclResult, PbCdclSolver,
    PbInstance, PbObjective,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Parses an inline OPB string and returns the instance.
fn parse(opb: &str) -> PbInstance {
    parse_opb(opb).unwrap_or_else(|e| panic!("parse failed: {e}\ninput:\n{opb}"))
}

/// Solves a decision instance with native CDCL.
fn solve_native(instance: &PbInstance) -> PbCdclResult {
    let mut solver = PbCdclSolver::new(instance);
    solver.solve()
}

/// Solves an optimization instance with native CDCL.
fn solve_optimize_native(instance: &PbInstance, objective: &PbObjective) -> PbCdclResult {
    let mut solver = PbCdclSolver::new(instance);
    solver.solve_optimize(objective, None)
}

/// Solves a decision instance via SAT encoding + brute-force.
/// Returns Some(model) if SAT, None if UNSAT.
/// Only works for small instances (num_vars <= 20).
fn solve_via_encoding(instance: &PbInstance) -> Option<Vec<bool>> {
    let encoded = CnfEncoder::encode_instance(instance);
    let num_vars = encoded.num_vars as usize;

    if num_vars > 20 {
        return None;
    }

    for mask in 0..(1u64 << num_vars) {
        let assignment: Vec<bool> = (0..num_vars).map(|i| (mask >> i) & 1 == 1).collect();
        let all_satisfied = encoded.clauses.iter().all(|clause| {
            if clause.is_empty() {
                return false;
            }
            clause.iter().any(|&lit| {
                let var_idx = (lit.unsigned_abs() - 1) as usize;
                if var_idx >= assignment.len() {
                    return false;
                }
                if lit > 0 {
                    assignment[var_idx]
                } else {
                    !assignment[var_idx]
                }
            })
        });
        if all_satisfied {
            let orig_model: Vec<bool> = assignment[..instance.num_vars as usize].to_vec();
            return Some(orig_model);
        }
    }
    None
}

/// Brute-force finds the optimal value for a small instance.
/// Returns None if infeasible.
fn brute_force_optimal(instance: &PbInstance, objective: &PbObjective) -> Option<i128> {
    let num_vars = instance.num_vars as usize;
    if num_vars > 20 {
        return None;
    }

    let mut best: Option<i128> = None;
    for mask in 0..(1u64 << num_vars) {
        let assignment: Vec<bool> = (0..num_vars).map(|i| (mask >> i) & 1 == 1).collect();
        if verify_all_constraints(&instance.constraints, &assignment) {
            let val = eval_objective(objective, &assignment);
            best = Some(best.map_or(val, |b: i128| b.min(val)));
        }
    }
    best
}

/// Asserts that a model satisfies ALL constraints, with detailed error on failure.
fn assert_model_valid(instance: &PbInstance, model: &[bool], context: &str) {
    for (i, constraint) in instance.constraints.iter().enumerate() {
        assert!(
            eval_constraint(constraint, model),
            "{context}: constraint {i} violated by model.\nconstraint: {constraint:?}\nmodel: {model:?}"
        );
    }
}

/// Cross-validates native CDCL vs SAT encoding on a decision instance.
/// Both must agree on SAT/UNSAT. If SAT, both models must satisfy all constraints.
fn cross_validate_decision(opb: &str, expected_sat: bool, context: &str) {
    let instance = parse(opb);

    // Native CDCL
    let native_result = solve_native(&instance);
    let native_sat = matches!(native_result, PbCdclResult::Satisfiable(_));
    assert_eq!(
        native_sat, expected_sat,
        "{context}: native CDCL expected SAT={expected_sat}, got {native_result:?}"
    );

    if let PbCdclResult::Satisfiable(ref model) = native_result {
        assert_model_valid(&instance, model, &format!("{context} (native)"));
    }

    // SAT encoding (only for linear, small instances)
    if is_linear(&instance) && instance.num_vars <= 20 {
        let encoding_model = solve_via_encoding(&instance);
        let encoding_sat = encoding_model.is_some();
        assert_eq!(
            native_sat, encoding_sat,
            "{context}: native and encoding disagree on SAT/UNSAT"
        );

        if let Some(ref model) = encoding_model {
            assert_model_valid(&instance, model, &format!("{context} (encoding)"));
        }
    }
}

/// Validates an optimization instance. Checks native CDCL finds the correct optimum
/// and verifies via brute force on small instances.
fn validate_optimization(opb: &str, expected_opt: i128, context: &str) {
    let instance = parse(opb);
    let objective = instance
        .objective
        .as_ref()
        .unwrap_or_else(|| panic!("{context}: instance must have objective"));

    let result = solve_optimize_native(&instance, objective);
    match result {
        PbCdclResult::Optimal(ref model, value) => {
            assert_eq!(
                value, expected_opt,
                "{context}: solver optimal {value} != expected {expected_opt}"
            );
            assert_model_valid(&instance, model, context);
            let computed = eval_objective(objective, model);
            assert_eq!(
                computed, value,
                "{context}: objective evaluation {computed} != claimed {value}"
            );

            // Brute-force verification
            if let Some(bf_opt) = brute_force_optimal(&instance, objective) {
                assert_eq!(
                    value, bf_opt,
                    "{context}: solver optimal {value} != brute-force optimal {bf_opt}"
                );
            }
        }
        PbCdclResult::Feasible(ref model, value) => {
            // Accept feasible (timeout), but model must be valid
            assert_model_valid(&instance, model, context);
            let computed = eval_objective(objective, model);
            assert_eq!(computed, value, "{context}: feasible objective mismatch");
        }
        other => panic!("{context}: expected Optimal or Feasible, got {other:?}"),
    }
}

// ===========================================================================
// SATISFIABLE DECISION INSTANCES
// ===========================================================================

#[test]
fn test_sat_trivial_single_var() {
    cross_validate_decision("+1 x1 >= 1 ;\n", true, "trivial single variable x1 >= 1");
}

#[test]
fn test_sat_at_least_k_cardinality() {
    cross_validate_decision(
        "* #variable= 3 #constraint= 1\n+1 x1 +1 x2 +1 x3 >= 2 ;\n",
        true,
        "at-least-2 cardinality",
    );
}

#[test]
fn test_sat_weighted_constraint() {
    cross_validate_decision(
        "+3 x1 +2 x2 +1 x3 >= 4 ;\n",
        true,
        "weighted 3x1+2x2+x3 >= 4",
    );
}

#[test]
fn test_sat_multiple_constraints_unique_solution() {
    // x1 + x2 + x3 = 2 AND x1 >= 1 AND x3 >= 1
    // Only solution: x1=T, x2=F, x3=T (sum=2, x1=T, x3=T)
    cross_validate_decision(
        "* #variable= 3 #constraint= 3\n\
         +1 x1 +1 x2 +1 x3 = 2 ;\n\
         +1 x1 >= 1 ;\n\
         +1 x3 >= 1 ;\n",
        true,
        "multiple constraints unique solution",
    );
}

#[test]
fn test_sat_equality_exactly_one() {
    cross_validate_decision(
        "* #variable= 3 #constraint= 1\n+1 x1 +1 x2 +1 x3 = 1 ;\n",
        true,
        "equality x1+x2+x3 = 1",
    );
}

#[test]
fn test_sat_equality_sum_zero() {
    // x1 + x2 = 0 means both false
    cross_validate_decision("+1 x1 +1 x2 = 0 ;\n", true, "equality x1+x2 = 0");
}

#[test]
fn test_sat_negated_literals() {
    // ~x1 + ~x2 >= 1 (at most one true)
    cross_validate_decision(
        "+1 ~x1 +1 ~x2 >= 1 ;\n",
        true,
        "negated literals ~x1+~x2 >= 1",
    );
}

#[test]
fn test_sat_mixed_negated_and_positive() {
    // x1 + ~x2 >= 1 AND ~x1 + x2 >= 1
    // Solutions: exactly one true (x1=T,x2=F or x1=F,x2=T)
    // OR both true: x1+~x2=1>=1 and ~x1+x2=1>=1
    // OR both false: 0+1=1>=1 and 1+0=1>=1
    cross_validate_decision(
        "+1 x1 +1 ~x2 >= 1 ;\n+1 ~x1 +1 x2 >= 1 ;\n",
        true,
        "mixed negated and positive",
    );
}

#[test]
fn test_sat_at_most_k_via_negation() {
    // At most 2 of 4: ~x1+~x2+~x3+~x4 >= 2 AND at least 1: x1+x2+x3+x4 >= 1
    cross_validate_decision(
        "* #variable= 4 #constraint= 2\n\
         +1 ~x1 +1 ~x2 +1 ~x3 +1 ~x4 >= 2 ;\n\
         +1 x1 +1 x2 +1 x3 +1 x4 >= 1 ;\n",
        true,
        "at-most-2-of-4 with at-least-1",
    );
}

#[test]
fn test_sat_weighted_large_coefficients() {
    // 100*x1 + 200*x2 + 50*x3 >= 250
    // x2=T alone gives 200 < 250, need x2+x1 (300>=250) or x2+x3 (250>=250) etc.
    cross_validate_decision(
        "+100 x1 +200 x2 +50 x3 >= 250 ;\n",
        true,
        "weighted large coefficients",
    );
}

#[test]
fn test_sat_single_var_with_large_coeff() {
    // 1000*x1 >= 1 means x1 must be true
    let instance = parse("+1000 x1 >= 1 ;\n");
    let result = solve_native(&instance);
    match result {
        PbCdclResult::Satisfiable(model) => {
            assert!(model[0], "x1 must be true for 1000*x1 >= 1");
            assert_model_valid(&instance, &model, "large coeff single var");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// ===========================================================================
// UNSATISFIABLE DECISION INSTANCES
// ===========================================================================

#[test]
fn test_unsat_direct_contradiction() {
    cross_validate_decision(
        "+1 x1 >= 1 ;\n+1 ~x1 >= 1 ;\n",
        false,
        "direct contradiction x1 AND ~x1",
    );
}

#[test]
fn test_unsat_pigeonhole_3_2() {
    // 3 pigeons, 2 holes
    // Variables: x1=p1h1, x2=p1h2, x3=p2h1, x4=p2h2, x5=p3h1, x6=p3h2
    cross_validate_decision(
        "* #variable= 6 #constraint= 5\n\
         +1 x1 +1 x2 >= 1 ;\n\
         +1 x3 +1 x4 >= 1 ;\n\
         +1 x5 +1 x6 >= 1 ;\n\
         +1 ~x1 +1 ~x3 +1 ~x5 >= 2 ;\n\
         +1 ~x2 +1 ~x4 +1 ~x6 >= 2 ;\n",
        false,
        "pigeonhole 3/2",
    );
}

#[test]
fn test_unsat_coefficient_forced() {
    // 3*x1 + 2*x2 >= 6 with 2 variables, max sum = 5 (3+2)
    cross_validate_decision(
        "+3 x1 +2 x2 >= 6 ;\n",
        false,
        "coefficient-forced UNSAT (max 5 < 6)",
    );
}

#[test]
fn test_unsat_equality_impossible() {
    // x1 + x2 = 3 with only 2 binary vars (max = 2)
    cross_validate_decision("+1 x1 +1 x2 = 3 ;\n", false, "equality impossible x1+x2=3");
}

#[test]
fn test_unsat_weighted_mutual_exclusion() {
    // 3*x1 + 2*x2 >= 4 AND 2*~x1 + 3*~x2 >= 4
    // Exhaustive: (T,T): 5>=4 OK, 0<4 FAIL. (T,F): 3<4 FAIL.
    // (F,T): 2<4 FAIL. (F,F): 0<4 FAIL.
    cross_validate_decision(
        "+3 x1 +2 x2 >= 4 ;\n+2 ~x1 +3 ~x2 >= 4 ;\n",
        false,
        "weighted mutual exclusion",
    );
}

#[test]
fn test_unsat_overconstrained_equality() {
    // x1 + x2 = 0 AND x1 >= 1 (x1 must be true but sum must be 0)
    cross_validate_decision(
        "+1 x1 +1 x2 = 0 ;\n+1 x1 >= 1 ;\n",
        false,
        "overconstrained equality",
    );
}

#[test]
fn test_unsat_all_vars_both_ways() {
    // Each var must be true AND each var must be false
    cross_validate_decision(
        "+1 x1 >= 1 ;\n+1 x2 >= 1 ;\n+1 ~x1 >= 1 ;\n+1 ~x2 >= 1 ;\n",
        false,
        "all vars both true and false",
    );
}

#[test]
fn test_unsat_empty_constraint_positive_rhs() {
    // No terms, rhs = 1: 0 >= 1 is always false
    // Cannot easily write this in OPB format (parser needs terms), so use API directly
    let instance = PbInstance {
        num_vars: 0,
        num_constraints: 1,
        constraints: vec![ay_pb::PbConstraint {
            terms: vec![],
            rel: ay_pb::PbRel::Ge,
            rhs: 1,
        }],
        objective: None,
    };
    let result = solve_native(&instance);
    assert_eq!(
        result,
        PbCdclResult::Unsatisfiable,
        "empty constraint with rhs=1 must be UNSAT"
    );
}

// ===========================================================================
// OPTIMIZATION INSTANCES (PBO)
// ===========================================================================

#[test]
fn test_opt_min_with_single_feasible() {
    // min x1 + x2 subject to x1 + x2 >= 1 -> optimal = 1
    validate_optimization(
        "* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n",
        1,
        "min x1+x2 s.t. x1+x2>=1",
    );
}

#[test]
fn test_opt_weighted_objective() {
    // min 3*x1 + 2*x2 + x3 subject to x1 + x2 + x3 >= 2
    // Optimal: x2=T, x3=T -> cost = 2+1 = 3
    validate_optimization(
        "* #variable= 3 #constraint= 1\nmin: +3 x1 +2 x2 +1 x3 ;\n+1 x1 +1 x2 +1 x3 >= 2 ;\n",
        3,
        "weighted opt min 3x1+2x2+x3 s.t. >=2",
    );
}

#[test]
fn test_opt_zero_optimal() {
    // min x2 subject to x1 >= 1 -> x1=T, x2=F -> cost 0
    validate_optimization(
        "* #variable= 2 #constraint= 1\nmin: +1 x2 ;\n+1 x1 >= 1 ;\n",
        0,
        "zero cost optimal",
    );
}

#[test]
fn test_opt_all_must_be_true() {
    // min x1 + x2 + x3 subject to x1 + x2 + x3 >= 3 -> all true, cost = 3
    validate_optimization(
        "* #variable= 3 #constraint= 1\nmin: +1 x1 +1 x2 +1 x3 ;\n+1 x1 +1 x2 +1 x3 >= 3 ;\n",
        3,
        "all must be true, cost=3",
    );
}

#[test]
fn test_opt_exactly_two_of_four_cheapest() {
    // min 2*x1 + 3*x2 + 5*x3 + 7*x4
    // subject to: x1+x2+x3+x4 >= 2 AND ~x1+~x2+~x3+~x4 >= 2
    // (exactly 2 true) -> cheapest pair: x1+x2 = 5
    validate_optimization(
        "* #variable= 4 #constraint= 2\n\
         min: +2 x1 +3 x2 +5 x3 +7 x4 ;\n\
         +1 x1 +1 x2 +1 x3 +1 x4 >= 2 ;\n\
         +1 ~x1 +1 ~x2 +1 ~x3 +1 ~x4 >= 2 ;\n",
        5,
        "exactly-2-of-4 cheapest",
    );
}

#[test]
fn test_opt_infeasible() {
    // min x1 subject to x1 >= 1 AND ~x1 >= 1 -> UNSAT
    let instance = parse("min: +1 x1 ;\n+1 x1 >= 1 ;\n+1 ~x1 >= 1 ;\n");
    let objective = instance.objective.as_ref().unwrap();
    let result = solve_optimize_native(&instance, objective);
    assert_eq!(
        result,
        PbCdclResult::Unsatisfiable,
        "infeasible optimization must return UNSAT"
    );
}

#[test]
fn test_opt_negated_literal_in_objective() {
    // min ~x1 + ~x2 subject to x1 + x2 >= 1
    // If x1=T, x2=T: cost = 0 (both negated are false)
    // If x1=T, x2=F: cost = 1 (~x2=true)
    // Optimal: both true, cost = 0
    validate_optimization(
        "* #variable= 2 #constraint= 1\nmin: +1 ~x1 +1 ~x2 ;\n+1 x1 +1 x2 >= 1 ;\n",
        0,
        "negated literals in objective",
    );
}

#[test]
fn test_opt_multiple_constraints() {
    // min x1 + x2 + x3 + x4
    // subject to: x1 + x2 >= 1 AND x3 + x4 >= 1
    // Optimal: one from each pair -> cost = 2
    validate_optimization(
        "* #variable= 4 #constraint= 2\n\
         min: +1 x1 +1 x2 +1 x3 +1 x4 ;\n\
         +1 x1 +1 x2 >= 1 ;\n\
         +1 x3 +1 x4 >= 1 ;\n",
        2,
        "multiple constraints disjoint pairs",
    );
}

// ===========================================================================
// NON-LINEAR CONSTRAINT INSTANCES (NLC)
// ===========================================================================

#[test]
fn test_nlc_product_sat() {
    // x1*x2 + x3 >= 1: SAT (x3=T works, or x1=T and x2=T)
    let instance = parse("* #variable= 3 #constraint= 1\n+1 x1 x2 +1 x3 >= 1 ;\n");

    // Native requires linearization
    let linearized = linearize(&instance);
    let result = solve_native(&linearized);
    match result {
        PbCdclResult::Satisfiable(model) => {
            assert_model_valid(&linearized, &model, "nlc product linearized");
            let orig_model: Vec<bool> = model[..instance.num_vars as usize].to_vec();
            assert_model_valid(&instance, &orig_model, "nlc product original");
        }
        other => panic!("expected SAT for nlc product, got {other:?}"),
    }

    // Encoding handles NLC natively
    let encoding_model = solve_via_encoding(&instance);
    assert!(
        encoding_model.is_some(),
        "encoding should find SAT for nlc product"
    );
    if let Some(model) = encoding_model {
        assert_model_valid(&instance, &model, "nlc product encoding");
    }
}

#[test]
fn test_nlc_multiple_products() {
    // x1*x2 + x2*x3 >= 1: SAT (many solutions)
    let instance = parse("* #variable= 3 #constraint= 1\n+1 x1 x2 +1 x2 x3 >= 1 ;\n");

    let linearized = linearize(&instance);
    let result = solve_native(&linearized);
    match result {
        PbCdclResult::Satisfiable(model) => {
            assert_model_valid(&linearized, &model, "nlc multiple products linearized");
            let orig_model: Vec<bool> = model[..instance.num_vars as usize].to_vec();
            assert_model_valid(&instance, &orig_model, "nlc multiple products original");
        }
        other => panic!("expected SAT for nlc multiple products, got {other:?}"),
    }
}

#[test]
fn test_nlc_product_unsat() {
    // x1*x2 >= 1 AND ~x1 >= 1
    // x1*x2 >= 1 requires x1=T and x2=T, but ~x1 >= 1 requires x1=F
    let instance = parse("* #variable= 2 #constraint= 2\n+1 x1 x2 >= 1 ;\n+1 ~x1 >= 1 ;\n");

    let linearized = linearize(&instance);
    let result = solve_native(&linearized);
    assert_eq!(
        result,
        PbCdclResult::Unsatisfiable,
        "nlc product with contradictory constraint must be UNSAT"
    );

    // Verify via encoding
    let encoding_model = solve_via_encoding(&instance);
    assert!(
        encoding_model.is_none(),
        "encoding should also find UNSAT for contradictory nlc"
    );
}

#[test]
fn test_nlc_triple_product() {
    // x1*x2*x3 >= 1: all three must be true
    let instance = parse("* #variable= 3 #constraint= 1\n+1 x1 x2 x3 >= 1 ;\n");

    let linearized = linearize(&instance);
    let result = solve_native(&linearized);
    match result {
        PbCdclResult::Satisfiable(model) => {
            let orig_model: Vec<bool> = model[..3].to_vec();
            assert!(
                orig_model[0] && orig_model[1] && orig_model[2],
                "all three must be true for x1*x2*x3 >= 1"
            );
            assert_model_valid(&instance, &orig_model, "nlc triple product original");
        }
        other => panic!("expected SAT for triple product, got {other:?}"),
    }
}

#[test]
fn test_nlc_product_with_linear_mix() {
    // 2*x1*x2 + 3*x3 >= 4: need x3=T (gives 3) and x1=T and x2=T (gives 2) for 5>=4
    // or x3=T alone: 3 < 4, so both product and x3 needed
    let instance = parse("* #variable= 3 #constraint= 1\n+2 x1 x2 +3 x3 >= 4 ;\n");

    let linearized = linearize(&instance);
    let result = solve_native(&linearized);
    match result {
        PbCdclResult::Satisfiable(model) => {
            let orig_model: Vec<bool> = model[..3].to_vec();
            assert_model_valid(&instance, &orig_model, "nlc product+linear mix");
        }
        other => panic!("expected SAT for product+linear mix, got {other:?}"),
    }
}

#[test]
fn test_nlc_linearize_preserves_sat() {
    let instance = parse("* #variable= 3 #constraint= 1\n+1 x1 x2 +1 x3 >= 1 ;\n");
    assert!(!is_linear(&instance), "instance should have NLC terms");
    let linearized = linearize(&instance);
    assert!(is_linear(&linearized), "linearized should be fully linear");

    // Solve linearized and project to original vars
    let result = solve_native(&linearized);
    match result {
        PbCdclResult::Satisfiable(model) => {
            let orig_model: Vec<bool> = model[..instance.num_vars as usize].to_vec();
            assert_model_valid(&instance, &orig_model, "linearize preserves SAT");
        }
        other => panic!("expected SAT after linearization, got {other:?}"),
    }
}

// ===========================================================================
// WBO (WEIGHTED BOOLEAN OPTIMIZATION)
// ===========================================================================

#[test]
fn test_wbo_hard_only() {
    // WBO with only hard constraints, no soft
    let wbo_str = "soft: 10 ;\n\
                    +1 x1 +1 x2 >= 1 ;\n";
    let wbo = parse_wbo(wbo_str).unwrap();
    assert!(wbo.soft_constraints.is_empty());
    assert_eq!(wbo.hard_constraints.len(), 1);

    let pbo = wbo_to_pbo(&wbo);
    let result = solve_native(&pbo);
    match result {
        PbCdclResult::Satisfiable(model) => {
            // Verify against original hard constraints
            assert!(
                verify_all_constraints(&wbo.hard_constraints, &model[..wbo.num_vars as usize]),
                "model must satisfy hard constraints"
            );
        }
        other => panic!("expected SAT for hard-only WBO, got {other:?}"),
    }
}

#[test]
fn test_wbo_single_soft() {
    // Hard: x1 + x2 >= 1
    // Soft (cost 5): x1 >= 1
    // Optimal: satisfy hard with x2=T, violate soft (x1=F), cost=5? No wait.
    // Optimal: satisfy both: x1=T costs 0 in relaxation
    let wbo_str = "soft: 10 ;\n\
                    +1 x1 +1 x2 >= 1 ;\n\
                    [5] +1 x1 >= 1 ;\n";
    let wbo = parse_wbo(wbo_str).unwrap();
    let pbo = wbo_to_pbo(&wbo);
    let objective = pbo.objective.as_ref().unwrap();

    let result = solve_optimize_native(&pbo, objective);
    match result {
        PbCdclResult::Optimal(model, value) => {
            assert_eq!(value, 0, "can satisfy both hard and soft, cost=0");
            assert_model_valid(&pbo, &model, "wbo single soft");
        }
        PbCdclResult::Feasible(model, value) => {
            assert_model_valid(&pbo, &model, "wbo single soft feasible");
            assert!(value >= 0, "cost must be non-negative");
        }
        other => panic!("expected Optimal/Feasible for WBO, got {other:?}"),
    }
}

#[test]
fn test_wbo_conflicting_soft() {
    // Hard: (none)
    // Soft (cost 3): x1 >= 1
    // Soft (cost 2): ~x1 >= 1
    // Must violate exactly one: cheaper to violate cost-2, so cost=2
    let wbo_str = "soft: 10 ;\n\
                    [3] +1 x1 >= 1 ;\n\
                    [2] +1 ~x1 >= 1 ;\n";
    let wbo = parse_wbo(wbo_str).unwrap();
    let pbo = wbo_to_pbo(&wbo);
    let objective = pbo.objective.as_ref().unwrap();

    let result = solve_optimize_native(&pbo, objective);
    match result {
        PbCdclResult::Optimal(model, value) => {
            assert_eq!(value, 2, "should violate cost-2 soft, total cost=2");
            assert_model_valid(&pbo, &model, "wbo conflicting soft");
        }
        PbCdclResult::Feasible(model, value) => {
            assert_model_valid(&pbo, &model, "wbo conflicting soft feasible");
            assert!(value <= 3, "feasible cost should be at most 3");
        }
        other => panic!("expected Optimal/Feasible for WBO, got {other:?}"),
    }
}

#[test]
fn test_wbo_soft_equality_satisfied_costs_zero() {
    let wbo_str = "soft: 10 ;\n\
                    [5] +1 x1 +1 x2 = 1 ;\n";
    let wbo = parse_wbo(wbo_str).unwrap();
    let pbo = wbo_to_pbo(&wbo);
    let objective = pbo.objective.as_ref().unwrap();

    assert_eq!(brute_force_optimal(&pbo, objective), Some(0));

    match solve_optimize_native(&pbo, objective) {
        PbCdclResult::Optimal(model, value) => {
            assert_eq!(value, 0, "satisfied soft equality must pay zero");
            assert_model_valid(&pbo, &model, "wbo soft equality satisfied");
            assert!(eval_constraint(
                &wbo.soft_constraints[0].1,
                &model[..wbo.num_vars as usize]
            ));
            assert!(
                !model[wbo.num_vars as usize],
                "relaxation variable must stay false when equality is satisfied"
            );
        }
        other => panic!("expected Optimal for satisfiable soft equality, got {other:?}"),
    }
}

#[test]
fn test_wbo_soft_equality_violation_pays_weight() {
    let wbo_str = "soft: 10 ;\n\
                    +1 x1 >= 1 ;\n\
                    +1 x2 >= 1 ;\n\
                    [5] +1 x1 +1 x2 = 1 ;\n";
    let wbo = parse_wbo(wbo_str).unwrap();
    let pbo = wbo_to_pbo(&wbo);
    let objective = pbo.objective.as_ref().unwrap();

    assert_eq!(brute_force_optimal(&pbo, objective), Some(5));

    match solve_optimize_native(&pbo, objective) {
        PbCdclResult::Optimal(model, value) => {
            assert_eq!(value, 5, "violated soft equality must pay its weight");
            assert_model_valid(&pbo, &model, "wbo soft equality violated");
            assert!(
                !eval_constraint(&wbo.soft_constraints[0].1, &model[..wbo.num_vars as usize]),
                "hard constraints should force the soft equality to be violated"
            );
            assert!(
                model[wbo.num_vars as usize],
                "relaxation variable must be enabled when equality is violated"
            );
        }
        other => panic!("expected Optimal for violated soft equality, got {other:?}"),
    }
}

#[test]
fn test_wbo_hard_plus_soft() {
    // Hard: x1 + x2 >= 2 (both must be true)
    // Soft (cost 1): ~x1 >= 1 (wants x1 false — impossible with hard)
    // Soft (cost 1): ~x2 >= 1 (wants x2 false — impossible with hard)
    // Both soft violated, cost = 2
    let wbo_str = "soft: 10 ;\n\
                    +1 x1 +1 x2 >= 2 ;\n\
                    [1] +1 ~x1 >= 1 ;\n\
                    [1] +1 ~x2 >= 1 ;\n";
    let wbo = parse_wbo(wbo_str).unwrap();
    let pbo = wbo_to_pbo(&wbo);
    let objective = pbo.objective.as_ref().unwrap();

    let result = solve_optimize_native(&pbo, objective);
    match result {
        PbCdclResult::Optimal(model, value) => {
            assert_eq!(value, 2, "both soft must be violated, cost=2");
            assert_model_valid(&pbo, &model, "wbo hard+soft");
        }
        PbCdclResult::Feasible(model, value) => {
            assert_model_valid(&pbo, &model, "wbo hard+soft feasible");
            // Value must be at least 2 since both soft are violated
            assert!(value >= 2, "cost must be >= 2");
        }
        other => panic!("expected Optimal/Feasible for WBO hard+soft, got {other:?}"),
    }
}

#[test]
fn test_wbo_to_pbo_conversion_correctness() {
    // Verify the WBO->PBO conversion preserves structure
    let wbo_str = "soft: 100 ;\n\
                    +1 x1 +1 x2 >= 1 ;\n\
                    [5] +1 x3 >= 1 ;\n\
                    [3] +1 x4 >= 1 ;\n";
    let wbo = parse_wbo(wbo_str).unwrap();
    let pbo = wbo_to_pbo(&wbo);

    // Should have 4 original + 2 relaxation vars
    assert_eq!(pbo.num_vars, 6);
    // 1 hard + 2 relaxed soft
    assert_eq!(pbo.constraints.len(), 3);
    // Objective has 2 terms for relaxation variables
    let obj = pbo.objective.as_ref().unwrap();
    assert_eq!(obj.terms.len(), 2);
    assert_eq!(obj.terms[0].coeff, 5);
    assert_eq!(obj.terms[1].coeff, 3);
}

// ===========================================================================
// EDGE CASES / REGRESSION TESTS
// ===========================================================================

#[test]
fn test_edge_empty_constraint_rhs_zero() {
    // No terms, rhs 0: 0 >= 0 is trivially SAT
    let instance = PbInstance {
        num_vars: 1,
        num_constraints: 1,
        constraints: vec![ay_pb::PbConstraint {
            terms: vec![],
            rel: ay_pb::PbRel::Ge,
            rhs: 0,
        }],
        objective: None,
    };
    let result = solve_native(&instance);
    assert!(
        matches!(result, PbCdclResult::Satisfiable(_)),
        "empty constraint rhs=0 must be SAT, got {result:?}"
    );
}

#[test]
fn test_edge_negative_coefficient() {
    // +2 x1 -1 x2 >= 1
    // x1=T, x2=T: 2-1=1>=1 OK. x1=T, x2=F: 2>=1 OK.
    // x1=F, x2=T: -1<1 FAIL. x1=F, x2=F: 0<1 FAIL.
    let instance = parse("+2 x1 -1 x2 >= 1 ;\n");
    let result = solve_native(&instance);
    match result {
        PbCdclResult::Satisfiable(model) => {
            assert!(model[0], "x1 must be true for 2x1-x2>=1");
            assert_model_valid(&instance, &model, "negative coefficient");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_edge_negative_rhs() {
    // +1 x1 >= -5: trivially SAT (any assignment works since 0 >= -5)
    cross_validate_decision("+1 x1 >= -5 ;\n", true, "negative rhs");
}

#[test]
fn test_edge_large_coefficients_near_overflow() {
    // Use coefficients near i64::MAX / 2 to stress arithmetic
    let large = i64::MAX / 4;
    let opb = format!("+{large} x1 +{large} x2 >= {large} ;\n");
    let instance = parse(&opb);
    let result = solve_native(&instance);
    match result {
        PbCdclResult::Satisfiable(model) => {
            assert_model_valid(&instance, &model, "large coefficients near overflow");
        }
        other => panic!("expected SAT for large coefficients, got {other:?}"),
    }
}

#[test]
fn test_edge_objective_with_zero_coefficient() {
    // min 0*x1 + 1*x2 subject to x1 + x2 >= 1
    // The 0-coefficient term should be harmless
    // Optimal: x1=T, x2=F -> cost = 0
    validate_optimization(
        "* #variable= 2 #constraint= 1\nmin: +0 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n",
        0,
        "zero coefficient in objective",
    );
}

#[test]
fn test_edge_all_negated_constraint() {
    // ~x1 + ~x2 + ~x3 >= 3 means all must be false
    let instance = parse("+1 ~x1 +1 ~x2 +1 ~x3 >= 3 ;\n");
    let result = solve_native(&instance);
    match result {
        PbCdclResult::Satisfiable(model) => {
            assert!(
                !model[0] && !model[1] && !model[2],
                "all vars must be false for ~x1+~x2+~x3>=3"
            );
            assert_model_valid(&instance, &model, "all negated constraint");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_edge_single_equality_forces_value() {
    // x1 = 1 means x1 must be true
    let instance = parse("+1 x1 = 1 ;\n");
    let result = solve_native(&instance);
    match result {
        PbCdclResult::Satisfiable(model) => {
            assert!(model[0], "x1 must be true for x1=1");
            assert_model_valid(&instance, &model, "single equality forces value");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_edge_tautological_constraint() {
    // x1 + ~x1 >= 1 is always true (tautological)
    cross_validate_decision("+1 x1 +1 ~x1 >= 1 ;\n", true, "tautological x1 + ~x1 >= 1");
}

#[test]
fn test_edge_many_variables_at_least_one() {
    // x1 + x2 + ... + x10 >= 1
    let instance = parse(
        "* #variable= 10 #constraint= 1\n\
         +1 x1 +1 x2 +1 x3 +1 x4 +1 x5 +1 x6 +1 x7 +1 x8 +1 x9 +1 x10 >= 1 ;\n",
    );
    let result = solve_native(&instance);
    match result {
        PbCdclResult::Satisfiable(model) => {
            let any_true = model.iter().any(|&v| v);
            assert!(any_true, "at least one variable must be true");
            assert_model_valid(&instance, &model, "10 vars at-least-1");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

#[test]
fn test_edge_rhs_equals_sum_of_coefficients() {
    // 2*x1 + 3*x2 + 5*x3 >= 10, max sum = 10, so all must be true
    let instance = parse("+2 x1 +3 x2 +5 x3 >= 10 ;\n");
    let result = solve_native(&instance);
    match result {
        PbCdclResult::Satisfiable(model) => {
            assert!(
                model[0] && model[1] && model[2],
                "all must be true when rhs = sum of coefficients"
            );
            assert_model_valid(&instance, &model, "rhs = sum of coeffs");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// ===========================================================================
// CROSS-VALIDATION: BATCH TEST
// ===========================================================================

/// Runs cross-validation on every SAT decision instance in the test suite.
/// This is the ultimate "zero wrong answers" check.
#[test]
fn test_cross_validation_batch() {
    let sat_instances = [
        ("+1 x1 >= 1 ;\n", true, "trivial"),
        ("+1 x1 +1 x2 +1 x3 >= 2 ;\n", true, "card-2-of-3"),
        ("+3 x1 +2 x2 +1 x3 >= 4 ;\n", true, "weighted-3-2-1"),
        (
            "+1 x1 +1 ~x2 >= 1 ;\n+1 ~x1 +1 x2 >= 1 ;\n",
            true,
            "mixed-neg",
        ),
        ("+1 x1 >= 1 ;\n+1 ~x1 >= 1 ;\n", false, "contradiction"),
        ("+3 x1 +2 x2 >= 6 ;\n", false, "coeff-forced"),
        ("+1 x1 +1 x2 = 1 ;\n", true, "eq-exactly-one"),
        ("+1 x1 +1 x2 = 3 ;\n", false, "eq-impossible"),
        ("+1 ~x1 +1 ~x2 >= 1 ;\n", true, "at-most-one-neg"),
        ("+1 x1 +1 ~x1 >= 1 ;\n", true, "tautology"),
        ("+1 x1 >= -5 ;\n", true, "negative-rhs"),
    ];

    for (opb, expected_sat, label) in sat_instances {
        cross_validate_decision(opb, expected_sat, label);
    }
}

/// For every optimization instance, verify the claimed optimum matches brute force.
#[test]
fn test_optimization_batch_brute_force() {
    let opt_instances = [
        (
            "min: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n",
            1,
            "min-x1+x2-geq1",
        ),
        (
            "min: +3 x1 +2 x2 +1 x3 ;\n+1 x1 +1 x2 +1 x3 >= 2 ;\n",
            3,
            "weighted-opt-geq2",
        ),
        ("min: +1 x2 ;\n+1 x1 >= 1 ;\n", 0, "zero-cost-opt"),
        (
            "min: +1 x1 +1 x2 +1 x3 ;\n+1 x1 +1 x2 +1 x3 >= 3 ;\n",
            3,
            "all-true-opt",
        ),
        (
            "* #variable= 4 #constraint= 2\nmin: +2 x1 +3 x2 +5 x3 +7 x4 ;\n\
             +1 x1 +1 x2 +1 x3 +1 x4 >= 2 ;\n\
             +1 ~x1 +1 ~x2 +1 ~x3 +1 ~x4 >= 2 ;\n",
            5,
            "exactly-2-cheapest",
        ),
        (
            "min: +1 ~x1 +1 ~x2 ;\n+1 x1 +1 x2 >= 1 ;\n",
            0,
            "negated-obj-opt",
        ),
    ];

    for (opb, expected_opt, label) in opt_instances {
        validate_optimization(opb, expected_opt, label);
    }
}

// ===========================================================================
// PARSER ROUND-TRIP
// ===========================================================================

#[test]
fn test_parser_accepts_comment_lines() {
    let opb = "* This is a comment\n* #variable= 2 #constraint= 1\n+1 x1 +1 x2 >= 1 ;\n";
    let instance = parse(opb);
    assert_eq!(instance.constraints.len(), 1);
}

#[test]
fn test_parser_no_header() {
    // OPB without the * #variable=... header
    let opb = "+1 x1 +1 x2 >= 1 ;\n";
    let instance = parse(opb);
    assert_eq!(instance.constraints.len(), 1);
    assert!(instance.num_vars >= 2, "should infer at least 2 variables");
}

#[test]
fn test_parser_equality_constraint() {
    let opb = "+1 x1 +1 x2 = 1 ;\n";
    let instance = parse(opb);
    assert_eq!(instance.constraints[0].rel, ay_pb::PbRel::Eq);
    assert_eq!(instance.constraints[0].rhs, 1);
}

#[test]
fn test_parser_optimization_header() {
    let opb = "min: +3 x1 +2 x2 ;\n+1 x1 +1 x2 >= 1 ;\n";
    let instance = parse(opb);
    assert!(instance.objective.is_some(), "should parse objective");
    let obj = instance.objective.as_ref().unwrap();
    assert_eq!(obj.terms.len(), 2);
    assert_eq!(obj.terms[0].coeff, 3);
    assert_eq!(obj.terms[1].coeff, 2);
}

#[test]
fn test_parser_rejects_missing_semicolon_on_objective() {
    let err = parse_opb("min: +3 x1 +2 x2\n+1 x1 +1 x2 >= 1 ;\n")
        .expect_err("objective line without semicolon must be rejected");
    assert!(matches!(err, ParseError::ExpectedSemicolon { line: 1 }));
}

#[test]
fn test_wbo_parser_round_trip() {
    let wbo_str = "soft: 10 ;\n\
                    +1 x1 +1 x2 >= 1 ;\n\
                    [5] +1 x3 >= 1 ;\n";
    let wbo = parse_wbo(wbo_str).unwrap();
    assert_eq!(wbo.top_cost, Some(10));
    assert_eq!(wbo.hard_constraints.len(), 1);
    assert_eq!(wbo.soft_constraints.len(), 1);
    assert_eq!(wbo.soft_constraints[0].0, 5);
}

#[test]
fn test_wbo_parser_rejects_missing_semicolon_on_soft_decl() {
    let err = parse_wbo("soft: 10\n[5] +1 x3 >= 1 ;\n")
        .expect_err("soft declaration without semicolon must be rejected");
    assert!(matches!(err, ParseError::ExpectedSemicolon { line: 1 }));
}

// ===========================================================================
// PREPROCESSING SOUNDNESS
// ===========================================================================

#[test]
fn test_preprocessing_does_not_flip_sat_to_unsat() {
    let sat_instances = [
        "+1 x1 >= 1 ;\n",
        "+1 x1 +1 x2 +1 x3 >= 2 ;\n",
        "+3 x1 +2 x2 +1 x3 >= 4 ;\n",
        "+1 x1 +1 x2 +1 x3 = 1 ;\n",
    ];

    for opb in sat_instances {
        let instance = parse(opb);
        let result = solve_native(&instance);
        assert!(
            matches!(result, PbCdclResult::Satisfiable(_)),
            "preprocessing must not make SAT instance UNSAT: {opb}"
        );
    }
}

#[test]
fn test_preprocessing_does_not_flip_unsat_to_sat() {
    let unsat_instances = [
        "+1 x1 >= 1 ;\n+1 ~x1 >= 1 ;\n",
        "+3 x1 +2 x2 >= 6 ;\n",
        "+1 x1 +1 x2 = 3 ;\n",
    ];

    for opb in unsat_instances {
        let instance = parse(opb);
        let result = solve_native(&instance);
        assert_eq!(
            result,
            PbCdclResult::Unsatisfiable,
            "preprocessing must not make UNSAT instance SAT: {opb}"
        );
    }
}

// ===========================================================================
// MODEL VERIFICATION STRESS
// ===========================================================================

/// For every instance that returns SAT, verify EVERY constraint individually.
/// This catches subtle bugs where verify_all_constraints might mask individual failures.
#[test]
fn test_individual_constraint_verification() {
    let sat_instances = [
        "+1 x1 +1 x2 +1 x3 >= 2 ;\n+1 x1 >= 1 ;\n",
        "+1 ~x1 +1 ~x2 +1 ~x3 >= 2 ;\n+1 x1 +1 x2 +1 x3 >= 1 ;\n",
        "+1 x1 +1 x2 +1 x3 = 2 ;\n+1 x1 >= 1 ;\n+1 x3 >= 1 ;\n",
    ];

    for opb in sat_instances {
        let instance = parse(opb);
        let result = solve_native(&instance);
        if let PbCdclResult::Satisfiable(model) = result {
            for (i, constraint) in instance.constraints.iter().enumerate() {
                assert!(
                    eval_constraint(constraint, &model),
                    "constraint {i} violated in instance: {opb}\nconstraint: {constraint:?}\nmodel: {model:?}"
                );
            }
        }
    }
}
