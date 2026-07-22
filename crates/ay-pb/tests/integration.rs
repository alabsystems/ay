// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for the ay-pb pseudo-Boolean solver.
//!
//! Tests parse real OPB-format instances, solve them via both SAT encoding
//! and native CDCL, then verify results are correct:
//! - SAT: model satisfies ALL original constraints
//! - UNSAT: both solver paths agree
//! - Optimization: optimal value is verified and both paths agree
//! - Preprocessing: does not change satisfiability

use ay_pb::{
    parse_opb, verify_all_constraints, CnfEncoder, PbCdclResult, PbCdclSolver, PbInstance,
    PbObjective,
};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Loads an OPB instance from the tests/instances/ directory.
fn load_instance(name: &str) -> PbInstance {
    let path = format!("{}/tests/instances/{name}", env!("CARGO_MANIFEST_DIR"));
    let content =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("failed to read {path}: {e}"));
    parse_opb(&content).unwrap_or_else(|e| panic!("failed to parse {path}: {e}"))
}

/// Solves a decision instance with native CDCL and returns the result.
fn solve_native(instance: &PbInstance) -> PbCdclResult {
    let mut solver = PbCdclSolver::new(instance);
    solver.solve()
}

/// Solves an optimization instance with native CDCL.
fn solve_optimize_native(instance: &PbInstance, objective: &PbObjective) -> PbCdclResult {
    let mut solver = PbCdclSolver::new(instance);
    solver.solve_optimize(objective, None)
}

/// Evaluates the objective function on a model (assignment indexed 0..num_vars-1).
fn eval_obj(objective: &PbObjective, model: &[bool]) -> i128 {
    ay_pb::eval_objective(objective, model)
}

/// Verifies that every constraint in the instance is satisfied by `model`.
fn assert_model_valid(instance: &PbInstance, model: &[bool], context: &str) {
    assert!(
        verify_all_constraints(&instance.constraints, model),
        "{context}: model fails constraint verification. model={model:?}"
    );
}

/// Solves a decision instance via SAT encoding and brute-force checking.
/// Returns true if SAT (any assignment satisfies all encoded clauses), false if UNSAT.
fn solve_via_encoding(instance: &PbInstance) -> Option<Vec<bool>> {
    let encoded = CnfEncoder::encode_instance(instance);
    let num_vars = encoded.num_vars as usize;

    // For small instances, brute-force all assignments.
    if num_vars > 20 {
        // Skip brute force for large instances.
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
            // Extract original variables only.
            let orig_model: Vec<bool> = assignment[..instance.num_vars as usize].to_vec();
            return Some(orig_model);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// SAT instance tests
// ---------------------------------------------------------------------------

#[test]
fn test_sat_simple_native_cdcl() {
    let instance = load_instance("sat_simple.opb");
    assert_eq!(instance.num_vars, 3);
    assert_eq!(instance.constraints.len(), 2);

    let result = solve_native(&instance);
    match result {
        PbCdclResult::Satisfiable(model) => {
            assert_eq!(model.len(), 3);
            assert_model_valid(&instance, &model, "sat_simple native");
        }
        other => panic!("expected SAT for sat_simple.opb, got {other:?}"),
    }
}

#[test]
fn test_sat_simple_encoding_agrees() {
    let instance = load_instance("sat_simple.opb");

    // Native CDCL says SAT.
    let native_result = solve_native(&instance);
    assert!(
        matches!(native_result, PbCdclResult::Satisfiable(_)),
        "native should say SAT"
    );

    // Encoding should also find a satisfying assignment.
    let encoding_model = solve_via_encoding(&instance);
    assert!(
        encoding_model.is_some(),
        "encoding should also find SAT for sat_simple.opb"
    );

    // Verify encoding model satisfies original constraints.
    let model = encoding_model.unwrap();
    assert_model_valid(&instance, &model, "sat_simple encoding");
}

// ---------------------------------------------------------------------------
// UNSAT instance tests
// ---------------------------------------------------------------------------

#[test]
fn test_unsat_simple_native_cdcl() {
    let instance = load_instance("unsat_simple.opb");
    let result = solve_native(&instance);
    assert_eq!(
        result,
        PbCdclResult::Unsatisfiable,
        "unsat_simple.opb should be UNSAT"
    );
}

#[test]
fn test_unsat_simple_encoding_agrees() {
    let instance = load_instance("unsat_simple.opb");

    // Native says UNSAT.
    assert_eq!(solve_native(&instance), PbCdclResult::Unsatisfiable);

    // Encoding brute force should also find no solution.
    let encoding_model = solve_via_encoding(&instance);
    assert!(
        encoding_model.is_none(),
        "encoding should also find UNSAT for unsat_simple.opb"
    );
}

// ---------------------------------------------------------------------------
// Cardinality constraint tests
// ---------------------------------------------------------------------------

#[test]
fn test_cardinality_3of5_native() {
    let instance = load_instance("cardinality_3of5.opb");
    assert_eq!(instance.num_vars, 5);
    assert_eq!(instance.constraints.len(), 2);

    let result = solve_native(&instance);
    match result {
        PbCdclResult::Satisfiable(model) => {
            assert_eq!(model.len(), 5);
            let true_count = model.iter().filter(|&&v| v).count();
            assert!(
                (3..=4).contains(&true_count),
                "cardinality_3of5: expected 3 or 4 true, got {true_count}"
            );
            assert_model_valid(&instance, &model, "cardinality_3of5 native");
        }
        other => panic!("expected SAT for cardinality_3of5.opb, got {other:?}"),
    }
}

#[test]
fn test_cardinality_3of5_encoding_agrees() {
    let instance = load_instance("cardinality_3of5.opb");

    let native_sat = matches!(solve_native(&instance), PbCdclResult::Satisfiable(_));
    let encoding_model = solve_via_encoding(&instance);
    let encoding_sat = encoding_model.is_some();

    assert_eq!(
        native_sat, encoding_sat,
        "native and encoding must agree on SAT/UNSAT for cardinality_3of5.opb"
    );

    if let Some(model) = encoding_model {
        assert_model_valid(&instance, &model, "cardinality_3of5 encoding");
    }
}

// ---------------------------------------------------------------------------
// Non-linear constraint tests
// ---------------------------------------------------------------------------

#[test]
fn test_nlc_product_native() {
    let instance = load_instance("nlc_product.opb");
    assert_eq!(instance.num_vars, 3);

    // Linearize before solving with native CDCL (native handles linear only).
    let linearized = ay_pb::linearize(&instance);
    let result = solve_native(&linearized);
    match result {
        PbCdclResult::Satisfiable(model) => {
            // Verify against linearized constraints.
            assert_model_valid(&linearized, &model, "nlc_product linearized native");

            // Also verify against original constraints (project to original vars).
            let orig_model: Vec<bool> = model[..instance.num_vars as usize].to_vec();
            assert_model_valid(&instance, &orig_model, "nlc_product original");
        }
        other => panic!("expected SAT for nlc_product.opb (linearized), got {other:?}"),
    }
}

#[test]
fn test_nlc_product_encoding_agrees() {
    let instance = load_instance("nlc_product.opb");

    // Encoding handles non-linear terms natively via AND-variable linearization.
    let encoding_model = solve_via_encoding(&instance);
    assert!(
        encoding_model.is_some(),
        "encoding should find SAT for nlc_product.opb"
    );
    let model = encoding_model.unwrap();
    assert_model_valid(&instance, &model, "nlc_product encoding");
}

// ---------------------------------------------------------------------------
// Optimization tests
// ---------------------------------------------------------------------------

#[test]
fn test_opt_pigeonhole_native() {
    let instance = load_instance("opt_pigeonhole.opb");
    assert!(
        instance.objective.is_some(),
        "pigeonhole should have objective"
    );
    let objective = instance.objective.as_ref().unwrap();

    let result = solve_optimize_native(&instance, objective);
    match result {
        PbCdclResult::Optimal(model, value) => {
            assert_model_valid(&instance, &model, "opt_pigeonhole");
            let computed = eval_obj(objective, &model);
            assert_eq!(
                computed, value,
                "objective evaluation must match claimed optimal"
            );
            // Verify via brute force.
            let num_vars = instance.num_vars as usize;
            let mut brute_opt = i128::MAX;
            for mask in 0..(1u64 << num_vars) {
                let a: Vec<bool> = (0..num_vars).map(|i| (mask >> i) & 1 == 1).collect();
                if verify_all_constraints(&instance.constraints, &a) {
                    let v = eval_obj(objective, &a);
                    if v < brute_opt {
                        brute_opt = v;
                    }
                }
            }
            assert_eq!(
                value, brute_opt,
                "solver optimal must match brute-force optimal"
            );
        }
        PbCdclResult::Feasible(model, value) => {
            // Accept feasible if solver times out, but verify model is valid.
            assert_model_valid(&instance, &model, "opt_pigeonhole feasible");
            let computed = eval_obj(objective, &model);
            assert_eq!(computed, value);
        }
        other => panic!("expected Optimal or Feasible for opt_pigeonhole.opb, got {other:?}"),
    }
}

#[test]
fn test_weighted_opt_native() {
    let instance = load_instance("weighted_opt.opb");
    assert!(instance.objective.is_some());
    let objective = instance.objective.as_ref().unwrap();

    let result = solve_optimize_native(&instance, objective);
    match result {
        PbCdclResult::Optimal(model, value) => {
            assert_model_valid(&instance, &model, "weighted_opt");
            let computed = eval_obj(objective, &model);
            assert_eq!(computed, value, "objective must match evaluation");

            // With exactly-2 constraint and costs [2,3,5,7], optimal is x1+x2=5.
            assert_eq!(value, 5, "optimal value should be 5 (x1=2 + x2=3)");

            let true_count = model.iter().filter(|&&v| v).count();
            assert_eq!(true_count, 2, "exactly 2 variables must be true");
        }
        PbCdclResult::Feasible(model, value) => {
            assert_model_valid(&instance, &model, "weighted_opt feasible");
            let computed = eval_obj(objective, &model);
            assert_eq!(computed, value);
        }
        other => panic!("expected Optimal or Feasible for weighted_opt.opb, got {other:?}"),
    }
}

#[test]
fn test_weighted_opt_optimality_proof() {
    // Verify that the claimed optimal is truly optimal by checking that
    // no feasible solution with a lower objective exists.
    let instance = load_instance("weighted_opt.opb");
    let objective = instance.objective.as_ref().unwrap();

    let result = solve_optimize_native(&instance, objective);
    if let PbCdclResult::Optimal(_, opt_value) = result {
        // Brute-force: find the minimum objective among all feasible assignments.
        let num_vars = instance.num_vars as usize;
        let mut best_brute = i128::MAX;
        for mask in 0..(1u64 << num_vars) {
            let assignment: Vec<bool> = (0..num_vars).map(|i| (mask >> i) & 1 == 1).collect();
            if verify_all_constraints(&instance.constraints, &assignment) {
                let obj_val = eval_obj(objective, &assignment);
                if obj_val < best_brute {
                    best_brute = obj_val;
                }
            }
        }
        assert_eq!(
            opt_value, best_brute,
            "solver optimal ({opt_value}) must match brute-force optimal ({best_brute})"
        );
    }
}

// ---------------------------------------------------------------------------
// Preprocessing soundness tests
// ---------------------------------------------------------------------------

#[test]
fn test_preprocessing_preserves_sat_simple() {
    let instance = load_instance("sat_simple.opb");

    // Solve without preprocessing (raw instance, solver preprocesses internally).
    let result = solve_native(&instance);
    assert!(
        matches!(result, PbCdclResult::Satisfiable(_)),
        "sat_simple should be SAT through preprocessing"
    );
}

#[test]
fn test_preprocessing_preserves_unsat_simple() {
    let instance = load_instance("unsat_simple.opb");
    let result = solve_native(&instance);
    assert_eq!(
        result,
        PbCdclResult::Unsatisfiable,
        "unsat_simple should remain UNSAT through preprocessing"
    );
}

#[test]
fn test_preprocessing_preserves_cardinality() {
    let instance = load_instance("cardinality_3of5.opb");
    let result = solve_native(&instance);
    match result {
        PbCdclResult::Satisfiable(model) => {
            assert_model_valid(&instance, &model, "cardinality_3of5 after preprocessing");
        }
        other => panic!("cardinality_3of5 should remain SAT through preprocessing, got {other:?}"),
    }
}

#[test]
fn test_preprocess_explicit_api() {
    // Test the preprocess API directly to verify it doesn't change satisfiability.
    let instance = load_instance("sat_simple.opb");
    let preprocessed = ay_pb::preprocess(&instance);
    match preprocessed {
        ay_pb::PreprocessResult::Simplified {
            instance: simplified,
            fixed_literals,
        } => {
            // The simplified instance should be satisfiable.
            let mut solver = PbCdclSolver::new(&simplified);
            let result = solver.solve();
            match result {
                PbCdclResult::Satisfiable(mut model) => {
                    // Apply fixed literals to model.
                    for (&var, &val) in &fixed_literals {
                        let idx = (var - 1) as usize;
                        if idx < model.len() {
                            model[idx] = val;
                        }
                    }
                    // Verify against original constraints.
                    // Need a full-length model covering all original variables.
                    let full_model: Vec<bool> = (0..instance.num_vars as usize)
                        .map(|i| {
                            let var = (i + 1) as u32;
                            if let Some(&val) = fixed_literals.get(&var) {
                                val
                            } else if i < model.len() {
                                model[i]
                            } else {
                                false
                            }
                        })
                        .collect();
                    assert_model_valid(&instance, &full_model, "preprocess explicit SAT");
                }
                PbCdclResult::Unsatisfiable => {
                    panic!("sat_simple should not become UNSAT after preprocessing")
                }
                _ => {} // Unknown is acceptable.
            }
        }
        ay_pb::PreprocessResult::Unsatisfiable => {
            panic!("sat_simple should not be detected as UNSAT during preprocessing");
        }
        _ => {
            panic!("unexpected PreprocessResult variant");
        }
    }
}

// ---------------------------------------------------------------------------
// Cross-validation: native CDCL vs encoding on all instances
// ---------------------------------------------------------------------------

#[test]
fn test_all_instances_native_and_encoding_agree_on_sat_unsat() {
    let decision_instances = [
        ("sat_simple.opb", true),
        ("unsat_simple.opb", false),
        ("cardinality_3of5.opb", true),
    ];

    for (name, expected_sat) in decision_instances {
        let instance = load_instance(name);

        // Native CDCL.
        let native_result = solve_native(&instance);
        let native_sat = matches!(native_result, PbCdclResult::Satisfiable(_));
        assert_eq!(
            native_sat, expected_sat,
            "{name}: native CDCL expected SAT={expected_sat}, got SAT={native_sat}"
        );

        // Encoding brute force (only for small instances).
        if instance.num_vars <= 20 && ay_pb::is_linear(&instance) {
            let encoding_model = solve_via_encoding(&instance);
            let encoding_sat = encoding_model.is_some();
            assert_eq!(
                native_sat, encoding_sat,
                "{name}: native and encoding disagree on SAT/UNSAT"
            );
        }
    }
}

// ---------------------------------------------------------------------------
// Model verification stress: every SAT result must pass constraint check
// ---------------------------------------------------------------------------

#[test]
fn test_model_verification_on_all_sat_instances() {
    let sat_instances = ["sat_simple.opb", "cardinality_3of5.opb"];

    for name in sat_instances {
        let instance = load_instance(name);
        let result = solve_native(&instance);
        if let PbCdclResult::Satisfiable(model) = result {
            // Verify every single constraint individually.
            for (i, constraint) in instance.constraints.iter().enumerate() {
                let satisfied = ay_pb::eval_constraint(constraint, &model);
                assert!(
                    satisfied,
                    "{name}: constraint {i} violated by model. constraint={constraint:?}, model={model:?}"
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Optimization cross-validation via brute force
// ---------------------------------------------------------------------------

#[test]
fn test_opt_pigeonhole_brute_force_optimality() {
    let instance = load_instance("opt_pigeonhole.opb");
    let objective = instance.objective.as_ref().unwrap();

    let result = solve_optimize_native(&instance, objective);
    if let PbCdclResult::Optimal(_, solver_opt) = result {
        // Brute-force all 2^6 = 64 assignments.
        let num_vars = instance.num_vars as usize;
        let mut brute_opt = i128::MAX;
        for mask in 0..(1u64 << num_vars) {
            let assignment: Vec<bool> = (0..num_vars).map(|i| (mask >> i) & 1 == 1).collect();
            if verify_all_constraints(&instance.constraints, &assignment) {
                let val = eval_obj(objective, &assignment);
                if val < brute_opt {
                    brute_opt = val;
                }
            }
        }
        assert_eq!(
            solver_opt, brute_opt,
            "pigeonhole: solver optimal ({solver_opt}) != brute-force optimal ({brute_opt})"
        );
    }
}

// ---------------------------------------------------------------------------
// Linearization + solve pipeline for NLC instances
// ---------------------------------------------------------------------------

#[test]
fn test_nlc_linearize_then_solve_preserves_satisfiability() {
    let instance = load_instance("nlc_product.opb");
    assert!(
        !ay_pb::is_linear(&instance),
        "nlc_product should have non-linear terms"
    );

    let linearized = ay_pb::linearize(&instance);
    assert!(
        ay_pb::is_linear(&linearized),
        "linearized instance should be fully linear"
    );

    // Solve linearized.
    let result = solve_native(&linearized);
    match result {
        PbCdclResult::Satisfiable(model) => {
            // Verify against linearized constraints (including auxiliary).
            assert_model_valid(&linearized, &model, "nlc linearized");
            // Project to original variables and verify original constraints.
            let orig_model: Vec<bool> = model[..instance.num_vars as usize].to_vec();
            assert_model_valid(&instance, &orig_model, "nlc original projected");
        }
        other => panic!("nlc_product should be SAT after linearization, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Edge case: empty objective optimization
// ---------------------------------------------------------------------------

#[test]
fn test_optimize_with_zero_cost_objective() {
    // Instance where objective can be driven to 0.
    let input = "* #variable= 2 #constraint= 1\nmin: +1 x2 ;\n+1 x1 >= 1 ;\n";
    let instance = parse_opb(input).unwrap();
    let objective = instance.objective.as_ref().unwrap();

    let mut solver = PbCdclSolver::new(&instance);
    let result = solver.solve_optimize(objective, None);
    match result {
        PbCdclResult::Optimal(model, value) => {
            assert_eq!(value, 0, "x2 can be false while x1=true");
            assert!(model[0], "x1 must be true");
            assert!(!model[1], "x2 should be false for cost 0");
            assert_model_valid(&instance, &model, "zero cost opt");
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Equality constraint integration
// ---------------------------------------------------------------------------

#[test]
fn test_equality_constraint_exactly_one() {
    let input = "* #variable= 3 #constraint= 1\n+1 x1 +1 x2 +1 x3 = 1 ;\n";
    let instance = parse_opb(input).unwrap();

    let result = solve_native(&instance);
    match result {
        PbCdclResult::Satisfiable(model) => {
            let true_count = model.iter().filter(|&&v| v).count();
            assert_eq!(true_count, 1, "exactly one variable should be true for =1");
            assert_model_valid(&instance, &model, "equality =1");
        }
        other => panic!("expected SAT for x1+x2+x3=1, got {other:?}"),
    }
}

#[test]
fn test_equality_constraint_unsat_overconstrained() {
    // x1 + x2 = 0 AND x1 >= 1 (x1 must be true but sum must be 0)
    let input = "+1 x1 +1 x2 = 0 ;\n+1 x1 >= 1 ;\n";
    let instance = parse_opb(input).unwrap();

    let result = solve_native(&instance);
    assert_eq!(
        result,
        PbCdclResult::Unsatisfiable,
        "x1+x2=0 with x1>=1 should be UNSAT"
    );
}

// ---------------------------------------------------------------------------
// Larger cardinality: at-most-k via PB constraints
// ---------------------------------------------------------------------------

#[test]
fn test_at_most_2_of_4() {
    // At most 2 of 4: ~x1+~x2+~x3+~x4 >= 2 (at most 2 true)
    // At least 1: x1+x2+x3+x4 >= 1
    let input = "\
* #variable= 4 #constraint= 2
+1 ~x1 +1 ~x2 +1 ~x3 +1 ~x4 >= 2 ;
+1 x1 +1 x2 +1 x3 +1 x4 >= 1 ;
";
    let instance = parse_opb(input).unwrap();

    let result = solve_native(&instance);
    match result {
        PbCdclResult::Satisfiable(model) => {
            let true_count = model.iter().filter(|&&v| v).count();
            assert!(
                (1..=2).contains(&true_count),
                "at-most-2-of-4: expected 1 or 2 true, got {true_count}"
            );
            assert_model_valid(&instance, &model, "at_most_2_of_4");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Negative coefficients in input
// ---------------------------------------------------------------------------

#[test]
fn test_negative_coefficient_constraint() {
    // +2 x1 -1 x2 >= 1 means 2*x1 - x2 >= 1
    // Solutions: x1=T,x2=T (2-1=1>=1), x1=T,x2=F (2-0=2>=1)
    // Not: x1=F,x2=T (0-1=-1<1), x1=F,x2=F (0-0=0<1)
    let input = "+2 x1 -1 x2 >= 1 ;\n";
    let instance = parse_opb(input).unwrap();

    let result = solve_native(&instance);
    match result {
        PbCdclResult::Satisfiable(model) => {
            assert!(model[0], "x1 must be true for 2*x1 - x2 >= 1");
            assert_model_valid(&instance, &model, "negative coeff");
        }
        other => panic!("expected SAT, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Parser round-trip test
// ---------------------------------------------------------------------------

#[test]
fn test_all_instances_parse_successfully() {
    let instances = [
        "sat_simple.opb",
        "unsat_simple.opb",
        "opt_pigeonhole.opb",
        "cardinality_3of5.opb",
        "weighted_opt.opb",
        "nlc_product.opb",
    ];

    for name in instances {
        let instance = load_instance(name);
        assert!(
            instance.num_vars > 0 || instance.constraints.is_empty(),
            "{name}: parsed instance should have variables or be empty"
        );
    }
}
