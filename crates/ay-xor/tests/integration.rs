// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Integration tests for ay-xor with the SAT solver.
//!
//! These tests verify that XorExtension integrates correctly with ay-sat's
//! solve_with_extension() API.

use ay_sat::{parse_dimacs, Literal, SatResult, Solver, Variable};
use ay_xor::{XorConstraint, XorExtension, XorFinder};
use ntest::timeout;
use std::path::PathBuf;

/// Helper to create a literal.
fn lit(var: u32, positive: bool) -> Literal {
    if positive {
        Literal::positive(Variable::new(var))
    } else {
        Literal::negative(Variable::new(var))
    }
}

fn benchmark_path(relative: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(relative)
}

#[test]
#[timeout(10000)]
fn test_xor_extension_simple_sat() {
    // x0 XOR x1 = 1
    // This is satisfiable (e.g., x0=1, x1=0 or x0=0, x1=1)
    let mut solver = Solver::new(2);
    let constraints = vec![XorConstraint::new(vec![0, 1], true)];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    match result {
        SatResult::Sat(model) => {
            // Verify the XOR is satisfied
            let v0 = model[0];
            let v1 = model[1];
            assert!(
                v0 != v1,
                "XOR constraint violated: x0={v0}, x1={v1}, but need x0 XOR x1 = 1"
            );
        }
        _ => panic!("Expected SAT, got {result:?}"),
    }
}

#[test]
#[timeout(10000)]
fn test_xor_extension_simple_unsat() {
    // x0 XOR x1 = 1 AND x0 XOR x1 = 0
    // This is unsatisfiable (contradiction)
    let mut solver = Solver::new(2);
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![0, 1], false),
    ];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    // Fixed: empty clause DB + contradictory XOR extension correctly returns
    // Unsat (was Unknown due to #5806, fixed in #5823).
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "Expected UNSAT, got {result:?}"
    );
}

#[test]
#[timeout(10000)]
fn test_xor_extension_with_cnf_constraints() {
    // Mix XOR and CNF constraints
    // XOR: x0 XOR x1 = 1
    // CNF: x2 must be true
    let mut solver = Solver::new(3);

    // Add CNF constraint: x2 = true
    solver.add_clause(vec![lit(2, true)]);

    let constraints = vec![XorConstraint::new(vec![0, 1], true)];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    match result {
        SatResult::Sat(model) => {
            let v0 = model[0];
            let v1 = model[1];
            let v2 = model[2];

            assert!(v0 != v1, "XOR constraint violated");
            assert!(v2, "CNF constraint violated: x2 should be true");
        }
        _ => panic!("Expected SAT, got {result:?}"),
    }
}

#[test]
#[timeout(10000)]
fn test_xor_extension_chain() {
    // Chain of XORs:
    // x0 XOR x1 = 1
    // x1 XOR x2 = 0
    // x2 XOR x3 = 1
    //
    // Solution must satisfy: x0 != x1, x1 == x2, x2 != x3
    // Example: x0=1, x1=0, x2=0, x3=1
    let mut solver = Solver::new(4);
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![1, 2], false),
        XorConstraint::new(vec![2, 3], true),
    ];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    match result {
        SatResult::Sat(model) => {
            let v0 = model[0];
            let v1 = model[1];
            let v2 = model[2];
            let v3 = model[3];

            assert!(v0 != v1, "x0 XOR x1 = 1 violated");
            assert!(v1 == v2, "x1 XOR x2 = 0 violated");
            assert!(v2 != v3, "x2 XOR x3 = 1 violated");
        }
        _ => panic!("Expected SAT, got {result:?}"),
    }
}

#[test]
#[timeout(10000)]
fn test_xor_extension_unsat_chain() {
    // Unsatisfiable chain:
    // x0 XOR x1 = 1
    // x1 XOR x2 = 1
    // x0 XOR x2 = 1
    //
    // Adding all: (x0 XOR x1) XOR (x1 XOR x2) XOR (x0 XOR x2) = 1 XOR 1 XOR 1 = 1
    // But LHS = 0 (parity of x0, x0, x1, x1, x2, x2 = 0)
    // So 0 = 1, contradiction
    let mut solver = Solver::new(3);
    let constraints = vec![
        XorConstraint::new(vec![0, 1], true),
        XorConstraint::new(vec![1, 2], true),
        XorConstraint::new(vec![0, 2], true),
    ];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    // Fixed: empty clause DB + contradictory XOR extension correctly returns
    // Unsat (was Unknown due to #5806, fixed in #5823).
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "Expected UNSAT for contradictory XOR chain, got {result:?}"
    );
}

#[test]
#[timeout(10000)]
fn test_xor_finder_and_extension_combined() {
    // Use XorFinder to detect XORs from CNF, then solve with XorExtension

    // CNF encoding of x0 XOR x1 = 1:
    // (-x0 OR -x1) forbids (1,1)
    // (x0 OR x1) forbids (0,0)
    let cnf_clauses = vec![
        vec![lit(0, false), lit(1, false)],
        vec![lit(0, true), lit(1, true)],
    ];

    // Detect XORs
    let mut finder = XorFinder::new();
    let xors = finder.find_xors(&cnf_clauses);
    assert_eq!(xors.len(), 1, "Should detect one XOR");

    // Create solver without the CNF clauses (XorExtension handles them)
    let mut solver = Solver::new(2);
    let mut ext = XorExtension::new(xors);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    match result {
        SatResult::Sat(model) => {
            let v0 = model[0];
            let v1 = model[1];
            assert!(v0 != v1, "XOR constraint violated");
        }
        _ => panic!("Expected SAT, got {result:?}"),
    }
}

#[test]
#[timeout(10000)]
fn test_xor_extension_with_forced_values() {
    // x0 XOR x1 = 1
    // Force x0 = true via CNF
    // Should propagate x1 = false
    let mut solver = Solver::new(2);
    solver.add_clause(vec![lit(0, true)]); // Force x0 = true

    let constraints = vec![XorConstraint::new(vec![0, 1], true)];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    match result {
        SatResult::Sat(model) => {
            let v0 = model[0];
            let v1 = model[1];

            assert!(v0, "x0 should be true (forced by CNF)");
            assert!(!v1, "x1 should be false (propagated by XOR)");
        }
        _ => panic!("Expected SAT, got {result:?}"),
    }
}

#[test]
#[timeout(10000)]
fn test_xor_extension_conflict_from_cnf() {
    // x0 XOR x1 = 1
    // Force x0 = true AND x1 = true via CNF
    // This conflicts with the XOR
    let mut solver = Solver::new(2);
    solver.add_clause(vec![lit(0, true)]); // Force x0 = true
    solver.add_clause(vec![lit(1, true)]); // Force x1 = true

    let constraints = vec![XorConstraint::new(vec![0, 1], true)];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    assert!(
        matches!(result, SatResult::Unsat(_)),
        "Expected UNSAT: x0=1, x1=1 violates x0 XOR x1 = 1"
    );
}

#[test]
#[timeout(10000)]
fn test_xor_extension_larger_xor() {
    // 4-variable XOR: x0 XOR x1 XOR x2 XOR x3 = 0
    // Satisfiable with even parity
    let mut solver = Solver::new(4);
    let constraints = vec![XorConstraint::new(vec![0, 1, 2, 3], false)];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    match result {
        SatResult::Sat(model) => {
            let parity: u32 = model.iter().map(|&v| u32::from(v)).sum();
            assert!(
                parity.is_multiple_of(2),
                "XOR=0 violated: parity should be even, got {parity}"
            );
        }
        _ => panic!("Expected SAT, got {result:?}"),
    }
}

#[test]
#[timeout(10000)]
fn test_xor_extension_empty_constraints() {
    // No XOR constraints - should behave like normal SAT
    let mut solver = Solver::new(2);
    solver.add_clause(vec![lit(0, true), lit(1, true)]); // x0 OR x1

    let constraints = vec![];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    assert!(
        matches!(result, SatResult::Sat(_)),
        "Expected SAT with empty XOR constraints"
    );
}

#[test]
#[timeout(10000)]
fn test_xor_extension_unit_initial_propagation() {
    // Single-variable XOR: x0 = 1
    // This should immediately propagate x0 = true
    let mut solver = Solver::new(2);
    solver.add_clause(vec![lit(1, true)]); // x1 must be true

    // x0 = 1 means x0 must be true
    let constraints = vec![XorConstraint::new(vec![0], true)];
    let mut ext = XorExtension::new(constraints);

    let result = solver.solve_with_extension(&mut ext).into_inner();

    match result {
        SatResult::Sat(model) => {
            assert!(model[0], "x0 should be true (unit XOR propagation)");
            assert!(model[1], "x1 should be true (CNF constraint)");
        }
        _ => panic!("Expected SAT, got {result:?}"),
    }
}

/// Generate CNF encoding of XOR: a XOR b = rhs
/// Uses standard 2-clause encoding for 2-var XOR
fn encode_xor_2var(a: u32, b: u32, rhs: bool) -> Vec<Vec<Literal>> {
    if rhs {
        // a XOR b = 1: forbid (0,0) and (1,1)
        vec![
            vec![lit(a, true), lit(b, true)],   // a OR b (forbids 0,0)
            vec![lit(a, false), lit(b, false)], // NOT a OR NOT b (forbids 1,1)
        ]
    } else {
        // a XOR b = 0: forbid (0,1) and (1,0)
        vec![
            vec![lit(a, true), lit(b, false)], // a OR NOT b (forbids 0,1)
            vec![lit(a, false), lit(b, true)], // NOT a OR b (forbids 1,0)
        ]
    }
}

/// Generate CNF encoding of XOR: a XOR b XOR c = rhs
/// Uses the standard 4-clause parity encoding for 3-variable XOR.
fn encode_xor_3var(a: u32, b: u32, c: u32, rhs: bool) -> Vec<Vec<Literal>> {
    let forbidden_assignments = if rhs {
        vec![
            [false, false, false],
            [true, true, false],
            [true, false, true],
            [false, true, true],
        ]
    } else {
        vec![
            [true, false, false],
            [false, true, false],
            [false, false, true],
            [true, true, true],
        ]
    };

    forbidden_assignments
        .into_iter()
        .map(|assignment| {
            [(a, assignment[0]), (b, assignment[1]), (c, assignment[2])]
                .into_iter()
                .map(|(var, value)| {
                    if value {
                        lit(var, false)
                    } else {
                        lit(var, true)
                    }
                })
                .collect()
        })
        .collect()
}

#[test]
#[timeout(10000)]
fn test_xor_finder_detects_five_constraints() {
    let mut clauses = Vec::new();
    clauses.extend(encode_xor_2var(0, 1, true));
    clauses.extend(encode_xor_2var(2, 3, false));
    clauses.extend(encode_xor_2var(4, 5, true));
    clauses.extend(encode_xor_3var(6, 7, 8, true));
    clauses.extend(encode_xor_3var(9, 10, 11, false));

    let mut finder = XorFinder::new();
    let (mut xors, used_indices) = finder.find_xors_with_indices(&clauses);

    xors.sort_by(|lhs, rhs| lhs.vars.cmp(&rhs.vars).then(lhs.rhs.cmp(&rhs.rhs)));

    assert_eq!(
        xors,
        vec![
            XorConstraint::new(vec![0, 1], true),
            XorConstraint::new(vec![2, 3], false),
            XorConstraint::new(vec![4, 5], true),
            XorConstraint::new(vec![6, 7, 8], true),
            XorConstraint::new(vec![9, 10, 11], false),
        ]
    );
    assert_eq!(used_indices.len(), 14, "all XOR clauses should be consumed");
}

#[test]
#[timeout(10000)]
fn test_xor_finder_classifies_mixed_xor_and_non_xor_clauses() {
    let mut clauses = Vec::new();
    clauses.extend(encode_xor_2var(0, 1, true));
    clauses.push(vec![lit(6, true)]);
    clauses.extend(encode_xor_3var(2, 3, 4, false));
    clauses.push(vec![lit(1, true), lit(5, false)]);
    clauses.push(vec![lit(0, false), lit(2, false), lit(6, true)]);

    let mut finder = XorFinder::new();
    let (mut xors, used_indices) = finder.find_xors_with_indices(&clauses);

    xors.sort_by(|lhs, rhs| lhs.vars.cmp(&rhs.vars).then(lhs.rhs.cmp(&rhs.rhs)));

    assert_eq!(
        xors,
        vec![
            XorConstraint::new(vec![0, 1], true),
            XorConstraint::new(vec![2, 3, 4], false),
        ]
    );

    assert_eq!(used_indices.len(), 6);
    assert!(used_indices.contains(&0));
    assert!(used_indices.contains(&1));
    assert!(used_indices.contains(&3));
    assert!(used_indices.contains(&4));
    assert!(used_indices.contains(&5));
    assert!(used_indices.contains(&6));
    assert!(!used_indices.contains(&2));
    assert!(!used_indices.contains(&7));
    assert!(!used_indices.contains(&8));
}

/// Test XOR preprocessing on crypto-style linear system
#[test]
#[timeout(10000)]
fn test_xor_preprocessing_crypto_style() {
    use ay_xor::{preprocess_clauses, solve_with_xor_detection_stats};

    // Create a crypto-style linear system:
    // Chain of XORs that forms a linear system over GF(2)
    // x0 XOR x1 = 1
    // x1 XOR x2 = 0
    // x2 XOR x3 = 1
    // ... etc
    // This is the kind of structure found in hash functions

    let num_vars = 20;
    let mut clauses = Vec::new();

    // Add XOR chain
    for i in 0..(num_vars - 1) {
        let rhs = i % 2 == 0; // alternating 1, 0, 1, 0, ...
        clauses.extend(encode_xor_2var(i as u32, (i + 1) as u32, rhs));
    }

    // Verify preprocessing detects all XORs
    let (remaining, xor_ext) = preprocess_clauses(&clauses);

    assert!(
        remaining.is_empty(),
        "All clauses should be consumed as XOR encoding"
    );
    let ext = xor_ext.expect("Should detect XOR constraints");
    assert_eq!(
        ext.num_constraints(),
        num_vars - 1,
        "Should detect {} XOR constraints",
        num_vars - 1
    );

    // Solve with XOR detection
    let xor_result = solve_with_xor_detection_stats(num_vars, &clauses);

    match xor_result.result.result() {
        SatResult::Sat(model) => {
            // Verify the XOR chain is satisfied
            for i in 0..(num_vars - 1) {
                let expected_xor = i % 2 == 0;
                let actual_xor = model[i] ^ model[i + 1];
                assert_eq!(
                    actual_xor,
                    expected_xor,
                    "XOR chain violated at position {}: x{}={}, x{}={}, expected XOR={}",
                    i,
                    i,
                    model[i],
                    i + 1,
                    model[i + 1],
                    expected_xor
                );
            }
        }
        _ => panic!("Expected SAT, got {:?}", xor_result.result),
    }

    // Verify stats
    assert_eq!(xor_result.stats.xors_detected, num_vars - 1);
    assert_eq!(xor_result.stats.clauses_consumed, (num_vars - 1) * 2);
}

/// Test larger XOR system (more stressful)
#[test]
#[timeout(10000)]
fn test_xor_preprocessing_larger_system() {
    use ay_xor::solve_with_xor_detection_stats;

    // 100 variables, 99 XOR constraints
    let num_vars = 100;
    let mut clauses = Vec::new();

    // Create XOR chain
    for i in 0..(num_vars - 1) {
        let rhs = i % 2 == 0;
        clauses.extend(encode_xor_2var(i as u32, (i + 1) as u32, rhs));
    }

    let xor_result = solve_with_xor_detection_stats(num_vars, &clauses);

    match xor_result.result.result() {
        SatResult::Sat(model) => {
            // Spot check a few constraints
            assert!(model[0] ^ model[1], "x0 XOR x1 should be 1");
            assert!(!(model[1] ^ model[2]), "x1 XOR x2 should be 0");
            assert!(model[98] ^ model[99], "x98 XOR x99 should be 1");
        }
        _ => panic!("Expected SAT, got {:?}", xor_result.result),
    }

    assert_eq!(xor_result.stats.xors_detected, 99);
}

#[test]
#[timeout(10000)]
fn test_two_trees_511v_preprocessing_shape_recovers_partial_xors() {
    use ay_xor::preprocess_clauses_with_stats;

    let content = std::fs::read_to_string(benchmark_path(
        "benchmarks/sat/satcomp2024-sample/16c5482d8e658b54e20d59cfd4b1d588-two-trees-511v.sanitized.cnf",
    ))
    .expect("failed to read two-trees benchmark");
    let formula = parse_dimacs(&content).expect("failed to parse two-trees benchmark");

    let (remaining, xor_ext, stats) = preprocess_clauses_with_stats(&formula.clauses);

    assert!(xor_ext.is_some(), "expected XOR preprocessing on two-trees");
    assert_eq!(stats.xors_detected, 509);
    assert_eq!(stats.clauses_consumed, 1960);
    assert_eq!(remaining.len(), 79);
}

/// Test XOR with additional CNF constraints
#[test]
#[timeout(10000)]
fn test_xor_preprocessing_with_cnf() {
    use ay_xor::solve_with_xor_detection_stats;

    let num_vars = 10;
    let mut clauses = Vec::new();

    // XOR constraints
    clauses.extend(encode_xor_2var(0, 1, true)); // x0 XOR x1 = 1
    clauses.extend(encode_xor_2var(2, 3, false)); // x2 XOR x3 = 0

    // Regular CNF constraints (not XOR patterns)
    clauses.push(vec![lit(0, true)]); // x0 must be true
    clauses.push(vec![lit(4, true), lit(5, false)]); // x4 OR NOT x5

    let xor_result = solve_with_xor_detection_stats(num_vars, &clauses);

    match xor_result.result.result() {
        SatResult::Sat(model) => {
            // x0 = true (from CNF)
            assert!(model[0], "x0 should be true");
            // x0 XOR x1 = 1, so x1 = false
            assert!(
                !model[1],
                "x1 should be false (since x0=true and x0 XOR x1 = 1)"
            );
            // x2 XOR x3 = 0
            assert_eq!(model[2], model[3], "x2 and x3 should be equal");
        }
        _ => panic!("Expected SAT, got {:?}", xor_result.result),
    }

    // Should detect 2 XORs (consuming 4 clauses)
    assert_eq!(xor_result.stats.xors_detected, 2);
    assert_eq!(xor_result.stats.clauses_consumed, 4);
}

/// Acceptance test for #7874: two-trees-511v must solve within the timeout budget.
///
/// This benchmark is a 511-variable, 2039-clause SAT instance dominated by XOR
/// constraints. With partial XOR recovery (binary clause support), the XOR finder
/// detects 509 constraints consuming 1960 clauses, leaving only 79 CNF clauses.
/// Gauss-Jordan elimination then solves the XOR system by pure propagation.
///
/// Prior to partial XOR recovery, the finder detected only 433 constraints (1732
/// consumed, 307 remaining), which left too many clauses for efficient XOR-driven
/// solving and the benchmark timed out at 20s.
#[test]
#[timeout(10000)]
fn test_two_trees_511v_solves_sat_7874() {
    use ay_xor::solve_with_xor_detection_stats;

    let content = std::fs::read_to_string(benchmark_path(
        "benchmarks/sat/satcomp2024-sample/16c5482d8e658b54e20d59cfd4b1d588-two-trees-511v.sanitized.cnf",
    ))
    .expect("failed to read two-trees benchmark");
    let formula = parse_dimacs(&content).expect("failed to parse two-trees benchmark");

    let xor_result = solve_with_xor_detection_stats(formula.num_vars, &formula.clauses);

    // Must solve to SAT
    let model = match xor_result.result.into_inner() {
        SatResult::Sat(model) => model,
        other => panic!(
            "two-trees-511v must be SAT, got {other:?} (XOR stats: {} detected, {} consumed)",
            xor_result.stats.xors_detected, xor_result.stats.clauses_consumed,
        ),
    };

    // Verify the model satisfies all original clauses
    for (clause_idx, clause) in formula.clauses.iter().enumerate() {
        let satisfied = clause.iter().any(|lit| {
            let var_idx = lit.variable().id() as usize;
            let val = model[var_idx];
            if lit.is_positive() {
                val
            } else {
                !val
            }
        });
        assert!(
            satisfied,
            "Model violates original clause {clause_idx}: {clause:?}"
        );
    }
}

/// Verify that XOR-derived UNSAT proofs include DRAT addition records for all
/// theory lemmas and end with the empty clause derivation (#4533).
///
/// The XOR preprocessing extension consumes original CNF clauses and produces
/// theory lemmas via Gauss-Jordan elimination. Each lemma must appear as a
/// DRAT addition line so external proof checkers (drat-trim) can verify the
/// UNSAT certificate.
///
/// Formula:
///   x0 XOR x1 = 1 (CNF: {x0,x1}, {-x0,-x1})
///   x1 XOR x2 = 1 (CNF: {x1,x2}, {-x1,-x2})
///   x0 XOR x2 = 1 (CNF: {x0,x2}, {-x0,-x2})
///
/// The XOR system is contradictory: (x0 XOR x1) XOR (x1 XOR x2) = x0 XOR x2 = 0,
/// but the third constraint says x0 XOR x2 = 1. Gauss-Jordan detects 0 = 1.
#[test]
#[timeout(10000)]
fn test_xor_preprocessing_drat_proof_completeness_4533() {
    use ay_sat::ProofOutput;

    // Contradictory XOR system (all constraints consumed by XOR finder).
    let mut clauses = Vec::new();
    clauses.extend(encode_xor_2var(0, 1, true)); // x0 XOR x1 = 1
    clauses.extend(encode_xor_2var(1, 2, true)); // x1 XOR x2 = 1
    clauses.extend(encode_xor_2var(0, 2, true)); // x0 XOR x2 = 1 (contradicts chain)

    let proof_output = ProofOutput::drat_text(Vec::new());
    let mut solver = Solver::with_proof_output(3, proof_output);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver
        .solve_with_preprocessing_extension::<XorExtension, _>(|active_clauses| {
            let total = active_clauses.len();
            let mut finder = XorFinder::new();
            let (xors, used_indices) = finder.find_xors_with_indices(active_clauses);
            if xors.is_empty() {
                return None;
            }
            let consumed = used_indices.len();
            let remaining = total.saturating_sub(consumed);
            if !ay_xor::should_enable_gauss_elimination(consumed, remaining, xors.len()) {
                return None;
            }
            let frozen_variables: Vec<Variable> = xors
                .iter()
                .flat_map(|xor| xor.vars.iter().copied())
                .collect::<std::collections::HashSet<u32>>()
                .into_iter()
                .map(Variable::new)
                .collect();
            Some(ay_sat::PreparedExtension::new(
                XorExtension::new(xors),
                used_indices.into_iter().collect(),
                frozen_variables,
            ))
        })
        .into_inner();

    assert!(
        result.is_unsat(),
        "Contradictory XOR system must be UNSAT, got {result:?}"
    );

    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof_bytes = writer.into_vec().expect("flush");
    let proof = String::from_utf8(proof_bytes).expect("UTF-8 proof");

    // DRAT proof must be non-empty: theory lemmas should have been emitted.
    assert!(
        !proof.is_empty(),
        "DRAT proof must not be empty for XOR-derived UNSAT (#4533)"
    );

    // Verify the proof contains at least one addition line (non-deletion).
    // DRAT addition lines are literal sequences ending with 0.
    // Deletion lines start with 'd'.
    let add_lines: Vec<&str> = proof
        .lines()
        .filter(|line| !line.trim_start().starts_with('d'))
        .collect();
    assert!(
        !add_lines.is_empty(),
        "DRAT proof must contain addition lines for XOR-derived theory lemmas (#4533).\n\
         Full proof:\n{proof}"
    );

    // The proof must contain the empty clause (final UNSAT derivation).
    let has_empty_clause = proof.lines().any(|line| line.trim() == "0");
    assert!(
        has_empty_clause,
        "DRAT proof must end with empty clause derivation for XOR UNSAT (#4533).\n\
         Full proof:\n{proof}"
    );
}

/// Verify that XOR preprocessing with mixed CNF+XOR UNSAT produces a complete
/// DRAT proof with addition records (theory lemmas) (#4533).
///
/// Formula uses 3-variable XOR constraints (4-clause CNF encoding each) to
/// avoid BCP detecting UNSAT during init_solve before the XOR extension runs.
/// The extra non-XOR binary clause {x3, x4} ensures a mixed CNF+XOR formula.
///
/// XOR system:
///   x0 XOR x1 XOR x2 = 1 (consumed by XOR finder)
///   x0 XOR x1 XOR x2 = 0 (consumed by XOR finder, contradicts above)
///
/// Non-XOR clause:
///   {x3, x4} (kept in SAT solver, not part of XOR)
///
/// UNSAT from XOR Gauss-Jordan: 1=0 contradiction.
#[test]
#[timeout(10000)]
fn test_xor_preprocessing_mixed_cnf_drat_proof_4533() {
    use ay_sat::ProofOutput;

    let mut clauses = Vec::new();
    // 3-variable XOR: x0 XOR x1 XOR x2 = 1 (4 clauses, all 3-lit)
    clauses.extend(encode_xor_3var(0, 1, 2, true));
    // 3-variable XOR: x0 XOR x1 XOR x2 = 0 (4 clauses, contradicts above)
    clauses.extend(encode_xor_3var(0, 1, 2, false));
    // Non-XOR binary clause (kept in SAT solver)
    clauses.push(vec![lit(3, true), lit(4, true)]);

    let proof_output = ProofOutput::drat_text(Vec::new());
    let mut solver = Solver::with_proof_output(5, proof_output);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver
        .solve_with_preprocessing_extension::<XorExtension, _>(|active_clauses| {
            let total = active_clauses.len();
            let mut finder = XorFinder::new();
            let (xors, used_indices) = finder.find_xors_with_indices(active_clauses);
            if xors.is_empty() {
                return None;
            }
            let consumed = used_indices.len();
            let remaining = total.saturating_sub(consumed);
            if !ay_xor::should_enable_gauss_elimination(consumed, remaining, xors.len()) {
                return None;
            }
            let frozen_variables: Vec<Variable> = xors
                .iter()
                .flat_map(|xor| xor.vars.iter().copied())
                .collect::<std::collections::HashSet<u32>>()
                .into_iter()
                .map(Variable::new)
                .collect();
            Some(ay_sat::PreparedExtension::new(
                XorExtension::new(xors),
                used_indices.into_iter().collect(),
                frozen_variables,
            ))
        })
        .into_inner();

    assert!(
        result.is_unsat(),
        "Mixed CNF+XOR formula must be UNSAT, got {result:?}"
    );

    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof_bytes = writer.into_vec().expect("flush");
    let proof = String::from_utf8(proof_bytes).expect("UTF-8 proof");

    assert!(
        !proof.is_empty(),
        "DRAT proof must not be empty for mixed CNF+XOR UNSAT (#4533)"
    );

    // Verify addition records exist (theory lemmas from XOR extension or
    // preprocessing-derived clauses). DRAT deletion records are optional
    // optimization hints and are not checked here.
    let add_lines: Vec<&str> = proof
        .lines()
        .filter(|line| !line.trim_start().starts_with('d'))
        .collect();
    assert!(
        !add_lines.is_empty(),
        "DRAT proof must contain addition lines for XOR theory lemmas (#4533).\n\
         Full proof:\n{proof}"
    );

    // The proof must contain the empty clause.
    let has_empty_clause = proof.lines().any(|line| line.trim() == "0");
    assert!(
        has_empty_clause,
        "DRAT proof must end with empty clause derivation for XOR UNSAT (#4533).\n\
         Full proof:\n{proof}"
    );
}

/// Verify that XOR-derived UNSAT proofs are semantically valid via ay-drat-check (#4533).
///
/// Unlike the structural tests above, this test runs the actual DRAT forward
/// checker on the proof to ensure every theory lemma is RUP-derivable from
/// the original clause set. This catches the bug where consumed clause
/// deletion lines precede theory lemma additions, making lemmas non-RUP.
#[test]
#[timeout(10000)]
fn test_xor_preprocessing_drat_proof_verified_4533() {
    use ay_drat_check::checker::DratChecker;
    use ay_drat_check::cnf_parser::parse_cnf;
    use ay_drat_check::drat_parser::parse_drat;
    use ay_sat::ProofOutput;

    // Contradictory XOR system: all constraints consumed by XOR finder.
    //   x0 XOR x1 = 1 (CNF: {x0,x1}, {-x0,-x1})
    //   x1 XOR x2 = 1 (CNF: {x1,x2}, {-x1,-x2})
    //   x0 XOR x2 = 1 (CNF: {x0,x2}, {-x0,-x2})
    // Chain: (x0^x1)^(x1^x2) = x0^x2 = 0, contradicts x0^x2 = 1.
    let mut clauses = Vec::new();
    clauses.extend(encode_xor_2var(0, 1, true));
    clauses.extend(encode_xor_2var(1, 2, true));
    clauses.extend(encode_xor_2var(0, 2, true));

    let num_vars = 3;

    // Build DIMACS text for the DRAT checker's CNF parser.
    let dimacs = {
        let mut s = format!("p cnf {num_vars} {}\n", clauses.len());
        for clause in &clauses {
            for lit in clause {
                let var = (lit.variable().index() as i32) + 1;
                let dimacs_lit = if lit.is_positive() { var } else { -var };
                s.push_str(&format!("{dimacs_lit} "));
            }
            s.push_str("0\n");
        }
        s
    };

    let proof_output = ProofOutput::drat_text(Vec::new());
    let mut solver = Solver::with_proof_output(num_vars, proof_output);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver
        .solve_with_preprocessing_extension::<XorExtension, _>(|active_clauses| {
            let mut finder = XorFinder::new();
            let (xors, used_indices) = finder.find_xors_with_indices(active_clauses);
            if xors.is_empty() {
                return None;
            }
            let total = active_clauses.len();
            let consumed = used_indices.len();
            let remaining = total.saturating_sub(consumed);
            if !ay_xor::should_enable_gauss_elimination(consumed, remaining, xors.len()) {
                return None;
            }
            let frozen_variables: Vec<Variable> = xors
                .iter()
                .flat_map(|xor| xor.vars.iter().copied())
                .collect::<std::collections::HashSet<u32>>()
                .into_iter()
                .map(Variable::new)
                .collect();
            Some(ay_sat::PreparedExtension::new(
                XorExtension::new(xors),
                used_indices.into_iter().collect(),
                frozen_variables,
            ))
        })
        .into_inner();

    assert!(
        result.is_unsat(),
        "Contradictory XOR system must be UNSAT, got {result:?}"
    );

    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof_bytes = writer.into_vec().expect("flush");
    assert!(
        !proof_bytes.is_empty(),
        "DRAT proof must not be empty for XOR-derived UNSAT (#4533)"
    );

    let cnf = parse_cnf(dimacs.as_bytes()).unwrap_or_else(|e| panic!("CNF parse for checker: {e}"));
    let steps = parse_drat(&proof_bytes).unwrap_or_else(|e| panic!("DRAT proof parse failed: {e}"));
    assert!(!steps.is_empty(), "DRAT proof parsed to 0 steps (#4533)");

    let mut checker = DratChecker::new(num_vars, true);
    checker.verify(&cnf.clauses, &steps).unwrap_or_else(|e| {
        let proof_text = String::from_utf8_lossy(&proof_bytes);
        panic!(
            "DRAT verification FAILED for XOR extension proof (#4533): {e}\n\
                 Proof ({} bytes, {} steps):\n{proof_text}",
            proof_bytes.len(),
            steps.len()
        )
    });
}

/// Validate XOR-derived DRAT proofs with external drat-trim (#4533).
///
/// Writes the DIMACS CNF and DRAT proof to temporary files, then runs
/// drat-trim to verify the proof is accepted by an independent checker.
/// This is the gold standard for DRAT proof verification.
///
/// Formula: contradictory XOR system via preprocessing path.
///   x0 XOR x1 = 1, x1 XOR x2 = 1, x0 XOR x2 = 1
#[test]
#[timeout(30000)]
fn test_xor_drat_proof_validated_by_drat_trim_4533() {
    use ay_sat::ProofOutput;
    use std::process::Command;

    // Check drat-trim is available
    let drat_trim = which_drat_trim();
    if drat_trim.is_none() {
        eprintln!("SKIP: drat-trim not found in PATH or ~/.local/bin");
        return;
    }
    let drat_trim = drat_trim.unwrap();

    // Contradictory XOR system (all constraints consumed by XOR finder).
    let mut clauses = Vec::new();
    clauses.extend(encode_xor_2var(0, 1, true));
    clauses.extend(encode_xor_2var(1, 2, true));
    clauses.extend(encode_xor_2var(0, 2, true));

    let num_vars = 3;

    // Build DIMACS text
    let dimacs = build_dimacs(num_vars, &clauses);

    let proof_output = ProofOutput::drat_text(Vec::new());
    let mut solver = Solver::with_proof_output(num_vars, proof_output);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver
        .solve_with_preprocessing_extension::<XorExtension, _>(|active_clauses| {
            let total = active_clauses.len();
            let mut finder = XorFinder::new();
            let (xors, used_indices) = finder.find_xors_with_indices(active_clauses);
            if xors.is_empty() {
                return None;
            }
            let consumed = used_indices.len();
            let remaining = total.saturating_sub(consumed);
            if !ay_xor::should_enable_gauss_elimination(consumed, remaining, xors.len()) {
                return None;
            }
            let frozen_variables: Vec<Variable> = xors
                .iter()
                .flat_map(|xor| xor.vars.iter().copied())
                .collect::<std::collections::HashSet<u32>>()
                .into_iter()
                .map(Variable::new)
                .collect();
            Some(ay_sat::PreparedExtension::new(
                XorExtension::new(xors),
                used_indices.into_iter().collect(),
                frozen_variables,
            ))
        })
        .into_inner();

    assert!(result.is_unsat(), "Expected UNSAT, got {result:?}");

    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof_bytes = writer.into_vec().expect("flush");
    let proof = String::from_utf8(proof_bytes.clone()).expect("UTF-8 proof");
    assert!(!proof.is_empty(), "DRAT proof must not be empty");

    // Write to temp files and run drat-trim
    let tmp_dir = std::env::temp_dir();
    let cnf_path = tmp_dir.join("ay_xor_drat_test.cnf");
    let proof_path = tmp_dir.join("ay_xor_drat_test.drat");

    std::fs::write(&cnf_path, &dimacs).expect("write CNF");
    std::fs::write(&proof_path, &proof_bytes).expect("write proof");

    let output = Command::new(&drat_trim)
        .arg(&cnf_path)
        .arg(&proof_path)
        .output()
        .unwrap_or_else(|e| panic!("drat-trim execution failed: {e}"));

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    // drat-trim prints "s VERIFIED" on success
    assert!(
        stdout.contains("VERIFIED") || stdout.contains("ACCEPTED"),
        "drat-trim REJECTED XOR-derived DRAT proof (#4533).\n\
         Exit code: {:?}\nstdout: {stdout}\nstderr: {stderr}\n\
         DIMACS:\n{dimacs}\nProof:\n{proof}",
        output.status.code()
    );

    // Cleanup
    let _ = std::fs::remove_file(&cnf_path);
    let _ = std::fs::remove_file(&proof_path);
}

/// Validate XOR-derived DRAT proofs for the non-preprocessing (solve_with_extension)
/// path with external drat-trim (#4533).
///
/// This tests the ext_dimacs-style path where XOR constraints are added directly
/// as an extension (not extracted from CNF preprocessing). The original CNF
/// clauses remain in the solver AND in the proof.
#[test]
#[timeout(30000)]
fn test_xor_extension_drat_proof_validated_by_drat_trim_4533() {
    use ay_sat::ProofOutput;
    use std::process::Command;

    let drat_trim = which_drat_trim();
    if drat_trim.is_none() {
        eprintln!("SKIP: drat-trim not found in PATH or ~/.local/bin");
        return;
    }
    let drat_trim = drat_trim.unwrap();

    // Formula: x0 XOR x1 = 1, but x0=false and x1=false from CNF.
    let constraints = vec![XorConstraint::new(vec![0, 1], true)];
    let cnf_clauses = vec![
        vec![Literal::negative(Variable::new(0))], // x0 = false
        vec![Literal::negative(Variable::new(1))], // x1 = false
    ];

    let num_vars = 2;
    let dimacs = build_dimacs(num_vars, &cnf_clauses);

    let proof_output = ProofOutput::drat_text(Vec::new());
    let mut solver = Solver::with_proof_output(num_vars, proof_output);
    for clause in &cnf_clauses {
        solver.add_clause(clause.clone());
    }
    solver.set_extension_trusted_lemmas(true);

    let mut ext = XorExtension::new(constraints);
    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert!(result.is_unsat(), "Expected UNSAT, got {result:?}");

    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof_bytes = writer.into_vec().expect("flush");
    let proof = String::from_utf8(proof_bytes.clone()).expect("UTF-8 proof");
    assert!(!proof.is_empty(), "DRAT proof must not be empty");

    let tmp_dir = std::env::temp_dir();
    let cnf_path = tmp_dir.join("ay_xor_ext_drat_test.cnf");
    let proof_path = tmp_dir.join("ay_xor_ext_drat_test.drat");

    std::fs::write(&cnf_path, &dimacs).expect("write CNF");
    std::fs::write(&proof_path, &proof_bytes).expect("write proof");

    let output = Command::new(&drat_trim)
        .arg(&cnf_path)
        .arg(&proof_path)
        .output()
        .unwrap_or_else(|e| panic!("drat-trim execution failed: {e}"));

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stdout.contains("VERIFIED") || stdout.contains("ACCEPTED"),
        "drat-trim REJECTED XOR extension DRAT proof (#4533).\n\
         Exit code: {:?}\nstdout: {stdout}\nstderr: {stderr}\n\
         DIMACS:\n{dimacs}\nProof:\n{proof}",
        output.status.code()
    );

    let _ = std::fs::remove_file(&cnf_path);
    let _ = std::fs::remove_file(&proof_path);
}

/// Validate DRAT proof for XOR propagation path (non-empty conflict) (#4533).
///
/// Unlike the initial-conflict tests above, this forces the solver to do
/// assignments and propagations before reaching the conflict, exercising
/// the add_theory_propagation proof emission path.
#[test]
#[timeout(30000)]
fn test_xor_propagation_drat_proof_validated_by_drat_trim_4533() {
    use ay_sat::ProofOutput;
    use std::process::Command;

    let drat_trim = which_drat_trim();
    if drat_trim.is_none() {
        eprintln!("SKIP: drat-trim not found in PATH or ~/.local/bin");
        return;
    }
    let drat_trim = drat_trim.unwrap();

    // Formula via preprocessing:
    //   x0 XOR x1 = 1 (CNF: {x0,x1}, {-x0,-x1})
    //   x2 XOR x3 = 1 (CNF: {x2,x3}, {-x2,-x3})
    //   Plus CNF unit: x0=true, x1=true (forces XOR conflict after propagation)
    let mut clauses = Vec::new();
    clauses.extend(encode_xor_2var(0, 1, true));
    clauses.extend(encode_xor_2var(2, 3, true));
    clauses.push(vec![Literal::positive(Variable::new(0))]); // x0 = true
    clauses.push(vec![Literal::positive(Variable::new(1))]); // x1 = true (conflict with XOR)

    let num_vars = 4;
    let dimacs = build_dimacs(num_vars, &clauses);

    let proof_output = ProofOutput::drat_text(Vec::new());
    let mut solver = Solver::with_proof_output(num_vars, proof_output);
    for clause in &clauses {
        solver.add_clause(clause.clone());
    }

    let result = solver
        .solve_with_preprocessing_extension::<XorExtension, _>(|active_clauses| {
            let total = active_clauses.len();
            let mut finder = XorFinder::new();
            let (xors, used_indices) = finder.find_xors_with_indices(active_clauses);
            if xors.is_empty() {
                return None;
            }
            let consumed = used_indices.len();
            let remaining = total.saturating_sub(consumed);
            if !ay_xor::should_enable_gauss_elimination(consumed, remaining, xors.len()) {
                return None;
            }
            let frozen_variables: Vec<Variable> = xors
                .iter()
                .flat_map(|xor| xor.vars.iter().copied())
                .collect::<std::collections::HashSet<u32>>()
                .into_iter()
                .map(Variable::new)
                .collect();
            Some(ay_sat::PreparedExtension::new(
                XorExtension::new(xors),
                used_indices.into_iter().collect(),
                frozen_variables,
            ))
        })
        .into_inner();

    assert!(result.is_unsat(), "Expected UNSAT, got {result:?}");

    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof_bytes = writer.into_vec().expect("flush");
    let proof = String::from_utf8(proof_bytes.clone()).expect("UTF-8 proof");
    assert!(!proof.is_empty(), "DRAT proof must not be empty");

    let tmp_dir = std::env::temp_dir();
    let cnf_path = tmp_dir.join("ay_xor_prop_drat_test.cnf");
    let proof_path = tmp_dir.join("ay_xor_prop_drat_test.drat");

    std::fs::write(&cnf_path, &dimacs).expect("write CNF");
    std::fs::write(&proof_path, &proof_bytes).expect("write proof");

    let output = Command::new(&drat_trim)
        .arg(&cnf_path)
        .arg(&proof_path)
        .output()
        .unwrap_or_else(|e| panic!("drat-trim execution failed: {e}"));

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        stdout.contains("VERIFIED") || stdout.contains("ACCEPTED"),
        "drat-trim REJECTED XOR propagation DRAT proof (#4533).\n\
         Exit code: {:?}\nstdout: {stdout}\nstderr: {stderr}\n\
         DIMACS:\n{dimacs}\nProof:\n{proof}",
        output.status.code()
    );

    let _ = std::fs::remove_file(&cnf_path);
    let _ = std::fs::remove_file(&proof_path);
}

#[test]
#[timeout(10000)]
fn test_xor_lrat_boundary_fails_closed_without_explicit_chains_4533() {
    let (blocked_result, blocked) = solve_binary_xor_lrat_with_trust(false);
    assert!(
        blocked_result.is_unsat(),
        "the semantic XOR extension must still report UNSAT when external LRAT \
         output is disabled for theory lemmas, got {blocked_result:?}"
    );
    assert_eq!(
        non_empty_hintless_lrat_adds(&blocked),
        0,
        "untrusted XOR/theory lemmas must fail closed in LRAT by suppressing \
         non-empty hintless additions.\nProof:\n{blocked}"
    );

    let (trusted_result, trusted) = solve_binary_xor_lrat_with_trust(true);
    assert!(
        trusted_result.is_unknown(),
        "internal TrustedTransform classification is not representable in LRAT; \
         missing chains must downgrade UNSAT to Unknown, got {trusted_result:?}"
    );
    assert_eq!(
        non_empty_hintless_lrat_adds(&trusted),
        0,
        "trusted XOR lemmas without explicit chains must not be serialized as \
         LRAT axioms.\nProof:\n{trusted}"
    );
}

fn solve_binary_xor_lrat_with_trust(trusted: bool) -> (SatResult, String) {
    use ay_sat::ProofOutput;

    let proof_output = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver = Solver::with_proof_output(2, proof_output);
    assert!(solver.add_clause(vec![Literal::negative(Variable::new(0))]));
    assert!(solver.add_clause(vec![Literal::negative(Variable::new(1))]));
    if trusted {
        solver.set_extension_trusted_lemmas(true);
    }

    let mut ext = XorExtension::new(vec![XorConstraint::new(vec![0, 1], true)]);
    let result = solver.solve_with_extension(&mut ext).into_inner();

    let writer = solver.take_proof_writer().expect("proof writer must exist");
    let proof_bytes = writer.into_vec().expect("flush LRAT proof");
    (
        result,
        String::from_utf8(proof_bytes).expect("LRAT text proof must be UTF-8"),
    )
}

fn non_empty_hintless_lrat_adds(proof: &str) -> usize {
    proof
        .lines()
        .filter_map(lrat_add_counts)
        .filter(|(literal_count, hint_count)| *literal_count > 0 && *hint_count == 0)
        .count()
}

fn lrat_add_counts(line: &str) -> Option<(usize, usize)> {
    let mut tokens = line.split_whitespace();
    let id = tokens.next()?;
    if id == "d" || id.parse::<u64>().is_err() {
        return None;
    }

    let mut literal_count = 0;
    for token in tokens.by_ref() {
        if token == "0" {
            break;
        }
        literal_count += 1;
    }

    for (hint_count, token) in tokens.enumerate() {
        if token == "0" {
            return Some((literal_count, hint_count));
        }
    }
    None
}

/// Find drat-trim binary in PATH or common locations.
fn which_drat_trim() -> Option<PathBuf> {
    // Check PATH first
    if let Ok(output) = std::process::Command::new("which")
        .arg("drat-trim")
        .output()
    {
        if output.status.success() {
            let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !path.is_empty() {
                return Some(PathBuf::from(path));
            }
        }
    }

    // Check common locations
    let home = std::env::var("HOME").unwrap_or_default();
    let candidates = [
        format!("{home}/.local/bin/drat-trim"),
        "/usr/local/bin/drat-trim".to_string(),
        "/tmp/drat-trim/drat-trim".to_string(),
    ];
    for candidate in &candidates {
        let path = PathBuf::from(candidate);
        if path.exists() {
            return Some(path);
        }
    }
    None
}

/// Build a DIMACS string from variable count and clauses.
fn build_dimacs(num_vars: usize, clauses: &[Vec<Literal>]) -> String {
    let mut s = format!("p cnf {num_vars} {}\n", clauses.len());
    for clause in clauses {
        for lit in clause {
            let var = (lit.variable().index() as i32) + 1;
            let dimacs_lit = if lit.is_positive() { var } else { -var };
            s.push_str(&format!("{dimacs_lit} "));
        }
        s.push_str("0\n");
    }
    s
}

/// Test UNSAT detection through XOR preprocessing
#[test]
#[timeout(10000)]
fn test_xor_preprocessing_unsat() {
    use ay_xor::solve_with_xor_detection;

    // Create contradictory XOR system:
    // x0 XOR x1 = 1
    // x1 XOR x2 = 1
    // x0 XOR x2 = 1
    // Chain implies x0 XOR x2 = 0, but we say = 1 -> contradiction
    let mut clauses = Vec::new();
    clauses.extend(encode_xor_2var(0, 1, true)); // x0 XOR x1 = 1
    clauses.extend(encode_xor_2var(1, 2, true)); // x1 XOR x2 = 1
    clauses.extend(encode_xor_2var(0, 2, true)); // x0 XOR x2 = 1 (contradicts chain)

    let result = solve_with_xor_detection(3, &clauses);

    // Fixed: empty clause DB + contradictory XOR extension correctly returns
    // Unsat (was Unknown due to #5806, fixed in #5823).
    assert!(
        result.is_unsat(),
        "Contradictory XOR system should be UNSAT, got {result:?}"
    );
}
