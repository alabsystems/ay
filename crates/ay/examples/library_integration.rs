// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// This example uses deprecated panicking convenience methods.
// New code should use the try_* variants (e.g., try_add, try_eq, try_assert_term).
#![allow(deprecated)]

//! Library Integration Example for AY SMT Solver
//!
//! This example demonstrates how to use AY as a library dependency in Rust
//! projects. It covers the native API for building SMT constraints
//! programmatically without parsing SMT-LIB text.
//!
//! # Integration Patterns
//!
//! AY exposes three integration patterns:
//!
//! 1. **Native API (this example)** - Type-safe term construction, no parsing overhead
//! 2. **Executor API** - When you have SMT-LIB text to execute
//! 3. **CHC API** - For constrained Horn clause solving (see ay-chc crate)
//!
//! # Target Audience
//!
//! - Rust verification tools that need an SMT backend
//! - Applications that build constraints programmatically
//! - External Rust developers embedding SMT solving
//!
//! # API Usage Pattern
//!
//! Due to Rust's borrow checker, term creation and assertion must be on
//! separate lines:
//!
//! ```text
//! // Correct: create term first, then assert
//! let constraint = solver.gt(x, zero);
//! solver.assert_term(constraint);
//!
//! // Incorrect: double mutable borrow
//! // solver.assert_term(solver.gt(x, zero));  // Won't compile
//! ```

use ay::api::{BitVecSort, Logic, Model, SolveResult, Solver, SolverScope, Sort};

fn main() {
    println!("AY SMT Solver - Library Integration Examples\n");

    scenario_1_basic_sat();
    scenario_2_unsat_detection();
    scenario_3_incremental_solving();
    scenario_4_bitvectors();
    scenario_5_model_extraction();

    println!("\nAll scenarios completed successfully!");
}

/// Scenario 1: Basic SAT (QF_LIA)
///
/// Demonstrates:
/// - Creating a solver with logic selection
/// - Declaring integer variables
/// - Building arithmetic constraints
/// - Checking satisfiability
fn scenario_1_basic_sat() {
    println!("=== Scenario 1: Basic SAT (QF_LIA) ===");

    // Create solver for quantifier-free linear integer arithmetic
    let mut solver = Solver::new(Logic::QfLia);

    // Declare integer variables
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    // Create constants
    let zero = solver.int_const(0);
    let ten = solver.int_const(10);

    // Assert constraints: x > 0, y > 0, x + y = 10
    // Note: create terms first, then assert (borrow checker requirement)
    let c1 = solver.gt(x, zero);
    solver.assert_term(c1);
    let c2 = solver.gt(y, zero);
    solver.assert_term(c2);
    let sum = solver.add(x, y);
    let c3 = solver.eq(sum, ten);
    solver.assert_term(c3);

    // Check satisfiability — check_sat() returns VerifiedSolveResult;
    // use .result() to pattern-match on the underlying SolveResult.
    match solver.check_sat().result() {
        SolveResult::Sat => {
            println!("  Result: SAT");
            if let Some(verified_model) = solver.model() {
                let model = verified_model.model();
                println!(
                    "  Model: x = {}, y = {}",
                    model
                        .int_val("x")
                        .map(ToString::to_string)
                        .unwrap_or_else(|| "?".into()),
                    model
                        .int_val("y")
                        .map(ToString::to_string)
                        .unwrap_or_else(|| "?".into()),
                );
            }
        }
        SolveResult::Unsat(_) => println!("  Result: UNSAT (unexpected)"),
        SolveResult::Unknown | _ => println!("  Result: Unknown"),
    }
    println!();
}

/// Scenario 2: UNSAT Detection
///
/// Demonstrates:
/// - Detecting unsatisfiable constraints
/// - Contradiction detection
fn scenario_2_unsat_detection() {
    println!("=== Scenario 2: UNSAT Detection ===");

    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);

    // Assert contradictory constraints: x > 0 AND x < 0
    let c1 = solver.gt(x, zero);
    solver.assert_term(c1);
    let c2 = solver.lt(x, zero);
    solver.assert_term(c2);

    match solver.check_sat().result() {
        SolveResult::Sat => println!("  Result: SAT (unexpected)"),
        SolveResult::Unsat(_) => {
            println!("  Result: UNSAT (correct - constraints are contradictory)")
        }
        SolveResult::Unknown | _ => println!("  Result: Unknown"),
    }
    println!();
}

/// Scenario 3: Incremental Solving with SolverScope
///
/// Demonstrates:
/// - Using `SolverScope` (RAII guard) for scoped assertions
/// - Automatic pop on scope exit — no manual push/pop pairing
/// - Testing multiple hypotheses efficiently
/// - Backtracking to previous states
fn scenario_3_incremental_solving() {
    println!("=== Scenario 3: Incremental Solving (SolverScope) ===");

    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let five = solver.int_const(5);

    // Base constraint: x > 0
    let base = solver.gt(x, zero);
    solver.assert_term(base);
    println!("  Base constraint: x > 0");

    // Test hypothesis 1: x < 5 (using SolverScope for automatic pop)
    {
        let mut scope = SolverScope::new(&mut solver).expect("push succeeds");
        let hyp1 = scope.lt(x, five);
        scope.assert_term(hyp1);
        let result1 = scope.check_sat();
        println!("  Hypothesis 1 (x > 0 AND x < 5): {result1:?}");
        // scope dropped here → automatic pop
    }

    // Test hypothesis 2: x < 0 (contradicts base)
    {
        let mut scope = SolverScope::new(&mut solver).expect("push succeeds");
        let hyp2 = scope.lt(x, zero);
        scope.assert_term(hyp2);
        let result2 = scope.check_sat();
        println!("  Hypothesis 2 (x > 0 AND x < 0): {result2:?}");
        // scope dropped here → automatic pop
    }

    // Base constraint still valid after scope drops
    let result_base = solver.check_sat();
    println!("  After scope drops (x > 0 only): {result_base:?}");
    println!();
}

/// Scenario 4: Bitvectors (QF_BV)
///
/// Demonstrates:
/// - Bitvector declarations with width
/// - BV arithmetic operations
/// - Model extraction for bitvectors
fn scenario_4_bitvectors() {
    println!("=== Scenario 4: Bitvectors (QF_BV) ===");

    let mut solver = Solver::new(Logic::QfBv);

    // Declare 8-bit bitvector variables
    let x = solver.declare_const("x", Sort::BitVec(BitVecSort::new(8)));
    let y = solver.declare_const("y", Sort::BitVec(BitVecSort::new(8)));

    // Create BV constants
    let target = solver.bv_const(0xFF, 8); // 255 in 8 bits

    // Assert: x + y = 0xFF (wrapping 8-bit addition)
    let sum = solver.bvadd(x, y);
    let c1 = solver.eq(sum, target);
    solver.assert_term(c1);

    // Add constraints to get interesting values: x > 0, y > 0
    let zero_bv = solver.bv_const(0, 8);
    let c2 = solver.bvult(zero_bv, x); // 0 < x
    solver.assert_term(c2);
    let c3 = solver.bvult(zero_bv, y); // 0 < y
    solver.assert_term(c3);

    match solver.check_sat().result() {
        SolveResult::Sat => {
            println!("  Result: SAT");
            if let Some(verified_model) = solver.model() {
                let model = verified_model.model();
                if let Some((val, width)) = model.bv_val("x") {
                    println!("  x = {val} (width={width})");
                }
                if let Some((val, width)) = model.bv_val("y") {
                    println!("  y = {val} (width={width})");
                }
            }
        }
        SolveResult::Unsat(_) => println!("  Result: UNSAT (unexpected)"),
        SolveResult::Unknown | _ => println!("  Result: Unknown"),
    }
    println!();
}

/// Scenario 5: Model Extraction
///
/// Demonstrates:
/// - Complete model extraction workflow
/// - Multiple variable types in one problem
/// - Verifying model values
fn scenario_5_model_extraction() {
    println!("=== Scenario 5: Model Extraction ===");

    let mut solver = Solver::new(Logic::QfLia);

    // Declare variables
    let a = solver.declare_const("a", Sort::Int);
    let b = solver.declare_const("b", Sort::Int);
    let c = solver.declare_const("c", Sort::Int);

    // Create constants
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let three = solver.int_const(3);

    // Assert: a = 1, b = 2, c = a + b + 3
    let c1 = solver.eq(a, one);
    solver.assert_term(c1);
    let c2 = solver.eq(b, two);
    solver.assert_term(c2);
    let a_plus_b = solver.add(a, b);
    let sum = solver.add(a_plus_b, three);
    let c3 = solver.eq(c, sum); // c = 1 + 2 + 3 = 6
    solver.assert_term(c3);

    match solver.check_sat().result() {
        SolveResult::Sat => {
            println!("  Result: SAT");
            if let Some(verified_model) = solver.model() {
                verify_model(verified_model.model());
            }
        }
        SolveResult::Unsat(_) => println!("  Result: UNSAT (unexpected)"),
        SolveResult::Unknown | _ => println!("  Result: Unknown"),
    }
    println!();
}

/// Helper to verify model values
fn verify_model(model: &Model) {
    let a = model.int_val_i64("a").expect("missing a");
    let b = model.int_val_i64("b").expect("missing b");
    let c = model.int_val_i64("c").expect("missing c");

    println!("  Model: a = {a}, b = {b}, c = {c}");

    // Verify constraints
    assert_eq!(a, 1, "a should be 1");
    assert_eq!(b, 2, "b should be 2");
    assert_eq!(c, 6, "c should be 6 (a + b + 3)");
    println!("  Verification: PASSED");
}

// =============================================================================
// Tests - these run with `cargo test --example library_integration`
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_sat() {
        let mut solver = Solver::new(Logic::QfLia);
        let x = solver.declare_const("x", Sort::Int);
        let y = solver.declare_const("y", Sort::Int);
        let zero = solver.int_const(0);
        let ten = solver.int_const(10);

        let c1 = solver.gt(x, zero);
        solver.assert_term(c1);
        let c2 = solver.gt(y, zero);
        solver.assert_term(c2);
        let sum = solver.add(x, y);
        let c3 = solver.eq(sum, ten);
        solver.assert_term(c3);

        assert_eq!(solver.check_sat(), SolveResult::Sat);

        let model = solver.model().expect("expected model").into_inner();
        let x_val = model.int_val_i64("x").expect("missing x");
        let y_val = model.int_val_i64("y").expect("missing y");
        assert!(x_val > 0 && y_val > 0 && x_val + y_val == 10);
    }

    #[test]
    fn test_unsat() {
        let mut solver = Solver::new(Logic::QfLia);
        let x = solver.declare_const("x", Sort::Int);
        let zero = solver.int_const(0);

        let c1 = solver.gt(x, zero);
        solver.assert_term(c1);
        let c2 = solver.lt(x, zero);
        solver.assert_term(c2);

        assert!(matches!(solver.check_sat().result(), SolveResult::Unsat(_)));
    }

    #[test]
    fn test_incremental() {
        let mut solver = Solver::new(Logic::QfLia);
        let x = solver.declare_const("x", Sort::Int);
        let zero = solver.int_const(0);
        let five = solver.int_const(5);

        let c1 = solver.gt(x, zero);
        solver.assert_term(c1);

        // SolverScope: automatic pop on scope exit
        {
            let mut scope = SolverScope::new(&mut solver).expect("push succeeds");
            let c2 = scope.lt(x, five);
            scope.assert_term(c2);
            assert_eq!(scope.check_sat(), SolveResult::Sat);
        }

        {
            let mut scope = SolverScope::new(&mut solver).expect("push succeeds");
            let c3 = scope.lt(x, zero);
            scope.assert_term(c3);
            assert!(matches!(scope.check_sat().result(), SolveResult::Unsat(_)));
        }

        assert_eq!(solver.check_sat(), SolveResult::Sat);
    }

    #[test]
    fn test_bitvectors() {
        let mut solver = Solver::new(Logic::QfBv);
        let x = solver.declare_const("x", Sort::BitVec(BitVecSort::new(8)));
        let y = solver.declare_const("y", Sort::BitVec(BitVecSort::new(8)));
        let target = solver.bv_const(0xFF, 8);

        let sum = solver.bvadd(x, y);
        let c1 = solver.eq(sum, target);
        solver.assert_term(c1);

        assert_eq!(solver.check_sat(), SolveResult::Sat);
    }

    #[test]
    fn test_model_extraction() {
        let mut solver = Solver::new(Logic::QfLia);
        let a = solver.declare_const("a", Sort::Int);
        let b = solver.declare_const("b", Sort::Int);
        let one = solver.int_const(1);
        let two = solver.int_const(2);

        let c1 = solver.eq(a, one);
        solver.assert_term(c1);
        let c2 = solver.eq(b, two);
        solver.assert_term(c2);

        assert_eq!(solver.check_sat(), SolveResult::Sat);

        let model = solver.model().expect("expected model").into_inner();
        assert_eq!(model.int_val_i64("a"), Some(1));
        assert_eq!(model.int_val_i64("b"), Some(2));
    }

    #[test]
    fn test_lra() {
        let mut solver = Solver::new(Logic::QfLra);
        let x = solver.declare_const("x", Sort::Real);
        let half = solver.rational_const(1, 2);
        let one = solver.real_const(1.0);

        let c1 = solver.gt(x, half);
        solver.assert_term(c1);
        let c2 = solver.lt(x, one);
        solver.assert_term(c2);

        assert_eq!(solver.check_sat(), SolveResult::Sat);
    }

    #[test]
    fn test_boolean_logic() {
        let mut solver = Solver::new(Logic::QfUf);
        let a = solver.declare_const("a", Sort::Bool);
        let b = solver.declare_const("b", Sort::Bool);

        // a OR b, NOT a, NOT b is UNSAT
        let a_or_b = solver.or(a, b);
        solver.assert_term(a_or_b);
        let not_a = solver.not(a);
        solver.assert_term(not_a);
        let not_b = solver.not(b);
        solver.assert_term(not_b);

        assert!(matches!(solver.check_sat().result(), SolveResult::Unsat(_)));
    }
}
