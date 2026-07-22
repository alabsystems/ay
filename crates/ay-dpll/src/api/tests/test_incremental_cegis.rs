// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Incremental solving examples for CEGIS (Counter-Example Guided Inductive
//! Synthesis) verification loops.
//!
//! Demonstrates three incremental solving patterns that EXTERNAL_CODEGEN and other
//! consumers can use for iterative verification:
//!
//! 1. **Push/pop pattern** -- `try_push()` / `try_pop()` to retract
//!    candidate-specific assertions while keeping base declarations.
//! 2. **Assumption-based pattern** -- `check_sat_assuming(&[...])` to add
//!    temporary constraints without modifying the assertion stack.
//! 3. **SolverScope RAII guard** -- `SolverScope::new(&mut solver)` for
//!    exception-safe scoped assertions that auto-pop on drop.
//!
//! Filed for #8689: [EXTERNAL_CODEGEN] Incremental solving (push/pop) example and
//! guidance for CEGIS verification loops.

use std::time::Duration;

use num_bigint::BigInt;

use crate::api::*;

// =========================================================================
// Pattern 1: Push/pop CEGIS loop with QF_BV
// =========================================================================

/// Demonstrates a CEGIS-style verification loop using push/pop.
///
/// Scenario: We want to find a 4-bit constant `c` such that for all `x`,
/// `(x ^ c) != x` (i.e., XOR with c always flips at least one bit).
/// The only value that fails this is c = 0.
///
/// The CEGIS loop:
/// 1. Create solver with base variable declarations (done once).
/// 2. Push a scope.
/// 3. Assert the candidate-specific formula.
/// 4. Check sat (looking for a counterexample).
/// 5. If UNSAT: candidate is correct (no counterexample exists).
/// 6. If SAT: extract counterexample, pop scope, refine candidate.
#[test]
fn test_cegis_push_pop_bv_xor_synthesis() {
    let mut solver = Solver::try_new(Logic::QfBv).expect("QF_BV solver");

    // Declare variables once -- these survive across push/pop
    let x = solver.declare_const("x", Sort::bitvec(4));
    let c = solver.declare_const("c", Sort::bitvec(4));
    let _zero_4 = solver.bv_const(0, 4);

    // Try candidate c = 5 (0b0101): xor with any x should differ from x
    // We check: exists x such that (x ^ 5) == x?  If UNSAT, candidate works.
    let candidates: &[i64] = &[5, 0, 3];
    let mut results = Vec::new();

    for &candidate_val in candidates {
        let candidate_bv = solver.bv_const(candidate_val, 4);

        // Push scope for this candidate
        solver.try_push().expect("push should succeed");

        // Assert c == candidate
        let c_eq = solver.eq(c, candidate_bv);
        solver.try_assert_term(c_eq).expect("assert c == candidate");

        // Assert the counterexample condition: (x ^ c) == x
        // If SAT, the candidate fails (there exists an x that is a fixpoint).
        let xor_result = solver.bvxor(x, c);
        let is_fixpoint = solver.eq(xor_result, x);
        solver
            .try_assert_term(is_fixpoint)
            .expect("assert fixpoint");

        let result = solver.try_check_sat().expect("check_sat should not panic");

        let candidate_works = result.is_unsat();
        results.push((candidate_val, candidate_works));

        if result.is_sat() {
            // Extract the counterexample for potential refinement
            if let Some(ModelValue::BitVec { value, .. }) = solver.value(x) {
                // For c = 0, every x is a fixpoint; for c = 5, no x is
                assert!(
                    !candidate_works,
                    "SAT means candidate c={candidate_val} has fixpoint at x={value}"
                );
            }
        }

        // Pop scope to retract candidate-specific assertions
        solver.try_pop().expect("pop should succeed");
    }

    // c = 5: no fixpoint exists (UNSAT) -- candidate works
    assert!(results[0].1, "c=5 should work (no fixpoint for XOR)");

    // c = 0: x ^ 0 == x for all x (SAT) -- candidate fails
    assert!(!results[1].1, "c=0 should fail (every x is a fixpoint)");

    // c = 3: no fixpoint exists (UNSAT) -- candidate works
    assert!(results[2].1, "c=3 should work (no fixpoint for XOR)");

    // Solver is reusable after all push/pop cycles
    assert_eq!(solver.num_scopes(), 0, "all scopes should be cleaned up");
}

// =========================================================================
// Pattern 2: Assumption-based CEGIS loop
// =========================================================================

/// Demonstrates using `check_sat_assuming` for CEGIS without push/pop.
///
/// This is more efficient than push/pop when the candidate constraint is a
/// single literal or conjunction of literals, because assumptions do not
/// modify the assertion stack at all.
#[test]
fn test_cegis_assumptions_bv_equivalence_check() {
    let mut solver = Solver::try_new(Logic::QfBv).expect("QF_BV solver");

    // Problem: check if candidate expressions are equivalent to `x + 1`
    // for 8-bit bitvectors.
    let x = solver.declare_const("x", Sort::bitvec(8));
    let one = solver.bv_const(1, 8);
    let target = solver.bvadd(x, one); // x + 1

    // Base assertion: we are looking for x where candidate != target
    // (counterexample search). We use assumptions for each candidate.

    // Candidate 1: (x | 1) -- incorrect, not equivalent to x+1
    let candidate1 = solver.bvor(x, one);
    let neq1 = solver
        .try_distinct(&[candidate1, target])
        .expect("distinct");

    // check_sat_assuming with the inequality -- SAT means not equivalent
    let result1 = solver.check_sat_assuming(&[neq1]);
    assert!(
        result1.is_sat(),
        "x|1 != x+1 should be satisfiable (candidates differ)"
    );

    // Extract the counterexample
    if let Some(ModelValue::BitVec { value, .. }) = solver.value(x) {
        // Verify: at this x, (x|1) != (x+1)
        let x_val = value.to_bytes_le().1;
        let x_byte = if x_val.is_empty() { 0u8 } else { x_val[0] };
        let or_val = x_byte | 1;
        let add_val = x_byte.wrapping_add(1);
        assert_ne!(
            or_val, add_val,
            "counterexample should demonstrate the difference"
        );
    }

    // Candidate 2: (x - (-1)) which IS equivalent to x+1 in BV arithmetic
    let neg_one = solver.bv_const(-1i64, 8);
    let candidate2 = solver.bvsub(x, neg_one);
    let neq2 = solver
        .try_distinct(&[candidate2, target])
        .expect("distinct");

    // check_sat_assuming -- UNSAT means equivalent
    let result2 = solver.check_sat_assuming(&[neq2]);
    assert!(
        result2.is_unsat(),
        "x - (-1) == x + 1 should be UNSAT (equivalent in BV)"
    );

    // No push/pop needed -- assumptions are automatically temporary
    assert_eq!(
        solver.num_scopes(),
        0,
        "assumptions should not change scope level"
    );
}

// =========================================================================
// Pattern 3: SolverScope RAII guard for exception-safe CEGIS
// =========================================================================

/// Demonstrates using `SolverScope` for automatic push/pop.
///
/// `SolverScope` is preferred when the scoped block might return early
/// via `?` or panic, because the guard ensures `try_pop()` is always called.
#[test]
fn test_cegis_solver_scope_raii_guard() {
    let mut solver = Solver::try_new(Logic::QfBv).expect("QF_BV solver");

    let x = solver.declare_const("x", Sort::bitvec(8));
    let y = solver.declare_const("y", Sort::bitvec(8));

    // Base constraint: y is an unknown target value
    // We want to find y such that y == x for a specific x

    // Iteration 1: try x = 42
    {
        let mut scope = SolverScope::new(&mut solver).expect("push scope");
        let forty_two = scope.bv_const(42, 8);
        let x_eq = scope.eq(x, forty_two);
        scope.try_assert_term(x_eq).expect("assert x = 42");

        let y_eq = scope.eq(y, forty_two);
        scope.try_assert_term(y_eq).expect("assert y = 42");

        let result = scope.try_check_sat().expect("check_sat");
        assert!(result.is_sat(), "x=42, y=42 should be satisfiable");
    }
    // scope dropped here -- pop is automatic

    // Iteration 2: try a conflicting constraint (should be independent)
    {
        let mut scope = SolverScope::new(&mut solver).expect("push scope");
        let zero = scope.bv_const(0, 8);
        let max_val = scope.bv_const(0xFF, 8);

        // x == 0 AND x == 0xFF -- contradictory
        let x_eq_zero = scope.eq(x, zero);
        let x_eq_max = scope.eq(x, max_val);
        scope.try_assert_term(x_eq_zero).expect("assert x = 0");
        scope.try_assert_term(x_eq_max).expect("assert x = 0xFF");

        let result = scope.try_check_sat().expect("check_sat");
        assert!(result.is_unsat(), "x=0 AND x=0xFF should be UNSAT");
    }

    // After both scopes, solver is clean
    assert_eq!(solver.num_scopes(), 0);

    // Iteration 3: solver still works with new constraints
    {
        let mut scope = SolverScope::new(&mut solver).expect("push scope");
        let one = scope.bv_const(1, 8);
        let x_eq_one = scope.eq(x, one);
        scope.try_assert_term(x_eq_one).expect("assert x = 1");

        let result = scope.try_check_sat().expect("check_sat");
        assert!(result.is_sat(), "x=1 should be satisfiable");
    }

    assert_eq!(solver.num_scopes(), 0);
}

// =========================================================================
// Pattern 4: Nested push/pop for CEGIS with refinement
// =========================================================================

/// Demonstrates nested scopes for a two-level CEGIS loop.
///
/// Outer loop: iterates over candidate programs.
/// Inner loop: for each candidate, tries multiple counterexample seeds.
#[test]
fn test_cegis_nested_push_pop() {
    let mut solver = Solver::try_new(Logic::QfBv).expect("QF_BV solver");

    let x = solver.declare_const("x", Sort::bitvec(8));
    let result_var = solver.declare_const("result", Sort::bitvec(8));

    // Outer loop: try different "program" candidates
    for shift_amt in [1u8, 2, 0] {
        solver.try_push().expect("outer push");

        // Candidate program: result = x << shift_amt
        let shift = solver.bv_const(i64::from(shift_amt), 8);
        let candidate_result = solver.bvshl(x, shift);
        let result_eq = solver.eq(result_var, candidate_result);
        solver
            .try_assert_term(result_eq)
            .expect("assert candidate program");

        // Inner loop: check specific input values
        for test_input in [0u8, 1, 127, 255] {
            solver.try_push().expect("inner push");

            let input_bv = solver.bv_const(i64::from(test_input), 8);
            let x_eq = solver.eq(x, input_bv);
            solver.try_assert_term(x_eq).expect("assert test input");

            let check = solver.try_check_sat().expect("check_sat");
            assert!(
                check.is_sat(),
                "shift by {shift_amt} with input {test_input} should be SAT"
            );

            // Verify model: result should be test_input << shift_amt (mod 256)
            if let Some(ModelValue::BitVec { value, .. }) = solver.value(result_var) {
                let expected =
                    BigInt::from(u64::from(test_input.wrapping_shl(u32::from(shift_amt))));
                assert_eq!(
                    value, expected,
                    "model result for input={test_input}, shift={shift_amt}"
                );
            }

            solver.try_pop().expect("inner pop");
        }

        solver.try_pop().expect("outer pop");
    }

    assert_eq!(solver.num_scopes(), 0, "all nested scopes cleaned up");
}

// =========================================================================
// Pattern 5: Push/pop with check_sat_with_timeout
// =========================================================================

/// Demonstrates combining incremental solving with per-call timeouts.
///
/// In a CEGIS loop, some candidates may produce hard queries. Using
/// `check_sat_with_timeout` prevents any single candidate from blocking
/// the entire synthesis run.
#[test]
fn test_cegis_push_pop_with_timeout() {
    let mut solver = Solver::try_new(Logic::QfBv).expect("QF_BV solver");

    let x = solver.declare_const("x", Sort::bitvec(16));
    let y = solver.declare_const("y", Sort::bitvec(16));

    // For each candidate, use a timeout to bound the check
    let timeout = Duration::from_secs(5);
    let mut sat_count = 0u32;

    for candidate_val in [0i64, 1, 0x7FFF, -1] {
        solver.try_push().expect("push for candidate");

        let c = solver.bv_const(candidate_val, 16);
        let sum = solver.bvadd(x, y);
        let eq = solver.eq(sum, c);
        solver.try_assert_term(eq).expect("assert x + y == c");

        // Use per-call timeout -- does not modify solver.timeout permanently
        let result = solver.check_sat_with_timeout(timeout);

        if result.is_sat() {
            sat_count += 1;
            // Extract counterexample for refinement
            let _x_val = solver.value(x);
            let _y_val = solver.value(y);
        } else if result == SolveResult::Unknown {
            // Timeout or resource limit -- skip this candidate
        }

        solver.try_pop().expect("pop for candidate");
    }

    // All candidates should be satisfiable (x + y == c always has solutions
    // for 16-bit BV)
    assert_eq!(sat_count, 4, "all candidates should be SAT for 16-bit BV");
    assert_eq!(solver.num_scopes(), 0);
}

// =========================================================================
// Pattern 6: Assumption-based with unsat assumption extraction
// =========================================================================

/// Demonstrates extracting the conflicting subset of assumptions after UNSAT.
///
/// This is useful in CEGIS when the verification query has multiple
/// independent constraints and you want to know which constraint group
/// is responsible for the conflict.
#[test]
fn test_cegis_assumptions_with_unsat_extraction() {
    let mut solver = Solver::try_new(Logic::QfBv).expect("QF_BV solver");

    let x = solver.declare_const("x", Sort::bitvec(8));
    let zero = solver.bv_const(0, 8);
    let ten = solver.bv_const(10, 8);
    let twenty = solver.bv_const(20, 8);

    // Permanent constraint: x is unsigned-less-than 10
    let x_ult_10 = solver.bvult(x, ten);
    solver.try_assert_term(x_ult_10).expect("assert x < 10");

    // Assumption 1: x != 0 (compatible)
    let x_neq_0 = solver.try_distinct(&[x, zero]).expect("distinct");

    // Assumption 2: x >= 20 (conflicts with permanent x < 10)
    // We encode "x >= 20" as "NOT (x < 20)"
    let x_ult_20 = solver.bvult(x, twenty);
    let x_ge_20 = solver.not(x_ult_20);

    // Check with both assumptions
    let result = solver.check_sat_assuming(&[x_neq_0, x_ge_20]);
    assert!(result.is_unsat(), "x < 10 AND x >= 20 should be UNSAT");

    // Extract which assumptions contributed to the conflict
    let unsat_assumptions = solver.unsat_assumptions();
    assert!(
        unsat_assumptions.is_some(),
        "should have unsat assumptions after UNSAT"
    );

    // Now check with just the compatible assumption
    let result2 = solver.check_sat_assuming(&[x_neq_0]);
    assert!(
        result2.is_sat(),
        "x < 10 AND x != 0 should be SAT (e.g., x = 1)"
    );
}

// =========================================================================
// Cross-logic validation: push/pop works with multiple logics
// =========================================================================

/// Confirms push/pop works with QF_BV (the primary EXTERNAL_CODEGEN logic).
#[test]
fn test_incremental_qf_bv() {
    let mut solver = Solver::try_new(Logic::QfBv).expect("QF_BV solver");
    let x = solver.declare_const("x", Sort::bitvec(32));
    let zero = solver.bv_const(0, 32);

    solver.try_push().expect("push");
    let eq = solver.eq(x, zero);
    solver.try_assert_term(eq).expect("assert");
    assert!(solver.try_check_sat().expect("check").is_sat());
    solver.try_pop().expect("pop");

    // After pop, x == 0 is no longer asserted
    let one = solver.bv_const(1, 32);
    solver.try_push().expect("push 2");
    let eq2 = solver.eq(x, one);
    solver.try_assert_term(eq2).expect("assert x = 1");
    assert!(solver.try_check_sat().expect("check").is_sat());
    solver.try_pop().expect("pop 2");
}

/// Confirms push/pop works with QF_ABV (arrays of bitvectors).
#[test]
fn test_incremental_qf_abv() {
    let mut solver = Solver::try_new(Logic::QfAbv).expect("QF_ABV solver");
    let mem = solver.declare_const("mem", Sort::array(Sort::bitvec(32), Sort::bitvec(8)));
    let addr = solver.declare_const("addr", Sort::bitvec(32));

    solver.try_push().expect("push");
    let zero_addr = solver.bv_const(0, 32);
    let addr_eq = solver.eq(addr, zero_addr);
    solver.try_assert_term(addr_eq).expect("assert addr = 0");

    let val = solver.select(mem, addr);
    let forty_two = solver.bv_const(42, 8);
    let val_eq = solver.eq(val, forty_two);
    solver
        .try_assert_term(val_eq)
        .expect("assert mem[addr] = 42");

    assert!(solver.try_check_sat().expect("check").is_sat());
    solver.try_pop().expect("pop");

    // After pop, we can use a different address
    solver.try_push().expect("push 2");
    let one_addr = solver.bv_const(1, 32);
    let addr_eq2 = solver.eq(addr, one_addr);
    solver.try_assert_term(addr_eq2).expect("assert addr = 1");
    assert!(solver.try_check_sat().expect("check").is_sat());
    solver.try_pop().expect("pop 2");
}

/// Confirms push/pop works with QF_LIA (integer arithmetic).
#[test]
fn test_incremental_qf_lia() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA solver");
    let x = solver.declare_const("x", Sort::Int);

    solver.try_push().expect("push");
    let zero = solver.int_const(0);
    let x_gt_0 = solver.try_gt(x, zero).expect("gt");
    solver.try_assert_term(x_gt_0).expect("assert x > 0");
    assert!(solver.try_check_sat().expect("check").is_sat());
    solver.try_pop().expect("pop");

    solver.try_push().expect("push 2");
    let neg = solver.int_const(-5);
    let x_eq_neg = solver.eq(x, neg);
    solver.try_assert_term(x_eq_neg).expect("assert x = -5");
    assert!(solver.try_check_sat().expect("check").is_sat());
    solver.try_pop().expect("pop 2");
}

/// Confirms push/pop works with QF_LRA (real arithmetic).
#[test]
fn test_incremental_qf_lra() {
    let mut solver = Solver::try_new(Logic::QfLra).expect("QF_LRA solver");
    let x = solver.declare_const("x", Sort::Real);

    solver.try_push().expect("push");
    let half = solver.real_const(0.5);
    let x_eq = solver.eq(x, half);
    solver.try_assert_term(x_eq).expect("assert x = 0.5");
    assert!(solver.try_check_sat().expect("check").is_sat());
    solver.try_pop().expect("pop");
}

// =========================================================================
// Stress: many iterations without leaking state
// =========================================================================

/// Verifies that 100 push/pop cycles do not accumulate state.
///
/// This mirrors the EXTERNAL_CODEGEN use case of iterating over many candidates
/// in a synthesis loop.
#[test]
fn test_incremental_many_iterations_no_leak() {
    let mut solver = Solver::try_new(Logic::QfBv).expect("QF_BV solver");
    let x = solver.declare_const("x", Sort::bitvec(8));

    for i in 0..100u8 {
        solver.try_push().expect("push");

        let val = solver.bv_const(i64::from(i), 8);
        let eq = solver.eq(x, val);
        solver.try_assert_term(eq).expect("assert x == i");

        let result = solver.try_check_sat().expect("check_sat");
        assert!(result.is_sat(), "x = {i} should always be SAT");

        if let Some(ModelValue::BitVec { value, .. }) = solver.value(x) {
            assert_eq!(value, BigInt::from(i), "model should match asserted value");
        }

        solver.try_pop().expect("pop");
    }

    assert_eq!(solver.num_scopes(), 0, "all 100 scopes cleaned up");
}

/// Verifies that 100 assumption-based iterations do not accumulate state.
#[test]
fn test_incremental_many_assumption_iterations() {
    let mut solver = Solver::try_new(Logic::QfBv).expect("QF_BV solver");
    let x = solver.declare_const("x", Sort::bitvec(8));

    for i in 0..100u8 {
        let val = solver.bv_const(i64::from(i), 8);
        let eq = solver.eq(x, val);

        let result = solver.check_sat_assuming(&[eq]);
        assert!(result.is_sat(), "x = {i} should always be SAT");
    }

    assert_eq!(
        solver.num_scopes(),
        0,
        "assumptions should not alter scopes"
    );
}

// =========================================================================
// Combined: assumption within a pushed scope
// =========================================================================

/// Demonstrates mixing push/pop and assumptions in the same CEGIS loop.
///
/// Pattern: push a scope for the candidate's structural constraints,
/// then use assumptions for quick variant checks within that scope.
#[test]
fn test_cegis_push_pop_plus_assumptions() {
    let mut solver = Solver::try_new(Logic::QfBv).expect("QF_BV solver");

    let x = solver.declare_const("x", Sort::bitvec(8));
    let y = solver.declare_const("y", Sort::bitvec(8));

    // Candidate: y = x + 1
    solver.try_push().expect("push for candidate");
    let one = solver.bv_const(1, 8);
    let x_plus_1 = solver.bvadd(x, one);
    let y_eq = solver.eq(y, x_plus_1);
    solver.try_assert_term(y_eq).expect("assert y = x + 1");

    // Quick assumption checks for specific inputs within this candidate
    let zero = solver.bv_const(0, 8);
    let x_eq_0 = solver.eq(x, zero);
    let result = solver.check_sat_assuming(&[x_eq_0]);
    assert!(result.is_sat(), "x=0 => y=1 should be SAT");
    if let Some(ModelValue::BitVec { value, .. }) = solver.value(y) {
        assert_eq!(value, BigInt::from(1), "y should be 1 when x is 0");
    }

    let max_val = solver.bv_const(0xFF, 8);
    let x_eq_max = solver.eq(x, max_val);
    let result2 = solver.check_sat_assuming(&[x_eq_max]);
    assert!(
        result2.is_sat(),
        "x=0xFF => y=0x00 should be SAT (wrapping)"
    );
    if let Some(ModelValue::BitVec { value, .. }) = solver.value(y) {
        assert_eq!(value, BigInt::from(0), "y should wrap to 0 when x is 0xFF");
    }

    solver.try_pop().expect("pop candidate");
    assert_eq!(solver.num_scopes(), 0);
}

// =========================================================================
// Lemma persistence across push/pop (advanced incremental feature)
// =========================================================================

/// Demonstrates enabling lemma persistence for incremental solving.
///
/// When the same theory lemmas apply across multiple candidates (common in
/// binary analysis where path constraints share most structure), enabling
/// lemma persistence avoids re-deriving them after each pop.
#[test]
fn test_cegis_lemma_persistence() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA solver");
    solver.set_lemma_persistence(true);
    assert!(solver.lemma_persistence());

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    // Shared constraint: x + y > 10
    let ten = solver.int_const(10);
    let sum = solver.try_add(x, y).expect("add");
    let sum_gt_10 = solver.try_gt(sum, ten).expect("gt");
    solver
        .try_assert_term(sum_gt_10)
        .expect("assert x + y > 10");

    // First candidate: x = 5
    solver.try_push().expect("push");
    let five = solver.int_const(5);
    let x_eq_5 = solver.eq(x, five);
    solver.try_assert_term(x_eq_5).expect("assert x = 5");
    let result1 = solver.try_check_sat().expect("check");
    assert!(result1.is_sat(), "x=5, x+y>10 should be SAT (y > 5)");
    solver.try_pop().expect("pop");

    // Second candidate: x = 20
    solver.try_push().expect("push");
    let twenty = solver.int_const(20);
    let x_eq_20 = solver.eq(x, twenty);
    solver.try_assert_term(x_eq_20).expect("assert x = 20");
    let result2 = solver.try_check_sat().expect("check");
    assert!(result2.is_sat(), "x=20, x+y>10 should be SAT (y > -10)");
    solver.try_pop().expect("pop");

    // Lemmas from first solve may speed up subsequent solves
    // (no correctness assertion here -- it is a performance optimization)
    assert_eq!(solver.num_scopes(), 0);
}
