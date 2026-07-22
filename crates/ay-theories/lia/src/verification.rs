// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kani verification proofs for LIA solver.
//!
//! These proofs verify algebraic properties and invariants of the LIA solver
//! using bounded model checking.

use super::*;

// ========================================================================
// Integer Detection Invariants
// ========================================================================

/// is_integer returns true for whole numbers
#[kani::proof]
fn proof_is_integer_for_whole_numbers() {
    let n: i32 = kani::any();
    kani::assume(n > -1000 && n < 1000);

    let rat = BigRational::from(BigInt::from(n));
    assert!(LiaSolver::is_integer(&rat), "Whole numbers are integers");
}

/// is_integer returns false for proper fractions
#[kani::proof]
fn proof_is_integer_for_fractions() {
    let numer: i32 = kani::any();
    let denom: i32 = kani::any();
    kani::assume(numer > -100 && numer < 100);
    kani::assume(denom > 1 && denom < 10);
    kani::assume(numer % denom != 0); // Not divisible

    let rat = BigRational::new(BigInt::from(numer), BigInt::from(denom));
    assert!(
        !LiaSolver::is_integer(&rat),
        "Proper fractions are not integers"
    );
}

/// is_integer returns true when numerator is divisible by denominator
#[kani::proof]
fn proof_is_integer_when_divisible() {
    let k: i32 = kani::any();
    let d: i32 = kani::any();
    kani::assume(k > -50 && k < 50);
    kani::assume(d > 0 && d < 10);

    // k*d / d = k, which is an integer
    let rat = BigRational::new(BigInt::from(k * d), BigInt::from(d));
    assert!(LiaSolver::is_integer(&rat), "k*d/d should be integer k");
}

// ========================================================================
// Floor/Ceil Invariants
// ========================================================================

/// floor_rational/ceil_rational: floor <= value <= ceil
///
/// Uses deterministic concrete cases to avoid deep `num_bigint` unwinding
/// that makes symbolic BigRational intractable for Kani.
/// Covers: positive/negative fractions, zero, integers, boundary values.
#[kani::proof]
fn proof_floor_ceil_bounds() {
    // Representative (numer, denom) covering key edge cases
    let cases: [(i32, i32); 8] = [
        (0, 1),  // zero
        (7, 3),  // positive non-integer (2.33...)
        (-7, 3), // negative non-integer (-2.33...)
        (6, 3),  // positive integer (2)
        (-6, 3), // negative integer (-2)
        (1, 7),  // small positive fraction
        (-1, 7), // small negative fraction
        (99, 1), // large positive integer
    ];

    let idx: usize = kani::any();
    kani::assume(idx < cases.len());
    let (numer, denom) = cases[idx];

    let rat = BigRational::new(BigInt::from(numer), BigInt::from(denom));
    let (floor, ceil) = (
        LiaSolver::floor_rational(&rat),
        LiaSolver::ceil_rational(&rat),
    );

    let floor_rat = BigRational::from(floor.clone());
    let ceil_rat = BigRational::from(ceil.clone());

    assert!(floor_rat <= rat, "floor <= value");
    assert!(rat <= ceil_rat, "value <= ceil");
}

/// floor_rational/ceil_rational: floor + 1 >= ceil (they're adjacent or equal)
#[kani::proof]
fn proof_floor_ceil_adjacent() {
    let numer: i32 = kani::any();
    let denom: i32 = kani::any();
    kani::assume(numer > -100 && numer < 100);
    kani::assume(denom > 0 && denom < 10);

    let rat = BigRational::new(BigInt::from(numer), BigInt::from(denom));
    let (floor, ceil) = (
        LiaSolver::floor_rational(&rat),
        LiaSolver::ceil_rational(&rat),
    );

    let diff = &ceil - &floor;
    assert!(diff <= BigInt::one(), "ceil - floor <= 1");
    assert!(diff >= BigInt::zero(), "ceil >= floor");
}

/// floor_rational/ceil_rational: for integers, floor == ceil == value
#[kani::proof]
fn proof_floor_ceil_for_integers() {
    let n: i32 = kani::any();
    kani::assume(n > -100 && n < 100);

    let rat = BigRational::from(BigInt::from(n));
    let (floor, ceil) = (
        LiaSolver::floor_rational(&rat),
        LiaSolver::ceil_rational(&rat),
    );

    let expected = BigInt::from(n);
    assert!(floor == expected, "floor of integer is itself");
    assert!(ceil == expected, "ceil of integer is itself");
}

/// floor_rational/ceil_rational: for non-integers, floor < value < ceil
#[kani::proof]
fn proof_floor_ceil_for_non_integers() {
    let numer: i32 = kani::any();
    let denom: i32 = kani::any();
    kani::assume(numer > -50 && numer < 50);
    kani::assume(denom > 1 && denom < 5);
    kani::assume(numer % denom != 0); // Not an integer

    let rat = BigRational::new(BigInt::from(numer), BigInt::from(denom));
    let (floor, ceil) = (
        LiaSolver::floor_rational(&rat),
        LiaSolver::ceil_rational(&rat),
    );

    let floor_rat = BigRational::from(floor.clone());
    let ceil_rat = BigRational::from(ceil.clone());

    assert!(floor_rat < rat, "floor < value for non-integers");
    assert!(rat < ceil_rat, "value < ceil for non-integers");
    assert!(
        ceil == floor + BigInt::one(),
        "ceil = floor + 1 for non-integers"
    );
}

/// floor_rational/ceil_rational: negative values handled correctly
#[kani::proof]
fn proof_floor_ceil_negative() {
    // Test -1/2 = -0.5: floor should be -1, ceil should be 0
    let rat = BigRational::new(BigInt::from(-1), BigInt::from(2));
    let (floor, ceil) = (
        LiaSolver::floor_rational(&rat),
        LiaSolver::ceil_rational(&rat),
    );

    assert!(floor == BigInt::from(-1), "floor(-0.5) = -1");
    assert!(ceil == BigInt::from(0), "ceil(-0.5) = 0");

    // Test -3/2 = -1.5: floor should be -2, ceil should be -1
    let rat2 = BigRational::new(BigInt::from(-3), BigInt::from(2));
    let (floor2, ceil2) = (
        LiaSolver::floor_rational(&rat2),
        LiaSolver::ceil_rational(&rat2),
    );

    assert!(floor2 == BigInt::from(-2), "floor(-1.5) = -2");
    assert!(ceil2 == BigInt::from(-1), "ceil(-1.5) = -1");
}

// ========================================================================
// Split Request Invariants
// ========================================================================

/// Split request creates valid floor/ceil
#[kani::proof]
fn proof_split_request_validity() {
    let terms = ay_core::term::TermStore::new();
    let _solver = LiaSolver::new(&terms);

    let numer: i32 = kani::any();
    let denom: i32 = kani::any();
    kani::assume(numer > -50 && numer < 50);
    kani::assume(denom > 1 && denom < 5);
    kani::assume(numer % denom != 0); // Non-integer

    let value = BigRational::new(BigInt::from(numer), BigInt::from(denom));
    let dummy_term_id = ay_core::term::TermId(0);

    let split = LiaSolver::create_split_request(dummy_term_id, value.clone());

    // Verify floor < value < ceil
    let floor_rat = BigRational::from(split.floor.clone());
    let ceil_rat = BigRational::from(split.ceil.clone());

    assert!(floor_rat < value, "Split floor < value");
    assert!(value < ceil_rat, "value < Split ceil");
    assert!(
        split.ceil == split.floor + BigInt::one(),
        "ceil = floor + 1"
    );
}

// ========================================================================
// Solver State Invariants
// ========================================================================

/// Push/pop maintains scope stack correctly
#[kani::proof]
fn proof_push_pop_scope_depth() {
    let terms = ay_core::term::TermStore::new();
    let mut solver = LiaSolver::new(&terms);

    assert!(solver.scopes.is_empty(), "Initially no scopes");

    solver.push();
    assert!(solver.scopes.len() == 1, "Push adds scope");

    solver.push();
    assert!(solver.scopes.len() == 2, "Second push adds scope");

    solver.pop();
    assert!(solver.scopes.len() == 1, "Pop removes scope");

    solver.pop();
    assert!(solver.scopes.is_empty(), "Final pop returns to empty");
}

/// Pop on empty scopes is safe (no-op)
#[kani::proof]
fn proof_pop_empty_is_safe() {
    let terms = ay_core::term::TermStore::new();
    let mut solver = LiaSolver::new(&terms);

    solver.pop();
    assert!(solver.scopes.is_empty(), "Pop on empty is no-op");
}

/// Reset clears all state
#[kani::proof]
fn proof_reset_clears_state() {
    let terms = ay_core::term::TermStore::new();
    let mut solver = LiaSolver::new(&terms);

    // Add some state
    solver.push();
    solver.integer_vars.insert(ay_core::term::TermId(42));
    solver.asserted.push((ay_core::term::TermId(1), true));

    solver.reset();

    assert!(solver.integer_vars.is_empty(), "Reset clears integer_vars");
    assert!(solver.asserted.is_empty(), "Reset clears asserted");
    assert!(solver.scopes.is_empty(), "Reset clears scopes");
}

/// Register integer var adds to set
#[kani::proof]
fn proof_register_integer_var() {
    let terms = ay_core::term::TermStore::new();
    let mut solver = LiaSolver::new(&terms);

    let term = ay_core::term::TermId(5);
    assert!(
        !solver.integer_vars.contains(&term),
        "Not initially registered"
    );

    solver.register_integer_var(term);
    assert!(solver.integer_vars.contains(&term), "Term is registered");

    // Registering twice is idempotent
    solver.register_integer_var(term);
    assert!(
        solver.integer_vars.len() == 1,
        "Duplicate registration is idempotent"
    );
}

/// Asserting a constant Bool contradiction is UNSAT.
///
/// This covers cases like `X != X` where the term layer folds `(= X X)` to `true`.
#[kani::proof]
fn proof_bool_constant_contradiction_is_unsat() {
    let mut terms = ay_core::term::TermStore::new();

    // X != X should be UNSAT (reflexivity of equality)
    let x = terms.mk_var("X", Sort::Int);
    let eq_xx = terms.mk_eq(x, x);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq_xx, false); // X != X

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "X != X must be UNSAT (reflexivity), got {:?}",
        result
    );
}

// ========================================================================
// LIA Completeness Proofs (#800)
// ========================================================================
//
// These proofs verify algebraic properties that ensure LIA completeness.
// They catch bugs like #793 where the solver returned Unknown for decidable QF_LIA.

/// Equality substitution completeness: If A = B, then (A + k) = (B + k).
///
/// Equivalently: A = B AND (A + k) != (B + k) must be UNSAT.
/// This is the exact property that #793 violated.
///
/// REQUIRES: LIA solver correctly handles equality constraints
/// ENSURES: For any k, asserting A = B AND (A + k) != (B + k) yields UNSAT
#[kani::proof]
#[kani::unwind(5)]
fn proof_equality_substitution_completeness() {
    let mut terms = ay_core::term::TermStore::new();

    // Use symbolic k from Kani
    let k_val: i32 = kani::any();
    kani::assume(k_val > -10 && k_val < 10);

    let a = terms.mk_var("A", Sort::Int);
    let b = terms.mk_var("B", Sort::Int);
    let k_term = terms.mk_int(BigInt::from(k_val));
    let one = terms.mk_int(BigInt::from(1));

    // A = B (using multiplication by 1 to match PDR's pattern)
    let one_times_b = terms.mk_mul(vec![one, b]);
    let eq_ab = terms.mk_eq(a, one_times_b);

    // (A + k) != (B + k)
    let a_plus_k = terms.mk_add(vec![a, k_term]);
    let b_plus_k = terms.mk_add(vec![b, k_term]);
    let diseq = terms.mk_eq(a_plus_k, b_plus_k);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq_ab, true); // A = B
    solver.assert_literal(diseq, false); // (A + k) != (B + k)

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_)
                | TheoryResult::UnsatWithFarkas(_)
                | TheoryResult::NeedSplit(_)
                | TheoryResult::NeedDisequalitySplit(_)
        ),
        "A = B AND (A + k) != (B + k) must be UNSAT or split request (not Unknown)"
    );
}

/// Transitivity completeness: If A = B and B = C, then A = C.
///
/// Equivalently: A = B AND B = C AND A != C must be UNSAT.
///
/// REQUIRES: LIA solver correctly handles equality transitivity
/// ENSURES: Asserting A = B AND B = C AND A != C yields UNSAT
#[kani::proof]
#[kani::unwind(5)]
fn proof_transitivity_completeness() {
    let mut terms = ay_core::term::TermStore::new();

    let a = terms.mk_var("A", Sort::Int);
    let b = terms.mk_var("B", Sort::Int);
    let c = terms.mk_var("C", Sort::Int);

    // A = B
    let eq_ab = terms.mk_eq(a, b);
    // B = C
    let eq_bc = terms.mk_eq(b, c);
    // A != C
    let eq_ac = terms.mk_eq(a, c);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq_ab, true); // A = B
    solver.assert_literal(eq_bc, true); // B = C
    solver.assert_literal(eq_ac, false); // A != C

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_)
                | TheoryResult::UnsatWithFarkas(_)
                | TheoryResult::NeedDisequalitySplit(_)
        ),
        "A = B AND B = C AND A != C must be UNSAT or split request"
    );
}
