// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for `check_sat_assuming` and `get_unsat_assumptions`.

use crate::api::*;

#[test]
fn test_check_sat_assuming_basic() {
    // Basic check_sat_assuming: assumptions are temporary
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    // Assert x >= 0 permanently
    let x_ge_0 = solver.ge(x, zero);
    solver.assert_term(x_ge_0);

    // SAT without assumptions
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    // Check with assumption x < 0 - should be UNSAT
    let x_lt_0 = solver.lt(x, zero);
    assert!(solver.check_sat_assuming(&[x_lt_0]).is_unsat());

    // SAT again - assumption was temporary
    let x_eq_1 = solver.eq(x, one);
    solver.assert_term(x_eq_1);
    assert_eq!(solver.check_sat(), SolveResult::Sat);
}

#[test]
fn test_check_sat_assuming_multiple() {
    // Multiple assumptions at once
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    // No permanent assertions
    // Check with assumptions: x = 1, y = 0
    let x_eq_1 = solver.eq(x, one);
    let y_eq_0 = solver.eq(y, zero);

    assert_eq!(
        solver.check_sat_assuming(&[x_eq_1, y_eq_0]),
        SolveResult::Sat
    );

    // Now check with conflicting assumptions: x > 0, x < 0
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);

    assert!(solver.check_sat_assuming(&[x_gt_0, x_lt_0]).is_unsat());
}

#[test]
fn test_get_unsat_assumptions() {
    // get_unsat_assumptions returns assumptions after UNSAT
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    // Assert x = 0 permanently
    let x_eq_0 = solver.eq(x, zero);
    solver.assert_term(x_eq_0);

    // Check with assumption x = 1 - should be UNSAT
    let x_eq_1 = solver.eq(x, one);
    let result = solver.check_sat_assuming(&[x_eq_1]);
    assert!(result.is_unsat());

    // get_unsat_assumptions should return the conflicting assumptions
    let unsat_assumptions = solver.unsat_assumptions();
    assert!(unsat_assumptions.is_some());
    // Current implementation returns all assumptions
    assert_eq!(unsat_assumptions.unwrap().len(), 1);
}

#[test]
fn test_get_unsat_assumptions_none_when_sat() {
    // get_unsat_assumptions returns None when last result was SAT
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);

    // Check with assumption x >= 0 - should be SAT
    let x_ge_0 = solver.ge(x, zero);
    let result = solver.check_sat_assuming(&[x_ge_0]);
    assert_eq!(result, SolveResult::Sat);

    // get_unsat_assumptions should return None
    assert!(solver.unsat_assumptions().is_none());
}

#[test]
fn test_check_sat_assuming_preserves_permanent() {
    // Assumptions don't affect permanent assertions
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let ten = solver.int_const(10);

    // Assert 0 <= x <= 10 permanently
    let x_ge_0 = solver.ge(x, zero);
    let x_le_10 = solver.le(x, ten);
    solver.assert_term(x_ge_0);
    solver.assert_term(x_le_10);

    // Make check-sat-assuming with conflicting assumption
    let minus_one = solver.int_const(-1);
    let x_lt_minus = solver.lt(x, minus_one);
    assert!(solver.check_sat_assuming(&[x_lt_minus]).is_unsat());

    // Original constraints still hold
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    // Model should be in [0, 10]
    let model = solver.model().expect("Expected model").into_inner();
    let x_val = model.int_val_i64("x").expect("x should be in model");
    assert!((0..=10).contains(&x_val));
}

#[test]
fn test_check_sat_assuming_empty_assumptions() {
    // check_sat_assuming with empty assumptions behaves like check_sat
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);

    // x >= 0 AND x <= 1 is SAT
    let x_ge_0 = solver.ge(x, zero);
    let x_le_1 = solver.le(x, one);
    solver.assert_term(x_ge_0);
    solver.assert_term(x_le_1);

    // Empty assumptions should return SAT like check_sat
    assert_eq!(solver.check_sat_assuming(&[]), SolveResult::Sat);
}

#[test]
fn test_check_sat_assuming_auflia_integer_split_cleanup_6689() {
    // AUFLIA check_sat_assuming must isolate split clauses and temporary theory
    // state so an UNSAT assumption-only split does not leak into the next solve.
    let mut solver = Solver::new(Logic::QfAuflia);

    let arr = solver.declare_const("arr", Sort::array(Sort::Int, Sort::Int));
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let forty_two = solver.int_const(42);

    let read0 = solver.select(arr, zero);
    let base_eq = solver.eq(read0, forty_two);
    solver.assert_term(base_eq);

    let two_x = solver.mul(two, x);
    let split_trigger = solver.eq(two_x, one);
    assert_eq!(
        solver.check_sat_assuming(&[split_trigger]),
        SolveResult::unsat(),
        "assumption-only AUFLIA integer split should be UNSAT"
    );

    assert_eq!(
        solver.check_sat_assuming(&[]),
        SolveResult::Sat,
        "empty AUFLIA assumptions after UNSAT should remain SAT"
    );
}

#[test]
fn test_get_unsat_assumptions_cleared_by_check_sat() {
    // get_unsat_assumptions is cleared when check_sat() is called
    // (to prevent returning stale assumptions)
    let mut solver = Solver::new(Logic::QfLia);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let neg_one = solver.int_const(-1);

    // First: check_sat_assuming with UNSAT result
    let x_gt_0 = solver.gt(x, zero);
    let x_lt_0 = solver.lt(x, zero);
    assert!(solver.check_sat_assuming(&[x_gt_0, x_lt_0]).is_unsat());
    // Assumptions are available
    assert!(solver.unsat_assumptions().is_some());

    // Now call regular check_sat with different constraints
    let x_gt_neg = solver.gt(x, neg_one);
    solver.assert_term(x_gt_neg);
    let x_lt_one = solver.lt(x, one);
    solver.assert_term(x_lt_one);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    // Assumptions should be cleared - get_unsat_assumptions returns None
    // (even if we made it UNSAT, the assumptions from before shouldn't be returned)
    assert!(
        solver.unsat_assumptions().is_none(),
        "get_unsat_assumptions should return None after check_sat()"
    );
}

#[test]
fn test_unsat_core_includes_assumption_literals_after_check_sat_assuming() {
    // #unsat-core-assumptions: after an assumption-bearing UNSAT with
    // :produce-unsat-cores, the core must include the load-bearing
    // assumption literal as verbatim term text alongside the named label
    // (z3-style flat mixed list). Soundness bar: the printed core together
    // with the unnamed assertions alone must be UNSAT — here the named
    // assertion (>= x 5) AND the assumption (< x 5) are both required.
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let five = solver.int_const(5);
    let ge = solver.ge(x, five);
    solver.try_assert_named(ge, "n1").unwrap();

    let lt = solver.lt(x, five);
    assert!(solver.check_sat_assuming(&[lt]).is_unsat());

    let core = solver.try_get_unsat_core().expect("core must be available");
    assert!(
        core.iter().any(|entry| entry == "n1"),
        "named participant must be in the core; got {core:?}"
    );
    assert!(
        core.iter()
            .any(|entry| entry.contains("x") && entry != "n1"),
        "the assumption literal must appear as verbatim term text (never \
         silently dropped); got {core:?}"
    );

    // get_unsat_assumptions stays a subset of the USER assumption terms
    // (SMT-LIB 2.6) even though the named assertion was assumption-tracked.
    let failed = solver
        .unsat_assumptions()
        .expect("unsat assumptions available");
    assert!(
        failed.iter().all(|t| t.id() == lt.id()),
        "unsat assumptions must be a subset of the user's literals"
    );
}

#[test]
fn test_unsat_core_assumptions_only_not_empty() {
    // Assumptions-only UNSAT (no named assertions): the core must carry the
    // contradicting assumption literals, not the historical empty list.
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let le = solver.le(x, zero);
    let ge = solver.ge(x, one);
    assert!(solver.check_sat_assuming(&[le, ge]).is_unsat());

    let core = solver.try_get_unsat_core().expect("core must be available");
    assert!(
        !core.is_empty(),
        "assumptions-only unsat must not print an empty core (the empty set \
         is satisfiable); got {core:?}"
    );
}

/// Shared setup for the #named-cores-ground-sat completeness pins below:
/// deductive-checks's standard encoding shape — `:produce-unsat-cores` + `:named`
/// ground mixed Int/BV/Array assertions that are trivially SAT together.
fn named_cores_ground_mixed_solver() -> (Solver, Term) {
    let mut solver = Solver::new(Logic::All);
    solver.set_produce_unsat_cores(true);

    let bv32 = Sort::bitvec(32);
    let arr = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
    let s = solver.declare_const("s", arr.clone());
    let s_pre = solver.declare_const("s_pre", arr);
    let seed = solver.declare_const("seed", bv32.clone());
    let seed_pre = solver.declare_const("seed_pre", bv32);
    let len = solver.declare_const("len", Sort::Int);
    let len_pre = solver.declare_const("len_pre", Sort::Int);

    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let idx0 = solver.bv_const_u64(0, 64);

    let dn0 = solver.le(zero, len);
    let dn1 = solver.le(zero, len_pre);
    let sel_pre = solver.select(s_pre, idx0);
    let dn2 = solver.eq(sel_pre, seed_pre);
    let sel = solver.select(s, idx0);
    let dn3 = solver.eq(sel, seed);
    let dn4 = solver.le(one, len_pre);
    let dn5 = solver.lt(len, one);

    solver.try_assert_named(dn0, "dn0").unwrap();
    solver.try_assert_named(dn1, "dn1").unwrap();
    solver.try_assert_named(dn2, "dn2").unwrap();
    solver.try_assert_named(dn3, "dn3").unwrap();
    solver.try_assert_named(dn4, "dn4").unwrap();
    solver.try_assert_named(dn5, "dn5").unwrap();

    (solver, dn1)
}

#[test]
fn test_named_cores_ground_mixed_int_bv_array_check_sat_stays_sat() {
    // #named-cores-ground-sat: the named→assumption core redirect must not
    // cost solve completeness on plain check-sat — the identical formula
    // without cores/names is sat, so this must be sat too (the API boundary
    // fail-closes any unminted Sat, so this also pins that the rescue path
    // mints its verdict through the #sat-chokepoint funnel).
    let (mut solver, _lit) = named_cores_ground_mixed_solver();
    assert_eq!(
        solver.check_sat(),
        SolveResult::Sat,
        "ground mixed Int/BV/Array with cores+named must stay sat"
    );
}

#[test]
fn test_named_cores_ground_mixed_int_bv_array_check_sat_assuming_stays_sat() {
    // #named-cores-ground-sat, check-sat-assuming flavor: this is deductive-checks's
    // incremental-Unknown rescue path (re-solving the identical query via the
    // assumption mechanism), which d5adb8dd rerouted through the
    // named→assumption redirect. A consistent assumption literal over the
    // same ground mixed shape must keep the sat verdict.
    let (mut solver, lit) = named_cores_ground_mixed_solver();
    assert!(
        solver.check_sat_assuming(&[lit]).is_sat(),
        "ground mixed Int/BV/Array with cores+named must stay sat under \
         check-sat-assuming with a consistent literal"
    );
}
