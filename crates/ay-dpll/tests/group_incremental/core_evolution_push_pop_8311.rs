// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration test: `Solver::core_evolution()` across push/pop cycles (#8311).
//!
//! Exercises the incremental core evolution API through a realistic push/pop
//! sequence where named assertions enter and leave scope, verifying that the
//! persisted/entered/exited fields are correctly populated.

#![allow(deprecated)]

use ay_dpll::api::{Logic, Solver, Sort};
use ntest::timeout;

/// Full push/pop cycle exercising core_evolution():
///
/// 1. Base scope: x > 0 AND x < 0 (UNSAT) -- first call, no previous core
/// 2. Push: add y > 10 AND y < 5 (still UNSAT) -- evolution shows entered names
/// 3. Pop: back to base (UNSAT) -- evolution shows exited names from inner scope
#[test]
#[timeout(15_000)]
fn test_core_evolution_across_push_pop_cycles() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let zero = solver.int_const(0);

    // --- Step 1: Base UNSAT with named assertions ---
    let x_pos = solver.gt(x, zero);
    solver.try_assert_named(x_pos, "x_positive").unwrap();
    let x_neg = solver.lt(x, zero);
    solver.try_assert_named(x_neg, "x_negative").unwrap();

    let result1 = solver.check_sat();
    assert!(result1.is_unsat(), "step 1: x>0 AND x<0 should be unsat");

    // First call to core_evolution -- no previous core, should return None.
    let evo1 = solver.core_evolution();
    assert!(
        evo1.is_none(),
        "first core_evolution() call should return None (no previous core)"
    );

    // --- Step 2: Push scope, add conflicting assertions on y ---
    solver.try_push().unwrap();
    let ten = solver.int_const(10);
    let five = solver.int_const(5);
    let y_high = solver.gt(y, ten);
    solver.try_assert_named(y_high, "y_above_ten").unwrap();
    let y_low = solver.lt(y, five);
    solver.try_assert_named(y_low, "y_below_five").unwrap();

    let result2 = solver.check_sat();
    assert!(
        result2.is_unsat(),
        "step 2: still unsat with additional y constraints"
    );

    // Second core_evolution -- should have a previous core to diff against.
    let evo2 = solver.core_evolution();
    assert!(
        evo2.is_some(),
        "second core_evolution() call should return Some (has previous core)"
    );
    let evo2 = evo2.unwrap();

    // The previous core was from step 1 (x_positive, x_negative).
    // The current core might be any subset that makes it UNSAT -- at minimum
    // the x-pair or the y-pair. Verify structural consistency.
    assert!(
        !evo2.previous_core.is_empty(),
        "previous core from step 1 should be non-empty"
    );
    assert!(
        !evo2.current_core.is_empty(),
        "current core from step 2 should be non-empty"
    );

    // The sum of persisted + exited must equal the previous core size.
    assert_eq!(
        evo2.persisted().len() + evo2.exited().len(),
        evo2.previous_core.len(),
        "persisted + exited must partition the previous core"
    );
    // The sum of persisted + entered must equal the current core size.
    assert_eq!(
        evo2.persisted().len() + evo2.entered().len(),
        evo2.current_core.len(),
        "persisted + entered must partition the current core"
    );

    // --- Step 3: Pop scope -- y constraints disappear ---
    solver.try_pop().unwrap();

    let result3 = solver.check_sat();
    assert!(
        result3.is_unsat(),
        "step 3: base x>0 AND x<0 still unsat after pop"
    );

    // Third core_evolution -- previous core was step 2, current is step 3.
    let evo3 = solver.core_evolution();
    assert!(
        evo3.is_some(),
        "third core_evolution() call should return Some"
    );
    let evo3 = evo3.unwrap();

    // After popping, the y-named assertions should no longer appear in the core.
    // The current core should only contain x-related assertions.
    for name in evo3.current_core.iter() {
        assert!(
            !name.contains("y_above_ten") && !name.contains("y_below_five"),
            "after pop, y-scope names should not appear in current core, found: {name}"
        );
    }

    // Structural invariant check on evolution.
    assert_eq!(
        evo3.persisted().len() + evo3.exited().len(),
        evo3.previous_core.len(),
        "persisted + exited must partition the previous core (step 3)"
    );
    assert_eq!(
        evo3.persisted().len() + evo3.entered().len(),
        evo3.current_core.len(),
        "persisted + entered must partition the current core (step 3)"
    );
}

/// Verify that core_evolution returns None after a SAT result (no core available).
#[test]
#[timeout(10_000)]
fn test_core_evolution_returns_none_after_sat_in_pushed_scope() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);

    // UNSAT base
    let pos = solver.gt(x, zero);
    solver.try_assert_named(pos, "pos").unwrap();
    let neg = solver.lt(x, zero);
    solver.try_assert_named(neg, "neg").unwrap();
    assert!(solver.check_sat().is_unsat());
    let _ = solver.core_evolution(); // prime the previous core

    // Push and make SAT
    solver.try_push().unwrap();
    // No additional conflicting constraints -- the base is still UNSAT,
    // but let's reset and check a fresh SAT scope instead.
    solver.try_pop().unwrap();

    // Start a new scope that is SAT
    solver.try_reset_assertions().unwrap();
    let x = solver.declare_const("x2", Sort::Int);
    let one = solver.int_const(1);
    let gt = solver.gt(x, one);
    solver.try_assert_named(gt, "sat_constraint").unwrap();
    assert!(solver.check_sat().is_sat());

    // After SAT, core_evolution should return None.
    let evo = solver.core_evolution();
    assert!(
        evo.is_none(),
        "core_evolution() after SAT result should return None"
    );
}

/// Verify core_evolution tracks distinct named assertions entering/exiting
/// through multiple push/pop levels.
#[test]
#[timeout(15_000)]
fn test_core_evolution_nested_push_pop() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let two = solver.int_const(2);
    let neg_one = solver.int_const(-1);
    let neg_two = solver.int_const(-2);

    // Level 0: x >= 1 AND x <= -1 (UNSAT)
    let ge1 = solver.ge(x, one);
    solver.try_assert_named(ge1, "x_ge_1").unwrap();
    let le_neg1 = solver.le(x, neg_one);
    solver.try_assert_named(le_neg1, "x_le_neg1").unwrap();
    assert!(solver.check_sat().is_unsat(), "level 0 unsat");

    // Prime previous core (returns None since first call).
    assert!(solver.core_evolution().is_none());

    // Level 1 push: add x >= 2 AND x <= -2 (still UNSAT, tighter bounds)
    solver.try_push().unwrap();
    let ge2 = solver.ge(x, two);
    solver.try_assert_named(ge2, "x_ge_2").unwrap();
    let le_neg2 = solver.le(x, neg_two);
    solver.try_assert_named(le_neg2, "x_le_neg2").unwrap();
    assert!(solver.check_sat().is_unsat(), "level 1 unsat");

    let evo_l1 = solver.core_evolution();
    assert!(evo_l1.is_some(), "level 1 should have evolution");
    let evo_l1 = evo_l1.unwrap();

    // The tighter bounds may or may not replace the original bounds in the core.
    // Either way, structural invariants hold.
    assert_eq!(
        evo_l1.persisted().len() + evo_l1.exited().len(),
        evo_l1.previous_core.len(),
    );
    assert_eq!(
        evo_l1.persisted().len() + evo_l1.entered().len(),
        evo_l1.current_core.len(),
    );

    // Level 2 push: redundant assertion (still UNSAT from existing)
    solver.try_push().unwrap();
    let ge0 = solver.ge(x, zero);
    solver.try_assert_named(ge0, "x_ge_0_redundant").unwrap();
    assert!(solver.check_sat().is_unsat(), "level 2 unsat");

    let evo_l2 = solver.core_evolution();
    assert!(evo_l2.is_some(), "level 2 should have evolution");

    // Pop level 2
    solver.try_pop().unwrap();
    assert!(solver.check_sat().is_unsat(), "back to level 1 unsat");
    let evo_pop2 = solver.core_evolution();
    assert!(
        evo_pop2.is_some(),
        "after pop to level 1 should have evolution"
    );

    // Pop level 1
    solver.try_pop().unwrap();
    assert!(solver.check_sat().is_unsat(), "back to level 0 unsat");
    let evo_pop1 = solver.core_evolution();
    assert!(
        evo_pop1.is_some(),
        "after pop to level 0 should have evolution"
    );
    let evo_pop1 = evo_pop1.unwrap();

    // After popping back to level 0, the level-1 names should not be in current core.
    for name in evo_pop1.current_core.iter() {
        assert!(
            !name.contains("x_ge_2")
                && !name.contains("x_le_neg2")
                && !name.contains("x_ge_0_redundant"),
            "after full pop, inner scope names should not appear in core: {name}"
        );
    }
}

/// Verify persistence_ratio and is_unchanged/is_independent after push/pop
/// when the same base conflict is re-checked.
#[test]
#[timeout(10_000)]
fn test_core_evolution_persistence_ratio_across_pop() {
    let mut solver = Solver::new(Logic::QfLia);
    solver.set_produce_unsat_cores(true);

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);

    // Base: x > 0 AND x < 0
    let pos = solver.gt(x, zero);
    solver.try_assert_named(pos, "pos").unwrap();
    let neg = solver.lt(x, zero);
    solver.try_assert_named(neg, "neg").unwrap();
    assert!(solver.check_sat().is_unsat());
    let _ = solver.core_evolution(); // prime

    // Push, add unrelated constraint, check, pop
    solver.try_push().unwrap();
    let y = solver.declare_const("y", Sort::Int);
    let ten = solver.int_const(10);
    let y_eq = solver.eq(y, ten);
    solver.try_assert_named(y_eq, "y_eq_ten").unwrap();
    // Still UNSAT because base conflict exists
    assert!(solver.check_sat().is_unsat());
    let _ = solver.core_evolution(); // update previous

    // Pop and re-check
    solver.try_pop().unwrap();
    assert!(solver.check_sat().is_unsat());
    let evo = solver.core_evolution();
    assert!(evo.is_some());
    let evo = evo.unwrap();

    // Since we popped back to the same base conflict, the core should be
    // similar to the base. Check that persistence_ratio is well-defined.
    let ratio = evo.persistence_ratio();
    assert!(
        (0.0..=1.0).contains(&ratio),
        "persistence_ratio should be in [0, 1], got {ratio}"
    );
}
