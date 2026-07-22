// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_small_dense_reduce_interval_cap_is_tighter_than_generic_small_cap() {
    let mut normal = Solver::new(100);
    normal.num_original_clauses = 1000;
    assert!(
        !normal.small_dense_learned_reduce_policy(),
        "exact density 10.0 keeps the generic small-formula reduce schedule"
    );
    assert_eq!(
        normal.small_formula_reduce_interval_cap(),
        Some(SMALL_FORMULA_REDUCE_CAP_MULT * normal.num_original_clauses as u64)
    );

    let mut dense = Solver::new(100);
    dense.num_original_clauses = 1001;
    assert!(
        dense.small_dense_learned_reduce_policy(),
        "density above 10.0 enables the small-dense reduce schedule"
    );
    assert_eq!(
        dense.small_formula_reduce_interval_cap(),
        Some(SMALL_DENSE_REDUCE_CAP_MULT * dense.num_original_clauses as u64),
        "small-dense formulas cap the next reduce interval closer to formula size"
    );
}

#[test]
fn test_small_dense_reduce_interval_cap_respects_first_reduce_floor() {
    let mut dense = Solver::new(10);
    dense.num_original_clauses = 101;

    assert!(dense.small_dense_learned_reduce_policy());
    assert_eq!(
        dense.small_formula_reduce_interval_cap(),
        Some(FIRST_REDUCE_DB),
        "small dense cap must not schedule reductions before the first-reduce floor"
    );
}

#[test]
fn test_large_formula_has_no_small_reduce_interval_cap() {
    let mut solver = Solver::new(100);
    solver.num_original_clauses = SMALL_FORMULA_REDUCE_CAP_THRESHOLD + 1;

    assert_eq!(solver.small_formula_reduce_interval_cap(), None);
}
