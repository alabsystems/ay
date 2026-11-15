// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `get_values` must return exactly what repeated `get_value` calls
//! return, including when assignments carry an infinitesimal (the
//! batch shares one materialisation δ, and every per-term value is
//! the same materialisation `get_value` would produce).

use super::*;

#[test]
fn batch_get_values_matches_single_get_value_with_epsilons() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let unregistered = terms.mk_var("w", Sort::Real);
    let zero = terms.mk_rational(num_rational::BigRational::zero());
    let one = terms.mk_rational(num_rational::BigRational::one());
    // Strict bounds force ε-carrying assignments (x = 0 + ε).
    let x_pos = terms.mk_gt(x, zero);
    let y_pos = terms.mk_gt(y, zero);
    let sum = terms.mk_add(vec![x, y]);
    let sum_lt = terms.mk_lt(sum, one);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(x_pos, true);
    solver.assert_literal(y_pos, true);
    solver.assert_literal(sum_lt, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let batch = solver.get_values(&[x, y, sum, unregistered]);
    let singles = [
        solver.get_value(x),
        solver.get_value(y),
        solver.get_value(sum),
        solver.get_value(unregistered),
    ];
    assert_eq!(batch.len(), 4);
    for (batched, single) in batch.iter().zip(singles.iter()) {
        assert_eq!(batched, single, "batch value must equal single value");
    }
    let xv = batch[0].clone().expect("x registered");
    let yv = batch[1].clone().expect("y registered");
    assert!(xv > num_rational::BigRational::zero());
    assert!(yv > num_rational::BigRational::zero());
    assert!(xv + yv < num_rational::BigRational::one());
    assert_eq!(batch[3], None, "unregistered term has no value");
}
