// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_dpll::api::{Logic, Solver, SolverError, Sort};

#[test]
fn structural_bitwise_applications_keep_explicit_triggers() {
    let mut solver = Solver::new(Logic::All);
    let x = solver.try_fresh_var("x", Sort::bitvec(8)).unwrap();
    let zero = solver.bv_const(0, 8);
    let ones = solver.bv_const(255, 8);
    let patterns = [
        (solver.try_bvor_structural(x, x).unwrap(), x, x),
        (solver.try_bvor_structural(x, zero).unwrap(), zero, x),
        (solver.try_bvor_structural(x, ones).unwrap(), ones, ones),
        (solver.try_bvand_structural(x, zero).unwrap(), zero, zero),
        (solver.try_bvxor_structural(x, x).unwrap(), x, zero),
    ];
    assert_eq!(solver.try_bvor(x, x).unwrap(), x);
    assert_eq!(solver.try_bvor(x, zero).unwrap(), x);
    assert_eq!(solver.try_bvor(x, ones).unwrap(), ones);
    for (pattern, rhs, value) in patterns {
        assert_eq!(solver.term_sort(pattern), Sort::bitvec(8));
        assert_eq!(solver.app_arg(pattern, 0), Some(x));
        assert_eq!(solver.app_arg(pattern, 1), Some(rhs));
        let body = solver.try_eq(pattern, value).unwrap();
        let quantifier = solver
            .try_forall_with_triggers(&[x], body, &[&[pattern]])
            .unwrap();
        assert_eq!(
            solver.quantifier_triggers(quantifier),
            Some(vec![vec![pattern]])
        );
    }

    let wide = solver.bv_const(0, 16);
    assert!(matches!(
        solver.try_bvor_structural(x, wide),
        Err(SolverError::SortMismatch { .. })
    ));
    let mut foreign = Solver::new(Logic::All);
    let outside = foreign.bv_const(0, 8);
    assert!(solver.try_bvor_structural(x, outside).is_err());
}

#[test]
fn structural_bitwise_ground_applications_keep_bitvector_semantics() {
    let mut solver = Solver::new(Logic::QfBv);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let zero = solver.bv_const(0, 8);
    let ones = solver.bv_const(255, 8);
    for (application, value) in [
        (solver.try_bvor_structural(x, x).unwrap(), x),
        (solver.try_bvor_structural(x, zero).unwrap(), x),
        (solver.try_bvor_structural(x, ones).unwrap(), ones),
        (solver.try_bvand_structural(x, zero).unwrap(), zero),
        (solver.try_bvxor_structural(x, x).unwrap(), zero),
    ] {
        assert_eq!(solver.app_num_args(application), 2);
        let equal = solver.try_eq(application, value).unwrap();
        let different = solver.try_not(equal).unwrap();
        solver.push();
        solver.assert_term(different);
        assert!(solver.check_sat().is_unsat());
        solver.pop();
    }
}
