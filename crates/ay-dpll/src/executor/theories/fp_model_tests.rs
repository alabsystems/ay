// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::TermStore;
use ay_fp::FpSolver;

#[test]
fn test_extract_fp_model_positive_zero() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 24));

    let mut fp_solver = FpSolver::new(&terms);
    let _decomp = fp_solver.get_fp(x);
    let num_vars = fp_solver.num_vars();
    let term_to_fp = fp_solver.term_to_fp().clone();

    // All bits false => sign=0, exp=0, sig=0 => +zero
    let sat_model = vec![false; num_vars as usize];

    let fp_model = Executor::extract_fp_model_from_bits(&sat_model, &term_to_fp, 0, &terms);

    assert_eq!(fp_model.values.len(), 1);
    let val = fp_model.values.get(&x).unwrap();
    assert_eq!(val.to_smtlib(), "(_ +zero 8 24)");
}

#[test]
fn test_extract_fp_model_nan() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::FloatingPoint(8, 24));

    let mut fp_solver = FpSolver::new(&terms);
    let _decomp = fp_solver.get_fp(x);
    let num_vars = fp_solver.num_vars();
    let term_to_fp = fp_solver.term_to_fp().clone();

    // All bits true => sign=1, exp=all-ones, sig=all-ones => NaN
    let sat_model = vec![true; num_vars as usize];

    let fp_model = Executor::extract_fp_model_from_bits(&sat_model, &term_to_fp, 0, &terms);

    assert_eq!(fp_model.values.len(), 1);
    let val = fp_model.values.get(&x).unwrap();
    assert_eq!(val.to_smtlib(), "(_ NaN 8 24)");
}
