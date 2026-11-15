// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::cell::Cell;
use std::panic::{catch_unwind, AssertUnwindSafe};

use super::*;
use crate::{FpBuildError, FpBuildStage};

#[test]
fn cancellation_inside_modular_rows_remains_sticky_after_reset() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let p = FpPrecision::Float16;
    let x = solver.fresh_decomposed(p);
    let y = solver.fresh_decomposed(p);
    let enabled = Cell::new(true);
    let calls = Cell::new(0);
    let rows = Cell::new(0);
    let mut stop = |progress: crate::FpBuildProgress| {
        calls.set(calls.get() + 1);
        if progress.stage == FpBuildStage::RemainderExponent {
            rows.set(rows.get() + 1);
            assert!(progress.clauses > 0);
        }
        enabled.get() && rows.get() >= 2
    };
    let mut attempt = FpConstruction::new(solver, &mut stop).expect("setup");
    assert!(matches!(
        attempt.try_make_truncating_rem(&x, &y),
        Err(FpBuildError::Interrupted)
    ));
    let stopped_calls = calls.get();
    enabled.set(false);
    assert!(matches!(
        attempt.try_make_truncating_rem(&x, &y),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
    assert_eq!(calls.get(), stopped_calls);
    assert_eq!(rows.get(), 2);
}

#[test]
fn callback_panic_cannot_publish_or_retry_partial_truncating_remainder() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let p = FpPrecision::Float16;
    let x = solver.fresh_decomposed(p);
    let y = solver.fresh_decomposed(p);
    let calls = Cell::new(0);
    let rows = Cell::new(0);
    let mut stop = |progress: crate::FpBuildProgress| {
        calls.set(calls.get() + 1);
        if progress.stage == FpBuildStage::RemainderExponent {
            rows.set(rows.get() + 1);
            if rows.get() == 2 {
                panic!("callback interrupted partial construction");
            }
        }
        false
    };
    let mut attempt = FpConstruction::new(solver, &mut stop).expect("setup");
    assert!(catch_unwind(AssertUnwindSafe(|| attempt.try_make_truncating_rem(&x, &y))).is_err());
    let stopped_calls = calls.get();
    assert!(matches!(
        attempt.try_make_truncating_rem(&x, &y),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
    assert_eq!(calls.get(), stopped_calls);
}

#[test]
fn finalization_refusal_drops_the_complete_encoding_without_publication() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let p = FpPrecision::Float16;
    let x = operand(&mut solver, p, (false, 17, 256));
    let y = operand(&mut solver, p, (false, 16, 512));
    let mut stop = |progress: crate::FpBuildProgress| progress.stage == FpBuildStage::Finalize;
    let mut attempt = FpConstruction::new(solver, &mut stop).expect("setup");
    attempt
        .try_make_truncating_rem(&x, &y)
        .expect("completed operation");
    assert!(matches!(attempt.finish(), Err(FpBuildError::Interrupted)));
}

#[test]
fn variable_frontier_refuses_before_any_new_operation_or_callback() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    solver.next_var = i32::MAX as u32 + 2;
    let calls = Cell::new(0);
    let mut stop = |_| {
        calls.set(calls.get() + 1);
        false
    };
    assert!(matches!(
        FpConstruction::new(solver, &mut stop),
        Err(FpBuildError::VariableLimit)
    ));
    assert_eq!(calls.get(), 0);
}

#[test]
fn symbolic_input_links_cannot_choose_an_ieee_remainder_instead() {
    let terms = TermStore::new();
    let mut solver = FpSolver::new(&terms);
    let p = FpPrecision::Float16;
    let x = solver.fresh_decomposed(p);
    let y = solver.fresh_decomposed(p);
    let mut healthy = |_| false;
    let mut attempt = FpConstruction::new(solver, &mut healthy).expect("setup");
    let result = attempt
        .try_make_truncating_rem(&x, &y)
        .expect("symbolic encoding");
    let mut built = attempt.finish().expect("complete symbolic encoding");
    assert!(!built.has_encoding_gap);
    for (fp, (sign, exponent, fraction)) in
        [(&x, (false, 17u64, 256u128)), (&y, (false, 16u64, 512u128))]
    {
        built
            .clauses
            .push(CnfClause::unit(if sign { fp.sign } else { -fp.sign }));
        for (i, &lit) in fp.exponent.iter().enumerate() {
            built
                .clauses
                .push(CnfClause::unit(if (exponent >> i) & 1 != 0 {
                    lit
                } else {
                    -lit
                }));
        }
        for (i, &lit) in fp.significand.iter().enumerate() {
            built
                .clauses
                .push(CnfClause::unit(if (fraction >> i) & 1 != 0 {
                    lit
                } else {
                    -lit
                }));
        }
    }
    let SatResult::Sat(model) = solve(&built, None) else {
        panic!("5 and 3 must be admitted by the generic symbolic circuit");
    };
    assert_eq!(
        exact::same_element(&decoded(p, &result, &model), &value(p, (false, 16, 0))),
        Some(true)
    );
    assert!(matches!(
        solve(&built, Some(CnfClause::unit(result.sign))),
        SatResult::Unsat(_)
    ));
}
