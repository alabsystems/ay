// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{FpDecomposed, FpPrecision, FpSolver, RoundingMode, TermStore};
use std::cell::{Cell, RefCell};
use std::panic::{catch_unwind, AssertUnwindSafe};

#[path = "tests/ownership.rs"]
mod ownership;
#[path = "tests/parity.rs"]
mod parity;
#[path = "tests/recursive.rs"]
mod recursive;
#[path = "tests/recursive_bv.rs"]
mod recursive_bv;
#[path = "tests/sqrt.rs"]
mod sqrt;

fn symbolic(
    terms: &TermStore,
    precision: FpPrecision,
) -> (FpSolver<'_>, FpDecomposed, FpDecomposed) {
    let mut solver = FpSolver::new(terms);
    let x = solver.fresh_decomposed(precision);
    let y = solver.fresh_decomposed(precision);
    (solver, x, y)
}

fn assert_monotone(trace: &[FpBuildProgress]) {
    assert_ne!(trace.len(), 0);
    assert_eq!(trace[0].stage, FpBuildStage::Setup);
    for pair in trace.windows(2) {
        assert!(pair[0].variables <= pair[1].variables);
        assert!(pair[0].clauses <= pair[1].clauses);
    }
}

fn interrupt_after_two_progressing_rows(precision: FpPrecision, stage: FpBuildStage) {
    let terms = TermStore::new();
    let (solver, x, y) = symbolic(&terms, precision);
    let initial_variables = solver.num_vars();
    let trace = RefCell::new(Vec::new());
    let last_row = Cell::new(None::<(u32, usize)>);
    let advances = Cell::new(0);
    let enabled = Cell::new(true);
    let mut stop = |progress: FpBuildProgress| {
        trace.borrow_mut().push(progress);
        if progress.stage == stage {
            if let Some((variables, clauses)) = last_row.get() {
                if progress.variables > variables && progress.clauses > clauses {
                    advances.set(advances.get() + 1);
                }
            }
            last_row.set(Some((progress.variables, progress.clauses)));
        }
        enabled.get() && advances.get() >= 2
    };
    let mut transaction = FpConstruction::new(solver, &mut stop).unwrap();
    let result = if stage == FpBuildStage::DivideRow {
        transaction.try_make_div(&x, &y, RoundingMode::RNE)
    } else {
        transaction.try_make_rem(&x, &y)
    };
    assert!(matches!(result, Err(FpBuildError::Interrupted)));
    assert_eq!(advances.get(), 2);
    let stopped = *trace.borrow().last().unwrap();
    assert_eq!(stopped.stage, stage);
    assert!(stopped.variables > initial_variables);
    assert!(stopped.clauses > 0);
    assert_monotone(&trace.borrow());
    let calls = trace.borrow().len();

    // Resetting the external token cannot recover an owned, partially emitted
    // encoding. Neither another operation nor finish may call it again.
    enabled.set(false);
    assert!(matches!(
        transaction.try_make_div(&x, &y, RoundingMode::RTZ),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(
        transaction.try_make_rem(&x, &y),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(
        transaction.finish(),
        Err(FpBuildError::Interrupted)
    ));
    assert_eq!(trace.borrow().len(), calls);
}

#[test]
fn native_division_interrupts_after_real_rows_and_never_publishes_partial_cnf() {
    for precision in [FpPrecision::Float16, FpPrecision::Float32] {
        interrupt_after_two_progressing_rows(precision, FpBuildStage::DivideRow);
    }
}

#[test]
fn native_remainder_interrupts_inside_real_multiply_and_exponent_loops() {
    // Float64 retains modular squaring; smaller exponent formats can now use
    // direct reduction and correctly never enter a modular multiplier.
    // Stop after two progressing rows, without completing the wide circuit.
    for stage in [FpBuildStage::MultiplyRow, FpBuildStage::RemainderExponent] {
        interrupt_after_two_progressing_rows(FpPrecision::Float64, stage);
    }
}

#[test]
fn callback_panic_is_sticky_after_partial_native_construction() {
    let terms = TermStore::new();
    let (solver, x, y) = symbolic(&terms, FpPrecision::Float16);
    let panic_enabled = Cell::new(true);
    let calls = Cell::new(0);
    let rows = Cell::new(0);
    let mut stop = |progress: FpBuildProgress| {
        calls.set(calls.get() + 1);
        if progress.stage == FpBuildStage::DivideRow {
            rows.set(rows.get() + 1);
            if rows.get() == 4 && panic_enabled.get() {
                assert!(progress.clauses > 0);
                panic!("test callback panic after divider rows");
            }
        }
        false
    };
    let mut transaction = FpConstruction::new(solver, &mut stop).unwrap();
    assert!(catch_unwind(AssertUnwindSafe(|| {
        transaction.try_make_div(&x, &y, RoundingMode::RNE)
    }))
    .is_err());
    assert_eq!(rows.get(), 4);
    let stopped_calls = calls.get();
    panic_enabled.set(false);
    assert!(matches!(
        transaction.try_make_rem(&x, &y),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(
        transaction.finish(),
        Err(FpBuildError::Interrupted)
    ));
    assert_eq!(calls.get(), stopped_calls);
}

#[test]
fn setup_operation_and_final_publication_are_separate_refusal_boundaries() {
    let terms = TermStore::new();
    for stage in [
        FpBuildStage::Setup,
        FpBuildStage::Operation,
        FpBuildStage::Finalize,
    ] {
        let (solver, x, y) = symbolic(&terms, FpPrecision::Float16);
        let trace = RefCell::new(Vec::new());
        let mut stop = |progress: FpBuildProgress| {
            trace.borrow_mut().push(progress);
            progress.stage == stage
        };
        let created = FpConstruction::new(solver, &mut stop);
        if stage == FpBuildStage::Setup {
            assert!(matches!(created, Err(FpBuildError::Interrupted)));
            assert_eq!(trace.borrow().len(), 1);
        } else {
            let mut transaction = created.unwrap();
            if stage == FpBuildStage::Operation {
                assert!(matches!(
                    transaction.try_make_div(&x, &y, RoundingMode::RNE),
                    Err(FpBuildError::Interrupted)
                ));
            }
            assert!(matches!(
                transaction.finish(),
                Err(FpBuildError::Interrupted)
            ));
        }
        assert_eq!(trace.borrow().last().unwrap().stage, stage);
        assert!(trace.borrow().iter().all(|p| p.clauses == 0));
    }
}

#[test]
fn both_finalization_polls_can_refuse_without_a_completed_artifact() {
    let terms = TermStore::new();
    for stop_at in [1, 2] {
        let calls = Cell::new(0);
        let finalizations = Cell::new(0);
        let mut stop = |progress: FpBuildProgress| {
            calls.set(calls.get() + 1);
            if progress.stage == FpBuildStage::Finalize {
                finalizations.set(finalizations.get() + 1);
            }
            finalizations.get() == stop_at
        };
        let transaction = FpConstruction::new(FpSolver::new(&terms), &mut stop).unwrap();
        assert!(matches!(
            transaction.finish(),
            Err(FpBuildError::Interrupted)
        ));
        assert_eq!(finalizations.get(), stop_at);
        assert_eq!(calls.get(), stop_at + 1); // Setup, then publication polls.
    }
}

#[test]
fn caught_encoder_panic_after_a_healthy_callback_also_poisoned_the_owner() {
    let terms = TermStore::new();
    let (solver, mut x, y) = symbolic(&terms, FpPrecision::Float16);
    // This intentionally violates the existing well-formed decomposition
    // contract. It tests unwind containment, not acceptance of malformed FP.
    x.exponent.clear();
    let calls = Cell::new(0);
    let mut stop = |_| {
        calls.set(calls.get() + 1);
        false
    };
    let mut transaction = FpConstruction::new(solver, &mut stop).unwrap();
    assert!(catch_unwind(AssertUnwindSafe(|| {
        transaction.try_make_div(&x, &y, RoundingMode::RNE)
    }))
    .is_err());
    assert!(calls.get() >= 2); // Setup and a healthy operation checkpoint.
    let stopped_calls = calls.get();
    assert!(matches!(
        transaction.try_make_rem(&y, &y),
        Err(FpBuildError::Interrupted)
    ));
    assert!(matches!(
        transaction.finish(),
        Err(FpBuildError::Interrupted)
    ));
    assert_eq!(calls.get(), stopped_calls);
}

#[test]
fn variable_frontier_refuses_before_callbacks_and_keeps_the_exact_empty_boundary() {
    let terms = TermStore::new();
    let calls = Cell::new(0);
    let mut allow = |_| {
        calls.set(calls.get() + 1);
        false
    };
    let mut invalid = FpSolver::new(&terms);
    invalid.next_var = i32::MAX as u32 + 2;
    assert!(matches!(
        FpConstruction::new(invalid, &mut allow),
        Err(FpBuildError::VariableLimit)
    ));
    assert_eq!(calls.get(), 0);

    let mut boundary = FpSolver::new(&terms);
    boundary.next_var = i32::MAX as u32 + 1;
    // The frontier can represent an existing imported namespace. No new
    // variable is allocated here: checkpoints are not allocator reservations.
    let built = FpConstruction::new(boundary, &mut allow)
        .unwrap()
        .finish()
        .unwrap();
    assert_eq!(built.cache.next_var, i32::MAX as u32 + 1);
    assert_eq!(built.clauses.len(), 0);
    assert_eq!(calls.get(), 3); // Setup and both final admission polls.

    let mut control = Cooperative::new(&mut allow);
    let invalid = FpBuildProgress {
        stage: FpBuildStage::Operation,
        variables: i32::MAX as u32 + 1,
        clauses: 0,
    };
    assert_eq!(
        control.checkpoint(invalid),
        Err(FpBuildError::VariableLimit)
    );
    assert_eq!(
        control.checkpoint(FpBuildProgress {
            variables: 0,
            ..invalid
        }),
        Err(FpBuildError::VariableLimit)
    );
    assert_eq!(calls.get(), 3);
}
