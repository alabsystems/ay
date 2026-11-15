// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use std::panic::AssertUnwindSafe;

#[derive(Clone, Copy)]
enum Boundary {
    Ground,
    Publication,
}

fn recover(
    solver: &BmcSolver,
    model: &FxHashMap<String, SmtValue>,
    witness: &DerivationWitness,
    names: &mut AcyclicNames<'_>,
    boundary: Boundary,
) -> bool {
    let queries = vec![&solver.problem.clauses()[1]];
    match boundary {
        Boundary::Ground => solver
            .ground_derivation_from_polynomial_witness(witness, model, &queries, names, deadline())
            .is_some(),
        Boundary::Publication => {
            match solver.verified_acyclic_dag_unsafe_from_model(
                witness.clone(),
                model,
                &queries,
                names,
                deadline(),
            ) {
                ChcEngineResult::Unsafe(cex) => {
                    assert!(
                        cex.has_ground_derivation(),
                        "must not enter legacy PDR fallback"
                    );
                    crate::ground_derivation::validate_ground_derivation(
                        &solver.problem,
                        cex.ground_derivation.as_ref().unwrap(),
                    )
                    .unwrap();
                    true
                }
                ChcEngineResult::Unknown => false,
                other => panic!("unexpected witness result: {other:?}"),
            }
        }
    }
}

fn run_ordinal(solver: &BmcSolver, boundary: Boundary, stop: usize) -> usize {
    let armed = Cell::new(false);
    let calls = Cell::new(0);
    let mut callback = || {
        if armed.get() {
            calls.set(calls.get() + 1);
            return calls.get() != stop;
        }
        true
    };
    let mut names = AcyclicNames::new(&solver.problem, &mut callback).unwrap();
    let model = model(solver, &SmtValue::BitVec(173, 8), &mut names);
    let witness = witness(solver, &model, &mut names).unwrap();
    // Establish a complete source-valid candidate before allowing the wrapper
    // to run: no test depends on a solver-backed recovery path.
    assert!(recover(
        solver,
        &model,
        &witness,
        &mut names,
        Boundary::Ground
    ));
    armed.set(true);
    let accepted = recover(solver, &model, &witness, &mut names, boundary);
    if stop == 0 {
        assert!(accepted);
        assert!(!names.stopped());
    } else {
        assert!(!accepted, "refusal at poll {stop}");
        assert!(names.stopped());
        assert_eq!(calls.get(), stop);
        assert!(!recover(solver, &model, &witness, &mut names, boundary));
        // Even an ordinary incomplete candidate must not reopen PDR once the
        // same naming/recovery attempt has refused.
        let mut incomplete = witness.clone();
        incomplete.query_clause = None;
        assert!(!recover(
            solver,
            &model,
            &incomplete,
            &mut names,
            Boundary::Publication
        ));
        assert_eq!(calls.get(), stop);
    }
    calls.get()
}

fn every_ordinal(boundary: Boundary) {
    let solver = fixture(ChcSort::BitVec(8));
    let before = format!("{:?}", solver.problem.clauses());
    let total = run_ordinal(&solver, boundary, 0);
    assert!(total > 5 && total < 1_000);
    for stop in 1..=total {
        run_ordinal(&solver, boundary, stop);
    }
    assert_eq!(run_ordinal(&solver, boundary, 0), total);
    assert_eq!(before, format!("{:?}", solver.problem.clauses()));
}

#[test]
fn every_ground_recovery_poll_refuses_stickily_and_fresh_retry_succeeds() {
    every_ordinal(Boundary::Ground);
}

#[test]
fn every_publication_poll_including_final_admission_refuses_without_fallback() {
    every_ordinal(Boundary::Publication);
}

#[test]
fn an_expired_deadline_refuses_before_callback_and_cannot_be_reopened() {
    let solver = fixture(ChcSort::BitVec(8));
    let armed = Cell::new(false);
    let calls = Cell::new(0);
    let mut callback = || {
        if armed.get() {
            calls.set(calls.get() + 1);
        }
        true
    };
    let mut names = AcyclicNames::new(&solver.problem, &mut callback).unwrap();
    let model = model(&solver, &SmtValue::BitVec(173, 8), &mut names);
    let witness = witness(&solver, &model, &mut names).unwrap();
    armed.set(true);
    let result = solver.verified_acyclic_dag_unsafe_from_model(
        witness.clone(),
        &model,
        &[&solver.problem.clauses()[1]],
        &mut names,
        ay_core::time::Instant::now(),
    );
    assert!(matches!(result, ChcEngineResult::Unknown));
    assert!(solver.stats.borrow().budget_exhausted);
    assert!(names.stopped());
    assert_eq!(calls.get(), 0);
    assert!(!recover(
        &solver,
        &model,
        &witness,
        &mut names,
        Boundary::Publication
    ));
    assert_eq!(calls.get(), 0);
}

#[test]
fn inherited_token_refusal_survives_parent_reset() {
    let mut solver = fixture(ChcSort::BitVec(8));
    let token = crate::CancellationToken::new();
    solver.config.base.cancellation_token = Some(token.child());
    let armed = Cell::new(false);
    let calls = Cell::new(0);
    let mut callback = || {
        if armed.get() {
            calls.set(calls.get() + 1);
        }
        true
    };
    let mut names = AcyclicNames::new(&solver.problem, &mut callback).unwrap();
    let model = model(&solver, &SmtValue::BitVec(173, 8), &mut names);
    let witness = witness(&solver, &model, &mut names).unwrap();
    token.cancel();
    armed.set(true);
    assert!(!recover(
        &solver,
        &model,
        &witness,
        &mut names,
        Boundary::Publication
    ));
    assert!(solver.stats.borrow().budget_exhausted);
    assert!(names.stopped());
    assert_eq!(calls.get(), 0);
    token.reset();
    assert!(!solver.config.base.is_cancelled());
    assert!(!recover(
        &solver,
        &model,
        &witness,
        &mut names,
        Boundary::Publication
    ));
    assert_eq!(calls.get(), 0);
}

#[test]
fn token_cancelled_by_an_accepting_callback_is_checked_before_ground_work() {
    let mut solver = fixture(ChcSort::BitVec(8));
    let token = crate::CancellationToken::new();
    solver.config.base.cancellation_token = Some(token.clone());
    let armed = Cell::new(false);
    let calls = Cell::new(0);
    let mut callback = || {
        if armed.get() {
            calls.set(calls.get() + 1);
            token.cancel();
        }
        true
    };
    let mut names = AcyclicNames::new(&solver.problem, &mut callback).unwrap();
    let model = model(&solver, &SmtValue::BitVec(173, 8), &mut names);
    let witness = witness(&solver, &model, &mut names).unwrap();
    armed.set(true);
    assert!(!recover(
        &solver,
        &model,
        &witness,
        &mut names,
        Boundary::Publication
    ));
    assert!(solver.stats.borrow().budget_exhausted);
    assert!(names.stopped());
    assert_eq!(calls.get(), 1);
    token.reset();
    assert!(!recover(
        &solver,
        &model,
        &witness,
        &mut names,
        Boundary::Publication
    ));
    assert_eq!(calls.get(), 1);
}

#[test]
fn caught_callback_panic_stays_terminal_but_a_fresh_attempt_can_publish() {
    let solver = fixture(ChcSort::BitVec(8));
    let armed = Cell::new(false);
    let calls = Cell::new(0);
    let mut callback = || {
        if armed.get() {
            calls.set(calls.get() + 1);
            panic!("typed witness callback panic");
        }
        true
    };
    let mut names = AcyclicNames::new(&solver.problem, &mut callback).unwrap();
    let model = model(&solver, &SmtValue::BitVec(173, 8), &mut names);
    let witness = witness(&solver, &model, &mut names).unwrap();
    assert!(recover(
        &solver,
        &model,
        &witness,
        &mut names,
        Boundary::Ground
    ));
    armed.set(true);
    let error = std::panic::catch_unwind(AssertUnwindSafe(|| {
        recover(&solver, &model, &witness, &mut names, Boundary::Publication)
    }))
    .expect_err("the callback panic must reach this guard");
    assert_eq!(
        error.downcast_ref::<&str>(),
        Some(&"typed witness callback panic")
    );
    assert!(names.stopped());
    armed.set(false);
    assert!(!recover(
        &solver,
        &model,
        &witness,
        &mut names,
        Boundary::Publication
    ));
    assert_eq!(calls.get(), 1);
    drop(names);
    assert!(run_ordinal(&solver, Boundary::Publication, 0) > 5);
}
