// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::panic::{catch_unwind, panic_any, AssertUnwindSafe};

use super::*;
use crate::executor_types::ExecutorError;

fn prepared() -> Executor {
    let mut exec = Executor::new();
    exec.execute_all(
        &ay_frontend::parse(
            "(set-option :produce-proofs true) (set-logic QF_NIA)
             (declare-const a Int) (declare-const b Int)
             (assert (> a 0)) (assert (> b 0)) (assert (< (div a b) 0))",
        )
        .expect("source script"),
    )
    .expect("source setup");
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    let roots = exec.ctx.assertions.clone();
    exec.install_proof_source_provenance(&roots);
    assert!(exec.proof_problem_assertion_provenance.is_some());
    assert!(exec.unsat_query_epoch.is_some());
    exec.set_counterexample_style(crate::CounterexampleStyle::Readable);
    exec
}

fn actual_preprocessing(exec: &mut Executor) {
    let roots = exec.ctx.assertions.clone();
    assert!(crate::executor::mod_div_elim::contains_symbolic_int_mod_div(&exec.ctx.terms, &roots,));
    let _ = exec.preprocess_nia_theory_window();
    assert_ne!(exec.ctx.assertions, roots);
    assert!(exec.ctx.assertions.iter().any(|term| !roots.contains(term)));
    assert!(exec.sat_validated_by_mod_div_or_branch);
    assert_eq!(exec.counterexample_style(), crate::CounterexampleStyle::Any);
}

#[derive(Clone, Copy)]
enum Exit {
    Error,
    Unwind,
}

#[derive(Clone, Copy)]
enum SourceAuthority {
    Present,
    Absent,
}

fn failed_window(exit: Exit, authority: SourceAuthority) {
    let mut exec = prepared();
    let roots = exec.ctx.assertions.clone();
    if matches!(authority, SourceAuthority::Present) {
        // Bind a real nonempty caller slice before the window, without
        // rebinding the empty slice of the fixture's preceding public epoch.
        exec.begin_public_solve(false);
        exec.bind_unsat_query_assumptions(&roots[..1]);
        assert_eq!(exec.unsat_query_caller_assumptions(), Some(&roots[..1]));
        exec.last_assumptions = Some(roots[..1].to_vec());
        exec.install_proof_source_provenance(&roots);
        assert!(exec.proof_problem_assertion_provenance.is_some());
        exec.sat_validated_by_mod_div_or_branch = true;
    }
    if matches!(authority, SourceAuthority::Absent) {
        exec.proof_problem_assertion_provenance = None;
    }
    let parsed = format!("{:?}", exec.ctx.assertions_parsed());
    let epoch = format!("{:?}", exec.unsat_query_epoch);
    let provenance = exec.proof_problem_assertion_provenance.clone();
    let assumptions = exec.last_assumptions.clone();
    let term_count = exec.ctx.terms.len();
    let division_validation = exec.sat_validated_by_mod_div_or_branch;
    let caught = catch_unwind(AssertUnwindSafe(|| {
        exec.with_nia_theory_window::<(), _>(|this| {
            actual_preprocessing(this);
            if division_validation {
                // Exercise the opposite restoration direction as well: a
                // later failing cleanup must not erase preexisting state.
                this.sat_validated_by_mod_div_or_branch = false;
            }
            match exit {
                Exit::Error => Err(ExecutorError::UnsupportedLogic("window-error".into())),
                Exit::Unwind => panic_any("window-unwind"),
            }
        })
    }));
    match exit {
        Exit::Error => assert!(matches!(
            caught.expect("ordinary error"),
            Err(ExecutorError::UnsupportedLogic(message)) if message == "window-error"
        )),
        Exit::Unwind => {
            let payload = caught.expect_err("original unwind must propagate");
            assert_eq!(payload.downcast_ref::<&str>(), Some(&"window-unwind"));
        }
    }
    assert_eq!(exec.ctx.assertions, roots);
    assert_eq!(format!("{:?}", exec.ctx.assertions_parsed()), parsed);
    assert_eq!(format!("{:?}", exec.unsat_query_epoch), epoch);
    assert_eq!(exec.last_assumptions, assumptions);
    assert_eq!(
        exec.counterexample_style(),
        crate::CounterexampleStyle::Readable
    );
    assert_eq!(exec.sat_validated_by_mod_div_or_branch, division_validation);
    assert!(
        exec.ctx.terms.len() > term_count,
        "keep appended term identities"
    );
    match (&exec.proof_problem_assertion_provenance, provenance) {
        (Some(actual), Some(expected)) => {
            assert_eq!(
                actual.original_problem_assertions,
                expected.original_problem_assertions
            );
            assert_eq!(actual.problem_assertions, expected.problem_assertions);
            assert_eq!(actual.assertion_sources, expected.assertion_sources);
        }
        (None, None) => {}
        _ => panic!("restored provenance changed presence"),
    }
}

#[test]
fn symbolic_error_restores_existing_source_authority() {
    failed_window(Exit::Error, SourceAuthority::Present);
}

#[test]
fn symbolic_error_preserves_absent_source_authority() {
    failed_window(Exit::Error, SourceAuthority::Absent);
}

#[test]
fn symbolic_unwind_restores_existing_source_authority() {
    failed_window(Exit::Unwind, SourceAuthority::Present);
}

#[test]
fn symbolic_unwind_preserves_absent_source_authority() {
    failed_window(Exit::Unwind, SourceAuthority::Absent);
}

#[test]
fn normal_sat_window_restores_raw_roots_and_keeps_division_validation_semantics() {
    let mut exec = prepared();
    let roots = exec.ctx.assertions.clone();
    let epoch = format!("{:?}", exec.unsat_query_epoch);
    let result = exec
        .with_nia_theory_window(|this| {
            actual_preprocessing(this);
            Ok((SolveResult::Sat, 42u32))
        })
        .expect("scope return");
    assert!(matches!(result, (SolveResult::Sat, 42)));
    assert_eq!(exec.ctx.assertions, roots);
    assert_eq!(format!("{:?}", exec.unsat_query_epoch), epoch);
    assert_eq!(
        exec.counterexample_style(),
        crate::CounterexampleStyle::Readable
    );
    assert!(exec.sat_validated_by_mod_div_or_branch);
    assert!(
        exec.last_model.is_none(),
        "the scope itself grants no model"
    );
}

#[test]
fn normal_unsat_retains_only_the_original_root_bridge() {
    let mut exec = prepared();
    let roots = exec.ctx.assertions.clone();
    let epoch = format!("{:?}", exec.unsat_query_epoch);
    let (result, ()) = exec
        .with_nia_theory_window(|this| {
            actual_preprocessing(this);
            Ok((SolveResult::unsat(), ()))
        })
        .expect("scope return");
    assert!(result.is_unsat());
    assert_eq!(exec.ctx.assertions, roots);
    assert_eq!(format!("{:?}", exec.unsat_query_epoch), epoch);
    let provenance = exec
        .proof_problem_assertion_provenance
        .as_ref()
        .expect("licensed bridge");
    assert_eq!(provenance.original_problem_assertions, roots);
    assert!(provenance
        .problem_assertions
        .iter()
        .all(|term| roots.contains(term)));
    assert!(provenance
        .assertion_sources
        .values()
        .flatten()
        .flatten()
        .all(|term| roots.contains(term)));
}

#[test]
#[ntest::timeout(10_000)]
fn repeated_public_queries_preserve_raw_roots_and_checked_division_values() {
    let mut exec = Executor::new();
    exec.execute_all(
        &ay_frontend::parse(
            "(set-logic QF_NIA) (declare-const a Int) (declare-const b Int)
         (assert (= a 5)) (assert (= b 2)) (assert (= (div a b) 2))",
        )
        .expect("source script"),
    )
    .expect("source setup");
    let roots = exec.ctx.assertions.clone();
    assert!(crate::executor::mod_div_elim::contains_symbolic_int_mod_div(&exec.ctx.terms, &roots));
    for _ in 0..2 {
        assert_eq!(
            exec.execute_all(&ay_frontend::parse("(check-sat)").expect("query"))
                .expect("solve"),
            vec!["sat"]
        );
        assert_eq!(exec.ctx.assertions, roots);
        assert!(exec.last_model_validated);
        assert_eq!(
            exec.execute_all(&ay_frontend::parse("(get-value ((div a b)))").expect("getter"))
                .expect("checked model getter"),
            vec!["(((div a b) 2))"]
        );
    }
}
