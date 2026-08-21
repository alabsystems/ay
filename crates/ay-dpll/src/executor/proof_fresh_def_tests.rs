// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end tests for the fresh-definition promotion lane.
//!
//! The unit-level conditions live with the code that decides them
//! (`ay_core::proof_validation::fresh_def_bound` for the shape, `ay_proof`'s
//! `FreshDefRegistry` for the whole-proof provenance and its sweeps). What is
//! left to pin HERE is the thing only a real solve can show: that `EqDiffVar`'s
//! definitional pair reaches proof reconstruction, that this lane converts it,
//! and that the conversion survives the checker the executor itself runs.

use ay_core::{AletheRule, ProofStep};

use super::is_fresh_def_bound_step;
use crate::Executor;
use ay_frontend::parse;

/// The `EqDiffVar` pass's own target shape: a guarded var-var equality chain.
/// Copied from `solve_harness::tests::eq_diffvar_runs_and_mandatory_unsat_certification_survives`
/// so the two tests are talking about the same solve.
const GUARDED_UNSAT: &str = r#"
    (set-logic QF_LIA)
    (declare-const g1 Bool)
    (declare-const g2 Bool)
    (declare-const x Int)
    (declare-const y Int)
    (declare-const a Int)
    (declare-const b Int)
    (assert (or (not g1) (= a x)))
    (assert (or (not g1) (= b y)))
    (assert (or g1 (= a y)))
    (assert (or g1 (= b x)))
    (assert (or (not g2) (= (+ x y) 1)))
    (assert (or g2 (= (+ a b) 1)))
    (assert (not (= (+ x y) 1)))
    (check-sat)
"#;

fn solve_guarded() -> Executor {
    let commands = parse(GUARDED_UNSAT).expect("parse");
    let mut exec = Executor::new();
    assert_eq!(
        exec.execute_all(&commands).expect("exec"),
        vec!["unsat"],
        "the guarded conservation network is UNSAT"
    );
    assert!(
        exec.statistics()
            .get_int("preprocess.eq_diffvar.diff_vars")
            .is_some_and(|n| n > 0),
        "the reduction must actually have run, or this test proves nothing"
    );
    exec
}

/// Every premiseless `trust` step whose clause is a unit mentioning a
/// difference variable. This is the population the lane exists to remove.
fn premiseless_trust_units_over_diff_vars(exec: &Executor) -> usize {
    exec.last_proof.as_ref().map_or(0, |proof| {
        proof
            .steps
            .iter()
            .filter(|step| {
                let ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    ..
                } = step
                else {
                    return false;
                };
                premises.is_empty()
                    && clause.len() == 1
                    && ay_proof::format_term_alethe(&exec.ctx.terms, clause[0])
                        .contains("__ay_eqdv")
                    && exec.fresh_def_bound_operands(clause[0]).is_some()
            })
            .count()
    })
}

fn fresh_def_bound_steps(exec: &Executor) -> usize {
    exec.last_proof.as_ref().map_or(0, |proof| {
        proof
            .steps
            .iter()
            .filter(|step| is_fresh_def_bound_step(&exec.ctx.terms, step))
            .count()
    })
}

#[test]
fn eq_diffvar_definitional_bounds_are_promoted_not_demoted() {
    let exec = solve_guarded();
    assert!(
        fresh_def_bound_steps(&exec) > 0,
        "the definitional pair must reach the proof as `fresh_def_bound` steps"
    );
    assert_eq!(
        premiseless_trust_units_over_diff_vars(&exec),
        0,
        "no definitional bound over a difference variable may remain an \
         unverified premiseless `trust` step"
    );
}

#[test]
fn the_promoted_proof_still_passes_the_executors_own_checker() {
    // The promotion is only worth anything if the checker the executor runs
    // accepts it. A `fresh_def_bound` the registry declined would be a HARD
    // `InvalidTheoryLemma` rejection — strictly worse than the rescuable
    // `trust` it replaced — so this asserts the specific error class never
    // appears, whatever the overall verdict is.
    let exec = solve_guarded();
    let proof = exec.last_proof.as_ref().expect("a proof was reconstructed");
    if let Err(error) = exec.check_proof_strict_with_datatypes(proof) {
        let rendered = error.to_string();
        assert!(
            !rendered.contains("fresh definition"),
            "the promotion lane must never produce a rejected fresh definition: {rendered}"
        );
    }
}

#[test]
fn the_published_unsat_is_still_backed_by_a_certificate() {
    // The lane must not trade a certificate for a shape change.
    let exec = solve_guarded();
    assert!(
        exec.last_command_unsat_was_strictly_verified()
            || exec.last_command_unsat_was_independently_verified()
            || exec.last_command_unsat_was_exact_semantically_verified(),
        "the `unsat` must stay backed by a real certificate"
    );
}

#[test]
fn a_bound_over_a_symbol_the_problem_constrains_is_left_alone() {
    // The producer-side admission test must agree with the checker's. Here the
    // `<=` bounds are over AUTHORED variables, so nothing may be promoted —
    // otherwise `(<= x 2)` would be certified as a free definition of `x`,
    // which is false at `x = 3`.
    let script = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (<= x y))
        (assert (<= y x))
        (assert (not (= x y)))
        (check-sat)
    "#;
    let commands = parse(script).expect("parse");
    let mut exec = Executor::new();
    assert_eq!(exec.execute_all(&commands).expect("exec"), vec!["unsat"]);
    assert_eq!(
        fresh_def_bound_steps(&exec),
        0,
        "bounds over authored variables are not definitions and must not be promoted"
    );
}
