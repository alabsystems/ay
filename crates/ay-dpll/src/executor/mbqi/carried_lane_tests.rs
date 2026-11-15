// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The two finite-universe lanes' own guards (2026-09-23 hunt, D1), pinned at
//! the lanes: a datatype binder is not a plain uninterpreted sort however it
//! is spelled, and the singleton lane declines a binder sort that datatype
//! values carry. End to end, MBQI's refusal of datatype binders and the
//! singleton lane's empty-sort occurrence scan keep both inputs away from the
//! lanes (0 of 244 file/posture pairs changed with either guard reverted,
//! 2026-09-25), so the guards are exercised here directly, on the model the
//! ground part yields.

use ay_frontend::Command;

use crate::executor::Executor;
use crate::logic_detection::LogicCategory;

fn load(smt: &str) -> Executor {
    let commands = ay_frontend::parse(smt).expect("fixture parses");
    let mut exec = Executor::new();
    for command in &commands {
        let output = exec.execute(command).expect("fixture executes");
        assert!(output.is_none(), "fixture must not contain a query command");
    }
    exec
}

/// Solve `ground` alone so the executor keeps its model, then restore the
/// whole assertion set.
fn solve_ground(exec: &mut Executor, ground: Vec<ay_core::TermId>) {
    let roots = exec.ctx.assertions.clone();
    exec.ctx.assertions = ground;
    let verdict = exec
        .execute(&Command::CheckSat)
        .expect("ground part solves");
    assert_eq!(
        verdict.as_deref(),
        Some("sat"),
        "the ground part is satisfiable"
    );
    assert!(
        exec.last_model.is_some(),
        "the ground solve keeps its model"
    );
    exec.ctx.assertions = roots;
}

/// `W` has three values, so `forall x:W. x = a` is false; enumerating the
/// ground `W`-terms `{a, w1}` as if `W` were uninterpreted would certify it.
#[test]
fn the_finite_universe_certificate_takes_no_datatype_binder() {
    let mut exec = load(
        r#"
        (set-logic ALL)
        (declare-datatype W ((w1) (w2) (w3)))
        (declare-const a W)
        (assert (= a w1))
        (assert (forall ((x W)) (= x a)))
        "#,
    );
    let roots = exec.ctx.assertions.clone();
    let (ground, universal) = (roots[0], roots[1]);
    solve_ground(&mut exec, vec![ground]);
    assert!(
        exec.mbqi_sat_validated_finite_uninterpreted_domain(&roots, &[universal])
            .is_none(),
        "a datatype binder is not a finite uninterpreted universe"
    );
}

/// `U` has no ground term (the singleton lane's case) and `V` has one, `v0`;
/// the universal makes `|V| = 1`, so `W` has two values and `(distinct a0 a1
/// a2)` is unsat. Instantiating `V` at `v0` alone misses the `V` elements the
/// `w`-values carry.
#[test]
fn the_singleton_lane_declines_a_binder_sort_datatype_values_carry() {
    let mut exec = load(
        r#"
        (set-logic ALL)
        (declare-sort U 0)
        (declare-sort V 0)
        (declare-datatypes ((W 0)) (((w (g V)) (w2))))
        (declare-const v0 V)
        (declare-const a0 W)
        (declare-const a1 W)
        (declare-const a2 W)
        (assert (distinct a0 a1 a2))
        (assert (forall ((x U) (y V)) (= y v0)))
        "#,
    );
    let roots = exec.ctx.assertions.clone();
    let universal = roots[1];
    assert!(
        exec.mbqi_empty_universe_singleton_decide(&roots, &[universal], LogicCategory::Other)
            .is_none(),
        "the carried V elements are outside the singleton lane's universe"
    );
}

/// The same class with an instance set the lane would refute: its universe
/// argument covers only the ground `V`-terms, so it declines the class
/// outright rather than decide it (main's generating-function test let it
/// through, and on the satisfiable side only the lane's final carrier check
/// stood in the way).
#[test]
fn the_singleton_lane_takes_no_class_whose_binder_sort_values_carry() {
    let mut exec = load(
        r#"
        (set-logic ALL)
        (declare-sort U 0)
        (declare-sort V 0)
        (declare-datatypes ((W 0)) (((w (g V)) (w2))))
        (declare-const v0 V)
        (declare-const a0 W)
        (declare-const a1 W)
        (assert (distinct a0 a1))
        (assert (forall ((x U) (y V)) (not (= y v0))))
        "#,
    );
    let roots = exec.ctx.assertions.clone();
    let universal = roots[1];
    assert!(
        exec.mbqi_empty_universe_singleton_decide(&roots, &[universal], LogicCategory::Other)
            .is_none(),
        "a binder sort that datatype values carry is outside the singleton lane's class"
    );
}
