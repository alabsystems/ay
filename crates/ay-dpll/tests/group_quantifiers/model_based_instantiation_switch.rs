// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! `(set-option :smt.mbqi false)` keeps the candidate-model refinement out of
//! a query.
//!
//! The query is the shape a program verifier sends: a boxed sort, clipped
//! arithmetic with range axioms, two binary definitions the goal never
//! applies, every axiom with its pattern, and, in a scope of its own, a
//! labelled goal over three boxed values.
//! When the goal does not follow, trigger matching stops with a satisfiable
//! ground problem, and the expected answer is `unknown` with the candidate
//! model. Without the option the refinement then instantiates the axioms at
//! every ground tuple the model falsifies (16 instances, then 280, each batch
//! minting the terms of the next) and the re-solves outgrow any budget:
//! measured, no answer in 18 CPU s against 0.2 s with the option honoured.
//!
//! The twin differs in one constant and is unsatisfiable: its refutation
//! comes from trigger matching and must not depend on the option.

use ay_dpll::{CandidateModelPolicy, Executor};
use ay_frontend::parse;
use ntest::timeout;

fn run(exec: &mut Executor, script: &str) -> Vec<String> {
    let commands = parse(script).unwrap_or_else(|err| panic!("parse failed: {err}\n{script}"));
    exec.execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\n{script}"))
}

/// Two clipped increments from `v0` cannot wrap below 200, so `v2` is
/// `v0 + 2`. `claimed` is the sum the goal denies; `L0` labels the goal.
fn boxed_increment_query(claimed: u32) -> String {
    format!(
        "(set-option :smt.mbqi false)
         (declare-sort Box 0)
         (declare-fun box (Int) Box)
         (declare-fun unbox (Box) Int)
         (assert (forall ((x Int)) (! (= x (unbox (box x))) :pattern ((box x)))))
         (declare-fun hi (Int) Int)
         (assert (= (hi 8) 256))
         (declare-fun clip (Int Int) Int)
         (assert (forall ((b Int) (i Int))
           (! (and (<= 0 (clip b i)) (< (clip b i) (hi b))) :pattern ((clip b i)))))
         (assert (forall ((b Int) (i Int))
           (! (=> (and (<= 0 i) (< i (hi b))) (= i (clip b i))) :pattern ((clip b i)))))
         (declare-fun add (Int Int) Int)
         (assert (forall ((x Int) (y Int)) (! (= (add x y) (+ x y)) :pattern ((add x y)))))
         (declare-fun sub (Int Int) Int)
         (assert (forall ((x Int) (y Int)) (! (= (sub x y) (- x y)) :pattern ((sub x y)))))
         (declare-fun op0 (Box Box) Int)
         (assert (forall ((x Box) (y Box))
           (! (= (op0 x y)
                 (ite (> (add (unbox x) (unbox y)) 255)
                      (clip 8 (sub (add (unbox x) (unbox y)) 256))
                      (clip 8 (add (unbox x) (unbox y)))))
              :pattern ((op0 x y)))))
         (declare-fun op1 (Box Box) Int)
         (assert (forall ((x Box) (y Box))
           (! (= (op1 x y)
                 (ite (< (sub (unbox x) (unbox y)) 1)
                      (clip 8 (add (sub (unbox x) (unbox y)) 256))
                      (clip 8 (sub (unbox x) (unbox y)))))
              :pattern ((op1 x y)))))
         (declare-const v0 Box)
         (assert (and (<= 0 (unbox v0)) (< (unbox v0) 256)))
         (declare-const v1 Box)
         (assert (and (<= 0 (unbox v1)) (< (unbox v1) 256)))
         (declare-const v2 Box)
         (assert (and (<= 0 (unbox v2)) (< (unbox v2) 256)))
         (assert (= (unbox v1) (clip 8 (add (unbox v0) 1))))
         (assert (< (unbox v0) 200))
         (assert (= (unbox v2) (clip 8 (add (unbox v1) 1))))
         (assert (< (unbox v1) 200))
         (push)
         (declare-const L0 Bool)
         (assert (not (=> L0 (= (unbox v2) (+ (unbox v0) {claimed})))))
         (check-sat)"
    )
}

/// The posture of a z3-compatible client: recorder shed, candidate model
/// published after `unknown`.
fn client_executor() -> Executor {
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec.set_candidate_model_policy(CandidateModelPolicy::PublishAfterUnknown);
    exec
}

/// `v2` is not `v0 + 3`, so the goal fails and the query is satisfiable.
/// With model-based instantiation off the answer is the `unknown` trigger
/// matching leaves, at once, and no refinement round ran.
#[test]
#[timeout(60_000)]
fn a_goal_that_fails_ends_unknown_when_model_based_instantiation_is_off() {
    let mut exec = Executor::new();
    let outputs = run(&mut exec, &boxed_increment_query(3));
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unknown"),
        "{outputs:?}"
    );
    assert_eq!(
        exec.statistics().get_int("quantifier.mbqi.rounds"),
        Some(0),
        "no candidate-model refinement round may run"
    );
}

/// The twin, one constant different: `v2` is `v0 + 2`, the denied goal holds,
/// and trigger matching alone refutes the query.
#[test]
#[timeout(60_000)]
fn the_twin_whose_goal_holds_is_refuted_when_model_based_instantiation_is_off() {
    let mut exec = Executor::new();
    let outputs = run(&mut exec, &boxed_increment_query(2));
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
}

/// The same pair as a z3-compatible client sees it: the `unknown` still
/// carries the candidate model that names the failing assertion.
#[test]
#[timeout(60_000)]
fn the_unknown_still_names_the_failing_assertion() {
    let mut exec = client_executor();
    let outputs = run(&mut exec, &boxed_increment_query(3));
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unknown"),
        "{outputs:?}"
    );
    let model = run(&mut exec, "(get-model)").pop().unwrap_or_default();
    assert!(model.contains("(define-fun L0 () Bool true)"), "{model}");
}

/// The client's twin: refuted, as in the default posture.
#[test]
#[timeout(60_000)]
fn the_client_twin_whose_goal_holds_is_refuted() {
    let mut exec = client_executor();
    let outputs = run(&mut exec, &boxed_increment_query(2));
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unsat"),
        "{outputs:?}"
    );
}

/// The option names the enumeration over ground tuples, not the bit-vector
/// lane. No 32-bit `a` is above every 32-bit `x`; no trigger reaches the
/// universal and no enumeration covers the width, so only that lane refutes
/// it (z3 with the option: unsat).
fn wide_binder_query(relation: &str) -> String {
    format!(
        "(set-option :smt.mbqi false)
         (set-logic BV)
         (declare-fun a () (_ BitVec 32))
         (assert (bvugt a #x00000005))
         (assert (forall ((x (_ BitVec 32))) ({relation} x a)))
         (check-sat)"
    )
}

#[test]
#[timeout(60_000)]
fn a_bit_vector_universal_is_still_refuted_when_model_based_instantiation_is_off() {
    let mut exec = Executor::new();
    assert_eq!(run(&mut exec, &wide_binder_query("bvult")), vec!["unsat"]);
    assert_eq!(
        exec.statistics().get_int("quantifier.mbqi.switched_off"),
        None,
        "the enumeration the option names was never reached"
    );
}

/// The twin differs in one operator: `x <=u a` holds for every `x` when `a`
/// is all ones, so the problem has a model (z3: sat).
#[test]
#[timeout(60_000)]
fn the_twin_a_wide_enough_bound_satisfies_is_not_refuted() {
    let mut exec = Executor::new();
    assert_eq!(run(&mut exec, &wide_binder_query("bvule")), vec!["sat"]);
}
