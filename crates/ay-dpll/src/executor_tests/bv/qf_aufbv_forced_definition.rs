// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A Bool-element array defined inside the one disjunct the model forces.
//!
//! The shape comes from model-checker-consumer's realloc_grow CHC (ask
//! 2026-10-14-realloc-grow-pre-discharge-chc-undecided-29a0f2cab). Each error
//! path is a disjunct that carries `obj_valid := (store (const true) 66 true)`.
//! The term store folds that store to `(const true)`. A definition nested in a
//! disjunct is withheld unless the model forces its arm. The forced-arm walk
//! saw only `store`, so the `const-array` stayed withheld. The strict gate then
//! refused every model (`arrays-read-conflict-uneval`), and z3-`sat` queries
//! came back `unknown`. The arm is also forced through a negated
//! Bool-element `select`, which the liveness test could not read.
//!
//! The `unsat` twins pin the other side: forcing the arm commits to its
//! definition, and a contradiction with that definition stays `unsat`.

use super::*;

fn run(input: &str) -> Vec<String> {
    let commands = parse(input).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("invariant: execute succeeds")
}

/// The 289-byte reproducer: the model takes `b`, so only the definition arm
/// is live.
#[test]
fn test_forced_const_array_definition_arm_is_sat() {
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const a (Array (_ BitVec 32) Bool))
        (declare-const b Bool)
        (declare-const c (Array (_ BitVec 32) Bool))
        (assert (or (and (not (select a #x00000042)) (not b))
                    (= c (store ((as const (Array (_ BitVec 32) Bool)) true) #x00000042 true))))
        (check-sat)
    "#;
    assert_eq!(run(input), vec!["sat"]);
}

/// The arm is forced by a negated Bool-element read, and the definition is
/// the folded const array: the model must give `c` the value `(const true)`.
#[test]
fn test_select_forced_const_array_definition_model() {
    let input = r#"
        (set-logic QF_AUFBV)
        (set-option :produce-models true)
        (declare-const a (Array (_ BitVec 32) Bool))
        (declare-const b Bool)
        (declare-const c (Array (_ BitVec 32) Bool))
        (assert (select a #x00000042))
        (assert (or (and (not (select a #x00000042)) (not b))
                    (= c (store ((as const (Array (_ BitVec 32) Bool)) true) #x00000042 true))))
        (check-sat)
        (get-value ((select c #x00000007)))
    "#;
    let out = run(input);
    assert_eq!(out[0], "sat", "{out:?}");
    assert_eq!(out[1], "(((select c #x00000007) true))", "{out:?}");
}

/// A real (unfolded) store chain behind a negated Bool-element read.
#[test]
fn test_select_forced_store_definition_model() {
    let input = r#"
        (set-logic QF_AUFBV)
        (set-option :produce-models true)
        (declare-const a (Array (_ BitVec 32) Bool))
        (declare-const c (Array (_ BitVec 32) Bool))
        (assert (select a #x00000042))
        (assert (or (not (select a #x00000042))
                    (= c (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000042 true))))
        (check-sat)
        (get-value ((select c #x00000042) (select c #x00000007)))
    "#;
    let out = run(input);
    assert_eq!(out[0], "sat", "{out:?}");
    assert!(
        out[1].contains("((select c #x00000042) true)")
            && out[1].contains("((select c #x00000007) false)"),
        "{out:?}"
    );
}

/// Negative twin of the const-array case: the forced definition makes every
/// cell of `c` true, so a false cell is a contradiction.
#[test]
fn test_forced_const_array_definition_contradiction_is_unsat() {
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const a (Array (_ BitVec 32) Bool))
        (declare-const b Bool)
        (declare-const c (Array (_ BitVec 32) Bool))
        (assert (select a #x00000042))
        (assert (or (and (not (select a #x00000042)) (not b))
                    (= c (store ((as const (Array (_ BitVec 32) Bool)) true) #x00000042 true))))
        (assert (not (select c #x00000007)))
        (check-sat)
    "#;
    assert_eq!(run(input), vec!["unsat"]);
}

/// Negative twin of the store case: the forced store writes `true` at #x42.
#[test]
fn test_forced_store_definition_contradiction_is_unsat() {
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const a (Array (_ BitVec 32) Bool))
        (declare-const c (Array (_ BitVec 32) Bool))
        (assert (select a #x00000042))
        (assert (or (not (select a #x00000042))
                    (= c (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000042 true))))
        (assert (not (select c #x00000042)))
        (check-sat)
    "#;
    assert_eq!(run(input), vec!["unsat"]);
}

/// An unresolvable `const-array` default must not poison a variable: a
/// Bool-element `select` default is a SAT atom with no BV bits, so the
/// forced-arm build of `(= e (const (select a #x3)))` fails. Before forced arms
/// recognised const arrays it was invisible and the query was `sat`; it must
/// stay `sat` (z3: sat), not degrade to `arrays-read-conflict-uneval`.
#[test]
fn test_unresolvable_const_array_default_does_not_poison_the_variable() {
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const a (Array (_ BitVec 4) Bool))
        (declare-const d (Array (_ BitVec 4) Bool))
        (declare-const e (Array (_ BitVec 4) Bool))
        (assert (or (= e (store d #x2 false))
                    (= e ((as const (Array (_ BitVec 4) Bool)) (select a #x3)))))
        (check-sat)
    "#;
    assert_eq!(run(input), vec!["sat"]);
}

/// The same for a UF default in a top-level conjunction (z3: sat).
#[test]
fn test_unresolvable_uf_const_array_default_does_not_poison_the_variable() {
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const c (Array (_ BitVec 4) Bool))
        (declare-const u (Array (_ BitVec 4) (_ BitVec 3)))
        (declare-const w (Array (_ BitVec 4) (_ BitVec 3)))
        (declare-const z (Array (_ BitVec 4) (_ BitVec 3)))
        (declare-const x (_ BitVec 4))
        (declare-const v (_ BitVec 3))
        (declare-fun g ((_ BitVec 4)) (_ BitVec 3))
        (assert (or (= w (store (store u #x1 v) (bvadd x #x1) v))
                    (= w ((as const (Array (_ BitVec 4) (_ BitVec 3))) v))))
        (assert (and (not (select c (bvadd x #x1)))
                     (= z ((as const (Array (_ BitVec 4) (_ BitVec 3))) (g x)))))
        (check-sat)
    "#;
    assert_eq!(run(input), vec!["sat"]);
}

/// Negative twin: the unresolvable default still constrains the model.
#[test]
fn test_unresolvable_const_array_default_contradiction_is_unsat() {
    let input = r#"
        (set-logic QF_AUFBV)
        (declare-const a (Array (_ BitVec 4) Bool))
        (declare-const d (Array (_ BitVec 4) Bool))
        (declare-const e (Array (_ BitVec 4) Bool))
        (assert (or (= e (store d #x2 false))
                    (= e ((as const (Array (_ BitVec 4) Bool)) (select a #x3)))))
        (assert (select e #x2))
        (assert (not (select e #x5)))
        (assert (select a #x3))
        (check-sat)
    "#;
    assert_eq!(run(input), vec!["unsat"]);
}
