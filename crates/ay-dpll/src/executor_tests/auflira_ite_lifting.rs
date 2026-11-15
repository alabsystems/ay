// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The AUFLIRA route lifts arithmetic ITEs before the split loop.
//!
//! The split loop's Tseitin setup lifts `(= a (+ x (ite c 0 1)))` into
//! `(ite c (= a (+ x 0)) (= a (+ x 1)))` before encoding it, but it hands the
//! theory only the atoms reachable from the assertions it was given. Without
//! the lift in `solve_auflira`, the branch atoms had SAT variables the theory
//! never received: the theory accepted assignments that violate them, or, for a
//! top-level fact, produced conflicts naming the unlifted atom, which has no
//! SAT variable, and the loop gave up with `unknown`. Each formula declares a
//! Real constant, which is what sends a UF + Int problem to this route.
//!
//! Verus's `dafny_axioms::set_axiom_02` needs the instance of
//! `axiom_set_insert_len`, `len(insert(s, a)) = Add(len(s), ite(contains(s, a),
//! 0, 1))`, in exactly this shape.

use crate::Executor;
use ay_frontend::parse;

fn execute(input: &str) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("valid SMT-LIB test input");
    let mut executor = Executor::new();
    let output = executor
        .execute_all(&commands)
        .expect("commands must execute");
    (executor, output)
}

fn answer_and_category(input: &str) -> (String, Option<String>) {
    let (executor, output) = execute(input);
    let category = executor
        .statistics()
        .get_string("solver.logic_category")
        .map(str::to_owned);
    (output.join("\n"), category)
}

/// The ITE sits in a top-level arithmetic equality, which the split loop also
/// asserts to the theory directly as a fact (z3: unsat).
#[test]
fn top_level_fact_with_an_ite_is_refuted() {
    let (answer, category) = answer_and_category(
        r#"
        (declare-fun g (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const c Bool)
        (declare-const r Real)
        (assert (= (+ r r) 1.0))
        (assert (not c))
        (assert (= y (g x)))
        (assert (= (g x) (+ x (ite c 0 1))))
        (assert (not (= y (+ x 1))))
        (check-sat)
    "#,
    );
    assert_eq!(category.as_deref(), Some("QfAuflira"));
    assert_eq!(answer, "unsat");
}

/// The same equality under a disjunction, so it reaches the theory only
/// through its lifted branch atoms (z3: unsat).
#[test]
fn nested_equality_with_an_ite_is_refuted() {
    let (answer, category) = answer_and_category(
        r#"
        (declare-fun g (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const c Bool)
        (declare-const b Bool)
        (declare-const r Real)
        (assert (= (+ r r) 1.0))
        (assert (not c))
        (assert (not b))
        (assert (= y (g x)))
        (assert (or b (= (g x) (+ x (ite c 0 1)))))
        (assert (not (= y (+ x 1))))
        (check-sat)
    "#,
    );
    assert_eq!(category.as_deref(), Some("QfAuflira"));
    assert_eq!(answer, "unsat");
}

/// The shape of the `set_axiom_02` goal: the ITE is an argument of the
/// uninterpreted `Add`, and a guarded instance defines `Add` (z3: unsat).
#[test]
fn set_insert_len_shape_is_refuted() {
    let (answer, category) = answer_and_category(
        r#"
        (declare-sort Poly 0)
        (declare-fun %R (Poly) Real)
        (declare-fun len (Poly) Int)
        (declare-fun insert (Poly Poly) Poly)
        (declare-fun contains (Poly Poly) Bool)
        (declare-fun finite (Poly) Bool)
        (declare-fun Add (Int Int) Int)
        (declare-fun nClip (Int) Int)
        (declare-const s Poly)
        (declare-const a Poly)
        (assert (finite s))
        (assert (not (=> (not (contains s a))
            (= (len (insert s a)) (nClip (Add (len s) 1))))))
        (assert (<= 0 (len s)))
        (assert (=> (finite s)
            (= (len (insert s a)) (Add (len s) (ite (contains s a) 0 1)))))
        (assert (= (Add (len s) 1) (+ (len s) 1)))
        (assert (= (Add (len s) (ite (contains s a) 0 1))
            (+ (len s) (ite (contains s a) 0 1))))
        (assert (=> (<= 0 (Add (len s) 1)) (= (Add (len s) 1) (nClip (Add (len s) 1)))))
        (check-sat)
    "#,
    );
    assert_eq!(category.as_deref(), Some("QfAuflira"));
    assert_eq!(answer, "unsat");
}

/// A satisfiable neighbour of the first formula: `y` differs from `x + 2`,
/// which the model `c = false`, `g(x) = y = x + 1` satisfies (z3: sat). The
/// lift must not refute it. ay answers `unknown` here, with or without the
/// ITE: the model this route builds for `g` fails the model gate.
#[test]
fn satisfiable_neighbour_is_not_refuted() {
    let (answer, category) = answer_and_category(
        r#"
        (declare-fun g (Int) Int)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const c Bool)
        (declare-const r Real)
        (assert (= (+ r r) 1.0))
        (assert (not c))
        (assert (= y (g x)))
        (assert (= (g x) (+ x (ite c 0 1))))
        (assert (not (= y (+ x 2))))
        (check-sat)
    "#,
    );
    assert_eq!(category.as_deref(), Some("QfAuflira"));
    assert_ne!(answer, "unsat");
}
