// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Verdict-level spec for universals under a unit-settled guard
//! (#unit-facts-shared, #unit-bool-eq, #conjunctive-closure, #unit-bcp; Verus
//! fix queue row D1).
//!
//! Verus writes every fuel-controlled definition as
//! `(=> (fuel_bool f) (forall x̄. B))`. The guard is either asserted by the goal
//! itself, as a conjunct of `(not (=> (fuel_bool f) ...))`, or derived from the
//! asserted `(fuel_bool_default f)` through the prelude's
//! `fuel_bool(id) = fuel_bool_default(id)` axiom. E-matching instantiated the
//! definition in the first case, and `degrade@277` then discarded the
//! refutation because its own walk did not see the guard as a fact; in the
//! second case the guard was never a fact at all.
//!
//! Ground truth for every fixture is in its doc comment and was checked with
//! z3 4.12.5 (the solver Verus ships).

/// Reduced by delta debugging from Verus `broadcast_forall::test2`, query 3.
/// **GROUND TRUTH: UNSAT** (z3 4.12.5). The goal asserts `(fuel_bool p)`, so
/// the guarded definition holds; its instance at `(I 10)` gives `f(I 10)`, and
/// the goal asserts `(not f(I 10))`.
const GUARD_ASSERTED_BY_THE_GOAL: &str = r#"
(declare-sort FuelId 0)
(declare-fun fuel_bool (FuelId) Bool)
(declare-sort Poly 0)
(declare-fun I (Int) Poly)
(declare-sort Type 0)
(declare-const INT Type)
(declare-fun has_type (Poly Type) Bool)
(assert (forall ((x Int)) (! (has_type (I x) INT) :pattern ((has_type (I x) INT)))))
(declare-const fuel%f FuelId)
(declare-const fuel%p FuelId)
(assert (distinct fuel%f fuel%p))
(declare-fun f.? (Poly) Bool)
(assert (=> (fuel_bool fuel%p)
  (forall ((i! Poly)) (! (=> (has_type i! INT) (f.? i!)) :pattern ((f.? i!))))))
(declare-const tmp%1 Bool)
(declare-const %%location_label%%0 Bool)
(assert (not (=> (fuel_bool fuel%p)
  (=> (= tmp%1 (f.? (I 10))) (=> %%location_label%%0 tmp%1)))))
(check-sat)
"#;

/// The same query with the guard FALSE. **GROUND TRUTH: SAT** (z3 4.12.5).
const GUARD_ASSERTED_FALSE: &str = r#"
(declare-sort FuelId 0)
(declare-fun fuel_bool (FuelId) Bool)
(declare-sort Poly 0)
(declare-fun I (Int) Poly)
(declare-sort Type 0)
(declare-const INT Type)
(declare-fun has_type (Poly Type) Bool)
(assert (forall ((x Int)) (! (has_type (I x) INT) :pattern ((has_type (I x) INT)))))
(declare-const fuel%f FuelId)
(declare-const fuel%p FuelId)
(assert (distinct fuel%f fuel%p))
(declare-fun f.? (Poly) Bool)
(assert (=> (fuel_bool fuel%p)
  (forall ((i! Poly)) (! (=> (has_type i! INT) (f.? i!)) :pattern ((f.? i!))))))
(declare-const tmp%1 Bool)
(declare-const %%location_label%%0 Bool)
(assert (not (fuel_bool fuel%p)))
(assert (not (=> (= tmp%1 (f.? (I 10))) (=> %%location_label%%0 tmp%1))))
(check-sat)
"#;

/// Verus's fuel prelude in miniature: the guard `(fuel_bool f)` follows only
/// from `(fuel_bool_default f)` through the `fuel_defaults` axiom, itself under
/// the asserted guard `fuel_defaults`. **GROUND TRUTH: UNSAT** (z3 4.12.5):
/// `f(5) = (5 > 0)`.
const GUARD_DERIVED_FROM_THE_DEFAULT: &str = r#"
(declare-sort FuelId 0)
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(assert (=> fuel_defaults
  (forall ((id FuelId)) (! (= (fuel_bool id) (fuel_bool_default id)) :pattern ((fuel_bool id))))))
(declare-const fuel%f FuelId)
(declare-fun f (Int) Bool)
(assert (fuel_bool_default fuel%f))
(assert (=> (fuel_bool fuel%f) (forall ((i Int)) (! (= (f i) (> i 0)) :pattern ((f i))))))
(assert fuel_defaults)
(assert (not (f 5)))
(check-sat)
"#;

/// The derived guard is FALSE: `(fuel_bool_default f)` is asserted false.
/// **GROUND TRUTH: SAT** (z3 4.12.5).
const DERIVED_GUARD_FALSE: &str = r#"
(declare-sort FuelId 0)
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(assert (=> fuel_defaults
  (forall ((id FuelId)) (! (= (fuel_bool id) (fuel_bool_default id)) :pattern ((fuel_bool id))))))
(declare-const fuel%f FuelId)
(declare-fun f (Int) Bool)
(assert (not (fuel_bool_default fuel%f)))
(assert (=> (fuel_bool fuel%f) (forall ((i Int)) (! (= (f i) (> i 0)) :pattern ((f i))))))
(assert fuel_defaults)
(assert (not (f 5)))
(check-sat)
"#;

/// The derived guard holds and the definition is consistent with the goal:
/// `f(0) = (0 > 0)` is false. **GROUND TRUTH: SAT** (z3 4.12.5).
const DERIVED_GUARD_CONSISTENT: &str = r#"
(declare-sort FuelId 0)
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(assert (=> fuel_defaults
  (forall ((id FuelId)) (! (= (fuel_bool id) (fuel_bool_default id)) :pattern ((fuel_bool id))))))
(declare-const fuel%f FuelId)
(declare-fun f (Int) Bool)
(assert (fuel_bool_default fuel%f))
(assert (=> (fuel_bool fuel%f) (forall ((i Int)) (! (= (f i) (> i 0)) :pattern ((f i))))))
(assert fuel_defaults)
(assert (not (f 0)))
(check-sat)
"#;

/// A universal under an `or` whose sibling is free, next to a unit-guarded
/// one. **GROUND TRUTH: SAT** (z3 4.12.5): `g := true`, nothing forces `q(c)`.
const FREE_DISJUNCT_SIBLING: &str = r#"
(set-logic UFLIA)
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(declare-const g Bool)
(declare-const h Bool)
(declare-const c Int)
(assert (and h (p c)))
(assert (=> h (forall ((x Int)) (! (p x) :pattern ((p x))))))
(assert (or g (forall ((y Int)) (! (q y) :pattern ((q y))))))
(assert (not (q c)))
(check-sat)
"#;

/// A broadcast chain in miniature whose lemma is consistent with the goal.
/// **GROUND TRUTH: SAT** (z3 4.12.5): `f(3) = g(3) = 4`.
const BROADCAST_CHAIN_CONSISTENT: &str = r#"
(declare-sort FuelId 0)
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(assert (=> fuel_defaults
  (forall ((id FuelId)) (! (= (fuel_bool id) (fuel_bool_default id)) :pattern ((fuel_bool id))))))
(declare-const fuel%lemma FuelId)
(declare-const fuel%group FuelId)
(declare-const fuel%top FuelId)
(assert (distinct fuel%lemma fuel%group fuel%top))
(assert (fuel_bool_default fuel%top))
(assert (=> (fuel_bool_default fuel%top) (and (fuel_bool_default fuel%group))))
(assert (=> (fuel_bool_default fuel%group) (fuel_bool_default fuel%lemma)))
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (forall ((x Int)) (! (= (g x) (+ x 1)) :pattern ((g x)))))
(assert (=> (fuel_bool fuel%lemma) (forall ((x Int)) (! (= (f x) (g x)) :pattern ((f x))))))
(assert fuel_defaults)
(assert (not (= (f 3) 5)))
(check-sat)
"#;

/// The same chain with the top group's default asserted false, so no member
/// is enabled. **GROUND TRUTH: SAT** (z3 4.12.5).
const BROADCAST_CHAIN_DISABLED: &str = r#"
(declare-sort FuelId 0)
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(assert (=> fuel_defaults
  (forall ((id FuelId)) (! (= (fuel_bool id) (fuel_bool_default id)) :pattern ((fuel_bool id))))))
(declare-const fuel%lemma FuelId)
(declare-const fuel%group FuelId)
(declare-const fuel%top FuelId)
(assert (distinct fuel%lemma fuel%group fuel%top))
(assert (not (fuel_bool_default fuel%top)))
(assert (=> (fuel_bool_default fuel%top) (and (fuel_bool_default fuel%group))))
(assert (=> (fuel_bool_default fuel%group) (fuel_bool_default fuel%lemma)))
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)
(assert (forall ((x Int)) (! (= (g x) (+ x 1)) :pattern ((g x)))))
(assert (=> (fuel_bool fuel%lemma) (forall ((x Int)) (! (= (f x) (g x)) :pattern ((f x))))))
(assert fuel_defaults)
(assert (not (= (f 3) 4)))
(check-sat)
"#;

/// The guard reached through an asserted implication chain and the
/// `fb(i) = fbd(i)` axiom, whose instance at 1 the presolve model already
/// satisfies. **GROUND TRUTH: UNSAT** (z3 4.12.5): `a` and `b` give `(fbd 1)`,
/// hence `(fb 1)`, hence `g(0) = 1`, and the goal asserts `g(0) = 5`.
const GUARD_THROUGH_A_SATISFIED_INSTANCE: &str = r#"
(set-logic ALL)
(declare-fun fb (Int) Bool)
(declare-fun fbd (Int) Bool)
(declare-fun g (Int) Int)
(declare-const a Bool)
(declare-const b Bool)
(assert (forall ((i Int)) (! (= (fb i) (fbd i)) :pattern ((fb i)))))
(assert (=> (fb 1) (forall ((x Int)) (! (= (g x) (+ x 1)) :pattern ((g x))))))
(assert (= (g 0) 5))
(assert (=> a b (fbd 1)))
(assert a)
(assert b)
(check-sat)
"#;

/// `GUARD_THROUGH_A_SATISFIED_INSTANCE` without `(assert b)`: the chain never
/// fires. **GROUND TRUTH: SAT.**
const GUARD_THROUGH_A_PARTIAL_CHAIN: &str = r#"
(set-logic ALL)
(declare-fun fb (Int) Bool)
(declare-fun fbd (Int) Bool)
(declare-fun g (Int) Int)
(declare-const a Bool)
(declare-const b Bool)
(assert (forall ((i Int)) (! (= (fb i) (fbd i)) :pattern ((fb i)))))
(assert (=> (fb 1) (forall ((x Int)) (! (= (g x) (+ x 1)) :pattern ((g x))))))
(assert (= (g 0) 5))
(assert (=> a b (fbd 1)))
(assert a)
(check-sat)
"#;

fn verdicts(smt: &str) -> Vec<String> {
    crate::common::solve_vec(smt)
}

/// CAPABILITY: before #unit-facts-shared this answered `unknown`.
#[test]
fn a_definition_guarded_by_the_goal_refutes() {
    let results = verdicts(GUARD_ASSERTED_BY_THE_GOAL);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "the goal asserts the fuel guard, so the definition's instance at \
         (I 10) contradicts the goal; got {results:?}"
    );
}

/// REGRESSION GUARD for #guarded-then-entailed. Solved before row D1 through
/// the proxy lane; with #unit-bool-eq the definition becomes entailed in the
/// second E-matching round, and while guarded bindings still entered the
/// persistent memo, its instance at 5 was never produced again and this
/// answered `unknown`.
#[test]
fn a_definition_guarded_through_the_fuel_default_refutes() {
    let results = verdicts(GUARD_DERIVED_FROM_THE_DEFAULT);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "fuel_bool(f) = fuel_bool_default(f) = true, so f(5) = (5 > 0); got \
         {results:?}"
    );
}

/// REGRESSION GUARD for #conjunctive-closure: answered `unsat` before the
/// implication chain made `(fb 1)` a unit fact. Once it is one, the
/// definition is instantiated as entailed, and `degrade@277` kept the
/// refutation only after the closure also replayed the unconditional instance
/// `(= (fb 1) (fbd 1))`, which the solve skipped as model-satisfied.
#[test]
fn a_guard_read_through_a_model_satisfied_instance_refutes() {
    let results = verdicts(GUARD_THROUGH_A_SATISFIED_INSTANCE);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "a and b give (fbd 1), so (fb 1) and g(0) = 1; got {results:?}"
    );
}

/// SOUNDNESS FLOOR: each fixture below differs from a refuted one only in the
/// guard's value or in the goal, and is satisfiable.
#[test]
fn guarded_definitions_never_refute_a_satisfiable_query() {
    for (name, smt) in [
        ("goal guard false", GUARD_ASSERTED_FALSE),
        ("derived guard false", DERIVED_GUARD_FALSE),
        ("derived guard, consistent goal", DERIVED_GUARD_CONSISTENT),
        ("free disjunct sibling", FREE_DISJUNCT_SIBLING),
        (
            "broadcast chain, consistent goal",
            BROADCAST_CHAIN_CONSISTENT,
        ),
        ("broadcast chain disabled", BROADCAST_CHAIN_DISABLED),
        ("partial implication chain", GUARD_THROUGH_A_PARTIAL_CHAIN),
    ] {
        for results in [verdicts(smt), crate::common::solve_selfcheck_vec(smt)] {
            assert!(
                !results.iter().any(|r| r == "unsat"),
                "WRONG ANSWER ({name}): this query is SATISFIABLE; got {results:?}"
            );
        }
    }
}

/// The recovered refutations never become `sat` in any posture.
#[test]
fn guarded_definitions_are_never_sat_when_refutable() {
    for smt in [
        GUARD_ASSERTED_BY_THE_GOAL,
        GUARD_DERIVED_FROM_THE_DEFAULT,
        GUARD_THROUGH_A_SATISFIED_INSTANCE,
    ] {
        for results in [verdicts(smt), crate::common::solve_selfcheck_vec(smt)] {
            assert!(
                !results.iter().any(|r| r == "sat"),
                "WRONG ANSWER: the query is UNSATISFIABLE; got {results:?}"
            );
        }
    }
}
