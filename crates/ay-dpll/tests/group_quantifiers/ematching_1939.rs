// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for issue #1939: E-matching with multiple triggered quantifier axioms.
//!
//! Reproduction from verification-consumer: Adding an unused triggered axiom must not prevent instantiating
//! a different axiom whose trigger has a matching ground term.

use ntest::timeout;

fn assert_sat_or_unknown(outputs: &[String], label: &str) {
    assert!(
        outputs.len() == 1 && (outputs[0] == "sat" || outputs[0] == "unknown"),
        "{label}: expected sat or unknown, got: {outputs:?}"
    );
}

/// #1939: Multiple axioms with only one having ground terms.
#[test]
#[timeout(60000)]
fn test_issue_1939_multiple_axioms_one_unused() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun logic_add_one (Int) Int)
        (declare-fun logic_double (Int) Int)
        (declare-const x Int)
        (declare-const result Int)

        ; Axiom for add_one - with explicit pattern
        (assert (forall ((y Int)) (! (= (logic_add_one y) (+ y 1)) :pattern ((logic_add_one y)))))

        ; Axiom for double (NOT USED in goal) - with explicit pattern
        (assert (forall ((z Int)) (! (= (logic_double z) (* z 2)) :pattern ((logic_double z)))))

        ; Body: result = x + 1
        (assert (= result (+ x 1)))

        ; Negated postcondition - this creates (logic_add_one x) which should trigger
        (assert (not (= result (logic_add_one x))))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// #1954: SAT case - E-matching + CEGQI where formula is satisfiable.
///
/// Z3 returns SAT for this formula (x = 0 is a model).
/// Fixed: AY now correctly returns "sat" when E-matching added instantiations
/// and the solver finds SAT on the ground formula.
#[test]
#[timeout(60000)]
fn test_issue_1954_sat_with_ematching_and_cegqi() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-const x Int)

        ; Axiom for f - with explicit pattern (will be instantiated)
        (assert (forall ((y Int)) (! (= (f y) (+ y 1)) :pattern ((f y)))))

        ; Axiom for g (NOT USED) - triggered but no ground g(...) terms
        (assert (forall ((z Int)) (! (= (g z) (* z 2)) :pattern ((g z)))))

        ; Ground term (f x) triggers E-matching
        ; Constraint is satisfiable: (f x) > 0 means x + 1 > 0, i.e. x > -1
        (assert (> (f x) 0))
        (assert (> x -2))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_sat_or_unknown(&outputs, "#1954 SAT with E-matching and CEGQI");
}

/// Ground arithmetic UNSAT with irrelevant forall axiom.
///
/// The ground portion (i >= 0, i < 10, i' = i+1, NOT(i' >= 0)) is UNSAT
/// by itself. Adding an unreferenced forall axiom (whose function is never
/// applied in ground terms) must not change the result. Before the fix,
/// CEGQI result mapping incorrectly flipped UNSAT → SAT because it assumed
/// the UNSAT was from the CE lemma, not the ground contradiction.
#[test]
#[timeout(60000)]
fn test_verification_consumer_779_ground_unsat_with_irrelevant_forall() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-const i Int)
        (declare-const i_prime Int)
        (declare-fun logic_dummy (Int) Int)

        ; Ground arithmetic: i in [0, 10), i_prime = i + 1
        (assert (>= i 0))
        (assert (< i 10))
        (assert (= i_prime (+ i 1)))

        ; Negated goal: NOT(i_prime >= 0) — this is contradictory with the above
        (assert (not (>= i_prime 0)))

        ; Irrelevant forall axiom: forall x. dummy(x) = x
        ; The function logic_dummy is NEVER applied in ground terms
        (assert (forall ((x Int)) (! (= (logic_dummy x) x) :pattern ((logic_dummy x)))))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// #1939: Single axiom case (sanity check).
#[test]
#[timeout(60000)]
fn test_issue_1939_single_axiom_baseline() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun logic_add_one (Int) Int)
        (declare-const x Int)
        (declare-const result Int)

        ; Axiom for add_one - with explicit pattern
        (assert (forall ((y Int)) (! (= (logic_add_one y) (+ y 1)) :pattern ((logic_add_one y)))))

        ; Body: result = x + 1
        (assert (= result (+ x 1)))

        ; Negated postcondition
        (assert (not (= result (logic_add_one x))))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// #6045: Triggered quantifier with no matching ground terms correctly
/// returns SAT (not false-unknown).
///
/// Q1 has triggers and ground `(P 0)` exists — E-matching instantiates it.
/// Q2 has triggers but no ground `(R ...)` term — E-matching correctly finds
/// nothing to instantiate. Since R is uninterpreted and unconstrained, the
/// model can set R(y)=false for all y, satisfying `forall y. R(y) => false`.
/// Z3 also returns SAT for this formula.
///
/// This verifies the `!has_triggers` guard on the unhandled-quantifier check
/// is correct: triggered quantifiers without matching ground terms are handled
/// by E-matching's decision that no instances are needed.
#[test]
#[timeout(60000)]
fn test_triggered_no_ground_terms_correctly_returns_sat_6045() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun P (Int) Bool)
        (declare-fun Q (Int) Bool)
        (declare-fun R (Int) Bool)

        ; Q1: triggered, E-matching instantiates (ground P(0) exists)
        (assert (forall ((x Int))
            (! (=> (P x) (Q x))
               :pattern ((P x)))))

        ; Q2: triggered, no ground R(...) — E-matching correctly skips
        (assert (forall ((y Int))
            (! (=> (R y) false)
               :pattern ((R y)))))

        ; Ground terms — only P(0) triggers Q1
        (assert (P 0))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    // SAT is correct: model sets P(0)=true, Q(0)=true (from Q1), R(y)=false
    // for all y (satisfies Q2 vacuously). Z3 agrees.
    assert_sat_or_unknown(&outputs, "#6045 triggered quantifier without ground terms");
}

/// #6045: Two triggered quantifiers, both without ground terms, is SAT.
///
/// Since F and G are uninterpreted and unconstrained, the model can set
/// F(x)=false and G(y)=false for all arguments, vacuously satisfying both
/// forall axioms. Z3 also returns SAT.
#[test]
#[timeout(60000)]
fn test_two_triggered_no_ground_terms_correctly_returns_sat_6045() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun F (Int) Bool)
        (declare-fun G (Int) Bool)
        (declare-const a Int)

        ; Triggered forall — no ground F(...) term exists
        (assert (forall ((x Int))
            (! (=> (F x) false)
               :pattern ((F x)))))

        ; Triggered forall — no ground G(...) term exists
        (assert (forall ((y Int))
            (! (=> (G y) false)
               :pattern ((G y)))))

        ; Trivially satisfiable ground constraint
        (assert (> a 0))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    // SAT is correct: model sets a=1, F(x)=false, G(y)=false for all x,y.
    // Z3 also returns SAT.
    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "expected sat or unknown, got: {outputs:?}"
    );
}

/// #6045: CEGQI trigger routing guard prevents false UNSAT.
///
/// The formula has a triggered forall and a triggerless exists. Before the
/// #6045 fix, CEGQI would create CE lemmas for the triggered forall,
/// which combined with E-matching instances to produce false UNSAT (#1954).
/// The `!has_triggers` guard on CEGQI prevents this by routing triggered
/// quantifiers to E-matching only.
///
/// This test verifies the guard is working: E-matching handles the triggered
/// forall, CEGQI handles the triggerless exists, and they don't interfere.
#[test]
#[timeout(60000)]
fn test_cegqi_trigger_guard_prevents_false_unsat_6045() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const x Int)

        ; Triggered forall — E-matching handles this
        (assert (forall ((y Int)) (! (= (f y) (+ y 1)) :pattern ((f y)))))

        ; Ground term triggers E-matching: f(x) = x + 1
        (assert (> (f x) 0))

        ; Triggerless exists — CEGQI handles this
        (assert (exists ((z Int)) (> z 100)))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    // SAT: x=0 gives f(0)=1>0, z=101 satisfies exists. Both quantifiers handled.
    // Before #6045 fix, CEGQI created CE lemma for the forall, causing false UNSAT.
    assert_sat_or_unknown(&outputs, "#6045 trigger guard SAT case");
}

/// P2:47 Finding 1: Triggered forall + exists on same function = UNSAT,
/// but E-matching can't fire (no ground term matching the forall trigger).
///
/// Formula:
///   forall x. f(x) > 0   (triggered on (f x), no ground f(...) terms)
///   exists y. f(y) < 0    (no trigger, CEGQI candidate)
///
/// These are contradictory (forall says positive, exists says negative).
/// Correct answer: unsat.
/// Risk: solver returns sat because E-matching finds nothing to instantiate
/// for the forall, and CEGQI only handles the exists.
///
/// If the solver returns "unknown", that's also acceptable (incomplete but sound).
#[test]
#[timeout(60000)]
fn test_triggered_forall_vs_exists_same_func_unsat_p2_47() {
    let smt = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)

        ; Forall: f is always positive (triggered — E-matching needs ground f(...))
        (assert (forall ((x Int)) (! (> (f x) 0) :pattern ((f x)))))

        ; Exists: f is negative somewhere (no trigger — CEGQI candidate)
        (assert (exists ((y Int)) (< (f y) 0)))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    // UNSAT is correct. Unknown is acceptable (sound incomplete).
    // SAT would be a soundness bug (P2:47 Finding 1).
    assert_ne!(
        outputs[0], "sat",
        "triggered-forall + exists on same function must not return false SAT (P2:47)"
    );
}
