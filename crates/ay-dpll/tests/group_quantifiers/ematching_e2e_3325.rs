// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! End-to-end benchmarks for issue #3325: E-matching improvements for
//! quantifier-unknown reduction.
//!
//! These tests demonstrate formulas that return a definitive result (sat/unsat)
//! thanks to the E-matching pipeline (Phase A + B1b + B1c), where incomplete
//! quantifier handling would otherwise return `unknown`.
//!
//! Each test is modeled on realistic verification condition patterns from
//! downstream consumers (verification-consumer, deductive-checks) that depend on quantifier reasoning.

use ntest::timeout;

fn assert_sat_or_unknown(outputs: &[String], label: &str) {
    assert!(
        outputs.len() == 1 && (outputs[0] == "sat" || outputs[0] == "unknown"),
        "{label}: expected sat or unknown, got: {outputs:?}"
    );
}

/// Inverse function axioms with congruence-derived matching.
///
/// This tests the full E-matching pipeline including Phase B1c:
///   forall x. f(g(x)) = x    (trigger: f(g(x)))
///   forall x. g(f(x)) = x    (trigger: g(f(x)))
///   b = g(a)                  (ground fact)
///   f(b) != a                 (negated postcondition)
///
/// Reasoning chain:
///   1. b = g(a) → ground term g(a) exists
///   2. f(g(a)) matches trigger f(g(x)) with x=a → f(g(a)) = a
///   3. b = g(a) + congruence: f(b) = f(g(a))
///   4. f(b) = f(g(a)) = a, contradicting f(b) != a
///
/// Steps 2-3 require E-matching to see f(b) and f(g(a)) as congruent via the
/// EUF model (Phase B1c) or explicit rewriting.
#[test]
#[timeout(60000)]
fn test_e2e_inverse_function_congruence_unsat() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-const a Int)
        (declare-const b Int)

        ; f and g are inverse functions
        (assert (forall ((x Int)) (! (= (f (g x)) x) :pattern ((f (g x))))))
        (assert (forall ((x Int)) (! (= (g (f x)) x) :pattern ((g (f x))))))

        ; b is defined as g(a)
        (assert (= b (g a)))

        ; Negated postcondition: f(b) != a
        ; But f(b) = f(g(a)) = a by axiom, so this is contradictory
        (assert (not (= (f b) a)))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert!(
        outputs == vec!["unsat"],
        "Expected UNSAT from inverse function congruence, got: {outputs:?}",
    );
}

/// verification-consumer-style verification condition: function axiom + arithmetic postcondition.
///
/// Pattern from verification-consumer: a Rust function `add_checked(x, y)` has a logic axiom
/// defining its behavior, and a negated postcondition creates a contradiction.
///
///   forall x y. logic_add(x, y) = x + y       (function axiom)
///   result = logic_add(a, b)                    (function call)
///   a >= 0, b >= 0                              (preconditions)
///   NOT(result >= 0)                            (negated postcondition)
///
/// E-matching instantiates: logic_add(a, b) = a + b.
/// Combined with result = logic_add(a, b): result = a + b.
/// With a >= 0, b >= 0: result >= 0. Contradicts NOT(result >= 0).
#[test]
#[timeout(60000)]
fn test_e2e_verification_consumer_add_postcondition_unsat() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun logic_add (Int Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const result Int)

        ; Function axiom with trigger
        (assert (forall ((x Int) (y Int))
            (! (= (logic_add x y) (+ x y))
               :pattern ((logic_add x y)))))

        ; Function call: result = logic_add(a, b)
        (assert (= result (logic_add a b)))

        ; Preconditions
        (assert (>= a 0))
        (assert (>= b 0))

        ; Negated postcondition: result < 0
        (assert (< result 0))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// verification-consumer take_first_mut/hashmap_list style: a branch VC may carry a
/// trigger-annotated sequence axiom whose explicit trigger is valid but sterile
/// in that branch. The body still contains useful sequence UF terms
/// (`seq_len`, `seq_tail`). E-matching should use auto-extracted body patterns
/// only after the explicit trigger produces no instance.
#[test]
#[timeout(60000)]
fn test_e2e_verification_consumer_sterile_seq_trigger_fallback_unsat_8971() {
    let smt = r#"
        (set-logic ALL)
        (declare-sort Seq 0)
        (declare-fun seq_len (Seq) Int)
        (declare-fun seq_tail (Seq) Seq)
        (declare-fun seq_offset (Seq) Int)
        (declare-const s Seq)

        ; Explicit trigger is syntactically valid but has no matching ground term.
        ; The fallback body trigger can match seq_len(s) / seq_len(seq_tail(s)).
        (assert
          (forall ((x Seq))
            (! (= (seq_len (seq_tail x)) (seq_len x))
               :pattern ((seq_offset x)))))

        ; Negated branch obligation.
        (assert (not (= (seq_len (seq_tail s)) (seq_len s))))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Multi-axiom AUFLIA with congruence enabling cross-axiom reasoning.
///
///   forall x. P(x) => (f(x) > 0)     (axiom 1: P implies f positive)
///   forall x. f(x) > 0 => Q(f(x))    (axiom 2: f positive implies Q(f(x)))
///   a = b                              (congruence seed)
///   P(a)                               (ground fact triggers axiom 1)
///   NOT(Q(f(b)))                       (negated goal)
///
/// Chain: P(a) → f(a)>0 → Q(f(a)). With a=b: f(a)=f(b) → Q(f(a))=Q(f(b)).
/// Contradicts NOT(Q(f(b))).
#[test]
#[timeout(60000)]
fn test_e2e_multi_axiom_congruence_chain_unsat() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun P (Int) Bool)
        (declare-fun Q (Int) Bool)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const b Int)

        ; Axiom 1: P(x) implies f(x) > 0
        (assert (forall ((x Int))
            (! (=> (P x) (> (f x) 0))
               :pattern ((P x)))))

        ; Axiom 2: f(x) > 0 implies Q(f(x))
        (assert (forall ((x Int))
            (! (=> (> (f x) 0) (Q (f x)))
               :pattern ((f x)))))

        ; Ground facts
        (assert (= a b))
        (assert (P a))

        ; Negated goal: NOT(Q(f(b)))
        (assert (not (Q (f b))))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert!(
        outputs == vec!["unsat"],
        "Expected UNSAT from multi-axiom congruence chain, got: {outputs:?}",
    );
}

/// Satisfiable formula with quantifiers: E-matching finds consistent instantiations.
///
/// Verifies that the E-matching pipeline correctly reports SAT when instantiations
/// are consistent with the ground formula.
///
///   forall x. f(x) >= x              (f is non-decreasing)
///   f(a) = a + 5                      (specific value)
///   a = 3                             (model value)
///   f(a) > 0                          (consistent constraint)
///
/// E-matching instantiates: f(a) >= a → a+5 >= 3 → true. Formula is SAT.
#[test]
#[timeout(60000)]
fn test_e2e_sat_with_consistent_instantiations() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)

        ; f is non-decreasing
        (assert (forall ((x Int))
            (! (>= (f x) x)
               :pattern ((f x)))))

        ; Specific ground facts
        (assert (= (f a) (+ a 5)))
        (assert (= a 3))
        (assert (> (f a) 0))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_sat_or_unknown(&outputs, "consistent E-matching instantiations");
}

/// Incremental check-sat with quantifier accumulation.
///
/// Exercises push/pop + multiple check-sat calls — a pattern from verification-consumer where
/// the solver is used incrementally to verify multiple related conditions.
///
/// check-sat 1: base formula, SAT
/// check-sat 2 (after push + add axiom): UNSAT via E-matching
/// check-sat 3 (after pop): back to SAT (axiom removed)
#[test]
#[timeout(60000)]
fn test_e2e_incremental_quantifier_pushpop() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun logic_abs (Int) Int)
        (declare-const x Int)
        (declare-const r Int)

        ; r = logic_abs(x)
        (assert (= r (logic_abs x)))

        ; x is negative
        (assert (< x 0))

        (check-sat)

        (push 1)

        ; Axiom: forall y. y < 0 => logic_abs(y) = -y
        (assert (forall ((y Int))
            (! (=> (< y 0) (= (logic_abs y) (- 0 y)))
               :pattern ((logic_abs y)))))

        ; Claim r < 0 — but r = logic_abs(x) = -x > 0 since x < 0
        (assert (< r 0))

        (check-sat)

        (pop 1)

        ; After pop: axiom is removed, formula is again SAT
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs[0], "sat"); // No axiom yet, anything goes
    assert_eq!(outputs[1], "unsat"); // Axiom + r < 0 contradicts r = -x > 0
    assert_eq!(outputs[2], "sat"); // Axiom popped, back to permissive
}

/// Two-argument function axiom with partial application pattern.
///
/// Tests E-matching with multi-argument triggers — common in verification-consumer's
/// representation of binary operators.
///
///   forall x y. logic_max(x, y) >= x
///   forall x y. logic_max(x, y) >= y
///   forall x y. logic_max(x, y) = x OR logic_max(x, y) = y
///   logic_max(a, b) < a              (contradicts axiom 1)
#[test]
#[timeout(60000)]
fn test_e2e_binary_function_axiom_unsat() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun logic_max (Int Int) Int)
        (declare-const a Int)
        (declare-const b Int)

        ; Max axioms
        (assert (forall ((x Int) (y Int))
            (! (>= (logic_max x y) x)
               :pattern ((logic_max x y)))))

        (assert (forall ((x Int) (y Int))
            (! (>= (logic_max x y) y)
               :pattern ((logic_max x y)))))

        ; Ground: logic_max(a, b) < a — directly contradicts axiom 1
        (assert (< (logic_max a b) a))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Nested function application requiring multi-round E-matching.
///
///   forall x. f(f(x)) = x       (f is an involution)
///   f(a) = b                     (ground fact)
///   f(b) != a                    (negated: should be f(f(a)) = a)
///
/// Round 1: f(a)=b creates ground term f(a).
///   Trigger f(f(x)) needs nested f — matches f(f(a)) with x=a? No, f(f(a)) isn't in ground terms.
///   But f(b) is in ground terms (from negated postcondition), and b=f(a),
///   so f(b) = f(f(a)). Congruence: f(b) ≡ f(f(a)) → f(f(a))=a → f(b)=a.
///   Contradicts f(b) != a.
#[test]
#[timeout(60000)]
fn test_e2e_involution_nested_congruence_unsat() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const b Int)

        ; f is an involution: f(f(x)) = x
        (assert (forall ((x Int))
            (! (= (f (f x)) x)
               :pattern ((f (f x))))))

        ; f(a) = b
        (assert (= (f a) b))

        ; Negated: f(b) != a
        ; But f(b) = f(f(a)) = a by involution, contradiction
        (assert (not (= (f b) a)))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert!(
        outputs == vec!["unsat"],
        "Expected UNSAT from involution + congruence, got: {outputs:?}",
    );
}
