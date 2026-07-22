// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for issue #2844: check_sat_internal permanently corrupts ctx.assertions.
//!
//! The quantifier processing block in check_sat_internal used to permanently remove
//! quantified assertions via `retain()` and accumulate E-matching instantiations.
//! This caused consecutive check-sat calls to see a mutated assertion set.

use ntest::timeout;

fn assert_sat_or_unknown(output: &str, label: &str) {
    assert!(
        output == "sat" || output == "unknown",
        "{label}: expected sat or unknown, got: {output}"
    );
}

/// #2844: Two consecutive check-sat calls must return the same result.
///
/// Before the fix, the first check-sat would permanently remove the forall
/// assertion via retain(), causing the second check-sat to see no quantifiers
/// and return an incorrect result.
#[test]
#[timeout(60000)]
fn test_consecutive_check_sat_with_forall() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)

        ; Axiom: f(x) = x for all x
        (assert (forall ((x Int)) (! (= (f x) x) :pattern ((f x)))))

        ; Negated property: f(5) != 5 — should be UNSAT via E-matching
        (assert (not (= (f 5) 5)))

        ; First check-sat — should be unsat
        (check-sat)

        ; Second check-sat — must also be unsat (same assertion set)
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    // Both check-sat calls should produce the same result
    assert_eq!(outputs.len(), 2, "Expected 2 outputs, got: {outputs:?}");
    assert_eq!(
        outputs[0], outputs[1],
        "Consecutive check-sat must return the same result, got: {outputs:?}"
    );
    assert_eq!(outputs[0], "unsat", "Expected unsat, got: {outputs:?}");
}

/// #2844: Assertion count must not change between check-sat calls.
///
/// Uses a formula that is UNSAT only because of the quantifier:
/// (forall x. g(x)=x) AND g(5)!=5. If check-sat corrupts assertions
/// by removing the quantifier, the second call would flip to SAT.
#[test]
#[timeout(60000)]
fn test_assertion_count_stable_after_check_sat() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun g (Int) Int)

        ; Axiom: g(x) = x for all x
        (assert (forall ((x Int)) (! (= (g x) x) :pattern ((g x)))))
        ; Ground contradiction: g(5) != 5 — UNSAT with the quantifier
        (assert (not (= (g 5) 5)))

        ; First check-sat — should be unsat
        (check-sat)

        ; Second check-sat — must also be unsat (assertions unchanged)
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs.len(), 2, "Expected 2 outputs, got: {outputs:?}");
    // Both must be UNSAT — if the quantifier is corrupted, the second would be SAT
    assert_eq!(
        outputs[0], "unsat",
        "First check-sat must be unsat, got: {outputs:?}"
    );
    assert_eq!(
        outputs[1], "unsat",
        "Second check-sat must be unsat (assertions preserved), got: {outputs:?}"
    );
}

/// #2844: push/pop with quantifiers must work correctly.
///
/// A forall assertion in an inner scope should not leak into the outer scope
/// or be destroyed by check-sat.
#[test]
#[timeout(60000)]
fn test_push_pop_with_forall_assertion() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun h (Int) Int)
        (declare-const a Int)

        ; Base assertion
        (assert (= a 42))

        (push 1)
        ; Add a forall axiom in inner scope
        (assert (forall ((x Int)) (! (= (h x) (+ x 1)) :pattern ((h x)))))
        ; Add a ground assertion using h
        (assert (not (= (h a) 43)))

        ; check-sat in inner scope — should be unsat (h(42) = 43 by axiom)
        (check-sat)
        (pop 1)

        ; After pop, the forall and ground assertions are removed
        ; Only (= a 42) remains — should be sat
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs.len(), 2, "Expected 2 outputs, got: {outputs:?}");
    assert_eq!(outputs[0], "unsat", "Inner scope should be unsat");
    assert_eq!(outputs[1], "sat", "Outer scope should be sat");
}

/// #2844: Re-pushing the same contradiction after pop must remain UNSAT.
///
/// This catches the scope-replay leak where the first check-sat strips the
/// quantified axiom from assertions and pop restores the wrong assertion prefix.
#[test]
#[timeout(60000)]
fn test_repush_replays_same_quantifier_contradiction_2844() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int)) (! (= (f x) x) :pattern ((f x)))))

        (push 1)
        (assert (not (= (f 5) 5)))
        (check-sat)
        (pop 1)

        (push 1)
        (assert (not (= (f 5) 5)))
        (check-sat)
        (pop 1)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs.len(), 2, "Expected 2 outputs, got: {outputs:?}");
    assert_eq!(
        outputs[0], "unsat",
        "First inner scope should be unsat, got: {outputs:?}"
    );
    assert_eq!(
        outputs[1], "unsat",
        "Second inner scope should also be unsat after pop/re-push, got: {outputs:?}"
    );
}

/// #2862: Three independent push/pop scopes with different quantifiers.
///
/// Exercises the lazy QM initialization path: the first push happens
/// before any check-sat has initialized the quantifier manager.
/// Without the fix, push is skipped (QM=None), so pop has nothing
/// to restore and stale generation/deferred state leaks.
#[test]
#[timeout(60000)]
fn test_push_pop_lazy_init_no_state_leak_2862() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (declare-fun g (Int) Int)
        (declare-fun h (Int) Int)

        ; Scope 1: f(x) = x
        (push 1)
        (assert (forall ((x Int)) (! (= (f x) x) :pattern ((f x)))))
        (assert (not (= (f 5) 5)))
        (check-sat)
        (pop 1)

        ; Scope 2: g(x) = x + 1 (independent)
        (push 1)
        (assert (forall ((x Int)) (! (= (g x) (+ x 1)) :pattern ((g x)))))
        (assert (not (= (g 5) 6)))
        (check-sat)
        (pop 1)

        ; Scope 3: h(x) = x * 2 — no contradiction, should be SAT
        (push 1)
        (assert (forall ((x Int)) (! (= (h x) (* 2 x)) :pattern ((h x)))))
        (assert (= (h 3) 6))
        (check-sat)
        (pop 1)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs.len(), 3, "Expected 3 outputs, got: {outputs:?}");
    assert_eq!(outputs[0], "unsat", "Scope 1: f(5) != 5 should be unsat");
    assert_eq!(outputs[1], "unsat", "Scope 2: g(5) != 6 should be unsat");
    assert_sat_or_unknown(&outputs[2], "Scope 3: h(3) = 6");
}

/// #2862: Nested push/pop (2 levels deep) with quantifiers.
///
/// Tests that the QM scope stack tracks nested scopes correctly
/// when initialized lazily during the first push.
#[test]
#[timeout(60000)]
fn test_nested_push_pop_with_lazy_init_2862() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun f (Int) Int)
        (declare-const a Int)

        (assert (= a 10))

        ; Outer push — QM may not exist yet
        (push 1)
        (assert (forall ((x Int)) (! (= (f x) (+ x 1)) :pattern ((f x)))))

        ; Inner push
        (push 1)
        (assert (not (= (f a) 11)))
        (check-sat)
        (pop 1)

        ; After inner pop, contradiction is gone. f(a)=a+1 still asserted.
        ; (= a 10) and forall still hold, no contradiction.
        (check-sat)
        (pop 1)

        ; After outer pop, only (= a 10) remains — SAT
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs.len(), 3, "Expected 3 outputs, got: {outputs:?}");
    assert_eq!(
        outputs[0], "unsat",
        "Inner scope: f(10) != 11 should be unsat"
    );
    // After inner pop: forall and (= a 10) remain. No contradiction.
    assert_sat_or_unknown(&outputs[1], "After inner pop: no contradiction");
    assert_eq!(outputs[2], "sat", "After outer pop: only (= a 10) remains");
}

/// #2865: Quantifiers over uninterpreted sorts that neither E-matching nor CEGQI
/// can handle must produce "unknown", not "sat".
///
/// Before the fix, such quantifiers were silently stripped from assertions and
/// the solver could return SAT without considering them — a soundness hole.
#[test]
#[timeout(60000)]
fn test_unhandled_quantifier_returns_unknown_2865() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-sort S 0)
        (declare-fun f (Int) Int)
        (declare-fun p (S) Bool)

        ; This quantifier CAN be handled by E-matching (Int domain + pattern)
        (assert (forall ((x Int)) (! (= (f x) x) :pattern ((f x)))))
        (assert (= (f 5) 5))

        ; This quantifier CANNOT be handled: uninterpreted sort S, no ground terms
        (assert (forall ((s S)) (p s)))

        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs.len(), 1, "Expected 1 output, got: {outputs:?}");
    assert_eq!(
        outputs[0], "unknown",
        "Unhandled quantifier over uninterpreted sort should produce unknown, got: {:?}",
        outputs[0]
    );
}

/// #8969: restored transparent-function quantifiers should use an invalid
/// model instance as a refinement before degrading to Unknown.
///
/// The trigger intentionally mentions `transparent_probe`, not
/// `logic_count8__log`, so initial E-matching only adds the `n = 0` instance.
/// Restored model validation then sees the skipped quantified definition and
/// finds the concrete bad `n = 1` instance. That instance is enough to prove
/// UNSAT once added back to the pre-restore ground assertions.
#[test]
#[timeout(60000)]
fn test_popcount_transparent_function_restore_refines_invalid_model_8969() {
    let smt = r#"
        (set-logic AUFLIA)
        (declare-fun logic_count8__log (Int) Int)
        (declare-fun transparent_probe (Int) Bool)

        (assert (transparent_probe 0))
        (assert
          (forall ((n Int))
            (! (= (logic_count8__log n)
                  (+ (ite (< (mod n 2) 1) 0 1)
                     (ite (< (mod n 4) 2) 0 1)
                     (ite (< (mod n 8) 4) 0 1)
                     (ite (< (mod n 16) 8) 0 1)
                     (ite (< (mod n 32) 16) 0 1)
                     (ite (< (mod n 64) 32) 0 1)
                     (ite (< (mod n 128) 64) 0 1)
                     (ite (< (mod n 256) 128) 0 1)))
               :pattern ((transparent_probe n)))))

        (assert (= (logic_count8__log 1) 0))

        (check-sat)
        (check-sat)
    "#;

    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat", "unsat"],
        "#8969 restored popcount-function quantifier should refine the invalid n=1 model instance, got: {outputs:?}"
    );
}
