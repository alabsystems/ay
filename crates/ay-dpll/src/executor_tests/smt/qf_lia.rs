// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_executor_qf_lia_simple_sat() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (<= x 10))
        (assert (>= x 5))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_lia_simple_unsat() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (<= x 5))
        (assert (>= x 10))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_lia_integer_gap_unsat() {
    // x > 5 and x < 6 where x is integer - no integer between 5 and 6
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (> x 5))
        (assert (< x 6))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // LIA should detect this is UNSAT (no integer in (5,6))
    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_lia_integer_boundary_sat() {
    // x >= 5 and x <= 6 where x is integer - x can be 5 or 6
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (>= x 5))
        (assert (<= x 6))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_lia_equality() {
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (assert (= x 5))
        (assert (>= x 1))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_lia_linear_constraint_sat() {
    // x + y <= 10, x >= 3, y >= 4: solution x=3, y=4 (integer)
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (<= (+ x y) 10))
        (assert (>= x 3))
        (assert (>= y 4))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_lia_linear_constraint_unsat() {
    // x + y <= 10, x >= 5, y >= 6: 5 + 6 = 11 > 10, so UNSAT
    let input = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (assert (<= (+ x y) 10))
        (assert (>= x 5))
        (assert (>= y 6))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}

fn arithmetic_ite_nonnegative_problem(
    extra_setup: &str,
    definition: &str,
    contradiction: &str,
) -> String {
    format!(
        r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const A Int)
        (declare-const B Int)
        (declare-const C Int)
        (declare-const D Int)
        (declare-const E Int)
        (declare-const F Int)
        (declare-const G Int)
        (declare-const H Int)
        (declare-const I Int)
        (declare-const J Int)
        {extra_setup}
        {definition}
        (assert (= H (+ C F)))
        (assert (= G (+ B 1)))
        (assert (= F (+ A 1)))
        (assert (= E (+ D G)))
        (assert (>= D 0))
        (assert (>= A 0))
        (assert (>= B 0))
        (assert (>= C 0))
        {contradiction}
        (check-sat)
    "#
    )
}

fn assert_arithmetic_ite_nonnegative_has_strict_proof(
    extra_setup: &str,
    definition: &str,
    contradiction: &str,
) {
    let input = arithmetic_ite_nonnegative_problem(extra_setup, definition, contradiction);
    let commands = parse(&input).expect("valid QF_LIA fixture");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("solver executes");

    assert_eq!(outputs, vec!["unsat"]);
    let proof = exec.last_proof().expect("UNSAT publishes a proof");
    let quality = ay_proof::check_proof_strict(proof, exec.terms())
        .expect("arithmetic-ITE contradiction has a strict proof");
    assert_eq!(
        quality.trust_count, 0,
        "proof must be trust-free: {quality}"
    );
    assert!(
        ay_proof::terminal_trust_report(proof).is_trust_free(),
        "the empty-clause derivation must not depend on trust"
    );
}

fn assert_arithmetic_ite_surface_is_strict_or_fails_closed(definition: &str) {
    let input = arithmetic_ite_nonnegative_problem("", definition, "(assert (< I 0))");
    let commands = parse(&input).expect("valid negated-condition fixture");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("solver executes");
    match outputs.as_slice() {
        [status] if status == "unknown" => assert!(exec.last_proof().is_none()),
        [status] if status == "unsat" => {
            let proof = exec.last_proof().expect("UNSAT publishes a proof");
            let quality = ay_proof::check_proof_strict(proof, exec.terms())
                .expect("published proof is strict");
            assert_eq!(quality.trust_count, 0, "proof must be trust-free");
        }
        _ => panic!("expected strict UNSAT or fail-closed UNKNOWN, got {outputs:?}"),
    }
}

/// Regression for the formula-level arithmetic-ITE trust gap isolated from
/// dillig12_m. Every branch is contradictory: `E = D + B + 1` and
/// `F = A + 1`, so `I` is nonnegative under either guard.
#[test]
fn arithmetic_ite_nonnegative_contradiction_has_strict_proof() {
    assert_arithmetic_ite_nonnegative_has_strict_proof(
        "",
        "(assert (ite (= J 1) (= I (+ E F)) (= I E)))",
        "(assert (< I 0))",
    );
}

/// The source spelling before formula-level ITE lifting must reach the same
/// strict, trust-free proof. This exercises the established `ite_intro`
/// fallback rather than relying on the post-lift provenance repair alone.
#[test]
fn rhs_arithmetic_ite_nonnegative_contradiction_has_strict_proof() {
    assert_arithmetic_ite_nonnegative_has_strict_proof(
        "",
        "(assert (= I (ite (= J 1) (+ E F) E)))",
        "(assert (< I 0))",
    );
}

/// Canonical ITE construction swaps branches under a negated condition. The
/// surface-aware repair must either bridge that spelling exactly or decline
/// publication; native TermIds alone are not sufficient proof authority.
#[test]
fn negated_condition_ite_surfaces_are_strict_or_fail_closed() {
    for definition in [
        "(assert (ite (not (= J 1)) (= I E) (= I (+ E F))))",
        "(assert (= I (ite (not (= J 1)) E (+ E F))))",
    ] {
        assert_arithmetic_ite_surface_is_strict_or_fails_closed(definition);
    }
}

/// A Boolean definition can enter the exact provenance source set through a
/// substitution chain even though it contributes nothing to the final linear
/// contradiction. The exported Farkas step must omit that zero-weight,
/// non-arithmetic row while retaining exact authored-premise authority.
#[test]
fn arithmetic_ite_irrelevant_bool_provenance_has_strict_proof() {
    assert_arithmetic_ite_nonnegative_has_strict_proof(
        r#"
        (declare-const K Bool)
        (declare-const W Int)
        (assert (= K true))
        (assert (= W (ite K 0 1)))
        "#,
        "(assert (ite (= J 1) (= I (+ E F)) (= I E)))",
        "(assert (< (+ I W (- W)) 0))",
    );
}

/// Regression for dillig12_m's successor-failure trust leaf. The authored
/// disjunction claims one derived value is negative, while the exact equality,
/// ITE, and nonnegative-input premises make every disjunct impossible.
#[test]
fn arithmetic_ite_successor_failure_or_has_strict_proof() {
    assert_arithmetic_ite_nonnegative_has_strict_proof(
        "",
        "(assert (ite (= J 1) (= I (+ E F)) (= I E)))",
        "(assert (or (< F 0) (< G 0) (< H 0) (< I 0)))",
    );
}

// ---------------------------------------------------------------------------
// Integer div/mod-by-zero soundness (#div0).
//
// SMT-LIB Ints makes div/mod TOTAL but leaves `(div a 0)`/`(mod a 0)`
// UNCONSTRAINED: each denotes a single consistent but unspecified integer.
// AY used to pin `(div a 0) = 0` and `(mod a 0) = a`, wrongly refuting any
// constraint that contradicted the pinned value (WRONG-UNSAT). The fix returns
// an unconstrained variable keyed by `(op, dividend)` so the value is free but
// consistent across occurrences — matching z3 exactly. These tests lock in the
// verdicts (all checked against z3).
// ---------------------------------------------------------------------------

fn solve_one(input: &str) -> String {
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    outputs.into_iter().next().unwrap()
}

#[test]
fn test_div_by_zero_value_is_free_not_pinned_to_0() {
    // `(div 1 0)` can be positive: z3 = sat. Must NEVER be unsat (was the bug).
    assert_eq!(
        solve_one("(set-logic QF_NIA)(assert (< 0 (div 1 0)))(check-sat)"),
        "sat"
    );
}

#[test]
fn test_mod_by_zero_value_is_free_not_pinned_to_dividend() {
    // `(mod 5 0)` need not equal 5: z3 = sat. Must NEVER be unsat (was the bug).
    assert_eq!(
        solve_one("(set-logic QF_NIA)(assert (distinct (mod 5 0) 5))(check-sat)"),
        "sat"
    );
}

/// DISTINCT dividends get INDEPENDENT values at a zero divisor — `(div a 0)`
/// is a function of `a`, so `(div 1 0)` and `(div 2 0)` may differ. z3 = sat.
///
/// This is the case that separates "read back the value the solve chose for
/// THIS term" from "read back some zero-divisor value": a witness lookup that
/// ignores the dividend confirms one of these two assertions against the
/// other's value.
#[test]
fn test_div_by_zero_distinct_dividends_are_independent() {
    assert_eq!(
        solve_one("(set-logic QF_NIA)(assert (= (div 1 0) 5))(assert (= (div 2 0) 7))(check-sat)"),
        "sat"
    );
    assert_eq!(
        solve_one("(set-logic QF_NIA)(assert (= (mod 1 0) 5))(assert (= (mod 2 0) 7))(check-sat)"),
        "sat"
    );
}

/// `div` and `mod` at a zero divisor are independent of EACH OTHER too, even
/// on the same dividend. z3 = sat.
#[test]
fn test_div_and_mod_by_zero_are_independent_of_each_other() {
    assert_eq!(
        solve_one("(set-logic QF_NIA)(assert (and (= (div 1 0) 5) (= (mod 1 0) 7)))(check-sat)"),
        "sat"
    );
}

/// A SYMBOLIC divisor that is zero must not pick up the value of a site whose
/// divisor is nonzero — that one is fully determined by Euclidean division and
/// has nothing to do with the under-specified case. z3 = sat.
#[test]
fn test_symbolic_zero_divisor_does_not_borrow_a_nonzero_site() {
    // The two sites deliberately share a DIVIDEND (`x`) and differ only in the
    // divisor, so a lookup keyed on the dividend alone finds the wrong one: it
    // would answer `(div x y)` with `6 div 2 = 3` instead of the unconstrained
    // `9`. A CONSTANT divisor would not exercise this — that takes the literal
    // elimination path and never creates a symbolic witness at all.
    // Both orders: the NONZERO site first is the one that matters, since a
    // lookup that ignores the divisor takes whichever witness it reaches first
    // and the sites are scanned in term order.
    for (first, second) in [
        ("(assert (= (div x z) 3))", "(assert (= (div x y) 9))"),
        ("(assert (= (div x y) 9))", "(assert (= (div x z) 3))"),
    ] {
        assert_eq!(
            solve_one(&format!(
                "(set-logic QF_NIA)\
                 (declare-const x Int)(declare-const y Int)(declare-const z Int)\
                 (assert (= x 6))(assert (= y 0))(assert (= z 2)){first}{second}(check-sat)"
            )),
            "sat",
            "with {first} before {second}"
        );
    }
    assert_eq!(
        solve_one(concat!(
            "(set-logic QF_NIA)",
            "(declare-const x Int)(declare-const y Int)(declare-const z Int)",
            "(assert (= x 6))(assert (= y 0))(assert (= z 2))",
            "(assert (= (mod x y) 9))(assert (= (mod x z) 0))(check-sat)"
        )),
        "sat"
    );
    // A constant divisor alongside the under-specified site, for good measure.
    assert_eq!(
        solve_one(concat!(
            "(set-logic QF_NIA)(declare-const x Int)(declare-const y Int)",
            "(assert (= y 0))(assert (= (div x y) 9))(assert (= (div 3 2) 1))(check-sat)"
        )),
        "sat"
    );
}

#[test]
fn test_div_by_zero_is_single_consistent_value() {
    // `(div 1 0)` is ONE value, so it cannot be both 0 and 1: z3 = unsat.
    // This guards the cross-assertion consistency of the keyed fresh var.
    assert_eq!(
        solve_one("(set-logic QF_NIA)(assert (= (div 1 0) 0))(assert (= (div 1 0) 1))(check-sat)"),
        "unsat"
    );
}

#[test]
fn test_mod_by_zero_is_single_consistent_value() {
    assert_eq!(
        solve_one("(set-logic QF_NIA)(assert (= (mod 5 0) 0))(assert (= (mod 5 0) 1))(check-sat)"),
        "unsat"
    );
}

#[test]
fn test_self_div_with_possible_zero_not_pinned() {
    // `x = 0` makes `(div x x)` = `(div 0 0)` unconstrained, so it need not be 1:
    // z3 = sat. The old `x div x = 1` fold wrongly returned unsat.
    assert_eq!(
        solve_one(
            "(set-logic QF_NIA)(declare-const x Int)(assert (= x 0))(assert (distinct (div x x) 1))(check-sat)"
        ),
        "sat"
    );
}

#[test]
fn test_self_mod_with_possible_zero_not_pinned() {
    // `x = 0` makes `(mod x x)` = `(mod 0 0)` unconstrained, so it need not be 0:
    // z3 = sat. The old `x mod x = 0` fold wrongly returned unsat.
    assert_eq!(
        solve_one(
            "(set-logic QF_NIA)(declare-const x Int)(assert (= x 0))(assert (distinct (mod x x) 0))(check-sat)"
        ),
        "sat"
    );
}

#[test]
fn test_div_mod_nonzero_constant_divisor_still_exact() {
    // Non-regression: nonzero constant divisors must still fold Euclidean-exactly.
    assert_eq!(
        solve_one("(set-logic QF_NIA)(assert (= (div 7 2) 3))(check-sat)"),
        "sat"
    );
    assert_eq!(
        solve_one("(set-logic QF_NIA)(assert (= (mod 7 3) 1))(check-sat)"),
        "sat"
    );
    // SMT-LIB Euclidean: (div -7 2) = -4, (mod -7 2) = 1 (remainder non-negative).
    assert_eq!(
        solve_one("(set-logic QF_NIA)(assert (= (div (- 7) 2) (- 4)))(check-sat)"),
        "sat"
    );
    assert_eq!(
        solve_one("(set-logic QF_NIA)(assert (= (mod (- 7) 2) 1))(check-sat)"),
        "sat"
    );
    // A WRONG Euclidean value must still be unsat.
    assert_eq!(
        solve_one("(set-logic QF_NIA)(assert (= (div 7 2) 4))(check-sat)"),
        "unsat"
    );
}

#[test]
fn test_mod_nonzero_symbolic_divisor_still_sat() {
    // Non-regression: `(mod a b)` with b pinned to a nonzero value still solves.
    assert_eq!(
        solve_one(
            "(set-logic QF_NIA)(declare-const a Int)(declare-const b Int)\
             (assert (= b 3))(assert (= (mod a b) 0))(assert (= a 6))(check-sat)"
        ),
        "sat"
    );
}

#[test]
fn test_nia_memory_guard_fails_closed_to_unknown() {
    // #nia-oom regression: the NIA branch-and-bound split loop and the
    // tangent/McCormick refinement loop carry the LIA/LRA tableau + learned
    // state across iterations, so a pathological nonlinear query can grow memory
    // without bound. With no memory poll on either loop this OOM-killed a 128 GB
    // machine at 203 GB resident (the auto half-RAM 64 GB ceiling was set but
    // never checked on the NIA path). The fix adds a fail-closed
    // `ay_sys::process_memory_exceeded()` poll to both loops.
    //
    // Proof of the guard: the same nonlinear problem solves `sat` normally, but
    // under a forced memory-ceiling breach must degrade to `unknown`
    // (resource-out) instead of continuing to allocate — never OOM, never panic.
    let script = "(set-logic QF_NIA)(declare-const x Int)(declare-const y Int)\
                  (assert (= (* x y) 12))(assert (> x 1))(assert (> y 1))\
                  (assert (< x y))(check-sat)";

    // Baseline: no pressure -> the solver decides it.
    assert_eq!(solve_one(script), "sat");

    // Forced ceiling breach (thread-local; cleared before the assertion so a
    // panic cannot leak the forced state into other tests on this thread).
    ay_sys::force_process_memory_exceeded_for_testing(true);
    let under_pressure = solve_one(script);
    ay_sys::force_process_memory_exceeded_for_testing(false);
    assert_eq!(
        under_pressure, "unknown",
        "NIA must fail closed to unknown under memory pressure, not OOM/grow the tableau"
    );
}

// QF_UFLIA (Uninterpreted Functions with Linear Integer Arithmetic) Tests
