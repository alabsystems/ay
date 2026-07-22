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
