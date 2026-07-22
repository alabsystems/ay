// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_executor_qf_lra_simple_sat() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (<= x 10.0))
        (assert (>= x 5.0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_lra_simple_unsat() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (<= x 5.0))
        (assert (>= x 10.0))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_lra_linear_constraint_unsat() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (<= (+ x y) 10.0))
        (assert (>= x 5.0))
        (assert (>= y 6.0))
        (check-sat)
    "#;
    // x >= 5, y >= 6, but x + y <= 10: 5 + 6 = 11 > 10, so UNSAT

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_lra_linear_constraint_sat() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (<= (+ x y) 10.0))
        (assert (>= x 3.0))
        (assert (>= y 4.0))
        (check-sat)
    "#;
    // x >= 3, y >= 4, x + y <= 10: 3 + 4 = 7 <= 10, so SAT

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
#[test]
fn test_executor_qf_lra_strict_inequality() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 5.0))
        (assert (> x 5.0))
        (check-sat)
    "#;
    // x < 5 and x > 5 is impossible

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_lra_equality_with_strict() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (= x 5.0))
        (assert (> x 5.0))
        (check-sat)
    "#;
    // x = 5 and x > 5 is impossible

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
/// Regression test for #1243: LRA Farkas verification panic on simple equalities + disjunction.
#[test]
fn test_executor_qf_lra_farkas_verification_regression_1243() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x_0 Real)
        (assert (>= x_0 0))
        (assert (<= x_0 1))
        (declare-const y_0 Real)
        (assert (= y_0 (+ (* 1 x_0) 1)))
        (assert (or (< y_0 0.5) (> y_0 2.5)))
        (check-sat)
    "#;
    // UNSAT because x ∈ [0,1] => y = x+1 ∈ [1,2] which contradicts y ∉ [0.5,2.5]

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unsat"]);
}
#[test]
fn test_executor_qf_lra_scaled_variable() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (>= (* 2.0 x) 10.0))
        (assert (>= x 5.0))
        (check-sat)
    "#;
    // 2x >= 10 and x >= 5: x >= 5 satisfies 2x >= 10

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat"]);
}
/// #5600: QF_LRA disequality (distinct) with arithmetic constraint.
///
/// Tests the NeedDisequalitySplit path in the LRA split-loop pipeline.
/// x != y with x + y = 10 is satisfiable (e.g., x=3, y=7).
#[test]
fn test_executor_qf_lra_distinct_sat_5600() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (assert (distinct x y))
        (assert (= (+ x y) 10.0))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["sat"],
        "#5600: distinct x y with x+y=10 is satisfiable"
    );
}
/// #5600: QF_LRA negated equality with tight bounds.
///
/// Tests the disequality split on a variable with tight rational bounds.
/// x != 5, x > 4, x < 6 is satisfiable (e.g., x=4.5 or x=5.5).
#[test]
fn test_executor_qf_lra_negated_equality_tight_bounds_5600() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (not (= x 5.0)))
        (assert (> x 4.0))
        (assert (< x 6.0))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["sat"],
        "#5600: x != 5 with 4 < x < 6 is satisfiable (e.g., x=4.5)"
    );
}
/// #5600: QF_LRA contradictory disequality — UNSAT.
///
/// x = 5 AND x != 5 is a direct contradiction.
#[test]
fn test_executor_qf_lra_contradictory_disequality_unsat_5600() {
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (= x 5.0))
        (assert (not (= x 5.0)))
        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");

    assert_eq!(
        outputs,
        vec!["unsat"],
        "#5600: x = 5 AND x != 5 is contradictory"
    );
}

// ---------------------------------------------------------------------------
// Real division-by-zero soundness (#div0-soundness).
//
// SMT-LIB Reals makes `/` TOTAL but leaves `(/ a 0)` UNCONSTRAINED: it denotes
// a single consistent but unspecified value (like int `div`/`mod`). AY used to
// constant-fold `(/ x x) -> 1` and `(/ 0 x) -> 0` even when `x` could be 0, and
// the real-arith path pinned `(/ x 0)`, so it WRONGLY refuted any constraint
// contradicting the pinned value (WRONG-UNSAT). The fix removes the unsound
// folds (guarding the numerator-zero fold on a known non-zero constant
// divisor); the NRA path then fails closed on a not-provably-nonzero divisor.
//
// Required outcome: sat (z3-matching) or unknown (fail-closed) — NEVER unsat.
// All verdicts checked against z3 4.16.0.
// ---------------------------------------------------------------------------

fn solve_one_lra(input: &str) -> String {
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execution succeeds");
    outputs.into_iter().next().expect("one (check-sat) output")
}

// SOUNDNESS REGRESSION: QF_LRA disequality + equality-alias-under-push must
// NOT return a false UNSAT. The disequality `(not (= a b))` is handled as a
// multi-var expression split; the model-value-equality (`assume_eqs`) guesser
// used to PREFER a proof-less guess that, through the asserted-equality
// closure, transitively closed the free disequality and drove the query to a
// false UNSAT. The fix (model_eq_guess_touches_disequality) suppresses such
// guesses so the loop falls through to the sound expression split. z3 = sat;
// AY must be sat or unknown, NEVER unsat.
#[test]
fn test_qf_lra_diseq_eq_alias_under_push_not_false_unsat() {
    // v4 != v2; v2 = v1; v1 = v3. Trivially SAT (v4 != v2; v2=v1=v3 free).
    let out = solve_one_lra(
        "(set-logic QF_LRA)\
         (declare-fun v4 () Real)(declare-fun v2 () Real)\
         (declare-fun v1 () Real)(declare-fun v3 () Real)\
         (push 1)\
         (assert (not (= v4 v2)))(assert (= v2 v1))(assert (= v1 v3))\
         (check-sat)",
    );
    assert_ne!(
        out, "unsat",
        "diseq + eq-alias chain does NOT pin v4-v2 to 0; false UNSAT is unsound"
    );
    assert!(out == "sat" || out == "unknown", "got {out}");
}

#[test]
fn test_qf_lra_diseq_eq_alias_longer_chain_not_false_unsat() {
    // v4 != v2; v2 = v1; v1 = v0. Free chain; SAT. (Mirrors fuzz seed 154.)
    let out = solve_one_lra(
        "(set-logic QF_LRA)\
         (declare-fun v0 () Real)(declare-fun v1 () Real)\
         (declare-fun v2 () Real)(declare-fun v4 () Real)\
         (push 1)\
         (assert (not (= v4 v2)))(assert (= v2 v1))(assert (= v1 v0))\
         (check-sat)",
    );
    assert_ne!(out, "unsat", "free eq-alias chain: false UNSAT is unsound");
    assert!(out == "sat" || out == "unknown", "got {out}");
}

// COMPLEMENT: genuinely-UNSAT disequality cases MUST still be refuted. The
// soundness gate only suppresses model-eq guesses that close a FREE
// disequality; when the disequality expression is actually FORCED to 0 by
// real equality/bound constraints, check_disequalities returns Unsat directly
// (never reaching the guess path), and that must be preserved.
#[test]
fn test_qf_lra_diseq_with_direct_equality_still_unsat() {
    // (not (= a b)) AND (= a b): forced contradiction.
    assert_eq!(
        solve_one_lra(
            "(set-logic QF_LRA)\
             (declare-fun a () Real)(declare-fun b () Real)\
             (push 1)(assert (not (= a b)))(assert (= a b))(check-sat)"
        ),
        "unsat"
    );
}

#[test]
fn test_qf_lra_diseq_with_bounds_pinning_still_unsat() {
    // (not (= a b)) with a and b both pinned to 0 by bounds: forced to 0.
    assert_eq!(
        solve_one_lra(
            "(set-logic QF_LRA)\
             (declare-fun a () Real)(declare-fun b () Real)(push 1)\
             (assert (not (= a b)))\
             (assert (<= a 0))(assert (>= a 0))(assert (<= b 0))(assert (>= b 0))\
             (check-sat)"
        ),
        "unsat"
    );
}

#[test]
fn test_real_self_div_by_zero_not_wrong_unsat() {
    // x = 0 ∧ (/ x x) != 1: z3 = sat ((/ 0 0) is unspecified, may differ from
    // 1). Must NEVER be unsat (was the bug — `(/ x x) -> 1` self-fold).
    let out = solve_one_lra(
        "(set-logic QF_NRA)(declare-const x Real)(assert (= x 0.0))\
         (assert (distinct (/ x x) 1.0))(check-sat)",
    );
    assert_ne!(
        out, "unsat",
        "(/ 0 0) unspecified ≠ 1 is satisfiable (#div0)"
    );
    assert!(out == "sat" || out == "unknown", "got {out}");
}

#[test]
fn test_real_div_one_by_zero_positive_not_wrong_unsat() {
    // x = 0 ∧ 0 < (/ 1 x): z3 = sat ((/ 1 0) may be positive). Must NEVER be
    // unsat (was the bug — pinned/folded `(/ 1 0)`).
    let out = solve_one_lra(
        "(set-logic QF_NRA)(declare-const x Real)(assert (= x 0.0))\
         (assert (< 0.0 (/ 1.0 x)))(check-sat)",
    );
    assert_ne!(out, "unsat", "(/ 1 0) may be positive (#div0)");
    assert!(out == "sat" || out == "unknown", "got {out}");
}

#[test]
fn test_real_zero_numerator_symbolic_divisor_not_wrong_unsat() {
    // x = 0 ∧ (/ 0 x) != 0: z3 = sat ((/ 0 0) is unspecified). Must NEVER be
    // unsat (was the bug — `(/ 0 x) -> 0` fold ignored x possibly 0).
    let out = solve_one_lra(
        "(set-logic QF_NRA)(declare-const x Real)(assert (= x 0.0))\
         (assert (distinct (/ 0.0 x) 0.0))(check-sat)",
    );
    assert_ne!(
        out, "unsat",
        "(/ 0 0) unspecified ≠ 0 is satisfiable (#div0)"
    );
    assert!(out == "sat" || out == "unknown", "got {out}");
}

#[test]
fn test_real_div_nonzero_const_divisor_still_sat() {
    // Non-regression: division by a known non-zero constant must still solve.
    assert_eq!(
        solve_one_lra("(set-logic QF_NRA)(assert (= (/ 6.0 2.0) 3.0))(check-sat)"),
        "sat"
    );
    assert_eq!(
        solve_one_lra(
            "(set-logic QF_NRA)(declare-const x Real)(assert (= x 4.0))\
             (assert (= (/ x 2.0) 2.0))(check-sat)"
        ),
        "sat"
    );
}

#[test]
fn test_real_div_nonzero_const_divisor_wrong_value_unsat() {
    // Non-regression: a wrong literal division result must still be UNSAT.
    assert_eq!(
        solve_one_lra("(set-logic QF_NRA)(assert (= (/ 6.0 2.0) 4.0))(check-sat)"),
        "unsat"
    );
}

#[test]
fn test_real_div_zero_divisor_two_occurrences_not_wrong_sat() {
    // x = 0 ∧ (/ 0 x) < (/ x 0): z3 = unsat. Both sides denote the SAME
    // unspecified `(/ 0 0)` value, so `a < a` is false. The NRA path would
    // otherwise over-approximate the two `/` terms as independent free
    // variables (the purification constraint `denom*div=num` is vacuous at
    // denom=0, and constant-zero divisors are never purified) and emit a
    // WRONG-SAT. We fail closed on the zero divisor → unknown (#div0-soundness).
    // Must NEVER be sat.
    let out = solve_one_lra(
        "(set-logic QF_NRA)(declare-const x Real)(assert (= x 0.0))\
         (assert (< (/ 0.0 x) (/ x 0.0)))(check-sat)",
    );
    assert_ne!(out, "sat", "(/ 0 0) < (/ 0 0) is false (#div0)");
    assert!(out == "unsat" || out == "unknown", "got {out}");
}

#[test]
fn test_real_div_single_zero_divisor_not_wrong_unsat() {
    // x = 0 ∧ (/ 1 x) != 5: z3 = sat. A SINGLE zero-denominator division is
    // trivially a consistent function extension, so the NRA theory now
    // certifies it Sat (`zero_divisor_model_is_unsound`, the
    // "unconstrained-but-consistent value machinery" promised in 28f8ca51;
    // unblocks Z3 #9319 parity — see the theory-level pins in
    // ay-nra `theory_tests`). At the executor surface the independent
    // model-validation gate still fails closed — `(/ 1.0 0.0)` evaluates to
    // Unknown — so `unknown` is tolerated here; `unsat` never is.
    let out = solve_one_lra(
        "(set-logic QF_NRA)(declare-const x Real)(assert (= x 0.0))\
         (assert (distinct (/ 1.0 x) 5.0))(check-sat)",
    );
    assert_ne!(
        out, "unsat",
        "(/ 1 0) is unconstrained, != 5 is satisfiable"
    );
    assert!(out == "sat" || out == "unknown", "got {out}");
}

#[test]
fn test_real_div_zero_divisor_consistency_unsat() {
    // (/ 1 0) = 0 ∧ (/ 1 0) = 1: z3 = unsat. The literal zero divisor folds to
    // the SAME interned `(/ 1.0 0.0)` term, so the value is consistent across
    // occurrences and the two equalities contradict. Must stay UNSAT.
    assert_eq!(
        solve_one_lra(
            "(set-logic QF_NRA)(declare-const x Real)(assert (= x 0.0))\
             (assert (= (/ 1.0 x) 0.0))(assert (= (/ 1.0 x) 1.0))(check-sat)"
        ),
        "unsat"
    );
}

// QF_LIA (Linear Integer Arithmetic) Tests
// =========================================
