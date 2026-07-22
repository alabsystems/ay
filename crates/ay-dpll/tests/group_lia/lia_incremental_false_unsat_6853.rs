// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #6853: QF_LIA incremental false-unsat.
//!
//! AY returns "unsat" when expected answer is "sat" on BMC/k-induction
//! benchmarks after many push/pop cycles. All wrong answers are false-unsat.

use ntest::timeout;
use std::fs;

fn results(output: &str) -> Vec<&str> {
    output
        .lines()
        .map(str::trim)
        .filter(|l| *l == "sat" || *l == "unsat" || *l == "unknown")
        .collect()
}

/// BMC-like pattern: many push/pop cycles with variable substitution.
///
/// Each cycle asserts an equality (triggering VariableSubstitution) plus
/// constraints that are satisfiable. After pop, the next cycle has different
/// equalities. This exercises the path where preprocessing produces different
/// derived assertions across check-sat calls.
#[test]
#[timeout(30_000)]
fn test_lia_incremental_bmc_many_cycles_variable_subst_6853() {
    let mut smt = String::from(
        "(set-logic QF_LIA)\n\
         (declare-const x Int)\n\
         (declare-const y Int)\n\
         (declare-const z Int)\n\
         (assert (>= x 0))\n\
         (assert (>= y 0))\n\
         (assert (>= z 0))\n\
         (check-sat)\n",
    );
    let mut expected = vec!["sat"];

    // Run 50 push/pop cycles with different equalities
    for i in 0..50 {
        smt.push_str("(push 1)\n");
        // Each cycle adds an equality that triggers variable substitution,
        // plus a satisfiable constraint.
        match i % 3 {
            0 => {
                smt.push_str(&format!(
                    "(assert (= x (+ y {})))\n\
                     (assert (<= x {}))\n",
                    i + 1,
                    1000 + i
                ));
            }
            1 => {
                smt.push_str(&format!(
                    "(assert (= y (+ z {})))\n\
                     (assert (<= y {}))\n",
                    i + 1,
                    1000 + i
                ));
            }
            _ => {
                smt.push_str(&format!(
                    "(assert (= z (+ x {})))\n\
                     (assert (<= z {}))\n",
                    i + 1,
                    1000 + i
                ));
            }
        }
        smt.push_str("(check-sat)\n");
        expected.push("sat");
        smt.push_str("(pop 1)\n");
    }

    // Final check: base constraints should still be SAT
    smt.push_str("(check-sat)\n");
    expected.push("sat");

    let output = crate::common::solve(&smt);
    let actual = results(&output);

    // Check each result individually for better diagnostics
    for (i, (&actual_result, &expected_result)) in actual.iter().zip(expected.iter()).enumerate() {
        assert_eq!(
            actual_result, expected_result,
            "check-sat #{i}: expected {expected_result}, got {actual_result}"
        );
    }
    assert_eq!(actual.len(), expected.len(), "wrong number of results");
}

/// BMC-like pattern with mod/div elimination across push/pop cycles.
///
/// Tests that fresh auxiliary variables created by mod/div elimination
/// don't accumulate contradictions in the persistent SAT solver.
#[test]
#[timeout(30_000)]
fn test_lia_incremental_bmc_mod_div_cycles_6853() {
    let mut smt = String::from(
        "(set-logic QF_LIA)\n\
         (declare-const x Int)\n\
         (declare-const y Int)\n\
         (assert (>= x 0))\n\
         (assert (= (mod x 5) 0))\n\
         (check-sat)\n",
    );
    let mut expected = vec!["sat"];

    for i in 0..30 {
        smt.push_str("(push 1)\n");
        smt.push_str(&format!(
            "(assert (>= y {}))\n\
             (assert (<= y {}))\n\
             (check-sat)\n",
            i * 5,
            i * 5 + 10
        ));
        expected.push("sat");
        smt.push_str("(pop 1)\n");
    }

    smt.push_str("(check-sat)\n");
    expected.push("sat");

    let output = crate::common::solve(&smt);
    let actual = results(&output);

    for (i, (&actual_result, &expected_result)) in actual.iter().zip(expected.iter()).enumerate() {
        assert_eq!(
            actual_result, expected_result,
            "check-sat #{i}: expected {expected_result}, got {actual_result}"
        );
    }
    assert_eq!(actual.len(), expected.len());
}

/// Pattern from real BMC benchmarks: scoped equalities that change
/// variable substitution, plus scoped comparisons that conflict
/// with stale global derived assertions.
///
/// This is the most targeted reproducer: a global assertion is
/// preprocessed differently in each scope due to variable substitution,
/// producing derived assertions at depth 0 that accumulate globally.
#[test]
#[timeout(30_000)]
fn test_lia_incremental_subst_changes_across_scopes_6853() {
    let smt = r#"
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)

        ; Global assertions
        (assert (>= x 0))
        (assert (<= x 100))
        (check-sat)

        ; Scope 1: equality x=y triggers substitution
        (push 1)
        (assert (= x y))
        (assert (>= y 50))
        (check-sat)
        (pop 1)

        ; Scope 2: different constraint on y (no equality)
        ; If stale "y >= 50" or "(>= y 0)" from scope 1 persists
        ; globally, this could be affected.
        (push 1)
        (assert (<= y (- 0 10)))
        (check-sat)
        (pop 1)

        ; Scope 3: equality y=x (reversed) triggers different substitution
        (push 1)
        (assert (= y x))
        (assert (<= y 5))
        (check-sat)
        (pop 1)

        ; Final: just global constraints
        (check-sat)
    "#;
    let output = crate::common::solve(smt);
    // Scope 2: y <= -10 with just (>= x 0) (<=x 100) is SAT (y=-10, x=50)
    assert_eq!(results(&output), vec!["sat", "sat", "sat", "sat", "sat"]);
}

/// Stress test: many push/pop cycles where each scope introduces
/// different variable substitutions that change how global assertions
/// are preprocessed. This targets the accumulated stale global
/// activations hypothesis.
#[test]
#[timeout(60_000)]
fn test_lia_incremental_stress_100_cycles_6853() {
    let mut smt = String::from(
        "(set-logic QF_LIA)\n\
         (declare-const a Int)\n\
         (declare-const b Int)\n\
         (declare-const c Int)\n\
         (declare-const d Int)\n\
         (assert (>= a 0))\n\
         (assert (<= a 1000))\n\
         (assert (>= b 0))\n\
         (assert (<= b 1000))\n\
         (check-sat)\n",
    );
    let mut expected = vec!["sat"];

    for i in 0..100 {
        smt.push_str("(push 1)\n");
        // Alternate between different equalities to change substitution
        match i % 4 {
            0 => smt.push_str(&format!("(assert (= a (+ b {i})))\n")),
            1 => smt.push_str(&format!("(assert (= b (+ c {i})))\n")),
            2 => smt.push_str(&format!("(assert (= c (+ d {i})))\n")),
            _ => smt.push_str(&format!("(assert (= d (+ a {i})))\n")),
        }
        smt.push_str(&format!(
            "(assert (<= c {}))\n\
             (assert (>= d {}))\n\
             (check-sat)\n",
            500 + i,
            i
        ));
        expected.push("sat");
        smt.push_str("(pop 1)\n");
    }

    smt.push_str("(check-sat)\n");
    expected.push("sat");

    let output = crate::common::solve(&smt);
    let actual = results(&output);

    let mut failures = Vec::new();
    for (i, (&actual_result, &expected_result)) in actual.iter().zip(expected.iter()).enumerate() {
        if actual_result != expected_result {
            failures.push(format!(
                "check-sat #{i}: expected {expected_result}, got {actual_result}"
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "{} wrong answers out of {}:\n{}",
        failures.len(),
        expected.len(),
        failures.join("\n")
    );
    assert_eq!(actual.len(), expected.len(), "wrong number of results");
}

/// Regression for #6882: `(assert false)` inside a push scope should not
/// poison the persistent SAT solver. After `(push 1)(assert false)(check-sat)
/// (pop 1)`, subsequent queries in fresh scopes must be unaffected.
///
/// The original trigger required 211 preceding check-sats because state
/// accumulated gradually. This simplified test exercises the key pattern:
/// LIA queries before and after a scoped `(assert false)`.
#[test]
#[timeout(30_000)]
fn test_lia_incremental_assert_false_no_poison_6882() {
    // Several LIA queries, then (assert false) scope, then more LIA queries.
    let smt = r#"
        (set-logic QF_LIA)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)

        ; CS#1-3: real LIA queries (all SAT)
        (push 1)
        (assert (and (>= x 0) (< x 100) (= y (+ x 1))))
        (check-sat)
        (pop 1)

        (push 1)
        (assert (and (= x (* 2 z)) (>= z 5) (<= z 10)))
        (check-sat)
        (pop 1)

        (push 1)
        (assert (and (> y x) (> x z) (>= z 0)))
        (check-sat)
        (pop 1)

        ; CS#4: assert false — UNSAT, must not poison
        (push 1)
        (assert false)
        (check-sat)
        (pop 1)

        ; CS#5-7: LIA queries after poison (all SAT)
        (push 1)
        (assert (and (>= x 0) (<= x 50) (= y (+ x 10))))
        (check-sat)
        (pop 1)

        (push 1)
        (assert (and (= z 7) (> x z)))
        (check-sat)
        (pop 1)

        (push 1)
        (assert (not (or (< x 0) (and (> y 100) (>= y 0)))))
        (check-sat)
        (pop 1)
    "#;
    let output = crate::common::solve(smt);
    let actual = results(&output);

    assert_eq!(
        actual,
        vec!["sat", "sat", "sat", "unsat", "sat", "sat", "sat"],
        "assert false must not poison subsequent queries (#6882)"
    );
}

/// Regression test for the actual gulwani_cegar benchmark that triggered #6853.
///
/// CS#212 returned false-UNSAT because accumulated Tseitin definition clauses
/// from 211 prior check-sats (each with different LIA preprocessed assertions)
/// over-constrained the variable space in the persistent LIA SAT solver.
/// The fix resets LIA-specific SAT state before each check-sat.
///
/// Z3 returns 205 sat + 7 unsat on this benchmark.
#[test]
#[timeout(60_000)]
fn test_gulwani_prefix_212_matches_z3_6853() {
    let path = crate::common::workspace_path(
        "benchmarks/smt-lib-incremental/QF_LIA/gulwani_prefix_212.smt2",
    );
    let smt = match fs::read_to_string(&path) {
        Ok(smt) => smt,
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => return,
        Err(err) => panic!("failed to read {}: {err}", path.display()),
    };
    let output = crate::common::solve(&smt);
    let actual: Vec<&str> = results(&output);

    // Z3 reference: 205 sat, 7 unsat, total 212.
    let sat_count = actual.iter().filter(|&&r| r == "sat").count();
    let unsat_count = actual.iter().filter(|&&r| r == "unsat").count();

    assert_eq!(actual.len(), 212, "expected 212 check-sat results");
    assert_eq!(sat_count, 205, "expected 205 sat (got {sat_count})");
    assert_eq!(unsat_count, 7, "expected 7 unsat (got {unsat_count})");

    // CS#212 (the last result) was the false-UNSAT that triggered #6853.
    assert_eq!(
        actual[211], "sat",
        "CS#212 must be sat (was false-UNSAT before fix)"
    );
}
