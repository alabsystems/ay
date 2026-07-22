// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #7449: UfNraSolver must route speculative equalities
//! through NeedModelEquality (SAT-level decisions) instead of asserting them
//! directly into EUF with empty reasons. The old code could cause false-UNSAT
//! when coincidentally-equal NRA model values for UF terms conflicted with
//! an EUF disequality.

use ntest::timeout;

/// Stronger variant: explicit disequality between UF applications where the
/// arithmetic arguments are forced to the same region. If the NRA model
/// evaluates both arguments to the same value, speculative equality routing
/// must still allow the SAT solver to explore alternatives.
#[test]
#[timeout(10_000)]
fn ufnra_speculative_eq_with_constrained_args_7449() {
    let smt = r#"
(set-logic QF_UFNRA)
(declare-fun g (Real) Real)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (>= a 1.0))
(assert (<= a 2.0))
(assert (>= b 1.0))
(assert (<= b 2.0))
(assert (not (= a b)))
(assert (not (= (g a) (g b))))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).expect("expected sat/unsat/unknown");
    // SAT: a and b in [1,2] with a != b, g is uninterpreted so g(a) != g(b) is fine.
    assert_ne!(
        result, "unsat",
        "#7449: constrained UFNRA speculative equalities must not cause false-UNSAT"
    );
}

/// UNSAT case: known unsat formula must still return unsat.
/// f(x) = f(y) and not (f(x) = f(y)) is always unsat.
#[test]
#[timeout(10_000)]
fn ufnra_genuine_unsat_preserved_7449() {
    let smt = r#"
(set-logic QF_UFNRA)
(declare-fun f (Real) Real)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= x y))
(assert (not (= (f x) (f y))))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    let result = crate::common::sat_result(&output).expect("expected sat/unsat/unknown");
    // x = y implies f(x) = f(y) by congruence, so not(f(x) = f(y)) is UNSAT.
    assert_ne!(
        result, "sat",
        "#7449 soundness: genuine UNSAT must not become SAT"
    );
}
