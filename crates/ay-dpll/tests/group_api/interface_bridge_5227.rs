// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #5227: InterfaceBridge in AufLraSolver and AufLiraSolver.
//!
//! Without InterfaceBridge, UF functions with Real/Int arithmetic arguments
//! (e.g., `f((+ x 1.0))`) are not evaluated by the bridge after LRA/LIA solving,
//! so EUF misses implied equalities and the solver returns Unknown instead of UNSAT.

use ntest::timeout;

/// QF_AUFLRA: UF function with arithmetic argument requires InterfaceBridge
/// to propagate `f(x+1.0) = f(3.0)` from LRA model evaluation to EUF.
#[test]
#[timeout(10_000)]
fn auflra_interface_bridge_uf_arith_arg_unsat() {
    let smt = r#"
(set-logic QF_AUFLRA)
(declare-fun x () Real)
(declare-fun f (Real) Real)
(assert (= x 2.0))
(assert (= (f 3.0) 10.0))
(assert (not (= (f (+ x 1.0)) 10.0)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "QF_AUFLRA with UF arithmetic arg should be UNSAT: f(x+1.0) = f(3.0) when x=2.0"
    );
}

/// QF_AUFLIRA: same pattern but with Int arithmetic argument.
/// `g(y+1)` where `y=2` should equal `g(3)`.
#[test]
#[timeout(10_000)]
fn auflira_interface_bridge_uf_int_arith_arg_unsat() {
    let smt = r#"
(set-logic QF_AUFLIRA)
(declare-fun y () Int)
(declare-fun g (Int) Int)
(assert (= y 2))
(assert (= (g 3) 10))
(assert (not (= (g (+ y 1)) 10)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "QF_AUFLIRA with UF Int arithmetic arg should be UNSAT: g(y+1) = g(3) when y=2"
    );
}

/// QF_AUFLIRA: Real-sorted UF function with arithmetic argument in mixed theory.
/// The Int variable `y` participates in a separate constraint to exercise both
/// LIA and LRA sub-solvers, but the UNSAT core is from the Real bridge.
#[test]
#[timeout(10_000)]
fn auflira_interface_bridge_uf_real_arith_arg_unsat() {
    let smt = r#"
(set-logic QF_AUFLIRA)
(declare-fun x () Real)
(declare-fun y () Int)
(declare-fun f (Real) Real)
(declare-fun g (Int) Int)
(assert (= x 2.0))
(assert (= y 5))
(assert (= (g y) 42))
(assert (= (f 3.0) 10.0))
(assert (not (= (f (+ x 1.0)) 10.0)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&result),
        Some("unsat"),
        "QF_AUFLIRA with UF Real arithmetic arg should be UNSAT"
    );
}

/// QF_AUFLIRA: SAT case — verify the Int bridge doesn't cause false UNSAT.
/// g(y+1) and g(3) are unconstrained when y != 2.
#[test]
#[timeout(10_000)]
fn auflira_interface_bridge_int_sat_case() {
    let smt = r#"
(set-logic QF_AUFLIRA)
(declare-fun y () Int)
(declare-fun g (Int) Int)
(assert (= y 1))
(assert (= (g 3) 10))
(assert (not (= (g (+ y 1)) 10)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    // y=1 means g(2) != 10 is SAT because g(2) is unconstrained.
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "QF_AUFLIRA: g(y+1) != g(3) is SAT when y=1 (different argument)"
    );
}

/// QF_AUFLRA: SAT case — verify the Real bridge doesn't cause false UNSAT.
/// f(x+1.0) and f(3.0) are unconstrained when x != 2.0.
#[test]
#[timeout(10_000)]
fn auflra_interface_bridge_sat_case() {
    let smt = r#"
(set-logic QF_AUFLRA)
(declare-fun x () Real)
(declare-fun f (Real) Real)
(assert (= x 1.0))
(assert (= (f 3.0) 10.0))
(assert (not (= (f (+ x 1.0)) 10.0)))
(check-sat)
"#;
    let result = crate::common::solve(smt);
    // x=1.0 means f(2.0) != 10.0 is SAT because f(2.0) is unconstrained.
    assert_eq!(
        crate::common::sat_result(&result),
        Some("sat"),
        "QF_AUFLRA: f(x+1.0) != f(3.0) is SAT when x=1.0 (different argument)"
    );
}
