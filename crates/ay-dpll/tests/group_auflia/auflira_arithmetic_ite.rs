// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Verdict-level spec for arithmetic `ite` on the AUFLIRA route
//! (#auflira-ite-lift). The route's arithmetic solvers take no term-level
//! `ite`, and before the lift a refutation that went through one came back
//! `unknown`. Verus reaches this route whenever a Real term is live, and vstd's
//! set lemmas put an `ite` inside arithmetic (`len(insert(s, a)) = len(s) +
//! (ite (contains s a) 0 1)`), which is how `dafny_axioms::set_axiom_02` was
//! lost. Ground truth for each fixture was checked with z3 4.12.5.

/// **GROUND TRUTH: UNSAT** (z3 4.12.5): `c` is false, so `f(0) = 3 + 1 = 4`.
const ITE_IN_ARITHMETIC_UNSAT: &str = r#"
(declare-fun f (Int) Int)
(declare-const r Real)
(declare-const c Bool)
(declare-const x Int)
(declare-const a (Array Int Int))
(assert (= (f 0) (+ x (ite c 0 1))))
(assert (not c))
(assert (= x 3))
(assert (not (= (f 0) 4)))
(assert (= (select a 0) 1))
(assert (> r 0.0))
(check-sat)
"#;

/// The same with `c` true: `f(0) = 3`, so `f(0) != 4` holds.
/// **GROUND TRUTH: SAT** (z3 4.12.5).
const ITE_IN_ARITHMETIC_SAT: &str = r#"
(declare-fun f (Int) Int)
(declare-const r Real)
(declare-const c Bool)
(declare-const x Int)
(declare-const a (Array Int Int))
(assert (= (f 0) (+ x (ite c 0 1))))
(assert c)
(assert (= x 3))
(assert (not (= (f 0) 4)))
(assert (= (select a 0) 1))
(assert (> r 0.0))
(check-sat)
"#;

#[test]
fn an_ite_inside_arithmetic_is_refuted_on_the_auflira_route() {
    let results = crate::common::solve_vec(ITE_IN_ARITHMETIC_UNSAT);
    assert!(
        results.iter().any(|r| r == "unsat"),
        "the ite's condition is fixed, so the arithmetic refutes the goal; \
         got {results:?}"
    );
}

#[test]
fn an_ite_inside_arithmetic_keeps_a_satisfiable_query_satisfiable() {
    let results = crate::common::solve_vec(ITE_IN_ARITHMETIC_SAT);
    assert!(
        !results.iter().any(|r| r == "unsat"),
        "WRONG ANSWER: this query is SATISFIABLE; got {results:?}"
    );
    assert!(
        results.iter().any(|r| r == "sat"),
        "the lifted formula has the same model; got {results:?}"
    );
}
