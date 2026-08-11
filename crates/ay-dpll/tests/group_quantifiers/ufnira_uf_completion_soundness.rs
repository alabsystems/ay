// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness boundary for shape-only UF completion in nonlinear Real logic.
//!
//! Substituting the universal definition `f(t) = -t` into the negated
//! consequence below makes both sides `a^2 + b`. The assertion set is therefore
//! UNSAT. A model-free lower `unknown` must never be promoted to `sat` merely
//! because every term mentions a syntactically completable UF head.

const DEFINITION_WITH_FALSE_COUNTEREXAMPLE: &str = r#"
    (set-logic UFNIRA)
    (declare-fun f (Real) Real)
    (declare-const a Real)
    (declare-const b Real)
    (assert (forall ((x Real)) (= (f x) (- x))))
    (assert (not (= (f (+ (* a (f a)) (f b)))
                    (+ b (* (f a) (f a))))))
    (check-sat)
"#;

const SAT_POINTWISE_DEFINITION: &str = r#"
    (set-logic UFNIRA)
    (declare-fun f (Real) Real)
    (assert (forall ((x Real)) (= (f x) (- x))))
    (check-sat)
"#;

#[test]
fn nonlinear_real_shape_completion_never_promotes_unknown_to_sat() {
    let results = crate::common::solve_vec(DEFINITION_WITH_FALSE_COUNTEREXAMPLE);
    assert!(
        !results.iter().any(|result| result == "sat"),
        "substitution proves the formula UNSAT, so a model-free completion may \
         return only `unsat` or `unknown`; got {results:?}"
    );
}

#[test]
fn nonlinear_real_shape_completion_selfcheck_stays_fail_closed() {
    let results = crate::common::solve_selfcheck_vec(DEFINITION_WITH_FALSE_COUNTEREXAMPLE);
    assert!(
        !results.iter().any(|result| result == "sat"),
        "self-check must not authorize the model-free nonlinear completion; got {results:?}"
    );
}

#[test]
fn satisfiable_pointwise_definition_is_not_rejected() {
    let results = crate::common::solve_vec(SAT_POINTWISE_DEFINITION);
    assert_eq!(
        results,
        vec!["sat"],
        "the soundness gate must preserve a genuine pointwise UF definition"
    );
}
