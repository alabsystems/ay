// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for issue #7150: nested existential Skolem functions.
//!
//! These cases used to degrade to `unknown` because nested existentials were
//! only Skolemized to constants. The fix carries visible outer universal
//! binders into Skolemization so the witness can depend on them.

use ntest::timeout;

/// `forall y. exists x. x > y` is satisfiable with witness `x = y + 1`.
///
/// The nested existential must be Skolemized to a function of `y`, not a
/// constant. Current HEAD still answers `unknown`, so the soundness contract is
/// "sat or unknown, but never unsat".
#[test]
#[timeout(30_000)]
fn test_nested_exists_single_outer_universal_not_unsat_7150() {
    let outputs = crate::common::solve_vec(
        r#"
        (set-logic LIA)
        (assert (forall ((y Int)) (exists ((x Int)) (> x y))))
        (check-sat)
    "#,
    );
    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "forall y. exists x. x > y must not be unsat; got {outputs:?}",
    );
}

/// `forall y z. exists x. x = y + z` requires the witness to depend on both
/// visible outer universals.
///
/// If Skolemization drops either dependency, the rewritten formula becomes too
/// strong and can no longer represent the addition witness exactly. Current
/// HEAD still answers `unknown`, so this guards the soundness boundary.
#[test]
#[timeout(30_000)]
fn test_nested_exists_two_outer_universals_not_unsat_7150() {
    let outputs = crate::common::solve_vec(
        r#"
        (set-logic LIA)
        (assert (forall ((y Int) (z Int)) (exists ((x Int)) (= x (+ y z)))))
        (check-sat)
    "#,
    );
    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "forall y z. exists x. x = y + z must not be unsat; got {outputs:?}",
    );
}
