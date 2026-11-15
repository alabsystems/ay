// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! B3 for arrays (2026-09-28, quantifier fix-up session 3): a `sat` prints a
//! model value for a declared array no assertion mentions. Split out of
//! [`crate::hunt_quantifier_fixup_verdicts`] to keep that file under the
//! test-file size limit.

use crate::hunt_quantifier_wrong_verdicts::{assert_never, solve, verdicts, POSTURES};

/// A declared array no assertion mentions, beside a universal the
/// constant-interpretation certificate proves: main printed `sat` and then
/// `(error "model value for array A is not available")` in both postures
/// (2026-09-28, fix-up session 3). The second fixture is fresh-seed family
/// file w1_62501_00318 (z3 5.1.0 undecided; satisfiable at `w = 1`, `a = 0`,
/// `f(v) = v + 1`), where the exact elimination turns main's wrong `--z3-mode`
/// `unsat` into `sat` and the model hit the same error.
const UNUSED_ARRAY_MODELS: [(&str, &str); 2] = [
    (
        "an unused array beside a proved universal",
        "(set-logic ALL) (declare-fun f (Int) Int) (declare-fun A () (Array Int Int))
         (assert (forall ((v Int)) (not (= (f v) v))))
         (check-sat) (get-model) (get-value (A))",
    ),
    (
        "w1_62501_00318",
        "(set-logic ALL) (declare-fun w () Int) (declare-fun a () Int)
         (declare-fun f (Int) Int) (declare-fun p () Bool) (declare-fun q () Bool)
         (declare-fun A () (Array Int Int))
         (assert (forall ((v Int)) (and (>= (+ (* v w) (* (- 1) v) a) (- 2)) (not (= (f v) v)))))
         (check-sat) (get-model) (get-value (A))",
    ),
];

/// A `sat` prints a value for an array the formula never mentions, and
/// w1_62501_00318 stays `sat` in `--z3-mode` (never `unsat`).
#[test]
fn an_unused_array_keeps_a_model_value() {
    for (name, smt) in UNUSED_ARRAY_MODELS {
        assert_never(name, smt, "unsat");
        let mut decided = 0;
        for posture in POSTURES {
            let got = solve(smt, posture, None);
            if verdicts(&got) != ["sat"] {
                continue;
            }
            decided += 1;
            let text = got.join("\n");
            assert!(
                !text.contains("(error"),
                "{name}: a `sat` must print a total model ({posture:?}); got {got:?}"
            );
            assert!(
                text.contains("define-fun A ") && text.contains("((A "),
                "{name}: the unused A needs a model value and a get-value answer \
                 ({posture:?}); got {got:?}"
            );
        }
        assert!(decided > 0, "{name}: sat in at least one posture");
    }
}
