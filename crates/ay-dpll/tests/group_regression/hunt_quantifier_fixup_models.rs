// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Total models after a confirmed quantified `sat` (2026-09-29, the
//! quantifier repair fix-up, session 4), beside
//! [`crate::hunt_quantifier_fixup_verdicts`]: the fix-up's partial-model
//! refusal (B3) must not cost a verdict whose model can be made total.

use crate::hunt_quantifier_wrong_verdicts::{assert_never, solve, verdicts, Posture, POSTURES};

/// Ground assertions that hold whatever a constant is: `(not (isnil (cons x
/// xs)))` under `∀l. isnil l = (l = nil)`. The quantified gate confirmed the
/// model with `x` (an element of an uninterpreted sort) and `xs` unassigned;
/// main printed `sat` and then `(error "model value for x is not available
/// (internal error: sat accepted without a total model)")`, and the fix-up's
/// refusal turned that into `unknown` (the corpus file below and the minimal
/// shape, both postures). z3 5.1.0 answers `sat`.
const CONFIRMED_MODEL_GAPS: [(&str, &str); 2] = [
    (
        "UFDT isnil over cons x xs",
        "(set-logic UFDT) (declare-sort A 0)
         (declare-datatypes ((L 0)) (((cons (hd A) (tl L)) (nil))))
         (declare-fun isnil (L) Bool) (declare-fun x () A) (declare-fun xs () L)
         (assert (forall ((l L)) (= (isnil l) (= l nil))))
         (assert (not (isnil (cons x xs))))
         (check-sat) (get-model) (get-value (x xs))",
    ),
    (
        "UFDT/20170428-Barrett/rec-fun-ijcar2016/wo/isa_nun_bench_v4_noenc/nunchaku2067278",
        "(set-logic UFDT) (declare-sort a__ 0)
         (declare-fun __nun_card_witness_0_ () a__)
         (declare-datatypes ((list__ 0))
           (((Cons__ (_select_Cons___0 a__) (_select_Cons___1 list__)) (Nil__))))
         (declare-fun null__ (list__) Bool)
         (assert (forall ((xs1_/15 list__)) (= (null__ xs1_/15) (= xs1_/15 Nil__))))
         (declare-fun x__ () a__) (declare-fun xs__ () list__)
         (assert (not (null__ (Cons__ x__ xs__))))
         (check-sat) (get-model) (get-value (x__ xs__))",
    ),
];

/// A constant the confirmed model leaves open gets its canonical default and
/// the model is gated again: `sat` with a total model, never `sat` followed by
/// an error and never the refusal's `unknown`. `--self-check` certifies the
/// model independently and fails closed here on main too (`unknown`), so that
/// posture only has to print a total model when it does answer `sat`.
#[test]
fn a_constant_the_confirmed_model_leaves_open_gets_a_value() {
    for (name, smt) in CONFIRMED_MODEL_GAPS {
        assert_never(name, smt, "unsat");
        for posture in POSTURES {
            let got = solve(smt, posture, None);
            if matches!(posture, Posture::SelfCheck) && verdicts(&got) == ["unknown"] {
                continue;
            }
            assert_eq!(
                verdicts(&got),
                ["sat"],
                "{name} ({posture:?}): z3 5.1.0 and main answer sat; got {got:?}"
            );
            let text = got.join("\n");
            assert!(
                !text.contains("(error"),
                "{name} ({posture:?}): a `sat` must print a total model; got {got:?}"
            );
            assert!(
                text.contains("((x") && text.contains("(xs"),
                "{name} ({posture:?}): get-value answers for both constants; got {got:?}"
            );
        }
    }
}
