// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Regression test for #8373: ITE deferral soundness bug.
///
/// The gasburner-prop3-2 benchmark (QF_LRA with ITE terms and Bool variables)
/// was non-deterministically returning false SAT (~50% of runs) because
/// check_impl's Phase 2 ITE deferral optimization incorrectly assumed that
/// if the theory returned Sat without inactive-branch atoms, those atoms
/// were irrelevant. In fact, the deferred atoms (e.g., `(= x_3 0.0)`)
/// constrained the model and their absence allowed a false SAT.
///
/// Run 20 times because the bug is non-deterministic (hashbrown HashMap
/// ordering affects SAT search order).
#[test]
fn regression_8373_ite_deferral_false_sat_gasburner() {
    let input = r#"
(set-logic QF_LRA)
(declare-fun x_0 () Bool)
(declare-fun x_1 () Real)
(declare-fun x_2 () Real)
(declare-fun x_3 () Real)
(declare-fun x_4 () Real)
(declare-fun x_5 () Bool)
(declare-fun x_6 () Real)
(declare-fun x_7 () Real)
(declare-fun x_8 () Real)
(declare-fun x_9 () Bool)
(declare-fun x_10 () Real)
(declare-fun x_11 () Real)
(declare-fun x_12 () Real)
(declare-fun x_13 () Real)
(declare-fun x_14 () Real)
(declare-fun x_15 () Real)
(declare-fun x_16 () Bool)
(assert (let ((?v_6 (not x_9)) (?v_1 (= x_10 0)) (?v_5 (+ x_1 x_6)) (?v_3 (= x_11 x_3)) (?v_2 (= x_12 x_4)) (?v_0 (= x_7 0)) (?v_8 (not x_0)) (?v_10 (= x_1 0)) (?v_13 (+ 0 x_2)) (?v_12 (= x_3 0)) (?v_11 (= x_4 0)) (?v_9 (not x_5)) (?v_4 (= x_7 1)) (?v_7 (not (< x_6 0)))) (and (and (and (and (and (and (and (and (and (and (and (<= x_14 1) (>= x_14 0)) (<= x_7 1)) (>= x_7 0)) ?v_8) (not (< x_13 0))) (= x_14 (ite ?v_4 0 1))) (or (or (and (and (and (and (and (and (= x_15 0) ?v_0) ?v_6) x_16) ?v_1) ?v_2) ?v_3) (and (and (and (and (and (and (and (= x_15 1) ?v_0) x_9) (not (< x_1 30))) (not x_16)) ?v_1) ?v_2) ?v_3)) (and (and (and (and (and (and (and (= x_15 2) ?v_4) ?v_7) (or x_9 (<= ?v_5 1))) (= x_10 ?v_5)) (= x_12 (+ x_4 x_6))) (= x_11 (ite ?v_6 (+ x_3 x_6) x_3))) (= x_16 x_9)))) ?v_7) (= x_7 (ite x_5 0 1))) (or (or (and (and (and (and (and (and (= x_8 0) ?v_9) ?v_8) x_9) ?v_10) ?v_11) ?v_12) (and (and (and (and (and (and (and (= x_8 1) ?v_9) x_0) (not (< 0 30))) ?v_6) ?v_10) ?v_11) ?v_12)) (and (and (and (and (and (and (and (= x_8 2) x_5) (not (< x_2 0))) (or x_0 (<= ?v_13 1))) (= x_1 ?v_13)) (= x_4 ?v_13)) (= x_3 (ite ?v_8 ?v_13 0))) (= x_9 x_0)))) (or (or (and (not (< x_12 60)) (not (<= (* x_11 20) x_12))) (and (not (< x_4 60)) (not (<= (* x_3 20) x_4)))) (and (not (< 0 60)) (not (<= (* 0 20) 0)))))))
(check-sat)
    "#;
    for i in 0..20 {
        let result = run_script(input);
        assert_eq!(
            result,
            vec!["unsat"],
            "Run {i}: gasburner-prop3-2 should be UNSAT (ITE deferral soundness, #8373)"
        );
    }
}

/// Regression for the #919-class false-SAT on the gasburner BMC family
/// (gasburner-prop3-{5,7,8,16}, all declared `:status unsat`; z3 = unsat).
///
/// AY returned `sat` because the SAT-acceptance model-validation pipeline
/// treated a PURE arithmetic ITE assertion that evaluated to a concrete
/// `false` under the extracted LRA model as a "model-extraction gap" and
/// accepted it via the #8373 SAT-fallback. The spurious model assigned (for
/// prop3-7) `x_46 = 121/40` while the assertion
/// `(= x_46 (ite (not x_44) (+ x_39 x_41) x_39))` with `x_44 = true` forces
/// `x_46 = x_39 = 3`. The fix:
///   * `ite_false_may_be_model_extraction_gap` no longer classifies pure
///     arithmetic/Boolean ITE assertions (no uninterpreted content) as a gap —
///     a concrete false from a complete model is authoritative and the model is
///     rejected, driving the split loop to a real UNSAT;
///   * the standalone LRA split loop clears `last_model_validated` on SAT so the
///     final validation runs against the ORIGINAL (pre-ITE-lift) assertions, not
///     the lifted Boolean-ITE skeleton.
///
/// This is the gasburner-prop3-5 body (smallest natural failing sibling).
/// Run repeatedly because the original false-SAT was non-deterministic
/// (HashMap iteration order affects SAT search order).
#[test]
fn regression_pure_arith_ite_false_sat_gasburner_prop3_5() {
    let input = r#"
(set-logic QF_LRA)
(declare-fun x_0 () Bool)
(declare-fun x_1 () Real)
(declare-fun x_2 () Real)
(declare-fun x_3 () Real)
(declare-fun x_4 () Real)
(declare-fun x_5 () Bool)
(declare-fun x_6 () Real)
(declare-fun x_7 () Real)
(declare-fun x_8 () Real)
(declare-fun x_9 () Bool)
(declare-fun x_10 () Real)
(declare-fun x_11 () Real)
(declare-fun x_12 () Real)
(declare-fun x_13 () Real)
(declare-fun x_14 () Real)
(declare-fun x_15 () Real)
(declare-fun x_16 () Bool)
(declare-fun x_17 () Real)
(declare-fun x_18 () Real)
(declare-fun x_19 () Real)
(declare-fun x_20 () Real)
(declare-fun x_21 () Real)
(declare-fun x_22 () Real)
(declare-fun x_23 () Bool)
(declare-fun x_24 () Real)
(declare-fun x_25 () Real)
(declare-fun x_26 () Real)
(declare-fun x_27 () Real)
(declare-fun x_28 () Real)
(declare-fun x_29 () Real)
(declare-fun x_30 () Bool)
(declare-fun x_31 () Real)
(declare-fun x_32 () Real)
(declare-fun x_33 () Real)
(declare-fun x_34 () Real)
(declare-fun x_35 () Real)
(declare-fun x_36 () Real)
(declare-fun x_37 () Bool)
(assert (let ((?v_6 (not x_30)) (?v_1 (= x_31 0)) (?v_5 (+ x_24 x_27)) (?v_3 (= x_32 x_25)) (?v_2 (= x_33 x_26)) (?v_0 (= x_28 0)) (?v_14 (not x_23)) (?v_9 (= x_24 0)) (?v_13 (+ x_17 x_20)) (?v_11 (= x_25 x_18)) (?v_10 (= x_26 x_19)) (?v_8 (= x_21 0)) (?v_22 (not x_16)) (?v_17 (= x_17 0)) (?v_21 (+ x_10 x_13)) (?v_19 (= x_18 x_11)) (?v_18 (= x_19 x_12)) (?v_16 (= x_14 0)) (?v_30 (not x_9)) (?v_25 (= x_10 0)) (?v_29 (+ x_1 x_6)) (?v_27 (= x_11 x_3)) (?v_26 (= x_12 x_4)) (?v_24 (= x_7 0)) (?v_32 (not x_0)) (?v_34 (= x_1 0)) (?v_37 (+ 0 x_2)) (?v_36 (= x_3 0)) (?v_35 (= x_4 0)) (?v_33 (not x_5)) (?v_4 (= x_28 1)) (?v_7 (not (< x_27 0))) (?v_12 (= x_21 1)) (?v_15 (not (< x_20 0))) (?v_20 (= x_14 1)) (?v_23 (not (< x_13 0))) (?v_28 (= x_7 1)) (?v_31 (not (< x_6 0)))) (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (and (<= x_35 1) (>= x_35 0)) (<= x_28 1)) (>= x_28 0)) (<= x_21 1)) (>= x_21 0)) (<= x_14 1)) (>= x_14 0)) (<= x_7 1)) (>= x_7 0)) ?v_32) (not (< x_34 0))) (= x_35 (ite ?v_4 0 1))) (or (or (and (and (and (and (and (and (= x_36 0) ?v_0) ?v_6) x_37) ?v_1) ?v_2) ?v_3) (and (and (and (and (and (and (and (= x_36 1) ?v_0) x_30) (not (< x_24 30))) (not x_37)) ?v_1) ?v_2) ?v_3)) (and (and (and (and (and (and (and (= x_36 2) ?v_4) ?v_7) (or x_30 (<= ?v_5 1))) (= x_31 ?v_5)) (= x_33 (+ x_26 x_27))) (= x_32 (ite ?v_6 (+ x_25 x_27) x_25))) (= x_37 x_30)))) ?v_7) (= x_28 (ite ?v_12 0 1))) (or (or (and (and (and (and (and (and (= x_29 0) ?v_8) ?v_14) x_30) ?v_9) ?v_10) ?v_11) (and (and (and (and (and (and (and (= x_29 1) ?v_8) x_23) (not (< x_17 30))) ?v_6) ?v_9) ?v_10) ?v_11)) (and (and (and (and (and (and (and (= x_29 2) ?v_12) ?v_15) (or x_23 (<= ?v_13 1))) (= x_24 ?v_13)) (= x_26 (+ x_19 x_20))) (= x_25 (ite ?v_14 (+ x_18 x_20) x_18))) (= x_30 x_23)))) ?v_15) (= x_21 (ite ?v_20 0 1))) (or (or (and (and (and (and (and (and (= x_22 0) ?v_16) ?v_22) x_23) ?v_17) ?v_18) ?v_19) (and (and (and (and (and (and (and (= x_22 1) ?v_16) x_16) (not (< x_10 30))) ?v_14) ?v_17) ?v_18) ?v_19)) (and (and (and (and (and (and (and (= x_22 2) ?v_20) ?v_23) (or x_16 (<= ?v_21 1))) (= x_17 ?v_21)) (= x_19 (+ x_12 x_13))) (= x_18 (ite ?v_22 (+ x_11 x_13) x_11))) (= x_23 x_16)))) ?v_23) (= x_14 (ite ?v_28 0 1))) (or (or (and (and (and (and (and (and (= x_15 0) ?v_24) ?v_30) x_16) ?v_25) ?v_26) ?v_27) (and (and (and (and (and (and (and (= x_15 1) ?v_24) x_9) (not (< x_1 30))) ?v_22) ?v_25) ?v_26) ?v_27)) (and (and (and (and (and (and (and (= x_15 2) ?v_28) ?v_31) (or x_9 (<= ?v_29 1))) (= x_10 ?v_29)) (= x_12 (+ x_4 x_6))) (= x_11 (ite ?v_30 (+ x_3 x_6) x_3))) (= x_16 x_9)))) ?v_31) (= x_7 (ite x_5 0 1))) (or (or (and (and (and (and (and (and (= x_8 0) ?v_33) ?v_32) x_9) ?v_34) ?v_35) ?v_36) (and (and (and (and (and (and (and (= x_8 1) ?v_33) x_0) (not (< 0 30))) ?v_30) ?v_34) ?v_35) ?v_36)) (and (and (and (and (and (and (and (= x_8 2) x_5) (not (< x_2 0))) (or x_0 (<= ?v_37 1))) (= x_1 ?v_37)) (= x_4 ?v_37)) (= x_3 (ite ?v_32 ?v_37 0))) (= x_9 x_0)))) (or (or (or (or (or (and (not (< x_33 60)) (not (<= (* x_32 20) x_33))) (and (not (< x_26 60)) (not (<= (* x_25 20) x_26)))) (and (not (< x_19 60)) (not (<= (* x_18 20) x_19)))) (and (not (< x_12 60)) (not (<= (* x_11 20) x_12)))) (and (not (< x_4 60)) (not (<= (* x_3 20) x_4)))) (and (not (< 0 60)) (not (<= (* 0 20) 0)))))))
(check-sat)
    "#;
    for i in 0..20 {
        let result = run_script(input);
        assert_eq!(
            result,
            vec!["unsat"],
            "Run {i}: gasburner-prop3-5 must be UNSAT (pure-arith ITE false-SAT soundness)"
        );
    }
}
