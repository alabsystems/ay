// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent replay for MODEL_CHECKER_CONSUMER's minimal nonlinear invariant fixture.

use super::{require_carcara_or_skip, run_carcara_trust_free, solve_unsat_and_get_proof};
use ntest::timeout;

const MODEL_CHECKER_CONSUMER_MINIMAL_NIA: &str = r#"
(set-logic QF_NIA)
(declare-const n Int)
(declare-const sum Int)
(declare-const i Int)
(declare-const sq Int)
(declare-const sum_next Int)
(declare-const i_next Int)
(declare-const sq_next Int)
(assert (>= n 0))
(assert (= (+ (* 2 sum) i) sq))
(assert (= sq (* i i)))
(assert (>= i 0))
(assert (<= i n))
(assert (>= sum 0))
(assert (>= sq 0))
(assert (<= sum sq))
(assert (< i n))
(assert (= sum_next (+ sum i)))
(assert (= i_next (+ i 1)))
(assert (= sq_next (+ sq (+ (* 2 i) 1))))
(assert
  (not
    (and (= (+ (* 2 sum_next) i_next) sq_next)
         (= sq_next (* i_next i_next))
         (>= i_next 0)
         (<= i_next n)
         (>= sum_next 0)
         (>= sq_next 0)
         (<= sum_next sq_next))))
(check-sat)
"#;

#[test]
#[timeout(60_000)]
fn model_checker_consumer_minimal_nia_is_trust_free_and_carcara_valid() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let label = "model_checker_consumer_minimal_nia";
    let proof = solve_unsat_and_get_proof(MODEL_CHECKER_CONSUMER_MINIMAL_NIA, label);
    assert!(!proof.contains(":rule hole"), "{proof}");
    assert!(!proof.contains(":rule trust"), "{proof}");
    assert!(
        proof.lines().any(|line| {
            line.contains("(not (= n n))") && line.contains(":rule eq_congruent_pred")
        }),
        "predicate congruence must carry its reflexive n=n argument:\n{proof}"
    );
    assert!(
        proof.contains(":rule refl"),
        "the reflexive hypothesis must be derived before resolution:\n{proof}"
    );
    assert!(
        run_carcara_trust_free(&carcara, label, MODEL_CHECKER_CONSUMER_MINIMAL_NIA, &proof),
        "MODEL_CHECKER_CONSUMER NIA proof must replay in Carcara without allowed trust"
    );
}
