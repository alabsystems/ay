// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression coverage for mixed-clause `had_sat_no_cube` handling.

use ay_chc::testing::pdr_solve_from_str;
use ay_chc::{PdrConfig, PdrResult};
use ntest::timeout;

fn soundness_config() -> PdrConfig {
    let mut config = PdrConfig::default();
    config.max_frames = 4;
    config.max_iterations = 200;
    config.max_obligations = 10_000;
    config.verbose = false;
    config
}

/// When one matching clause is SAT but predecessor cube extraction fails
/// (partial model) and another matching clause is UNSAT, PDR must not prove
/// `Safe` by creating a blocking lemma from the UNSAT-only evidence.
///
/// Sound outcomes are:
/// - `Unsafe`: predecessor extraction succeeded (complete model path), or
/// - `Unknown`: SAT-no-cube path was detected and conservatively preserved.
/// Returning `Safe` would be unsound for this benchmark shape.
#[test]
#[timeout(10_000)]
fn mixed_level0_sat_no_cube_is_not_proven_safe() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)

; Clause 1: SAT for x=0, but y is unconstrained. Query formulas mention only x,
; so model-based predecessor extraction for (x,y) is partial.
(assert (forall ((x Int) (y Int))
  (=> (= x 0)
      (Inv x y))))

; Clause 2: also matches Inv head, but UNSAT for bad-state x=0.
(assert (forall ((x Int) (y Int))
  (=> (= x 1)
      (Inv x y))))

; Bad state is exactly x=0 (reachable via clause 1).
(assert (forall ((x Int) (y Int))
  (=> (and (Inv x y) (= x 0))
      false)))

(check-sat)
"#;

    let result = pdr_solve_from_str(smt2, soundness_config()).expect("solver invocation failed");

    assert!(
        matches!(result, PdrResult::Unknown | PdrResult::Unsafe(_)),
        "expected Unknown or Unsafe (never Safe) for mixed SAT-no-cube path, got {result:?}"
    );
}

/// Same benchmark shape as above, repeated to guard against run-to-run
/// differences in model completion. Any `Safe` outcome would be unsound.
#[test]
#[timeout(20_000)]
fn mixed_level0_sat_no_cube_is_not_proven_safe_across_repeated_runs() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)
(assert (forall ((x Int) (y Int))
  (=> (= x 0)
      (Inv x y))))
(assert (forall ((x Int) (y Int))
  (=> (= x 1)
      (Inv x y))))
(assert (forall ((x Int) (y Int))
  (=> (and (Inv x y) (= x 0))
      false)))
(check-sat)
"#;

    for run in 0..20 {
        let result =
            pdr_solve_from_str(smt2, soundness_config()).expect("solver invocation failed");
        assert!(
            matches!(result, PdrResult::Unknown | PdrResult::Unsafe(_)),
            "run {run}: expected Unknown or Unsafe (never Safe) for mixed SAT-no-cube path, got {result:?}"
        );
    }
}

/// Mixed SAT-no-cube shape at non-level-0 predecessor extraction:
/// one transition into `Q` can satisfy the bad-state query, but may produce a
/// partial predecessor model; another matching transition is UNSAT. This should
/// never be proven `Safe`.
#[test]
#[timeout(10_000)]
fn mixed_nonlevel_sat_no_cube_is_not_proven_safe() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)
(declare-fun Q (Int Int) Bool)

; Init fact for P: x fixed, y unconstrained.
(assert (forall ((x Int) (y Int))
  (=> (= x 0)
      (P x y))))

; Transition 1: can reach bad Q(x=1), but predecessor y may remain partial.
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int))
  (=> (and (P x y)
           (= x1 (+ x 1))
           (= y1 y))
      (Q x1 y1))))

; Transition 2: matching Q head but UNSAT for bad Q(x=1).
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int))
  (=> (and (P x y)
           (= x1 (+ x 2))
           (= y1 y))
      (Q x1 y1))))

; Bad state targets Q(x=1).
(assert (forall ((x Int) (y Int))
  (=> (and (Q x y) (= x 1))
      false)))

(check-sat)
"#;

    let result = pdr_solve_from_str(smt2, soundness_config()).expect("solver invocation failed");
    assert!(
        matches!(result, PdrResult::Unknown | PdrResult::Unsafe(_)),
        "expected Unknown or Unsafe (never Safe) for mixed non-level SAT-no-cube path, got {result:?}"
    );
}
