// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ChcParser;

fn safe_test_config() -> PdrConfig {
    PdrConfig {
        max_iterations: 50,
        max_obligations: 5_000,
        max_frames: 5,
        solve_timeout: Some(Duration::from_secs(16)),
        ..PdrConfig::default()
    }
}

#[test]
fn test_try_case_split_solve_merges_and_strictly_verifies_all_safe_cases() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)

; The mode is unconstrained at entry and remains constant.
(assert (forall ((x Int) (m Int))
  (=> (= x 0)
      (P x m))))

; Both mode partitions preserve x = 0, but the ITE makes m = 1 an
; authenticated case-split candidate.
(assert (forall ((x Int) (y Int) (m Int))
  (=> (and (P x m)
           (= y (ite (= m 1) x 0)))
      (P y m))))

(assert (forall ((x Int) (m Int))
  (=> (and (P x m) (not (= x 0)))
      false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).expect("failed to parse safe case-split CHC");
    let candidates = PdrSolver::find_case_split_candidates(&problem, false);
    assert_eq!(candidates.len(), 1, "fixture must have one split authority");
    assert_eq!(candidates[0].1, 1, "the constant mode argument must split");
    assert_eq!(
        candidates[0].3.len(),
        2,
        "m=1 and its complement must cover all cases"
    );

    let result = PdrSolver::try_case_split_solve(&problem, safe_test_config())
        .expect("the case-split solver should apply");
    let model = match result {
        PdrResult::Safe(model) => model,
        other => panic!("both deterministic branches should be Safe, got {other:?}"),
    };

    let mut verifier = PdrSolver::case_split_strict_verifier(&problem, &PdrConfig::default(), None);
    assert!(
        verifier.verify_model_fresh(&model),
        "the merged branch model must independently verify on the original CHC"
    );
}
