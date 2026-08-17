// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Array frame-condition dead-parameter regressions.

use super::*;

/// Test: Frame-condition passthrough in self-loop (#5935).
///
/// Models the factorial regression pattern: P(n, result, arr) where arr
/// is passed through unchanged in the self-loop clause. The old Step 4
/// incorrectly marked arr as live because it appeared in both body P and
/// head P of the self-loop. The fix recognizes body→head sharing in the
/// same predicate at the same position as a frame condition, not a
/// cross-predicate dependency.
///
/// Reference: Z3 dl_mk_slice.cpp filter_unique_vars only counts body apps.
#[test]
fn test_dead_param_frame_condition_self_loop_5935() {
    // Use LIA (addition) instead of NIA (multiplication) so PDR can solve
    // the reduced problem. The original factorial used (* r n2) which is NIA
    // and causes AY (and Z3) to fail. The test's purpose is to verify dead
    // param elimination removes the unused array arg, not to test NIA solving.
    let input = r#"
(set-logic HORN)
(declare-fun P (Int Int (Array Int Int)) Bool)

; init: P(0, 0, arr)
(assert (forall ((n Int) (r Int) (arr (Array Int Int)))
    (=> (and (= n 0) (= r 0)) (P n r arr))))

; step: P(n+1, r+1, arr) <= P(n, r, arr) /\ n < 10
; arr is passed through UNCHANGED (frame condition)
(assert (forall ((n Int) (r Int) (arr (Array Int Int)) (n2 Int) (r2 Int))
    (=> (and (P n r arr) (= n2 (+ n 1)) (= r2 (+ r 1)) (< n 10)) (P n2 r2 arr))))

; query: r >= 0
(assert (forall ((n Int) (r Int) (arr (Array Int Int)))
    (=> (and (P n r arr) (< r 0)) false)))

(check-sat)
"#;
    let problem = parse_problem(input);
    assert_eq!(problem.predicates()[0].arity(), 3);
    assert!(matches!(
        problem.predicates()[0].arg_sorts[2],
        ChcSort::Array { .. }
    ));

    let eliminator = DeadParamEliminator::new();
    let (new_problem, position_map) = eliminator.eliminate(&problem);

    let mapping = &position_map[&PredicateId::new(0)];
    assert!(mapping[0].is_some(), "n should be live (in constraint)");
    assert!(mapping[1].is_some(), "r should be live (in constraint)");
    assert!(
        mapping[2].is_none(),
        "arr should be dead (frame condition passthrough, #5935)"
    );

    // After elimination, no array sort remains → PDR can solve
    assert_eq!(new_problem.predicates()[0].arity(), 2);

    let config = PortfolioConfig::with_engines(vec![EngineConfig::Pdr(PdrConfig::default())])
        .parallel(false);
    let solver = PortfolioSolver::new(new_problem, config);
    let result = solver.solve();
    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "LIA problem should be Safe after frame-condition elimination: {result:?}"
    );
}

/// Test: Multiple array frame-condition params in self-loop (like model-checker-consumer encoding).
///
/// Models the pattern from #5935: P(n, r, arr1..arr3) where all array
/// parameters are passed through unchanged. The eliminator must remove all.
#[test]
fn test_dead_param_multiple_array_frame_conditions() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int Int (Array Int Int) (Array Int Int) (Array Int Int)) Bool)

; init
(assert (forall ((n Int) (r Int) (a1 (Array Int Int)) (a2 (Array Int Int)) (a3 (Array Int Int)))
    (=> (and (= n 0) (= r 1)) (P n r a1 a2 a3))))

; step: arrays passed through unchanged
(assert (forall ((n Int) (r Int) (a1 (Array Int Int)) (a2 (Array Int Int)) (a3 (Array Int Int)) (n2 Int) (r2 Int))
    (=> (and (P n r a1 a2 a3) (= n2 (+ n 1)) (= r2 (* r n2)) (< n 10)) (P n2 r2 a1 a2 a3))))

; query
(assert (forall ((n Int) (r Int) (a1 (Array Int Int)) (a2 (Array Int Int)) (a3 (Array Int Int)))
    (=> (and (P n r a1 a2 a3) (< r 1)) false)))

(check-sat)
"#;
    let problem = parse_problem(input);
    assert_eq!(problem.predicates()[0].arity(), 5);

    let eliminator = DeadParamEliminator::new();
    let (new_problem, position_map) = eliminator.eliminate(&problem);

    let mapping = &position_map[&PredicateId::new(0)];
    assert!(mapping[0].is_some(), "n should be live");
    assert!(mapping[1].is_some(), "r should be live");
    assert!(mapping[2].is_none(), "a1 should be dead (frame condition)");
    assert!(mapping[3].is_none(), "a2 should be dead (frame condition)");
    assert!(mapping[4].is_none(), "a3 should be dead (frame condition)");

    assert_eq!(
        new_problem.predicates()[0].arity(),
        2,
        "only n and r should remain"
    );
}
