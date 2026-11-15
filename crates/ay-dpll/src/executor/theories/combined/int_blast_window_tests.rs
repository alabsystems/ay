// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Direct half-bounded window tests for the exact Int-blast lane.

use super::*;

/// The group regression `offset_and_negated_scaled_windows_keep_later_residue_witnesses_sat`
/// pins both SAT verdicts end to end. Call the lane directly as well: the
/// outer bridge may validate its own SAT candidate before needing this
/// fallback, which would otherwise leave the window route untested. Each
/// witness lies in a later period of its window (`x = 512`, `x = -30`).
#[test]
fn later_residue_witnesses_fit_the_exact_half_bounded_windows() {
    for (query, windows) in [
        (
            "(declare-const x Int) (declare-const y Int)
             (assert (>= x 0)) (assert (= y (+ x 257)))
             (assert (distinct x 0)) (assert (distinct x 256))
             (assert (= ((_ int2bv 8) y) #x01))",
            &[(0, 767), (257, 1024)][..],
        ),
        (
            "(declare-const x Int)
             (assert (not (< (* (- 3) x) (- 4))))
             (assert (distinct x (- 14)))
             (assert (= ((_ int2bv 4) x) #x2))",
            &[(-30, 1)][..],
        ),
    ] {
        let commands =
            ay_frontend::parse(&format!("(set-logic ALL) {query}")).expect("valid query");
        let mut executor = Executor::new();
        executor.execute_all(&commands).expect("install query");
        let roots = executor.ctx.assertions.clone();
        let plan = IntBlastPlan::analyze(&executor.ctx.terms, &roots)
            .expect("the half-bounded query must be in the lane's fragment");
        assert_eq!(plan.synthetic.len(), windows.len(), "{query}");
        for &(lo, hi) in windows {
            assert!(
                plan.synthetic.iter().any(|(_, interval)| {
                    interval.lo == BigInt::from(lo) && interval.hi == BigInt::from(hi)
                }),
                "{query}: expected synthetic window [{lo}, {hi}]"
            );
        }
        let got = executor
            .solve_bv_lia_by_int_blast(&roots)
            .expect("probe does not error");
        assert!(
            got.as_ref().is_some_and(SolveResult::is_sat),
            "{query}: {got:?}"
        );
    }
}
