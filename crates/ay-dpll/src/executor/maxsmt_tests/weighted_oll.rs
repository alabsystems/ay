// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Weighted OLL coverage and resource-limited objective-reporting regressions.

use super::*;
use crate::executor::optimization::maxsmt_test_hooks::CheckedDecisionDeclineGuard;

/// Assert the exact optimum when MaxSMT completed its proof, or validate the
/// honest upper-bound contract when a bounded authority probe made the parsed
/// SMT-LIB surface publish `:approximate` instead.
///
/// Returns `true` only for an exact result, so OLL coverage assertions do not
/// mistake a resource-limited fallback witness for completed optimization.
fn assert_exact_or_valid_approximate_cost(
    objectives_output: &str,
    exact_optimum: u64,
    total_weight: u64,
) -> bool {
    let cost = parse_soft_cost(objectives_output).expect("soft cost");
    if objectives_output.contains(":approximate") {
        assert!(
            (exact_optimum..=total_weight).contains(&cost),
            "approximate cost {cost} outside [opt={exact_optimum}, total={total_weight}]:\n\
             {objectives_output}"
        );
        false
    } else {
        assert_eq!(
            cost, exact_optimum,
            "unqualified MaxSMT objective must be the exact optimum"
        );
        true
    }
}

/// A bounded exact-search decline must qualify its feasible upper bound. The
/// thread-local hook lets base feasibility complete, then makes a weighted-bound
/// authority probe inconclusive without relying on wall time or host load.
#[test]
fn maxsmt_inconclusive_weight_probe_marks_approximate() {
    let _decline = CheckedDecisionDeclineGuard::after(1);
    let outputs = run_script(
        "(set-logic QF_UF)(set-option :ay-maxsmt-engine binary)\
         (declare-const p Bool)(declare-const q Bool)(assert (or p q))\
         (assert-soft (not p) :weight 7)(assert-soft (not q) :weight 7)\
         (assert-soft p :weight 1)(assert-soft q :weight 1)\
         (check-sat)(get-objectives)",
    );
    assert_eq!(
        outputs[0], "sat",
        "resource-bounded base witness: {outputs:?}"
    );
    assert!(
        outputs[1].contains(":approximate"),
        "an inconclusive exact search must qualify its objective: {outputs:?}"
    );
    assert!(!assert_exact_or_valid_approximate_cost(&outputs[1], 8, 16));
}

/// Weighted OLL must cover the non-uniform instance when every exact authority
/// probe completes. Under resource contention, its feasible fallback remains a
/// checked upper bound but must not count as OLL coverage.
#[test]
fn maxsmt_oll_weighted_covered_matches_baseline() {
    let script = |engine: &str| {
        format!(
            "(set-logic QF_UF)(set-option :ay-maxsmt-engine {engine})\
             (declare-const a Bool)(declare-const b Bool)\
             (assert (or a b))(assert (not (and a b)))\
             (assert-soft a :weight 5)(assert-soft b :weight 1)\
             (check-sat)(get-objectives)"
        )
    };
    let (oll_out, oll_rounds) = run_script_with_oll_rounds(&script("oll"));
    let binary_out = run_script(&script("binary"));
    assert_eq!(oll_out[0], "sat");
    assert_eq!(binary_out[0], "sat");
    let oll_exact = assert_exact_or_valid_approximate_cost(&oll_out[1], 1, 6);
    let binary_exact = assert_exact_or_valid_approximate_cost(&binary_out[1], 1, 6);
    if !oll_exact || !binary_exact {
        return;
    }
    assert!(
        oll_rounds >= 1,
        "weighted OLL must cover this instance, got {oll_rounds} rounds"
    );
    assert_eq!(
        parse_soft_cost(&oll_out[1]),
        parse_soft_cost(&binary_out[1]),
        "OLL weighted optimum must equal the binary baseline optimum"
    );
}

/// Relaxing two cheap softs must beat relaxing one expensive soft, despite the
/// higher violation count: `x=true` costs 4 and `x=false` costs 5.
#[test]
fn maxsmt_oll_weighted_two_cheap_beats_one_expensive() {
    let script = |engine: &str| {
        format!(
            "(set-logic QF_UF)(set-option :ay-maxsmt-engine {engine})\
             (declare-const x Bool)\
             (assert-soft x :weight 5)\
             (assert-soft (not x) :weight 2)\
             (assert-soft (not x) :weight 2)\
             (check-sat)(get-objectives)"
        )
    };
    let true_opt = brute_force_min_violated(1, &[], &[(0, true, 5), (0, false, 2), (0, false, 2)]);
    assert_eq!(true_opt, Some(4));
    let (oll_out, oll_rounds) = run_script_with_oll_rounds(&script("oll"));
    let binary_out = run_script(&script("binary"));
    assert_eq!(oll_out[0], "sat");
    assert_eq!(binary_out[0], "sat");
    let oll_exact = assert_exact_or_valid_approximate_cost(&oll_out[1], 4, 9);
    let binary_exact = assert_exact_or_valid_approximate_cost(&binary_out[1], 4, 9);
    if !oll_exact || !binary_exact {
        return;
    }
    assert!(
        oll_rounds >= 1,
        "weighted OLL must engage on this instance, got {oll_rounds} rounds"
    );
}

/// The cheapest feasible set is not the one with the fewest constraints:
/// p=T,q=F and p=F,q=T cost 8, while p=T,q=T costs 14.
#[test]
fn maxsmt_oll_weighted_least_total_weight_set() {
    let softs = [(0, false, 7u64), (1, false, 7), (0, true, 1), (1, true, 1)];
    let hard = [vec![(0usize, true), (1usize, true)]];
    assert_eq!(brute_force_min_violated(2, &hard, &softs), Some(8));

    let script = instance_to_script(2, &hard, &softs, "oll");
    let (outputs, oll_rounds) = run_script_with_oll_rounds(&script);
    assert_eq!(outputs[0], "sat");
    if !assert_exact_or_valid_approximate_cost(&outputs[1], 8, 16) {
        return;
    }
    assert!(
        oll_rounds >= 1,
        "weighted OLL must engage on this instance, got {oll_rounds} rounds"
    );
}

/// Three independent opposing-soft pairs force three weighted strata. The
/// optimum is min(9,4) + min(6,5) + min(8,3) = 12.
#[test]
fn maxsmt_oll_weighted_stratified_multiple_cores() {
    let softs = [
        (0, true, 9u64),
        (0, false, 4),
        (1, true, 6),
        (1, false, 5),
        (2, true, 8),
        (2, false, 3),
    ];
    let hard: [Vec<(usize, bool)>; 0] = [];
    assert_eq!(brute_force_min_violated(3, &hard, &softs), Some(12));

    let script = instance_to_script(3, &hard, &softs, "oll");
    let (outputs, oll_rounds) = run_script_with_oll_rounds(&script);
    assert_eq!(outputs[0], "sat");
    if !assert_exact_or_valid_approximate_cost(&outputs[1], 12, 35) {
        return;
    }
    assert!(
        oll_rounds >= 1,
        "weighted OLL must accumulate a core, got {oll_rounds} rounds"
    );
}
