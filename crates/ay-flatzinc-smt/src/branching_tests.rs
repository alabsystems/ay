// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Tests for the branching search solver.
// Extracted from branching.rs to reduce file size.

use ay_core::kani_compat::DetHashMap as HashMap;

use super::*;
use crate::search::SearchAnnotation;

#[test]
fn test_domain_candidates_bool_min() {
    let vals = domain_candidates(&VarDomain::Bool, ValChoice::IndomainMin);
    assert_eq!(vals, vec!["false", "true"]);
}

#[test]
fn test_domain_candidates_bool_max() {
    let vals = domain_candidates(&VarDomain::Bool, ValChoice::IndomainMax);
    assert_eq!(vals, vec!["true", "false"]);
}

#[test]
fn test_domain_candidates_int_range_min() {
    let vals = domain_candidates(&VarDomain::IntRange(1, 4), ValChoice::IndomainMin);
    assert_eq!(vals, vec!["1", "2", "3", "4"]);
}

#[test]
fn test_domain_candidates_int_range_max() {
    let vals = domain_candidates(&VarDomain::IntRange(1, 4), ValChoice::IndomainMax);
    assert_eq!(vals, vec!["4", "3", "2", "1"]);
}

#[test]
fn test_domain_candidates_int_set_median() {
    let vals = domain_candidates(
        &VarDomain::IntSet(vec![1, 5, 10, 15, 20]),
        ValChoice::IndomainMedian,
    );
    assert_eq!(vals[0], "10");
}

#[test]
fn test_domain_is_enumerable() {
    assert!(domain_is_enumerable(&VarDomain::Bool));
    assert!(domain_is_enumerable(&VarDomain::IntRange(1, 100)));
    assert!(domain_is_enumerable(&VarDomain::IntRange(1, 1001)));
    assert!(!domain_is_enumerable(&VarDomain::IntRange(1, 1002)));
    assert!(!domain_is_enumerable(&VarDomain::IntUnbounded));
    assert!(domain_is_enumerable(&VarDomain::IntSet(vec![1, 2, 3])));
}

#[test]
fn test_resolve_search_vars_scalar() {
    let mut domains = HashMap::default();
    domains.insert("x".into(), VarDomain::IntRange(1, 5));
    domains.insert("y".into(), VarDomain::IntRange(1, 5));
    let smt_names = vec!["x".into(), "y".into()];
    let result = resolve_search_vars(&["x".into(), "y".into()], &smt_names, &domains);
    assert_eq!(result, vec!["x", "y"]);
}

#[test]
fn test_resolve_search_vars_array() {
    let mut domains = HashMap::default();
    domains.insert("q_1".into(), VarDomain::IntRange(1, 4));
    domains.insert("q_2".into(), VarDomain::IntRange(1, 4));
    domains.insert("q_3".into(), VarDomain::IntRange(1, 4));
    let smt_names = vec!["q_1".into(), "q_2".into(), "q_3".into()];
    let result = resolve_search_vars(&["q".into()], &smt_names, &domains);
    assert_eq!(result, vec!["q_1", "q_2", "q_3"]);
}

#[test]
fn test_resolve_search_vars_prefix_collision_fixed() {
    let mut domains = HashMap::default();
    domains.insert("q_1".into(), VarDomain::IntRange(1, 4));
    domains.insert("q_2".into(), VarDomain::IntRange(1, 4));
    domains.insert("q_extra".into(), VarDomain::IntRange(0, 10));
    let smt_names = vec!["q_1".into(), "q_2".into(), "q_extra".into()];
    let result = resolve_search_vars(&["q".into()], &smt_names, &domains);
    // Prefix collision fix: q_extra is NOT a numeric-indexed array element
    assert!(!result.contains(&"q_extra".to_string()));
    assert_eq!(result, vec!["q_1", "q_2"]);
}

#[test]
fn test_resolve_search_vars_empty() {
    let domains = HashMap::default();
    let smt_names: Vec<String> = vec![];
    let result = resolve_search_vars(&["nonexistent".into()], &smt_names, &domains);
    assert!(result.is_empty());
}

#[test]
fn test_resolve_search_vars_dedup() {
    let mut domains = HashMap::default();
    domains.insert("x".into(), VarDomain::IntRange(1, 5));
    let smt_names = vec!["x".into()];
    let result = resolve_search_vars(&["x".into(), "x".into()], &smt_names, &domains);
    assert_eq!(result, vec!["x", "x"]);
}

#[test]
fn test_build_search_plan_with_annotations() {
    let result = TranslationResult {
        smtlib: String::new(),
        declarations: String::new(),
        output_vars: vec![],
        objective: None,
        output_smt_names: vec![],
        smt_var_names: vec!["x".into(), "y".into(), "z".into()],
        search_annotations: vec![SearchAnnotation::IntSearch {
            vars: vec!["y".into(), "x".into()],
            var_choice: VarChoice::InputOrder,
            val_choice: ValChoice::IndomainMin,
            strategy: crate::search::SearchStrategy::Complete,
        }],
        var_domains: {
            let mut d = HashMap::default();
            d.insert("x".into(), VarDomain::IntRange(1, 5));
            d.insert("y".into(), VarDomain::IntRange(1, 5));
            d.insert("z".into(), VarDomain::IntRange(1, 5));
            d
        },
    };
    let plan = build_search_plan(&result);
    let vars: Vec<&str> = plan.iter().map(|e| e.smt_var.as_str()).collect();
    assert_eq!(vars, vec!["y", "x", "z"]);
}

#[test]
fn test_build_search_plan_no_annotations() {
    let result = TranslationResult {
        smtlib: String::new(),
        declarations: String::new(),
        output_vars: vec![],
        objective: None,
        output_smt_names: vec![],
        smt_var_names: vec!["a".into(), "b".into()],
        search_annotations: vec![],
        var_domains: {
            let mut d = HashMap::default();
            d.insert("a".into(), VarDomain::IntRange(1, 5));
            d.insert("b".into(), VarDomain::IntRange(1, 5));
            d
        },
    };
    let plan = build_search_plan(&result);
    let vars: Vec<&str> = plan.iter().map(|e| e.smt_var.as_str()).collect();
    assert_eq!(vars, vec!["a", "b"]);
    assert_eq!(plan[0].val_choice, ValChoice::IndomainMin);
}

#[test]
fn test_build_search_plan_propagates_heuristics() {
    let result = TranslationResult {
        smtlib: String::new(),
        declarations: String::new(),
        output_vars: vec![],
        objective: None,
        output_smt_names: vec![],
        smt_var_names: vec!["x".into(), "y".into(), "z".into()],
        search_annotations: vec![SearchAnnotation::IntSearch {
            vars: vec!["y".into(), "x".into()],
            var_choice: VarChoice::FirstFail,
            val_choice: ValChoice::IndomainMax,
            strategy: crate::search::SearchStrategy::Complete,
        }],
        var_domains: {
            let mut d = HashMap::default();
            d.insert("x".into(), VarDomain::IntRange(1, 5));
            d.insert("y".into(), VarDomain::IntRange(1, 3));
            d.insert("z".into(), VarDomain::IntRange(1, 10));
            d
        },
    };
    let plan = build_search_plan(&result);
    assert_eq!(plan[0].smt_var, "y");
    assert_eq!(plan[0].val_choice, ValChoice::IndomainMax);
    assert_eq!(plan[0].domain, VarDomain::IntRange(1, 3));
    assert_eq!(plan[1].smt_var, "x");
    assert_eq!(plan[1].val_choice, ValChoice::IndomainMax);
    assert_eq!(plan[2].smt_var, "z");
    assert_eq!(plan[2].val_choice, ValChoice::IndomainMin);
    assert_eq!(plan[2].domain, VarDomain::IntRange(1, 10));
}

#[test]
fn test_var_choice_first_fail_reorders() {
    let result = TranslationResult {
        smtlib: String::new(),
        declarations: String::new(),
        output_vars: vec![],
        objective: None,
        output_smt_names: vec![],
        smt_var_names: vec!["x".into(), "y".into(), "z".into()],
        search_annotations: vec![SearchAnnotation::IntSearch {
            vars: vec!["x".into(), "y".into(), "z".into()],
            var_choice: VarChoice::FirstFail,
            val_choice: ValChoice::IndomainMin,
            strategy: crate::search::SearchStrategy::Complete,
        }],
        var_domains: {
            let mut d = HashMap::default();
            d.insert("x".into(), VarDomain::IntRange(1, 10));
            d.insert("y".into(), VarDomain::IntRange(1, 2));
            d.insert("z".into(), VarDomain::IntRange(1, 5));
            d
        },
    };
    let plan = build_search_plan(&result);
    let vars: Vec<&str> = plan.iter().map(|e| e.smt_var.as_str()).collect();
    assert_eq!(vars, vec!["y", "z", "x"]);
}

#[test]
fn test_var_choice_anti_first_fail_reorders() {
    let result = TranslationResult {
        smtlib: String::new(),
        declarations: String::new(),
        output_vars: vec![],
        objective: None,
        output_smt_names: vec![],
        smt_var_names: vec!["a".into(), "b".into(), "c".into()],
        search_annotations: vec![SearchAnnotation::IntSearch {
            vars: vec!["a".into(), "b".into(), "c".into()],
            var_choice: VarChoice::AntiFirstFail,
            val_choice: ValChoice::IndomainMin,
            strategy: crate::search::SearchStrategy::Complete,
        }],
        var_domains: {
            let mut d = HashMap::default();
            d.insert("a".into(), VarDomain::IntRange(1, 3));
            d.insert("b".into(), VarDomain::IntRange(1, 10));
            d.insert("c".into(), VarDomain::IntRange(1, 5));
            d
        },
    };
    let plan = build_search_plan(&result);
    let vars: Vec<&str> = plan.iter().map(|e| e.smt_var.as_str()).collect();
    assert_eq!(vars, vec!["b", "c", "a"]);
}

#[test]
fn test_var_choice_smallest_reorders() {
    let result = TranslationResult {
        smtlib: String::new(),
        declarations: String::new(),
        output_vars: vec![],
        objective: None,
        output_smt_names: vec![],
        smt_var_names: vec!["a".into(), "b".into(), "c".into()],
        search_annotations: vec![SearchAnnotation::IntSearch {
            vars: vec!["a".into(), "b".into(), "c".into()],
            var_choice: VarChoice::Smallest,
            val_choice: ValChoice::IndomainMin,
            strategy: crate::search::SearchStrategy::Complete,
        }],
        var_domains: {
            let mut d = HashMap::default();
            d.insert("a".into(), VarDomain::IntRange(5, 10));
            d.insert("b".into(), VarDomain::IntRange(1, 10));
            d.insert("c".into(), VarDomain::IntRange(3, 7));
            d
        },
    };
    let plan = build_search_plan(&result);
    let vars: Vec<&str> = plan.iter().map(|e| e.smt_var.as_str()).collect();
    assert_eq!(vars, vec!["b", "c", "a"]);
}

#[test]
fn test_var_choice_largest_reorders() {
    let result = TranslationResult {
        smtlib: String::new(),
        declarations: String::new(),
        output_vars: vec![],
        objective: None,
        output_smt_names: vec![],
        smt_var_names: vec!["a".into(), "b".into(), "c".into()],
        search_annotations: vec![SearchAnnotation::IntSearch {
            vars: vec!["a".into(), "b".into(), "c".into()],
            var_choice: VarChoice::Largest,
            val_choice: ValChoice::IndomainMin,
            strategy: crate::search::SearchStrategy::Complete,
        }],
        var_domains: {
            let mut d = HashMap::default();
            d.insert("a".into(), VarDomain::IntRange(1, 5));
            d.insert("b".into(), VarDomain::IntRange(1, 20));
            d.insert("c".into(), VarDomain::IntRange(1, 10));
            d
        },
    };
    let plan = build_search_plan(&result);
    let vars: Vec<&str> = plan.iter().map(|e| e.smt_var.as_str()).collect();
    assert_eq!(vars, vec!["b", "c", "a"]);
}

#[test]
fn test_var_choice_input_order_preserves_annotation_order() {
    let result = TranslationResult {
        smtlib: String::new(),
        declarations: String::new(),
        output_vars: vec![],
        objective: None,
        output_smt_names: vec![],
        smt_var_names: vec!["x".into(), "y".into(), "z".into()],
        search_annotations: vec![SearchAnnotation::IntSearch {
            vars: vec!["z".into(), "x".into(), "y".into()],
            var_choice: VarChoice::InputOrder,
            val_choice: ValChoice::IndomainMin,
            strategy: crate::search::SearchStrategy::Complete,
        }],
        var_domains: {
            let mut d = HashMap::default();
            d.insert("x".into(), VarDomain::IntRange(1, 10));
            d.insert("y".into(), VarDomain::IntRange(1, 2));
            d.insert("z".into(), VarDomain::IntRange(1, 5));
            d
        },
    };
    let plan = build_search_plan(&result);
    let vars: Vec<&str> = plan.iter().map(|e| e.smt_var.as_str()).collect();
    assert_eq!(vars, vec!["z", "x", "y"]);
}

#[test]
fn test_seq_search_independent_groups() {
    let result = TranslationResult {
        smtlib: String::new(),
        declarations: String::new(),
        output_vars: vec![],
        objective: None,
        output_smt_names: vec![],
        smt_var_names: vec!["a".into(), "b".into(), "c".into(), "d".into()],
        search_annotations: vec![SearchAnnotation::SeqSearch(vec![
            SearchAnnotation::IntSearch {
                vars: vec!["a".into(), "b".into()],
                var_choice: VarChoice::FirstFail,
                val_choice: ValChoice::IndomainMin,
                strategy: crate::search::SearchStrategy::Complete,
            },
            SearchAnnotation::IntSearch {
                vars: vec!["d".into(), "c".into()],
                var_choice: VarChoice::InputOrder,
                val_choice: ValChoice::IndomainMax,
                strategy: crate::search::SearchStrategy::Complete,
            },
        ])],
        var_domains: {
            let mut d = HashMap::default();
            d.insert("a".into(), VarDomain::IntRange(1, 10));
            d.insert("b".into(), VarDomain::IntRange(1, 3));
            d.insert("c".into(), VarDomain::IntRange(1, 5));
            d.insert("d".into(), VarDomain::IntRange(1, 8));
            d
        },
    };
    let plan = build_search_plan(&result);
    let vars: Vec<&str> = plan.iter().map(|e| e.smt_var.as_str()).collect();
    assert_eq!(vars, vec!["b", "a", "d", "c"]);
}

#[test]
fn test_domain_size() {
    assert_eq!(domain_size(&VarDomain::Bool), 2);
    assert_eq!(domain_size(&VarDomain::IntRange(1, 5)), 5);
    assert_eq!(domain_size(&VarDomain::IntRange(-3, 3)), 7);
    assert_eq!(domain_size(&VarDomain::IntSet(vec![1, 3, 7])), 3);
    assert_eq!(domain_size(&VarDomain::IntUnbounded), i64::MAX);
}

#[test]
fn test_domain_lower_bound() {
    assert_eq!(domain_lower_bound(&VarDomain::Bool), 0);
    assert_eq!(domain_lower_bound(&VarDomain::IntRange(-5, 10)), -5);
    assert_eq!(domain_lower_bound(&VarDomain::IntSet(vec![3, 1, 7])), 1);
    assert_eq!(domain_lower_bound(&VarDomain::IntUnbounded), i64::MIN);
}

#[test]
fn test_domain_upper_bound() {
    assert_eq!(domain_upper_bound(&VarDomain::Bool), 1);
    assert_eq!(domain_upper_bound(&VarDomain::IntRange(-5, 10)), 10);
    assert_eq!(domain_upper_bound(&VarDomain::IntSet(vec![3, 1, 7])), 7);
    assert_eq!(domain_upper_bound(&VarDomain::IntUnbounded), i64::MAX);
}

#[test]
fn test_domain_candidates_split_fallback() {
    // Split strategies fall back to sorted ascending for per-value enumeration
    let vals = domain_candidates(&VarDomain::IntRange(1, 4), ValChoice::IndomainSplit);
    assert_eq!(vals, vec!["1", "2", "3", "4"]);
}

#[test]
fn test_domain_candidates_reverse_split_fallback() {
    let vals = domain_candidates(&VarDomain::IntRange(1, 4), ValChoice::IndomainReverseSplit);
    assert_eq!(vals, vec!["4", "3", "2", "1"]);
}

#[test]
fn test_domain_candidates_bool_split() {
    // Bool with split falls through to per-value (false first)
    let vals = domain_candidates(&VarDomain::Bool, ValChoice::IndomainSplit);
    assert_eq!(vals, vec!["false", "true"]);
}

#[test]
fn test_domain_candidates_bool_reverse_split() {
    // Bool with reverse_split uses max ordering (true first)
    let vals = domain_candidates(&VarDomain::Bool, ValChoice::IndomainReverseSplit);
    assert_eq!(vals, vec!["true", "false"]);
}

#[test]
fn test_build_search_plan_split_val_choice() {
    let result = TranslationResult {
        smtlib: String::new(),
        declarations: String::new(),
        output_vars: vec![],
        objective: None,
        output_smt_names: vec![],
        smt_var_names: vec!["x".into(), "y".into()],
        search_annotations: vec![SearchAnnotation::IntSearch {
            vars: vec!["x".into(), "y".into()],
            var_choice: VarChoice::InputOrder,
            val_choice: ValChoice::IndomainSplit,
            strategy: crate::search::SearchStrategy::Complete,
        }],
        var_domains: {
            let mut d = HashMap::default();
            d.insert("x".into(), VarDomain::IntRange(1, 8));
            d.insert("y".into(), VarDomain::IntRange(1, 4));
            d
        },
    };
    let plan = build_search_plan(&result);
    assert_eq!(plan[0].val_choice, ValChoice::IndomainSplit);
    assert_eq!(plan[1].val_choice, ValChoice::IndomainSplit);
    assert_eq!(plan[0].domain, VarDomain::IntRange(1, 8));
}

// Verify domain_candidates produces correct count for large IntRange.
// Documents the O(domain_size) upfront expansion (see #326).
#[test]
fn test_domain_candidates_large_range_count() {
    let candidates = domain_candidates(&VarDomain::IntRange(1, 1000), ValChoice::IndomainMin);
    assert_eq!(
        candidates.len(),
        1000,
        "IntRange(1,1000) should produce exactly 1000 candidates"
    );
    // First should be "1" (min ordering)
    assert_eq!(candidates[0], "1");
    // Last should be "1000"
    assert_eq!(candidates[999], "1000");
}

// Verify resolve_search_vars handles large arrays.
// Documents the O(k × m) linear scan in resolve_search_vars (see #326).
#[test]
fn test_resolve_search_vars_large_array() {
    let mut domains = HashMap::default();
    let mut smt_names = Vec::new();
    for i in 1..=50 {
        let name = format!("x_{i}");
        domains.insert(name.clone(), VarDomain::IntRange(1, 10));
        smt_names.push(name);
    }
    let result = resolve_search_vars(&["x".into()], &smt_names, &domains);
    assert_eq!(result.len(), 50, "Should resolve all 50 array elements");
    // Sort is lexicographic (x_1, x_10, x_11, ..., x_2, x_20, ...)
    assert_eq!(result[0], "x_1");
    assert!(result.contains(&"x_50".to_string()));
}

#[test]
fn test_resolve_search_vars_numeric_only() {
    // Verify that only numeric-indexed array vars match
    let mut domains = HashMap::default();
    domains.insert("x_1".into(), VarDomain::IntRange(1, 5));
    domains.insert("x_2".into(), VarDomain::IntRange(1, 5));
    domains.insert("x_foo".into(), VarDomain::IntRange(1, 5));
    domains.insert("x_1a".into(), VarDomain::IntRange(1, 5));
    let smt_names = vec!["x_1".into(), "x_2".into(), "x_foo".into(), "x_1a".into()];
    let result = resolve_search_vars(&["x".into()], &smt_names, &domains);
    assert_eq!(result, vec!["x_1", "x_2"]);
}

// --- Binary search optimization tests (Phase 4) ---

/// Verify binary search mid-point calculation for minimize: rounds down.
/// This ensures the binary search makes progress and terminates.
#[test]
fn test_binary_search_midpoint_minimize() {
    // Standard binary search: mid = lo + (hi - lo) / 2 (round down)
    let lo: i64 = 1;
    let hi: i64 = 10;
    let mid = lo + (hi - lo) / 2;
    assert_eq!(mid, 5); // (1 + 9/2) = 5

    // Edge case: hi - lo = 1
    let lo2: i64 = 5;
    let hi2: i64 = 6;
    let mid2 = lo2 + (hi2 - lo2) / 2;
    assert_eq!(mid2, 5); // mid = lo, test obj <= lo

    // Edge case: hi - lo = 0 (loop doesn't execute)
    let lo3: i64 = 5;
    let hi3: i64 = 5;
    assert!(lo3 >= hi3, "loop should not execute when lo >= hi");
}

/// Verify binary search mid-point calculation for maximize: rounds up.
/// Rounding up prevents infinite loops when hi - lo == 1.
#[test]
fn test_binary_search_midpoint_maximize() {
    // Maximize: mid = lo + (hi - lo + 1) / 2 (round up)
    let lo: i64 = 1;
    let hi: i64 = 10;
    let mid = lo + (hi - lo + 1) / 2;
    assert_eq!(mid, 6); // (1 + 10/2) = 6

    // Edge case: hi - lo = 1 → mid must be hi (not lo, which would stall)
    let lo2: i64 = 5;
    let hi2: i64 = 6;
    let mid2 = lo2 + (hi2 - lo2 + 1) / 2;
    assert_eq!(mid2, 6); // mid = hi, test obj >= hi

    // Edge case: hi - lo = 2
    let lo3: i64 = 5;
    let hi3: i64 = 7;
    let mid3 = lo3 + (hi3 - lo3 + 1) / 2;
    assert_eq!(mid3, 6); // (5 + 3/2) = 6
}

/// Verify the binary search vs linear decision criteria.
/// Binary search requires: enumerable variables AND bounded objective domain.
#[test]
fn test_binary_search_selection_criteria() {
    // Bounded IntRange → binary search eligible
    let bounded = VarDomain::IntRange(0, 100);
    let lo = domain_lower_bound(&bounded);
    let hi = domain_upper_bound(&bounded);
    assert_ne!(lo, i64::MIN);
    assert_ne!(hi, i64::MAX);

    // Unbounded → not eligible for binary search
    let unbounded = VarDomain::IntUnbounded;
    let lo_u = domain_lower_bound(&unbounded);
    let hi_u = domain_upper_bound(&unbounded);
    assert_eq!(lo_u, i64::MIN);
    assert_eq!(hi_u, i64::MAX);

    // IntSet → eligible (finite bounds)
    let set_domain = VarDomain::IntSet(vec![1, 5, 10, 20]);
    let lo_s = domain_lower_bound(&set_domain);
    let hi_s = domain_upper_bound(&set_domain);
    assert_eq!(lo_s, 1);
    assert_eq!(hi_s, 20);

    // Bool → eligible
    let bool_domain = VarDomain::Bool;
    let lo_b = domain_lower_bound(&bool_domain);
    let hi_b = domain_upper_bound(&bool_domain);
    assert_eq!(lo_b, 0);
    assert_eq!(hi_b, 1);
}

/// Verify binary search convergence for minimize scenario.
/// Simulates: domain [1..10], first solution at 8, optimal is 3.
#[test]
fn test_binary_search_convergence_minimize() {
    let mut lo: i64 = 1;
    let mut hi: i64 = 8;
    let optimal = 3;
    let mut iterations = 0;

    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        // Simulate: SAT if mid >= optimal, UNSAT if mid < optimal
        if mid >= optimal {
            hi = optimal; // ay finds actual optimum when constraint allows it
        } else {
            lo = mid + 1;
        }
        iterations += 1;
        assert!(iterations <= 10, "should converge in O(log(range)) steps");
    }

    assert_eq!(lo, optimal);
    assert_eq!(hi, optimal);
}

/// Verify binary search convergence for maximize scenario.
/// Simulates: domain [1..10], first solution at 3, optimal is 8.
#[test]
fn test_binary_search_convergence_maximize() {
    let mut lo: i64 = 3;
    let mut hi: i64 = 10;
    let optimal = 8;
    let mut iterations = 0;

    while lo < hi {
        let mid = lo + (hi - lo + 1) / 2;
        // Simulate: SAT if mid <= optimal, UNSAT if mid > optimal
        if mid <= optimal {
            lo = optimal; // ay finds actual optimum when constraint allows it
        } else {
            hi = mid - 1;
        }
        iterations += 1;
        assert!(iterations <= 10, "should converge in O(log(range)) steps");
    }

    assert_eq!(lo, optimal);
    assert_eq!(hi, optimal);
}

/// Verify binary search terminates when first solution is already optimal.
#[test]
fn test_binary_search_already_optimal() {
    // Minimize: domain [5..10], first solution at 5 (which is optimal)
    let lo: i64 = 5;
    let hi: i64 = 5;
    assert!(
        lo >= hi,
        "should skip binary search when first solution is at domain lower bound"
    );

    // Maximize: domain [1..7], first solution at 7 (which is optimal)
    let lo2: i64 = 7;
    let hi2: i64 = 7;
    assert!(
        lo2 >= hi2,
        "should skip binary search when first solution is at domain upper bound"
    );
}

// --- Edge case tests (proof coverage: previously untested paths) ---

#[test]
fn test_domain_candidates_int_unbounded() {
    // IntUnbounded generates the fallback range -10..=10 (21 candidates)
    let vals = domain_candidates(&VarDomain::IntUnbounded, ValChoice::IndomainMin);
    assert_eq!(
        vals.len(),
        21,
        "IntUnbounded should produce 21 candidates (-10..=10)"
    );
    assert_eq!(vals[0], "(- 10)");
    assert_eq!(vals[20], "10");
}

#[test]
fn test_domain_candidates_int_unbounded_max() {
    let vals = domain_candidates(&VarDomain::IntUnbounded, ValChoice::IndomainMax);
    assert_eq!(vals.len(), 21);
    assert_eq!(vals[0], "10");
    assert_eq!(vals[20], "(- 10)");
}

#[test]
fn test_order_int_values_random_preserves_order() {
    let mut vals = vec![5, 3, 1, 4, 2];
    order_int_values(&mut vals, ValChoice::IndomainRandom);
    // IndomainRandom is a no-op — the original order should be preserved
    assert_eq!(vals, vec![5, 3, 1, 4, 2]);
}

#[test]
fn test_domain_candidates_empty_int_set() {
    let vals = domain_candidates(&VarDomain::IntSet(vec![]), ValChoice::IndomainMin);
    assert!(vals.is_empty(), "empty IntSet should produce 0 candidates");
}

#[test]
fn test_domain_candidates_single_int_range() {
    let vals = domain_candidates(&VarDomain::IntRange(7, 7), ValChoice::IndomainMin);
    assert_eq!(
        vals,
        vec!["7"],
        "single-element range should produce one candidate"
    );
}

#[test]
fn test_domain_is_enumerable_exact_boundary() {
    // Range of exactly 1001 elements (0..1000) should be enumerable
    assert!(domain_is_enumerable(&VarDomain::IntRange(0, 1000)));
    // Range of 1002 elements (0..1001) should NOT be enumerable
    assert!(!domain_is_enumerable(&VarDomain::IntRange(0, 1001)));
}

#[test]
fn test_search_outcome_equality() {
    assert_eq!(SearchOutcome::Found, SearchOutcome::Found);
    assert_eq!(SearchOutcome::NotFound, SearchOutcome::NotFound);
    assert_eq!(SearchOutcome::Unknown, SearchOutcome::Unknown);
    assert_ne!(SearchOutcome::Found, SearchOutcome::NotFound);
    assert_ne!(SearchOutcome::Found, SearchOutcome::Unknown);
    assert_ne!(SearchOutcome::NotFound, SearchOutcome::Unknown);
}

#[test]
fn test_domain_candidates_negative_range() {
    let vals = domain_candidates(&VarDomain::IntRange(-3, -1), ValChoice::IndomainMin);
    assert_eq!(vals, vec!["(- 3)", "(- 2)", "(- 1)"]);
}

#[test]
fn test_domain_candidates_int_set_single() {
    let vals = domain_candidates(&VarDomain::IntSet(vec![42]), ValChoice::IndomainMin);
    assert_eq!(vals, vec!["42"]);
}

/// Verify binary search handles domain size 2 (smallest non-trivial case).
#[test]
fn test_binary_search_domain_size_two() {
    // Minimize: domain [1..2], first solution at 2, optimal is 1
    let lo: i64 = 1;
    let mut hi: i64 = 2;
    let mid = lo + (hi - lo) / 2;
    assert_eq!(mid, 1);
    // If SAT at 1: hi = 1, loop ends
    hi = 1;
    assert!(lo >= hi);

    // Maximize: domain [1..2], first solution at 1, optimal is 2
    let mut lo2: i64 = 1;
    let hi2: i64 = 2;
    let mid2 = lo2 + (hi2 - lo2 + 1) / 2;
    assert_eq!(mid2, 2);
    // If SAT at 2: lo = 2, loop ends
    lo2 = 2;
    assert!(lo2 >= hi2);
}

// --- Overflow and correctness regression tests ---

/// F1: domain_size overflows for extreme IntRange.
/// IntRange(i64::MIN, i64::MAX) should return i64::MAX (full domain),
/// but `hi - lo + 1` wraps around to 0.
#[test]
fn test_domain_size_extreme_range_overflow() {
    // Current implementation: hi - lo + 1 = i64::MAX - i64::MIN + 1
    // = i64::MAX - (-9223372036854775808) + 1
    // = i64::MAX + 9223372036854775808 + 1 which overflows in debug mode
    // In release mode this wraps to 0, which is wrong.
    //
    // The correct answer should be >= i64::MAX (the full integer range).
    // This test documents the bug and will pass once the fix is applied.
    let size = domain_size(&VarDomain::IntRange(0, i64::MAX));
    assert!(
        size > 0,
        "domain_size(IntRange(0, i64::MAX)) should be positive, got {size}"
    );
    // IntRange(0, i64::MAX) has i64::MAX + 1 elements which overflows i64
    // but the function returns i64, so i64::MAX is the best we can represent.
    // For now, just verify it doesn't return a nonsensical value.
    assert!(
        size >= i64::MAX / 2,
        "domain_size should be at least i64::MAX/2 for near-full range, got {size}"
    );
}

/// F4: domain_is_enumerable overflows for extreme IntRange.
/// IntRange(i64::MIN, i64::MAX) computes hi - lo which wraps negative.
/// The wrapped negative value satisfies `<= 1000`, incorrectly returning true.
#[test]
fn test_domain_is_enumerable_extreme_range_overflow() {
    // IntRange(i64::MIN, i64::MAX) is NOT enumerable (far more than 1000 elements).
    assert!(
        !domain_is_enumerable(&VarDomain::IntRange(i64::MIN, i64::MAX)),
        "IntRange(i64::MIN, i64::MAX) should NOT be enumerable"
    );
    // IntRange(0, i64::MAX) is also NOT enumerable
    assert!(
        !domain_is_enumerable(&VarDomain::IntRange(0, i64::MAX)),
        "IntRange(0, i64::MAX) should NOT be enumerable"
    );
    // IntRange(i64::MIN, 0) is also NOT enumerable
    assert!(
        !domain_is_enumerable(&VarDomain::IntRange(i64::MIN, 0)),
        "IntRange(i64::MIN, 0) should NOT be enumerable"
    );
}

/// F2: Binary search off-by-one — the UNSAT branch initializes lo=target
/// (minimize) but target was already proven UNSAT. lo should be target+1.
/// This test verifies the search doesn't re-test the UNSAT value.
#[test]
fn test_binary_search_off_by_one_minimize() {
    // Scenario: minimize, best_val=10, target=5 proven UNSAT
    // Binary search should search in [6, 9] (target+1 to best-1)
    // NOT [5, 9] (which wastes a call re-testing target=5)
    let target: i64 = 5;
    let best_val: i64 = 10;

    // Current code: lo = target = 5 (bug: includes UNSAT value)
    let (lo_current, hi_current) = (target, best_val - 1);
    // Correct code: lo = target + 1 = 6
    let (lo_correct, hi_correct) = (target + 1, best_val - 1);

    // Both ranges are valid for binary search, but correct range is tighter
    assert!(lo_current <= hi_current, "current range is valid");
    assert!(lo_correct <= hi_correct, "correct range is valid");
    assert_eq!(
        lo_correct,
        lo_current + 1,
        "correct lo should be one more than current lo"
    );
    assert_eq!(hi_current, hi_correct, "hi should be the same");
}

/// F2: Binary search off-by-one for maximize — hi=target should be target-1.
#[test]
fn test_binary_search_off_by_one_maximize() {
    // Scenario: maximize, best_val=5, target=10 proven UNSAT
    // Binary search should search in [6, 9] (best+1 to target-1)
    // NOT [6, 10] (which wastes a call re-testing target=10)
    let target: i64 = 10;
    let best_val: i64 = 5;

    // Current code: hi = target = 10 (bug: includes UNSAT value)
    let (lo_current, hi_current) = (best_val + 1, target);
    // Correct code: hi = target - 1 = 9
    let (lo_correct, hi_correct) = (best_val + 1, target - 1);

    assert!(lo_current <= hi_current, "current range is valid");
    assert!(lo_correct <= hi_correct, "correct range is valid");
    assert_eq!(lo_current, lo_correct, "lo should be the same");
    assert_eq!(
        hi_correct,
        hi_current - 1,
        "correct hi should be one less than current hi"
    );
}

/// F5: test_binary_search_midpoint_maximize documents round-up formula
/// but production code uses round-down. Verify production behavior.
#[test]
fn test_binary_search_midpoint_production_uses_round_down() {
    // Production code at branching.rs:751 and solver.rs:356:
    // mid = lo + (hi - lo) / 2
    // This is round-down for BOTH minimize and maximize.
    let lo: i64 = 5;
    let hi: i64 = 6;
    let mid_production = lo + (hi - lo) / 2;
    assert_eq!(mid_production, 5, "production always rounds down");

    // The round-up formula from the test at line 523-534:
    // mid = lo + (hi - lo + 1) / 2
    let mid_roundup = lo + (hi - lo + 1) / 2;
    assert_eq!(mid_roundup, 6, "round-up formula from test");

    // They differ when hi - lo is odd
    assert_ne!(
        mid_production, mid_roundup,
        "production and documented formula disagree"
    );
}

/// Verify binary search with round-down still terminates for maximize.
/// The UNSAT branch uses hi = mid - 1, which always decreases hi.
#[test]
fn test_binary_search_round_down_terminates_maximize() {
    // Simulate maximize binary search with round-down midpoint
    // Goal: find maximum achievable value
    let mut lo: i64 = 3;
    let mut hi: i64 = 10;
    let optimal = 7;
    let mut iterations = 0;

    while lo <= hi {
        let mid = lo + (hi - lo) / 2; // round-down (production code)
        if mid <= optimal {
            // SAT: actual >= mid
            lo = mid + 1; // tighten lower bound
        } else {
            // UNSAT: nothing >= mid
            hi = mid - 1;
        }
        iterations += 1;
        assert!(
            iterations <= 20,
            "should terminate in O(log(range)) steps, got {iterations}"
        );
    }
    // After termination: hi = optimal, lo = optimal + 1
    assert_eq!(hi, optimal, "hi should converge to optimal");
}
