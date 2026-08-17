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

include!("branching_tests/large_domain_and_binary_search.rs");
