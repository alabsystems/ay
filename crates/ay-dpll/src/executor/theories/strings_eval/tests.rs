// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::Symbol;
use ay_core::Sort;
use num_bigint::BigInt;

use super::super::super::Executor;
use super::*;

#[test]
fn collect_top_level_ground_string_terms_marks_connected_component_with_constant() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let y = exec.ctx.terms.mk_fresh_var("y", Sort::String);
    let ab = exec.ctx.terms.mk_string("ab".to_string());
    let eq1 = exec.ctx.terms.mk_eq(x, y);
    let eq2 = exec.ctx.terms.mk_eq(y, ab);
    let assertion = exec.ctx.terms.mk_and(vec![eq1, eq2]);

    let ground_terms = exec.collect_top_level_ground_string_terms(&[assertion]);

    assert!(
        ground_terms.contains(&x),
        "x should inherit the component constant"
    );
    assert!(
        ground_terms.contains(&y),
        "y should inherit the component constant"
    );
}

#[test]
fn collect_top_level_ground_string_terms_ignores_conflicting_constants() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let ab = exec.ctx.terms.mk_string("ab".to_string());
    let cd = exec.ctx.terms.mk_string("cd".to_string());
    let eq1 = exec.ctx.terms.mk_eq(x, ab);
    let eq2 = exec.ctx.terms.mk_eq(x, cd);
    let assertion = exec.ctx.terms.mk_and(vec![eq1, eq2]);

    let ground_terms = exec.collect_top_level_ground_string_terms(&[assertion]);

    assert!(
        !ground_terms.contains(&x),
        "conflicting constants must not mark the component ground"
    );
}

#[test]
fn build_concat_component_index_supports_direct_component_hits() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let a = exec.ctx.terms.mk_fresh_var("a", Sort::String);
    let b = exec.ctx.terms.mk_fresh_var("b", Sort::String);
    let concat = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.++"), vec![a, b], Sort::String);
    let eq = exec.ctx.terms.mk_eq(x, concat);

    let index = exec.build_concat_component_index(&[eq]);

    assert!(
        Executor::needle_in_concat_components(&index, &exec.ctx.terms, x, a),
        "direct concat leaves must be indexed"
    );
}

#[test]
fn build_concat_component_index_supports_constant_substring_hits() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let left = exec.ctx.terms.mk_string("ab".to_string());
    let right = exec.ctx.terms.mk_string("cde".to_string());
    let needle = exec.ctx.terms.mk_string("cd".to_string());
    let concat = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.++"), vec![left, right], Sort::String);
    let eq = exec.ctx.terms.mk_eq(x, concat);

    let index = exec.build_concat_component_index(&[eq]);

    assert!(
        Executor::needle_in_concat_components(&index, &exec.ctx.terms, x, needle),
        "constant substring hits must be recognized through constant leaves"
    );
}

#[test]
fn ground_eval_string_term_evaluates_concat() {
    let mut exec = Executor::new();
    let hello = exec.ctx.terms.mk_string("he".to_string());
    let world = exec.ctx.terms.mk_string("llo".to_string());
    let concat = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.++"), vec![hello, world], Sort::String);

    assert_eq!(
        ground_eval_string_term(&exec.ctx.terms, concat),
        Some("hello".to_string())
    );
}

#[test]
fn ground_eval_string_term_evaluates_substr() {
    let mut exec = Executor::new();
    let hello = exec.ctx.terms.mk_string("hello".to_string());
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let three = exec.ctx.terms.mk_int(BigInt::from(3));
    let substr = exec.ctx.terms.mk_app(
        Symbol::named("str.substr"),
        vec![hello, one, three],
        Sort::String,
    );

    assert_eq!(
        ground_eval_string_term(&exec.ctx.terms, substr),
        Some("ell".to_string())
    );
}

#[test]
fn ground_eval_string_term_evaluates_replace() {
    let mut exec = Executor::new();
    let hello = exec.ctx.terms.mk_string("hello".to_string());
    let needle = exec.ctx.terms.mk_string("ll".to_string());
    let replacement = exec.ctx.terms.mk_string("y".to_string());
    let replace = exec.ctx.terms.mk_app(
        Symbol::named("str.replace"),
        vec![hello, needle, replacement],
        Sort::String,
    );

    assert_eq!(
        ground_eval_string_term(&exec.ctx.terms, replace),
        Some("heyo".to_string())
    );
}

#[test]
fn ground_eval_int_term_handles_constants_and_unary_minus() {
    let mut exec = Executor::new();
    let three = exec.ctx.terms.mk_int(BigInt::from(3));
    let minus_three = exec
        .ctx
        .terms
        .mk_app(Symbol::named("-"), vec![three], Sort::Int);

    assert_eq!(
        ground_eval_int_term(&exec.ctx.terms, three),
        Some(BigInt::from(3))
    );
    assert_eq!(
        ground_eval_int_term(&exec.ctx.terms, minus_three),
        Some(BigInt::from(-3))
    );
}

#[test]
fn eval_substr_boundary_behavior_returns_empty_string() {
    assert_eq!(
        eval_substr("hello", &BigInt::from(-1), &BigInt::from(2)),
        Some(String::new())
    );
    assert_eq!(
        eval_substr("hello", &BigInt::from(10), &BigInt::from(2)),
        Some(String::new())
    );
    assert_eq!(
        eval_substr("hello", &BigInt::from(1), &BigInt::from(0)),
        Some(String::new())
    );
}

#[test]
fn eval_str_at_boundary_behavior_returns_empty_string() {
    assert_eq!(eval_str_at("hello", &BigInt::from(-1)), Some(String::new()));
    assert_eq!(eval_str_at("hello", &BigInt::from(10)), Some(String::new()));
}

#[test]
fn suffix_prefix_overlap_no_overlap() {
    assert_eq!(suffix_prefix_overlap("ab", "cd"), 0);
}

#[test]
fn suffix_prefix_overlap_one_char() {
    assert_eq!(suffix_prefix_overlap("ab", "bc"), 1);
}

#[test]
fn suffix_prefix_overlap_full() {
    assert_eq!(suffix_prefix_overlap("abc", "abc"), 3);
}

#[test]
fn suffix_prefix_overlap_partial() {
    assert_eq!(suffix_prefix_overlap("xab", "abc"), 2);
}

#[test]
fn multi_contains_min_len_no_overlap() {
    assert_eq!(multi_contains_min_len("ab", "cd"), 4);
}

#[test]
fn multi_contains_min_len_with_overlap() {
    assert_eq!(multi_contains_min_len("ab", "bc"), 3);
}

#[test]
fn multi_contains_min_len_identical() {
    assert_eq!(multi_contains_min_len("abc", "abc"), 3);
}

#[test]
fn multi_contains_min_len_asymmetric_overlap() {
    assert_eq!(multi_contains_min_len("abc", "cde"), 5);
    assert_eq!(multi_contains_min_len("cde", "abc"), 5);
}

// --- Ground evaluation coverage for AC2 ---

#[test]
fn ground_eval_string_term_evaluates_str_at() {
    let mut exec = Executor::new();
    let hello = exec.ctx.terms.mk_string("hello".to_string());
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let at = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.at"), vec![hello, one], Sort::String);

    assert_eq!(
        ground_eval_string_term(&exec.ctx.terms, at),
        Some("e".to_string())
    );
}

#[test]
fn ground_eval_string_term_evaluates_from_int() {
    let mut exec = Executor::new();
    let n = exec.ctx.terms.mk_int(BigInt::from(42));
    let from_int = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.from_int"), vec![n], Sort::String);

    assert_eq!(
        ground_eval_string_term(&exec.ctx.terms, from_int),
        Some("42".to_string())
    );
}

#[test]
fn ground_eval_string_term_from_int_negative_returns_empty() {
    let mut exec = Executor::new();
    let neg = exec.ctx.terms.mk_int(BigInt::from(-1));
    let from_int = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.from_int"), vec![neg], Sort::String);

    assert_eq!(
        ground_eval_string_term(&exec.ctx.terms, from_int),
        Some(String::new())
    );
}

#[test]
fn ground_eval_string_term_evaluates_from_code() {
    let mut exec = Executor::new();
    let code = exec.ctx.terms.mk_int(BigInt::from(65)); // 'A'
    let from_code = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.from_code"), vec![code], Sort::String);

    assert_eq!(
        ground_eval_string_term(&exec.ctx.terms, from_code),
        Some("A".to_string())
    );
}

#[test]
fn ground_eval_string_term_evaluates_to_lower() {
    let mut exec = Executor::new();
    let upper = exec.ctx.terms.mk_string("HELLO".to_string());
    let lower = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.to_lower"), vec![upper], Sort::String);

    assert_eq!(
        ground_eval_string_term(&exec.ctx.terms, lower),
        Some("hello".to_string())
    );
}

#[test]
fn ground_eval_string_term_evaluates_to_upper() {
    let mut exec = Executor::new();
    let low = exec.ctx.terms.mk_string("hello".to_string());
    let upper = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.to_upper"), vec![low], Sort::String);

    assert_eq!(
        ground_eval_string_term(&exec.ctx.terms, upper),
        Some("HELLO".to_string())
    );
}

#[test]
fn ground_eval_string_term_evaluates_replace_all() {
    let mut exec = Executor::new();
    let s = exec.ctx.terms.mk_string("aabaa".to_string());
    let pat = exec.ctx.terms.mk_string("a".to_string());
    let rep = exec.ctx.terms.mk_string("x".to_string());
    let replace_all = exec.ctx.terms.mk_app(
        Symbol::named("str.replace_all"),
        vec![s, pat, rep],
        Sort::String,
    );

    assert_eq!(
        ground_eval_string_term(&exec.ctx.terms, replace_all),
        Some("xxbxx".to_string())
    );
}

#[test]
fn ground_eval_bool_term_contains_true() {
    let mut exec = Executor::new();
    let haystack = exec.ctx.terms.mk_string("hello world".to_string());
    let needle = exec.ctx.terms.mk_string("lo w".to_string());
    let contains = exec.ctx.terms.mk_app(
        Symbol::named("str.contains"),
        vec![haystack, needle],
        Sort::Bool,
    );

    assert_eq!(exec.ground_eval_bool_term(contains), Some(true));
}

#[test]
fn ground_eval_bool_term_contains_false() {
    let mut exec = Executor::new();
    let haystack = exec.ctx.terms.mk_string("hello".to_string());
    let needle = exec.ctx.terms.mk_string("xyz".to_string());
    let contains = exec.ctx.terms.mk_app(
        Symbol::named("str.contains"),
        vec![haystack, needle],
        Sort::Bool,
    );

    assert_eq!(exec.ground_eval_bool_term(contains), Some(false));
}

#[test]
fn ground_eval_bool_term_prefixof() {
    let mut exec = Executor::new();
    let prefix = exec.ctx.terms.mk_string("hel".to_string());
    let s = exec.ctx.terms.mk_string("hello".to_string());
    let prefixof =
        exec.ctx
            .terms
            .mk_app(Symbol::named("str.prefixof"), vec![prefix, s], Sort::Bool);

    assert_eq!(exec.ground_eval_bool_term(prefixof), Some(true));
}

#[test]
fn ground_eval_bool_term_suffixof() {
    let mut exec = Executor::new();
    let suffix = exec.ctx.terms.mk_string("llo".to_string());
    let s = exec.ctx.terms.mk_string("hello".to_string());
    let suffixof =
        exec.ctx
            .terms
            .mk_app(Symbol::named("str.suffixof"), vec![suffix, s], Sort::Bool);

    assert_eq!(exec.ground_eval_bool_term(suffixof), Some(true));
}

#[test]
fn ground_eval_bool_term_is_digit() {
    let mut exec = Executor::new();
    let digit = exec.ctx.terms.mk_string("5".to_string());
    let letter = exec.ctx.terms.mk_string("a".to_string());
    let is_digit_true =
        exec.ctx
            .terms
            .mk_app(Symbol::named("str.is_digit"), vec![digit], Sort::Bool);
    let is_digit_false =
        exec.ctx
            .terms
            .mk_app(Symbol::named("str.is_digit"), vec![letter], Sort::Bool);

    assert_eq!(exec.ground_eval_bool_term(is_digit_true), Some(true));
    assert_eq!(exec.ground_eval_bool_term(is_digit_false), Some(false));
}

#[test]
fn fold_ground_string_ops_folds_nested_concat_to_constant() {
    let mut exec = Executor::new();
    let a = exec.ctx.terms.mk_string("a".to_string());
    let b = exec.ctx.terms.mk_string("b".to_string());
    let concat = exec
        .ctx
        .terms
        .mk_app(Symbol::named("str.++"), vec![a, b], Sort::String);
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let eq = exec.ctx.terms.mk_eq(x, concat);

    let folded = exec.fold_ground_string_ops(&[eq]);

    assert_eq!(folded.len(), 1);
    // The concat "a" ++ "b" should be folded to "ab"
    let ab = exec.ctx.terms.mk_string("ab".to_string());
    let expected = exec.ctx.terms.mk_eq(x, ab);
    assert_eq!(
        folded[0], expected,
        "ground concat must be folded to constant"
    );
}

#[test]
fn ground_eval_string_term_returns_none_for_variable() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);

    assert_eq!(ground_eval_string_term(&exec.ctx.terms, x), None);
}

// --- Unit tests for term_has_ground_string_value (AC: #6356) ---

#[test]
fn term_has_ground_string_value_true_for_constant() {
    let mut exec = Executor::new();
    let abc = exec.ctx.terms.mk_string("abc".to_string());
    let empty_set = HashSet::default();

    assert!(
        exec.term_has_ground_string_value(&empty_set, abc),
        "string constant must return true"
    );
}

#[test]
fn term_has_ground_string_value_false_for_variable_not_in_ground_set() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let empty_set = HashSet::default();

    assert!(
        !exec.term_has_ground_string_value(&empty_set, x),
        "variable not in ground set must return false"
    );
}

#[test]
fn term_has_ground_string_value_true_for_variable_in_ground_set() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_fresh_var("x", Sort::String);
    let mut ground_set = HashSet::default();
    ground_set.insert(x);

    assert!(
        exec.term_has_ground_string_value(&ground_set, x),
        "variable in ground set must return true"
    );
}
