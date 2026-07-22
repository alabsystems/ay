// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Extended function tests: eval_str_*, resolve_*_term, extf effort-1 passes.

use super::*;
use ay_core::term::Symbol;
use ay_core::Sort;
use ay_core::TheoryResult;

#[test]
fn eval_str_at_basic() {
    assert_eq!(
        crate::eval::eval_str_at("hello", &BigInt::from(0)),
        Some("h".into())
    );
    assert_eq!(
        crate::eval::eval_str_at("hello", &BigInt::from(4)),
        Some("o".into())
    );
    assert_eq!(
        crate::eval::eval_str_at("hello", &BigInt::from(5)),
        Some(String::new())
    );
    assert_eq!(
        crate::eval::eval_str_at("hello", &BigInt::from(-1)),
        Some(String::new())
    );
    assert_eq!(
        crate::eval::eval_str_at("", &BigInt::from(0)),
        Some(String::new())
    );
}

#[test]
fn eval_str_substr_basic() {
    assert_eq!(
        crate::eval::eval_str_substr("hello", &BigInt::from(1), &BigInt::from(3)),
        Some("ell".into())
    );
    assert_eq!(
        crate::eval::eval_str_substr("hello", &BigInt::from(0), &BigInt::from(5)),
        Some("hello".into())
    );
    assert_eq!(
        crate::eval::eval_str_substr("hello", &BigInt::from(0), &BigInt::from(100)),
        Some("hello".into())
    );
    assert_eq!(
        crate::eval::eval_str_substr("hello", &BigInt::from(-1), &BigInt::from(3)),
        Some(String::new())
    );
    assert_eq!(
        crate::eval::eval_str_substr("hello", &BigInt::from(0), &BigInt::from(0)),
        Some(String::new())
    );
    assert_eq!(
        crate::eval::eval_str_substr("hello", &BigInt::from(10), &BigInt::from(3)),
        Some(String::new())
    );
}

#[test]
fn eval_str_replace_basic() {
    assert_eq!(crate::eval::eval_str_replace("hello", "ll", "r"), "hero");
    assert_eq!(crate::eval::eval_str_replace("hello", "x", "y"), "hello");
    assert_eq!(crate::eval::eval_str_replace("hello", "", "X"), "Xhello");
    assert_eq!(crate::eval::eval_str_replace("aaa", "a", "b"), "baa");
}

#[test]
fn eval_str_indexof_basic() {
    assert_eq!(
        crate::eval::eval_str_indexof("hello", "ll", &BigInt::from(0)),
        Some(BigInt::from(2))
    );
    assert_eq!(
        crate::eval::eval_str_indexof("hello", "x", &BigInt::from(0)),
        Some(BigInt::from(-1))
    );
    assert_eq!(
        crate::eval::eval_str_indexof("hello", "", &BigInt::from(3)),
        Some(BigInt::from(3))
    );
    assert_eq!(
        crate::eval::eval_str_indexof("hello", "lo", &BigInt::from(4)),
        Some(BigInt::from(-1))
    );
    assert_eq!(
        crate::eval::eval_str_indexof("hello", "lo", &BigInt::from(-1)),
        Some(BigInt::from(-1))
    );
}

#[test]
fn eval_str_to_int_basic() {
    assert_eq!(crate::eval::eval_str_to_int("123"), BigInt::from(123));
    assert_eq!(crate::eval::eval_str_to_int("0"), BigInt::from(0));
    assert_eq!(crate::eval::eval_str_to_int(""), BigInt::from(-1));
    assert_eq!(crate::eval::eval_str_to_int("abc"), BigInt::from(-1));
    assert_eq!(crate::eval::eval_str_to_int("12a"), BigInt::from(-1));
}

#[test]
fn resolve_string_term_evaluates_str_at() {
    let mut terms = TermStore::new();
    let hello = terms.mk_string("hello".to_string());
    let idx = terms.mk_int(BigInt::from(1));
    let at = terms.mk_app(Symbol::named("str.at"), vec![hello, idx], Sort::String);

    let state = SolverState::new();
    assert_eq!(
        CoreSolver::resolve_string_term(&terms, &state, at, 0),
        Some("e".into())
    );
}

#[test]
fn resolve_string_term_evaluates_str_substr() {
    let mut terms = TermStore::new();
    let hello = terms.mk_string("hello".to_string());
    let start = terms.mk_int(BigInt::from(1));
    let len = terms.mk_int(BigInt::from(3));
    let substr = terms.mk_app(
        Symbol::named("str.substr"),
        vec![hello, start, len],
        Sort::String,
    );

    let state = SolverState::new();
    assert_eq!(
        CoreSolver::resolve_string_term(&terms, &state, substr, 0),
        Some("ell".into())
    );
}

#[test]
fn resolve_string_term_evaluates_str_replace() {
    let mut terms = TermStore::new();
    let hello = terms.mk_string("hello".to_string());
    let ll = terms.mk_string("ll".to_string());
    let r = terms.mk_string("r".to_string());
    let replace = terms.mk_app(
        Symbol::named("str.replace"),
        vec![hello, ll, r],
        Sort::String,
    );

    let state = SolverState::new();
    assert_eq!(
        CoreSolver::resolve_string_term(&terms, &state, replace, 0),
        Some("hero".into())
    );
}

/// Regression for #3825: str.replace(y, y, "") reduces to "" even with unresolved y.
#[test]
fn resolve_string_term_replace_identity_reduces_to_replacement() {
    let mut terms = TermStore::new();
    let y = terms.mk_var("y", Sort::String);
    let empty = terms.mk_string(String::new());
    // str.replace(y, y, "") — same variable for haystack and pattern
    let replace = terms.mk_app(
        Symbol::named("str.replace"),
        vec![y, y, empty],
        Sort::String,
    );

    let state = SolverState::new();
    // y is unresolved, but since args[0] == args[1], reduce to args[2] = ""
    assert_eq!(
        CoreSolver::resolve_string_term(&terms, &state, replace, 0),
        Some(String::new())
    );
}

/// Identity reduction also works when two distinct terms are in the same EQC.
#[test]
fn resolve_string_term_replace_identity_via_eqc() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let xy_eq = terms.mk_eq(x, y);
    let replacement = terms.mk_string("R".to_string());
    // str.replace(x, y, "R") where x == y → "R"
    let replace = terms.mk_app(
        Symbol::named("str.replace"),
        vec![x, y, replacement],
        Sort::String,
    );

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, y);
    let _ = state.merge(x, y, TheoryLit::new(xy_eq, true));

    assert_eq!(
        CoreSolver::resolve_string_term(&terms, &state, replace, 0),
        Some("R".into())
    );
}

#[test]
fn resolve_int_term_evaluates_str_indexof() {
    let mut terms = TermStore::new();
    let hello = terms.mk_string("hello".to_string());
    let ll = terms.mk_string("ll".to_string());
    let zero = terms.mk_int(BigInt::from(0));
    let indexof = terms.mk_app(
        Symbol::named("str.indexof"),
        vec![hello, ll, zero],
        Sort::Int,
    );

    let state = SolverState::new();
    assert_eq!(
        CoreSolver::resolve_int_term(&terms, &state, indexof, 0),
        Some(BigInt::from(2))
    );
}

/// Post-NF extf effort 1: if x has NF "ab", then str.at(x, 1) must be "b".
///
/// This regression encodes:
/// - x = str.++("a", "b")   (no direct EQC constant for x before NF)
/// - str.at(x, 1) = "c"
///
/// Effort 0 cannot evaluate str.at(x, 1) because x has no EQC constant.
/// Effort 1 must use NF-derived substitution x ↦ "ab", evaluate to "b",
/// and detect conflict with "c".
#[test]
fn extf_effort1_uses_nf_constant_for_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let c = terms.mk_string("c".to_string());
    let one = terms.mk_int(BigInt::from(1));

    let ab = terms.mk_app(Symbol::named("str.++"), vec![a, b], Sort::String);
    let x_eq_ab = terms.mk_eq(x, ab);

    let at = terms.mk_app(Symbol::named("str.at"), vec![x, one], Sort::String);
    let at_eq_c = terms.mk_eq(at, c);

    let mut state = SolverState::new();
    state.assert_literal(&terms, x_eq_ab, true);
    state.assert_literal(&terms, at_eq_c, true);

    let mut infer = InferenceManager::new();
    let mut core = CoreSolver::new();
    let has_conflict = core.check(&terms, &state, &mut infer, &mut SkolemCache::new());

    assert!(
        has_conflict,
        "NF effort-1 pass must detect str.at(x,1) mismatch"
    );
    assert!(infer.has_conflict());
}

#[test]
fn extf_predicate_conflict_explanation_excludes_unrelated_assertion() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let ab = terms.mk_string("ab".to_string());
    let z = terms.mk_string("z".to_string());
    let c = terms.mk_string("c".to_string());

    let eq_x_ab = terms.mk_eq(x, ab);
    let eq_y_z = terms.mk_eq(y, z);
    let prefixof = terms.mk_app(Symbol::named("str.prefixof"), vec![c, x], Sort::Bool);

    let mut state = SolverState::new();
    // Deliberately include unrelated facts first to catch accidental
    // all-assertions explanations.
    state.assert_literal(&terms, eq_y_z, true);
    state.assert_literal(&terms, eq_x_ab, true);
    state.assert_literal(&terms, prefixof, true);

    let mut infer = InferenceManager::new();
    let mut core = CoreSolver::new();
    let has_conflict = core.check(&terms, &state, &mut infer, &mut SkolemCache::new());
    assert!(
        has_conflict,
        "str.prefixof(\"c\", \"ab\") asserted true must conflict"
    );

    let pred_lit = TheoryLit::new(prefixof, true);
    let eq_lit = TheoryLit::new(eq_x_ab, true);
    let unrelated_lit = TheoryLit::new(eq_y_z, true);
    match infer.to_theory_result() {
        TheoryResult::Unsat(lits) => {
            assert!(
                lits.contains(&pred_lit),
                "must include triggering predicate literal"
            );
            assert!(
                lits.contains(&eq_lit),
                "must include x=\"ab\" resolution literal"
            );
            assert!(
                !lits.contains(&unrelated_lit),
                "must not include unrelated assertion in conflict explanation"
            );
            assert!(
                lits.len() <= 3,
                "targeted explanation unexpectedly large: {lits:?}"
            );
        }
        other => panic!("expected Unsat conflict, got {other:?}"),
    }
}

#[test]
fn extf_effort1_contains_transitivity_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let abc = terms.mk_string("abc".to_string());

    let contains_xy = terms.mk_app(Symbol::named("str.contains"), vec![x, y], Sort::Bool);
    let contains_y_abc = terms.mk_app(Symbol::named("str.contains"), vec![y, abc], Sort::Bool);
    let contains_x_abc = terms.mk_app(Symbol::named("str.contains"), vec![x, abc], Sort::Bool);

    let mut state = SolverState::new();
    state.assert_literal(&terms, contains_xy, true);
    state.assert_literal(&terms, contains_y_abc, true);
    state.assert_literal(&terms, contains_x_abc, false);

    let mut infer = InferenceManager::new();
    let mut core = CoreSolver::new();
    let has_conflict = core.check(&terms, &state, &mut infer, &mut SkolemCache::new());

    assert!(
        has_conflict,
        "contains(x,y) ∧ contains(y,abc) ∧ ¬contains(x,abc) must conflict"
    );
    assert!(infer.has_conflict());
}

#[test]
fn extf_effort1_equal_after_substitution_infers_internal_equality() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let empty = terms.mk_string(String::new());

    let concat_x = terms.mk_app(Symbol::named("str.++"), vec![a, b], Sort::String);
    let inner = terms.mk_app(Symbol::named("str.++"), vec![empty, b], Sort::String);
    let concat_y = terms.mk_app(Symbol::named("str.++"), vec![a, inner], Sort::String);
    let eq_x = terms.mk_eq(x, concat_x);
    let eq_y = terms.mk_eq(y, concat_y);

    let upper_x = terms.mk_app(Symbol::named("str.to_upper"), vec![x], Sort::String);
    let upper_y = terms.mk_app(Symbol::named("str.to_upper"), vec![y], Sort::String);

    let mut state = SolverState::new();
    state.assert_literal(&terms, eq_x, true);
    state.assert_literal(&terms, eq_y, true);
    state.register_term(&terms, upper_x);
    state.register_term(&terms, upper_y);

    let mut core = CoreSolver::new();
    core.compute_normal_forms(&terms, &state);
    let mut infer = InferenceManager::new();
    let has_conflict = core.check_extf_eval_effort1(&terms, &state, &mut infer);
    assert!(!has_conflict);

    let eqs = infer.drain_internal_equalities();
    assert!(
        eqs.iter().any(|eq| {
            (eq.lhs == upper_x && eq.rhs == upper_y) || (eq.lhs == upper_y && eq.rhs == upper_x)
        }),
        "expected equal-after-substitution to infer to_upper(x) = to_upper(y)"
    );
}

#[test]
fn extf_effort1_extended_equality_rewriter_infers_replacement_equality() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let z = terms.mk_var("z", Sort::String);
    let c = terms.mk_string("target".to_string());

    let eq_xy = terms.mk_eq(x, y);
    let replace = terms.mk_app(Symbol::named("str.replace"), vec![x, y, z], Sort::String);
    let eq_replace_c = terms.mk_eq(replace, c);

    let mut state = SolverState::new();
    state.assert_literal(&terms, eq_xy, true);
    state.assert_literal(&terms, eq_replace_c, true);

    let mut core = CoreSolver::new();
    core.compute_normal_forms(&terms, &state);
    let mut infer = InferenceManager::new();
    let has_conflict = core.check_extf_eval_effort1(&terms, &state, &mut infer);
    assert!(!has_conflict);

    let eqs = infer.drain_internal_equalities();
    assert!(
        eqs.iter()
            .any(|eq| (eq.lhs == z && eq.rhs == c) || (eq.lhs == c && eq.rhs == z)),
        "expected rewrite of str.replace(x,x,z)=c to infer z=c"
    );
}

/// CTN_LHS_EMPTYSTR: str.contains("", x) ∧ x ≠ "" → UNSAT.
///
/// When haystack is "", the only way str.contains("", x) is true is x = "".
/// The inference x = "" should conflict with x ≠ "".
/// Regression test for #3850 benchmark #15.
#[test]
fn contains_empty_haystack_infers_needle_empty() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let empty = terms.mk_string(String::new());
    let contains = terms.mk_app(Symbol::named("str.contains"), vec![empty, x], Sort::Bool);

    let mut state = SolverState::new();
    state.set_empty_string_id(&terms, empty);
    state.assert_literal(&terms, contains, true);

    let mut core = CoreSolver::new();
    let mut infer = InferenceManager::new();
    let _has_conflict = core.check(&terms, &state, &mut infer, &mut SkolemCache::new());

    // The inference manager should contain x = "" as an internal equality.
    let eqs = infer.drain_internal_equalities();
    assert!(
        eqs.iter()
            .any(|eq| (eq.lhs == x && eq.rhs == empty) || (eq.lhs == empty && eq.rhs == x)),
        "str.contains(\"\", x) must infer x = \"\", got eqs: {eqs:?}"
    );
}

#[test]
fn eval_str_replace_all_basic() {
    assert_eq!(
        crate::eval::eval_str_replace_all("aabaa", "a", "x"),
        "xxbxx"
    );
}

#[test]
fn eval_str_replace_all_empty_pattern_returns_unchanged() {
    // SMT-LIB: str.replace_all(s, "", u) = s (no-op for empty pattern).
    assert_eq!(crate::eval::eval_str_replace_all("abc", "", "x"), "abc");
}

#[test]
fn eval_str_replace_all_no_match() {
    assert_eq!(
        crate::eval::eval_str_replace_all("hello", "xyz", "!"),
        "hello"
    );
}

#[test]
fn eval_str_replace_all_overlapping_pattern() {
    // "aaa" with pattern "aa" → replaces first "aa", leaving "a".
    assert_eq!(crate::eval::eval_str_replace_all("aaa", "aa", "b"), "ba");
}

#[test]
fn eval_str_replace_re_literal_match() {
    let mut terms = TermStore::new();
    let r = terms.mk_string("b".to_string());
    let re = terms.mk_app(Symbol::named("str.to_re"), vec![r], Sort::RegLan);
    assert_eq!(
        CoreSolver::eval_str_replace_re(&terms, "abc", re, "X"),
        Some("aXc".to_string())
    );
}

#[test]
fn eval_str_replace_re_no_match() {
    let mut terms = TermStore::new();
    let r = terms.mk_string("z".to_string());
    let re = terms.mk_app(Symbol::named("str.to_re"), vec![r], Sort::RegLan);
    assert_eq!(
        CoreSolver::eval_str_replace_re(&terms, "abc", re, "X"),
        Some("abc".to_string())
    );
}

#[test]
fn eval_str_replace_re_union_regex() {
    let mut terms = TermStore::new();
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let re_a = terms.mk_app(Symbol::named("str.to_re"), vec![a], Sort::RegLan);
    let re_b = terms.mk_app(Symbol::named("str.to_re"), vec![b], Sort::RegLan);
    let re = terms.mk_app(Symbol::named("re.union"), vec![re_a, re_b], Sort::RegLan);
    // Leftmost shortest match in "xba" is "b" at position 1.
    assert_eq!(
        CoreSolver::eval_str_replace_re(&terms, "xba", re, "Z"),
        Some("xZa".to_string())
    );
}

#[test]
fn eval_str_replace_re_all_literal() {
    let mut terms = TermStore::new();
    let r = terms.mk_string("a".to_string());
    let re = terms.mk_app(Symbol::named("str.to_re"), vec![r], Sort::RegLan);
    assert_eq!(
        CoreSolver::eval_str_replace_re_all(&terms, "banana", re, "X"),
        Some("bXnXnX".to_string())
    );
}

#[test]
fn eval_str_replace_re_all_empty_regex() {
    let mut terms = TermStore::new();
    // str.to_re("") only ever matches the EMPTY (zero-length) string.
    let r = terms.mk_string(String::new());
    let re = terms.mk_app(Symbol::named("str.to_re"), vec![r], Sort::RegLan);
    // SMT-LIB / cvc5 semantics: zero-length matches are never replaced, so the
    // empty regex acts as the identity. "ab" stays "ab" (NOT "XaXbX").
    assert_eq!(
        CoreSolver::eval_str_replace_re_all(&terms, "ab", re, "X"),
        Some("ab".to_string())
    );
}

#[test]
fn eval_str_replace_re_all_no_match() {
    let mut terms = TermStore::new();
    let r = terms.mk_app(Symbol::named("re.none"), vec![], Sort::RegLan);
    assert_eq!(
        CoreSolver::eval_str_replace_re_all(&terms, "abc", r, "X"),
        Some("abc".to_string())
    );
}

#[test]
fn eval_str_from_int_positive() {
    assert_eq!(crate::eval::eval_str_from_int(&BigInt::from(42)), "42");
}

#[test]
fn eval_str_from_int_zero() {
    assert_eq!(crate::eval::eval_str_from_int(&BigInt::from(0)), "0");
}

#[test]
fn eval_str_from_int_negative_returns_empty() {
    assert_eq!(crate::eval::eval_str_from_int(&BigInt::from(-1)), "");
}

#[test]
fn eval_str_to_code_single_ascii() {
    assert_eq!(crate::eval::eval_str_to_code("A"), BigInt::from(65));
}

#[test]
fn eval_str_to_code_empty_returns_minus_one() {
    assert_eq!(crate::eval::eval_str_to_code(""), BigInt::from(-1));
}

#[test]
fn eval_str_to_code_multi_char_returns_minus_one() {
    assert_eq!(crate::eval::eval_str_to_code("ab"), BigInt::from(-1));
}

#[test]
fn eval_str_to_code_max_smtlib_boundary() {
    // Code point 196607 (0x2FFFF) is the max SMT-LIB character.
    let s = char::from_u32(196607).unwrap().to_string();
    assert_eq!(crate::eval::eval_str_to_code(&s), BigInt::from(196607));
}

#[test]
fn eval_str_from_code_ascii() {
    assert_eq!(crate::eval::eval_str_from_code(&BigInt::from(65)), "A");
}

#[test]
fn eval_str_from_code_zero() {
    assert_eq!(
        crate::eval::eval_str_from_code(&BigInt::from(0)),
        "\u{0000}"
    );
}

#[test]
fn eval_str_from_code_negative_returns_empty() {
    assert_eq!(crate::eval::eval_str_from_code(&BigInt::from(-1)), "");
}

#[test]
fn eval_str_from_code_above_max_returns_empty() {
    assert_eq!(crate::eval::eval_str_from_code(&BigInt::from(196608)), "");
}

#[test]
fn eval_str_from_code_surrogate_returns_empty() {
    // U+D800 is a surrogate code point, not a valid char.
    assert_eq!(crate::eval::eval_str_from_code(&BigInt::from(0xD800)), "");
}

#[test]
fn eval_str_to_int_valid_digits() {
    assert_eq!(crate::eval::eval_str_to_int("123"), BigInt::from(123));
}

#[test]
fn eval_str_to_int_empty_returns_minus_one() {
    assert_eq!(crate::eval::eval_str_to_int(""), BigInt::from(-1));
}

#[test]
fn eval_str_to_int_non_digit_returns_minus_one() {
    assert_eq!(crate::eval::eval_str_to_int("12a"), BigInt::from(-1));
}

#[test]
fn eval_str_to_int_leading_zeros() {
    assert_eq!(crate::eval::eval_str_to_int("007"), BigInt::from(7));
}

#[test]
fn eval_str_indexof_empty_pattern_returns_start() {
    assert_eq!(
        crate::eval::eval_str_indexof("hello", "", &BigInt::from(2)),
        Some(BigInt::from(2))
    );
}

#[test]
fn eval_str_indexof_negative_start() {
    assert_eq!(
        crate::eval::eval_str_indexof("hello", "l", &BigInt::from(-1)),
        Some(BigInt::from(-1))
    );
}

#[test]
fn eval_str_indexof_start_past_end() {
    assert_eq!(
        crate::eval::eval_str_indexof("hi", "h", &BigInt::from(5)),
        Some(BigInt::from(-1))
    );
}

#[test]
fn eval_str_at_negative_index() {
    assert_eq!(
        crate::eval::eval_str_at("abc", &BigInt::from(-1)),
        Some(String::new())
    );
}

#[test]
fn eval_str_at_out_of_bounds() {
    assert_eq!(
        crate::eval::eval_str_at("abc", &BigInt::from(5)),
        Some(String::new())
    );
}

#[test]
fn eval_str_at_valid_index() {
    assert_eq!(
        crate::eval::eval_str_at("hello", &BigInt::from(1)),
        Some("e".to_string())
    );
}

#[test]
fn eval_str_substr_negative_start() {
    assert_eq!(
        crate::eval::eval_str_substr("hello", &BigInt::from(-1), &BigInt::from(3)),
        Some(String::new())
    );
}

#[test]
fn eval_str_substr_zero_length() {
    assert_eq!(
        crate::eval::eval_str_substr("hello", &BigInt::from(0), &BigInt::from(0)),
        Some(String::new())
    );
}

#[test]
fn eval_str_substr_clamps_to_end() {
    assert_eq!(
        crate::eval::eval_str_substr("hi", &BigInt::from(1), &BigInt::from(100)),
        Some("i".to_string())
    );
}

// Note: 4 replace_re* tests from dead core_tests.rs were not migrated here.
// They were never compiled (no `mod core_tests;` in lib.rs) and 2 of 4 fail
// at HEAD. The aspirational test coverage for replace_re ground evaluation
// exists at the StringSolver level in lib.rs tests instead.
