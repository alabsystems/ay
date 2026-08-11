// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::Symbol;
use ay_core::Sort;
use ay_core::TheoryResult;

// ── Helper constructors (tests have mutable TermStore) ─────────────

fn mk_re_none(terms: &mut TermStore) -> TermId {
    terms.mk_app(Symbol::named("re.none"), vec![], Sort::RegLan)
}

fn mk_re_all(terms: &mut TermStore) -> TermId {
    terms.mk_app(Symbol::named("re.all"), vec![], Sort::RegLan)
}

fn mk_str_to_re(terms: &mut TermStore, s: &str) -> TermId {
    let str_const = terms.mk_string(s.to_string());
    terms.mk_app(Symbol::named("str.to_re"), vec![str_const], Sort::RegLan)
}

fn mk_re_concat(terms: &mut TermStore, children: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named("re.++"), children, Sort::RegLan)
}

fn mk_re_union(terms: &mut TermStore, children: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named("re.union"), children, Sort::RegLan)
}

fn mk_re_inter(terms: &mut TermStore, children: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named("re.inter"), children, Sort::RegLan)
}

fn mk_re_star(terms: &mut TermStore, child: TermId) -> TermId {
    terms.mk_app(Symbol::named("re.*"), vec![child], Sort::RegLan)
}

fn mk_re_plus(terms: &mut TermStore, child: TermId) -> TermId {
    terms.mk_app(Symbol::named("re.+"), vec![child], Sort::RegLan)
}

fn mk_re_opt(terms: &mut TermStore, child: TermId) -> TermId {
    terms.mk_app(Symbol::named("re.opt"), vec![child], Sort::RegLan)
}

fn mk_re_comp(terms: &mut TermStore, child: TermId) -> TermId {
    terms.mk_app(Symbol::named("re.comp"), vec![child], Sort::RegLan)
}

fn mk_re_diff(terms: &mut TermStore, r1: TermId, r2: TermId) -> TermId {
    terms.mk_app(Symbol::named("re.diff"), vec![r1, r2], Sort::RegLan)
}

fn mk_re_range(terms: &mut TermStore, lo: &str, hi: &str) -> TermId {
    let lo_t = terms.mk_string(lo.to_string());
    let hi_t = terms.mk_string(hi.to_string());
    terms.mk_app(Symbol::named("re.range"), vec![lo_t, hi_t], Sort::RegLan)
}

fn mk_re_allchar(terms: &mut TermStore) -> TermId {
    terms.mk_app(Symbol::named("re.allchar"), vec![], Sort::RegLan)
}

fn mk_re_loop(terms: &mut TermStore, child: TermId, lo: u32, hi: u32) -> TermId {
    terms.mk_app(
        Symbol::indexed("re.loop", vec![lo, hi]),
        vec![child],
        Sort::RegLan,
    )
}

// ── delta tests ────────────────────────────────────────────────────

#[test]
fn delta_re_none_is_false() {
    let mut terms = TermStore::new();
    let r = mk_re_none(&mut terms);
    assert_eq!(RegExpSolver::delta(&terms, r), Some(false));
}

#[test]
fn delta_re_allchar_is_false() {
    let mut terms = TermStore::new();
    let r = mk_re_allchar(&mut terms);
    assert_eq!(RegExpSolver::delta(&terms, r), Some(false));
}

#[test]
fn delta_re_all_is_true() {
    let mut terms = TermStore::new();
    let r = mk_re_all(&mut terms);
    assert_eq!(RegExpSolver::delta(&terms, r), Some(true));
}

#[test]
fn delta_str_to_re_empty_is_true() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "");
    assert_eq!(RegExpSolver::delta(&terms, r), Some(true));
}

#[test]
fn delta_str_to_re_nonempty_is_false() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "a");
    assert_eq!(RegExpSolver::delta(&terms, r), Some(false));
}

#[test]
fn delta_re_star_is_true() {
    let mut terms = TermStore::new();
    let inner = mk_str_to_re(&mut terms, "a");
    let r = mk_re_star(&mut terms, inner);
    assert_eq!(RegExpSolver::delta(&terms, r), Some(true));
}

#[test]
fn delta_re_plus_nonempty_is_false() {
    let mut terms = TermStore::new();
    let inner = mk_str_to_re(&mut terms, "a");
    let r = mk_re_plus(&mut terms, inner);
    assert_eq!(RegExpSolver::delta(&terms, r), Some(false));
}

#[test]
fn delta_re_opt_is_true() {
    let mut terms = TermStore::new();
    let inner = mk_str_to_re(&mut terms, "a");
    let r = mk_re_opt(&mut terms, inner);
    assert_eq!(RegExpSolver::delta(&terms, r), Some(true));
}

#[test]
fn delta_re_concat_all_nullable() {
    let mut terms = TermStore::new();
    let r1 = mk_str_to_re(&mut terms, "");
    let inner = mk_str_to_re(&mut terms, "a");
    let r2 = mk_re_star(&mut terms, inner);
    let concat = mk_re_concat(&mut terms, vec![r1, r2]);
    assert_eq!(RegExpSolver::delta(&terms, concat), Some(true));
}

#[test]
fn delta_re_concat_one_not_nullable() {
    let mut terms = TermStore::new();
    let r1 = mk_str_to_re(&mut terms, "a");
    let inner = mk_str_to_re(&mut terms, "b");
    let r2 = mk_re_star(&mut terms, inner);
    let concat = mk_re_concat(&mut terms, vec![r1, r2]);
    assert_eq!(RegExpSolver::delta(&terms, concat), Some(false));
}

#[test]
fn delta_re_union_one_nullable() {
    let mut terms = TermStore::new();
    let r1 = mk_str_to_re(&mut terms, "a");
    let r2 = mk_str_to_re(&mut terms, "");
    let union = mk_re_union(&mut terms, vec![r1, r2]);
    assert_eq!(RegExpSolver::delta(&terms, union), Some(true));
}

#[test]
fn delta_re_union_none_nullable() {
    let mut terms = TermStore::new();
    let r1 = mk_str_to_re(&mut terms, "a");
    let r2 = mk_str_to_re(&mut terms, "b");
    let union = mk_re_union(&mut terms, vec![r1, r2]);
    assert_eq!(RegExpSolver::delta(&terms, union), Some(false));
}

#[test]
fn delta_re_comp_flips() {
    let mut terms = TermStore::new();
    let inner = mk_str_to_re(&mut terms, "a"); // not nullable
    let comp = mk_re_comp(&mut terms, inner);
    assert_eq!(RegExpSolver::delta(&terms, comp), Some(true));

    let inner2 = mk_str_to_re(&mut terms, ""); // nullable
    let comp2 = mk_re_comp(&mut terms, inner2);
    assert_eq!(RegExpSolver::delta(&terms, comp2), Some(false));
}

#[test]
fn delta_re_diff() {
    let mut terms = TermStore::new();
    let all = mk_re_all(&mut terms);
    let inner = mk_str_to_re(&mut terms, "a");
    let star = mk_re_star(&mut terms, inner);
    // diff(re.all, re.*(str.to_re("a"))): both nullable, so false
    let diff = mk_re_diff(&mut terms, all, star);
    assert_eq!(RegExpSolver::delta(&terms, diff), Some(false));
}

// ── evaluate tests ─────────────────────────────────────────────────

#[test]
fn eval_re_none() {
    let mut terms = TermStore::new();
    let r = mk_re_none(&mut terms);
    assert_eq!(RegExpSolver::evaluate(&terms, "", r), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", r), Some(false));
}

#[test]
fn eval_re_all() {
    let mut terms = TermStore::new();
    let r = mk_re_all(&mut terms);
    assert_eq!(RegExpSolver::evaluate(&terms, "", r), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "anything", r), Some(true));
}

#[test]
fn eval_allchar() {
    let mut terms = TermStore::new();
    let r = mk_re_allchar(&mut terms);
    assert_eq!(RegExpSolver::evaluate(&terms, "x", r), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "", r), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "ab", r), Some(false));
}

#[test]
fn eval_range() {
    let mut terms = TermStore::new();
    let r = mk_re_range(&mut terms, "a", "z");
    assert_eq!(RegExpSolver::evaluate(&terms, "m", r), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", r), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "z", r), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "A", r), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "", r), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "ab", r), Some(false));
}

#[test]
fn eval_range_empty_language() {
    // Per SMT-LIB, (re.range lo hi) is the EMPTY language whenever an endpoint
    // is not a single character, or lo > hi. Membership is false for every
    // string (including any single character that would fall "in range" if only
    // the first character of a multi-char endpoint were considered).
    let mut terms = TermStore::new();

    // Multi-char endpoints (the original wrong-SAT repro): (re.range "ab" "cd").
    let multi = mk_re_range(&mut terms, "ab", "cd");
    assert_eq!(RegExpSolver::evaluate(&terms, "b", multi), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", multi), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "c", multi), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "ab", multi), Some(false));

    // One bad endpoint: (re.range "ab" "x").
    let one_bad = mk_re_range(&mut terms, "ab", "x");
    assert_eq!(RegExpSolver::evaluate(&terms, "a", one_bad), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "b", one_bad), Some(false));

    // Empty endpoint(s): (re.range "" "a") and (re.range "a" "").
    let empty_lo = mk_re_range(&mut terms, "", "a");
    assert_eq!(RegExpSolver::evaluate(&terms, "a", empty_lo), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "", empty_lo), Some(false));
    let empty_hi = mk_re_range(&mut terms, "a", "");
    assert_eq!(RegExpSolver::evaluate(&terms, "a", empty_hi), Some(false));

    // Reversed single-char range: (re.range "z" "a") is empty.
    let reversed = mk_re_range(&mut terms, "z", "a");
    assert_eq!(RegExpSolver::evaluate(&terms, "m", reversed), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", reversed), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "z", reversed), Some(false));
}

#[test]
fn eval_str_to_re() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "hello");
    assert_eq!(RegExpSolver::evaluate(&terms, "hello", r), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "hell", r), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "helloo", r), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "", r), Some(false));
}

#[test]
fn eval_str_to_re_empty() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "");
    assert_eq!(RegExpSolver::evaluate(&terms, "", r), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", r), Some(false));
}

#[test]
fn eval_concat() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let b = mk_str_to_re(&mut terms, "b");
    let concat = mk_re_concat(&mut terms, vec![a, b]);
    assert_eq!(RegExpSolver::evaluate(&terms, "ab", concat), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "ba", concat), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", concat), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "", concat), Some(false));
}

#[test]
fn eval_union() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let b = mk_str_to_re(&mut terms, "b");
    let union = mk_re_union(&mut terms, vec![a, b]);
    assert_eq!(RegExpSolver::evaluate(&terms, "a", union), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "b", union), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "c", union), Some(false));
}

#[test]
fn eval_inter() {
    let mut terms = TermStore::new();
    // re.inter(re.*(a), re.*(a|b)) — both match "a" and "aaa", first doesn't match "b"
    let a = mk_str_to_re(&mut terms, "a");
    let star_a = mk_re_star(&mut terms, a);
    let a2 = mk_str_to_re(&mut terms, "a");
    let b = mk_str_to_re(&mut terms, "b");
    let union_ab = mk_re_union(&mut terms, vec![a2, b]);
    let star_ab = mk_re_star(&mut terms, union_ab);
    let inter = mk_re_inter(&mut terms, vec![star_a, star_ab]);
    assert_eq!(RegExpSolver::evaluate(&terms, "", inter), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", inter), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "aaa", inter), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "b", inter), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "ab", inter), Some(false));
}

#[test]
fn eval_star_empty_string() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let star = mk_re_star(&mut terms, a);
    assert_eq!(RegExpSolver::evaluate(&terms, "", star), Some(true));
}

#[test]
fn eval_star_single() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let star = mk_re_star(&mut terms, a);
    assert_eq!(RegExpSolver::evaluate(&terms, "a", star), Some(true));
}

#[test]
fn eval_star_repeated() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let star = mk_re_star(&mut terms, a);
    assert_eq!(RegExpSolver::evaluate(&terms, "aaa", star), Some(true));
}

#[test]
fn eval_star_non_matching() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let star = mk_re_star(&mut terms, a);
    assert_eq!(RegExpSolver::evaluate(&terms, "b", star), Some(false));
}

#[test]
fn eval_star_multi_char_pattern() {
    let mut terms = TermStore::new();
    let ab = mk_str_to_re(&mut terms, "ab");
    let star = mk_re_star(&mut terms, ab);
    assert_eq!(RegExpSolver::evaluate(&terms, "", star), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "ab", star), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "abab", star), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", star), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "aba", star), Some(false));
}

#[test]
fn eval_plus() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let plus = mk_re_plus(&mut terms, a);
    assert_eq!(RegExpSolver::evaluate(&terms, "", plus), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", plus), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "aaa", plus), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "b", plus), Some(false));
}

#[test]
fn eval_opt() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let opt = mk_re_opt(&mut terms, a);
    assert_eq!(RegExpSolver::evaluate(&terms, "", opt), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", opt), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "aa", opt), Some(false));
}

#[test]
fn eval_comp() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let comp = mk_re_comp(&mut terms, a);
    assert_eq!(RegExpSolver::evaluate(&terms, "a", comp), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "b", comp), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "", comp), Some(true));
}

#[test]
fn eval_diff() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let b = mk_str_to_re(&mut terms, "b");
    let union_ab = mk_re_union(&mut terms, vec![a, b]);
    let b2 = mk_str_to_re(&mut terms, "b");
    let diff = mk_re_diff(&mut terms, union_ab, b2);
    // (a|b) \ b = a
    assert_eq!(RegExpSolver::evaluate(&terms, "a", diff), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "b", diff), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "c", diff), Some(false));
}

// ── Complex regex evaluation ───────────────────────────────────────

#[test]
fn eval_star_a_then_b() {
    // (re.++ (re.* (str.to_re "a")) (str.to_re "b"))
    // Matches: "b", "ab", "aab", "aaab", ...
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let b = mk_str_to_re(&mut terms, "b");
    let star_a = mk_re_star(&mut terms, a);
    let concat = mk_re_concat(&mut terms, vec![star_a, b]);

    assert_eq!(RegExpSolver::evaluate(&terms, "b", concat), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "ab", concat), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "aab", concat), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "", concat), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", concat), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "ba", concat), Some(false));
}

#[test]
fn eval_digit_star() {
    // (re.* (re.range "0" "9"))
    let mut terms = TermStore::new();
    let digits = mk_re_range(&mut terms, "0", "9");
    let star = mk_re_star(&mut terms, digits);
    assert_eq!(RegExpSolver::evaluate(&terms, "", star), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "42", star), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "abc", star), Some(false));
}

#[test]
fn eval_email_like_pattern() {
    // Simplified: (re.++ (re.+ (re.range "a" "z")) (str.to_re "@") (re.+ (re.range "a" "z")))
    let mut terms = TermStore::new();
    let az = mk_re_range(&mut terms, "a", "z");
    let user = mk_re_plus(&mut terms, az);
    let at = mk_str_to_re(&mut terms, "@");
    let az2 = mk_re_range(&mut terms, "a", "z");
    let domain = mk_re_plus(&mut terms, az2);
    let email = mk_re_concat(&mut terms, vec![user, at, domain]);

    assert_eq!(RegExpSolver::evaluate(&terms, "a@b", email), Some(true));
    assert_eq!(
        RegExpSolver::evaluate(&terms, "user@host", email),
        Some(true)
    );
    assert_eq!(RegExpSolver::evaluate(&terms, "@host", email), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "user@", email), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "user", email), Some(false));
}

// ── check() integration tests ──────────────────────────────────────

#[test]
fn check_positive_membership_true_is_sat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let hello = terms.mk_string("hello".to_string());
    let a = mk_str_to_re(&mut terms, "hello");
    let star = mk_re_star(&mut terms, a);
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![x, star], Sort::Bool);
    let eq = terms.mk_eq(x, hello);

    let mut state = SolverState::new();
    state.assert_literal(&terms, in_re, true);
    state.assert_literal(&terms, eq, true);
    // Merge x with "hello" so resolve_string finds it.
    state.register_term(&terms, x);
    state.register_term(&terms, hello);
    let _ = state.merge(x, hello, TheoryLit::new(eq, true));

    let mut infer = InferenceManager::new();
    let mut solver = RegExpSolver::new();
    let conflict = solver.check(&terms, &state, &mut infer);

    // "hello" matches (re.* (str.to_re "hello")), positive assertion.
    // No conflict expected.
    assert!(!conflict, "positive membership true should not conflict");
}

#[test]
fn check_positive_membership_false_is_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let goodbye = terms.mk_string("goodbye".to_string());
    let a = mk_str_to_re(&mut terms, "hello");
    let star = mk_re_star(&mut terms, a);
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![x, star], Sort::Bool);
    let eq = terms.mk_eq(x, goodbye);

    let mut state = SolverState::new();
    state.assert_literal(&terms, in_re, true);
    state.assert_literal(&terms, eq, true);
    state.register_term(&terms, x);
    state.register_term(&terms, goodbye);
    let _ = state.merge(x, goodbye, TheoryLit::new(eq, true));

    let mut infer = InferenceManager::new();
    let mut solver = RegExpSolver::new();
    let conflict = solver.check(&terms, &state, &mut infer);

    // "goodbye" does NOT match (re.* (str.to_re "hello")), but asserted positively.
    assert!(conflict, "positive membership false should conflict");
}

#[test]
fn check_negative_membership_true_is_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let hello = terms.mk_string("hello".to_string());
    let a = mk_str_to_re(&mut terms, "hello");
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![x, a], Sort::Bool);
    let eq = terms.mk_eq(x, hello);

    let mut state = SolverState::new();
    state.assert_literal(&terms, in_re, false); // NOT in_re
    state.assert_literal(&terms, eq, true);
    state.register_term(&terms, x);
    state.register_term(&terms, hello);
    let _ = state.merge(x, hello, TheoryLit::new(eq, true));

    let mut infer = InferenceManager::new();
    let mut solver = RegExpSolver::new();
    let conflict = solver.check(&terms, &state, &mut infer);

    // "hello" matches (str.to_re "hello"), but asserted negatively.
    assert!(
        conflict,
        "negative membership of matching string should conflict"
    );
}

#[test]
fn check_conflict_explanation_excludes_unrelated_assertion() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let goodbye = terms.mk_string("goodbye".to_string());
    let unrelated = terms.mk_string("unrelated".to_string());
    let re_hello = mk_str_to_re(&mut terms, "hello");
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![x, re_hello], Sort::Bool);
    let eq_x_goodbye = terms.mk_eq(x, goodbye);
    let eq_y_unrelated = terms.mk_eq(y, unrelated);

    let mut state = SolverState::new();
    // Include an unrelated fact to ensure regex conflicts stay targeted.
    state.assert_literal(&terms, eq_y_unrelated, true);
    state.assert_literal(&terms, in_re, true);
    state.assert_literal(&terms, eq_x_goodbye, true);
    state.register_term(&terms, x);
    state.register_term(&terms, goodbye);
    let _ = state.merge(x, goodbye, TheoryLit::new(eq_x_goodbye, true));

    let mut infer = InferenceManager::new();
    let mut solver = RegExpSolver::new();
    let conflict = solver.check(&terms, &state, &mut infer);
    assert!(
        conflict,
        "x=\"goodbye\" does not satisfy str.in_re(x, \"hello\")"
    );

    let in_re_lit = TheoryLit::new(in_re, true);
    let eq_lit = TheoryLit::new(eq_x_goodbye, true);
    let unrelated_lit = TheoryLit::new(eq_y_unrelated, true);
    match infer.to_theory_result() {
        TheoryResult::Unsat(lits) => {
            assert!(
                lits.contains(&in_re_lit),
                "must include membership assertion"
            );
            assert!(
                lits.contains(&eq_lit),
                "must include x=\"goodbye\" assertion"
            );
            assert!(
                !lits.contains(&unrelated_lit),
                "must not include unrelated assertion in regex conflict explanation"
            );
            assert!(
                lits.len() <= 3,
                "targeted regex explanation unexpectedly large: {lits:?}"
            );
        }
        other => panic!("expected Unsat conflict, got {other:?}"),
    }
}

#[test]
fn check_unresolved_string_marks_incomplete() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let a = mk_str_to_re(&mut terms, "a");
    let star = mk_re_star(&mut terms, a);
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![x, star], Sort::Bool);

    let mut state = SolverState::new();
    state.assert_literal(&terms, in_re, true);
    state.register_term(&terms, x);

    let mut infer = InferenceManager::new();
    let mut solver = RegExpSolver::new();
    let conflict = solver.check(&terms, &state, &mut infer);

    assert!(!conflict, "unresolved string should not conflict");
    assert!(
        solver.is_incomplete(),
        "unresolved string should mark incomplete"
    );
}

// ── re.loop tests ─────────────────────────────────────────────────

#[test]
fn eval_loop_exact_match() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_loop(&mut terms, a, 3, 3);
    assert_eq!(RegExpSolver::evaluate(&terms, "aaa", r), Some(true));
}

#[test]
fn eval_loop_too_few() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_loop(&mut terms, a, 2, 5);
    assert_eq!(RegExpSolver::evaluate(&terms, "a", r), Some(false));
}

#[test]
fn eval_loop_too_many() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_loop(&mut terms, a, 2, 3);
    assert_eq!(RegExpSolver::evaluate(&terms, "aaaa", r), Some(false));
}

#[test]
fn eval_loop_zero_min_empty() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_loop(&mut terms, a, 0, 3);
    assert_eq!(RegExpSolver::evaluate(&terms, "", r), Some(true));
}

#[test]
fn eval_loop_multi_char_pattern() {
    let mut terms = TermStore::new();
    let ab = mk_str_to_re(&mut terms, "ab");
    let r = mk_re_loop(&mut terms, ab, 2, 4);
    assert_eq!(RegExpSolver::evaluate(&terms, "abab", r), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "ababab", r), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "ab", r), Some(false));
}

#[test]
fn eval_loop_lo_gt_hi_is_false() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_loop(&mut terms, a, 5, 2);
    assert_eq!(RegExpSolver::evaluate(&terms, "aaa", r), Some(false));
}

#[test]
fn delta_re_loop_zero_min_is_nullable() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_loop(&mut terms, a, 0, 5);
    assert_eq!(RegExpSolver::delta(&terms, r), Some(true));
}

#[test]
fn delta_re_loop_nonzero_min_nonempty_is_not_nullable() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_loop(&mut terms, a, 1, 5);
    assert_eq!(RegExpSolver::delta(&terms, r), Some(false));
}

#[test]
fn delta_re_loop_nonzero_min_nullable_inner() {
    let mut terms = TermStore::new();
    let empty = mk_str_to_re(&mut terms, "");
    let r = mk_re_loop(&mut terms, empty, 2, 5);
    assert_eq!(RegExpSolver::delta(&terms, r), Some(true));
}

// ── find_first_match tests ──────────────────────────────────────────

#[test]
fn find_first_match_literal_at_start() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "ab");
    match RegExpSolver::find_first_match(&terms, "abcdef", r) {
        MatchResult::Found(start, end) => {
            assert_eq!(start, 0);
            assert_eq!(end, 2);
        }
        other => panic!("expected Found, got {other:?}"),
    }
}

#[test]
fn find_first_match_literal_in_middle() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "cd");
    match RegExpSolver::find_first_match(&terms, "abcdef", r) {
        MatchResult::Found(start, end) => {
            assert_eq!(start, 2);
            assert_eq!(end, 4);
        }
        other => panic!("expected Found, got {other:?}"),
    }
}

#[test]
fn find_first_match_no_match() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "xyz");
    assert!(matches!(
        RegExpSolver::find_first_match(&terms, "abcdef", r),
        MatchResult::NoMatch
    ));
}

#[test]
fn find_first_match_empty_regex_matches_at_start() {
    let mut terms = TermStore::new();
    // str.to_re("") matches the empty string at every position.
    // Leftmost shortest → position 0, length 0.
    let r = mk_str_to_re(&mut terms, "");
    match RegExpSolver::find_first_match(&terms, "abc", r) {
        MatchResult::Found(start, end) => {
            assert_eq!(start, 0);
            assert_eq!(end, 0);
        }
        other => panic!("expected Found(0,0), got {other:?}"),
    }
}

#[test]
fn find_first_match_re_none_no_match() {
    let mut terms = TermStore::new();
    let r = mk_re_none(&mut terms);
    assert!(matches!(
        RegExpSolver::find_first_match(&terms, "abc", r),
        MatchResult::NoMatch
    ));
}

#[test]
fn find_first_match_union_picks_shortest() {
    let mut terms = TermStore::new();
    // re.union(str.to_re("a"), str.to_re("ab"))
    // In "xab", leftmost match starts at 1. Shortest at that position is "a".
    let a = mk_str_to_re(&mut terms, "a");
    let ab = mk_str_to_re(&mut terms, "ab");
    let r = mk_re_union(&mut terms, vec![a, ab]);
    match RegExpSolver::find_first_match(&terms, "xab", r) {
        MatchResult::Found(start, end) => {
            assert_eq!(start, 1);
            assert_eq!(end, 2); // "a" (1 byte)
        }
        other => panic!("expected Found, got {other:?}"),
    }
}

#[test]
fn find_first_match_re_star_matches_empty() {
    let mut terms = TermStore::new();
    // re.*(str.to_re("a")) matches "" at position 0 (shortest).
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_star(&mut terms, a);
    match RegExpSolver::find_first_match(&terms, "bbb", r) {
        MatchResult::Found(start, end) => {
            assert_eq!(start, 0);
            assert_eq!(end, 0);
        }
        other => panic!("expected Found(0,0), got {other:?}"),
    }
}

#[test]
fn find_first_match_range_digit() {
    let mut terms = TermStore::new();
    let r = mk_re_range(&mut terms, "0", "9");
    match RegExpSolver::find_first_match(&terms, "abc5def", r) {
        MatchResult::Found(start, end) => {
            assert_eq!(start, 3);
            assert_eq!(end, 4);
        }
        other => panic!("expected Found, got {other:?}"),
    }
}

#[test]
fn find_first_match_empty_string_empty_regex() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "");
    match RegExpSolver::find_first_match(&terms, "", r) {
        MatchResult::Found(start, end) => {
            assert_eq!(start, 0);
            assert_eq!(end, 0);
        }
        other => panic!("expected Found(0,0), got {other:?}"),
    }
}

#[test]
fn find_first_match_empty_string_nonempty_regex() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "a");
    assert!(matches!(
        RegExpSolver::find_first_match(&terms, "", r),
        MatchResult::NoMatch
    ));
}

// ── accepted_lengths tests (regex length-set disjointness) ──────────
//
// SOUNDNESS CONTRACT: `accepted_lengths(r) = Some(L)` means L is the EXACT set
// of lengths of strings R accepts. `None` means "unbounded / unknown — no info".
// Every assertion below pins down both the FINITE cases (where a refutation may
// fire) and the INFINITE cases (where it must NOT, i.e. returns None).

use std::collections::BTreeSet;

fn lenset(v: &[usize]) -> BTreeSet<usize> {
    v.iter().copied().collect()
}

#[test]
fn accepted_lengths_to_re_const() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "hello");
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, r),
        Some(lenset(&[5]))
    );
}

#[test]
fn accepted_lengths_to_re_empty_is_zero() {
    let mut terms = TermStore::new();
    let r = mk_str_to_re(&mut terms, "");
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, r),
        Some(lenset(&[0]))
    );
}

#[test]
fn accepted_lengths_union_of_consts() {
    // (re.union "ab" "cd") accepts exactly length 2 — the X2 case.
    let mut terms = TermStore::new();
    let ab = mk_str_to_re(&mut terms, "ab");
    let cd = mk_str_to_re(&mut terms, "cd");
    let r = mk_re_union(&mut terms, vec![ab, cd]);
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, r),
        Some(lenset(&[2]))
    );
}

#[test]
fn accepted_lengths_union_distinct_lengths() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let bcd = mk_str_to_re(&mut terms, "bcd");
    let r = mk_re_union(&mut terms, vec![a, bcd]);
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, r),
        Some(lenset(&[1, 3]))
    );
}

#[test]
fn accepted_lengths_concat_of_consts_is_sum() {
    // (re.++ "ab" "cd") accepts exactly length 4.
    let mut terms = TermStore::new();
    let ab = mk_str_to_re(&mut terms, "ab");
    let cd = mk_str_to_re(&mut terms, "cd");
    let r = mk_re_concat(&mut terms, vec![ab, cd]);
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, r),
        Some(lenset(&[4]))
    );
}

#[test]
fn accepted_lengths_concat_minkowski_sum() {
    // (re.++ (union "a" "bb") (union "c" "dd")) → lengths {1,2} ⊕ {1,2} = {2,3,4}.
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let bb = mk_str_to_re(&mut terms, "bb");
    let left = mk_re_union(&mut terms, vec![a, bb]);
    let c = mk_str_to_re(&mut terms, "c");
    let dd = mk_str_to_re(&mut terms, "dd");
    let right = mk_re_union(&mut terms, vec![c, dd]);
    let r = mk_re_concat(&mut terms, vec![left, right]);
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, r),
        Some(lenset(&[2, 3, 4]))
    );
}

#[test]
fn accepted_lengths_allchar_is_one() {
    let mut terms = TermStore::new();
    let r = mk_re_allchar(&mut terms);
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, r),
        Some(lenset(&[1]))
    );
}

#[test]
fn accepted_lengths_range_is_one() {
    let mut terms = TermStore::new();
    let r = mk_re_range(&mut terms, "a", "z");
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, r),
        Some(lenset(&[1]))
    );
}

#[test]
fn accepted_lengths_range_empty_when_reversed() {
    // lo > hi → empty language → empty length set.
    let mut terms = TermStore::new();
    let r = mk_re_range(&mut terms, "z", "a");
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, r),
        Some(BTreeSet::new())
    );
}

#[test]
fn accepted_lengths_range_empty_when_multichar_endpoint() {
    // Non-singleton endpoint(s) → empty language → empty length set (NOT {1}).
    let mut terms = TermStore::new();
    let multi = mk_re_range(&mut terms, "ab", "cd");
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, multi),
        Some(BTreeSet::new())
    );
    let one_bad = mk_re_range(&mut terms, "ab", "x");
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, one_bad),
        Some(BTreeSet::new())
    );
    let empty_lo = mk_re_range(&mut terms, "", "a");
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, empty_lo),
        Some(BTreeSet::new())
    );
}

#[test]
fn accepted_lengths_opt_adds_zero() {
    // (re.opt "ab") → {0, 2}.
    let mut terms = TermStore::new();
    let ab = mk_str_to_re(&mut terms, "ab");
    let r = mk_re_opt(&mut terms, ab);
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, r),
        Some(lenset(&[0, 2]))
    );
}

#[test]
fn accepted_lengths_none_is_empty() {
    let mut terms = TermStore::new();
    let r = mk_re_none(&mut terms);
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, r),
        Some(BTreeSet::new())
    );
}

#[test]
fn accepted_lengths_loop_range() {
    // (_ re.loop 2 3) allchar → {2, 3}.
    let mut terms = TermStore::new();
    let ch = mk_re_allchar(&mut terms);
    let r = mk_re_loop(&mut terms, ch, 2, 3);
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, r),
        Some(lenset(&[2, 3]))
    );
}

#[test]
fn accepted_lengths_loop_zero_lo_includes_empty() {
    // (_ re.loop 0 2) "ab" → {0, 2, 4}.
    let mut terms = TermStore::new();
    let ab = mk_str_to_re(&mut terms, "ab");
    let r = mk_re_loop(&mut terms, ab, 0, 2);
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, r),
        Some(lenset(&[0, 2, 4]))
    );
}

#[test]
fn accepted_lengths_loop_huge_zero_length_body_is_constant_time() {
    // Repeating an epsilon-only body any number of times still has exactly
    // length zero. Preserve this exact fold without walking the untrusted
    // upper bound.
    let mut terms = TermStore::new();
    let epsilon = mk_str_to_re(&mut terms, "");
    let r = mk_re_loop(&mut terms, epsilon, 0, u32::MAX);
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, r),
        Some(lenset(&[0]))
    );
}

#[test]
fn accepted_lengths_loop_huge_nonzero_body_fails_closed() {
    // A constant-size regex must not trigger 2^32 exact-length iterations.
    // `None` means callers learn no length fact, so this is fail-closed.
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_loop(&mut terms, a, 0, u32::MAX);
    assert_eq!(RegExpSolver::accepted_lengths(&terms, r), None);
}

#[test]
fn accepted_lengths_inter_intersects() {
    // (re.inter (union "ab" "cd") (++ allchar allchar)) → {2} ∩ {2} = {2}.
    let mut terms = TermStore::new();
    let ab = mk_str_to_re(&mut terms, "ab");
    let cd = mk_str_to_re(&mut terms, "cd");
    let u = mk_re_union(&mut terms, vec![ab, cd]);
    let a1 = mk_re_allchar(&mut terms);
    let a2 = mk_re_allchar(&mut terms);
    let cc = mk_re_concat(&mut terms, vec![a1, a2]);
    let r = mk_re_inter(&mut terms, vec![u, cc]);
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, r),
        Some(lenset(&[2]))
    );
}

// ── INFINITE-LANGUAGE cases: MUST return None (no refutation may fire) ──

#[test]
fn accepted_lengths_star_is_none() {
    // (re.* "ab") accepts unbounded even lengths — not finitely characterized.
    let mut terms = TermStore::new();
    let ab = mk_str_to_re(&mut terms, "ab");
    let r = mk_re_star(&mut terms, ab);
    assert_eq!(RegExpSolver::accepted_lengths(&terms, r), None);
}

#[test]
fn accepted_lengths_plus_is_none() {
    let mut terms = TermStore::new();
    let ab = mk_str_to_re(&mut terms, "ab");
    let r = mk_re_plus(&mut terms, ab);
    assert_eq!(RegExpSolver::accepted_lengths(&terms, r), None);
}

#[test]
fn accepted_lengths_all_is_none() {
    let mut terms = TermStore::new();
    let r = mk_re_all(&mut terms);
    assert_eq!(RegExpSolver::accepted_lengths(&terms, r), None);
}

#[test]
fn accepted_lengths_comp_is_none() {
    // Complement of a finite-length regex is generally infinite → None.
    let mut terms = TermStore::new();
    let ab = mk_str_to_re(&mut terms, "ab");
    let r = mk_re_comp(&mut terms, ab);
    assert_eq!(RegExpSolver::accepted_lengths(&terms, r), None);
}

#[test]
fn accepted_lengths_union_with_star_is_none() {
    // ANY infinite branch makes the union's length set None — the S9 soundness
    // case: must NOT return a finite set, else a length-disjoint refutation
    // could wrongly fire on a SAT instance.
    let mut terms = TermStore::new();
    let ab = mk_str_to_re(&mut terms, "ab");
    let ch = mk_re_allchar(&mut terms);
    let star = mk_re_star(&mut terms, ch);
    let r = mk_re_union(&mut terms, vec![ab, star]);
    assert_eq!(RegExpSolver::accepted_lengths(&terms, r), None);
}

#[test]
fn accepted_lengths_concat_with_star_is_none() {
    let mut terms = TermStore::new();
    let ab = mk_str_to_re(&mut terms, "ab");
    let ch = mk_re_allchar(&mut terms);
    let star = mk_re_star(&mut terms, ch);
    let r = mk_re_concat(&mut terms, vec![ab, star]);
    assert_eq!(RegExpSolver::accepted_lengths(&terms, r), None);
}

#[test]
fn accepted_lengths_diff_subset_of_lhs() {
    // (re.diff (union "ab" "cd") "ab") ⊆ lengths("ab"|"cd") = {2}. A necessary
    // condition on length — sound (may keep a length actually removed by RHS,
    // but never adds one outside the LHS).
    let mut terms = TermStore::new();
    let ab = mk_str_to_re(&mut terms, "ab");
    let cd = mk_str_to_re(&mut terms, "cd");
    let u = mk_re_union(&mut terms, vec![ab, cd]);
    let ab2 = mk_str_to_re(&mut terms, "ab");
    let r = mk_re_diff(&mut terms, u, ab2);
    assert_eq!(
        RegExpSolver::accepted_lengths(&terms, r),
        Some(lenset(&[2]))
    );
}

// ── `(_ re.loop lo hi)` with `lo > hi` is the EMPTY language ───────
//
// SMT-LIB 2.6: `((_ re.loop i n) e)` denotes `⋃_{k=i}^{n} L(e)^k`. When
// `i > n` the index set is empty, so the regex denotes the empty language —
// which is NOT nullable and matches nothing at all. `evaluate`,
// `accepted_lengths` and `WeRegex::loop_bounded` always folded this; `delta`
// (nullability) did NOT, and answered "yes, `\"\"` matches" for the empty
// language. Found by `crates/ay-proof/tests/string_ground_diff_fuzz.rs`
// (#regex-loop-degenerate-bounds); the end-to-end symptom was a WRONG-UNSAT on
// `(not (str.in_re "" (re.+ ((_ re.loop 4 3) (re.* re.allchar)))))`, which is
// satisfiable.

#[test]
fn degenerate_loop_bounds_are_not_nullable() {
    let mut terms = TermStore::new();
    let ch = mk_re_allchar(&mut terms);
    let star = mk_re_star(&mut terms, ch);
    let degenerate = mk_re_loop(&mut terms, star, 4, 3);
    assert_eq!(
        RegExpSolver::is_nullable(&terms, degenerate),
        Some(false),
        "((_ re.loop 4 3) R) is the EMPTY language and cannot contain \"\""
    );
    assert_eq!(RegExpSolver::evaluate(&terms, "", degenerate), Some(false));
    assert_eq!(RegExpSolver::evaluate(&terms, "a", degenerate), Some(false));
}

#[test]
fn plus_over_degenerate_loop_rejects_empty_string() {
    // The exact wrong-UNSAT shape: `re.+` over the empty language is empty.
    let mut terms = TermStore::new();
    let ch = mk_re_allchar(&mut terms);
    let star = mk_re_star(&mut terms, ch);
    let degenerate = mk_re_loop(&mut terms, star, 4, 3);
    let plus = mk_re_plus(&mut terms, degenerate);
    assert_eq!(RegExpSolver::evaluate(&terms, "", plus), Some(false));
}

#[test]
fn complement_of_degenerate_loop_is_nullable() {
    // `(re.comp ((_ re.loop 4 2) R))` = `¬∅` = `Σ*`, which DOES contain "".
    // Reporting it non-nullable would give the core solver a bogus `|x| > 0`.
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let degenerate = mk_re_loop(&mut terms, a, 4, 2);
    let comp = mk_re_comp(&mut terms, degenerate);
    assert_eq!(RegExpSolver::is_nullable(&terms, comp), Some(true));
    assert_eq!(RegExpSolver::evaluate(&terms, "", comp), Some(true));
}

// ── `str.substr` with an out-of-`usize` length ─────────────────────
//
// SMT-LIB 2.6: `(str.substr s m n)` is the unique `w` with `s = u·w·v`,
// `|u| = m`, `|w| = min(n, |s| - m)` when `0 <= m < |s|` and `0 < n`. `n` only
// CLAMPS, so an astronomically large `n` selects the whole suffix. The shared
// evaluator used to answer `None` ("unevaluable"), and the DPLL copy computed
// `start + len` unguarded — `(str.substr "abc" 1 18446744073709551615)`
// panicked with "attempt to add with overflow", losing an `unsat`
// (#string-substr-length-overflow).

#[test]
fn substr_with_out_of_usize_length_selects_the_whole_suffix() {
    use num_bigint::BigInt;
    let huge = BigInt::from(u64::MAX) * BigInt::from(u64::MAX);
    assert_eq!(
        crate::eval::eval_str_substr("abc", &BigInt::from(1), &huge),
        Some("bc".to_string())
    );
    assert_eq!(
        crate::eval::eval_str_substr("abc", &BigInt::from(1), &BigInt::from(usize::MAX)),
        Some("bc".to_string())
    );
    // An out-of-`usize` START is necessarily past the end: "".
    assert_eq!(
        crate::eval::eval_str_substr("abc", &huge, &BigInt::from(2)),
        Some(String::new())
    );
    assert_eq!(crate::eval::eval_str_at("abc", &huge), Some(String::new()));
    assert_eq!(
        crate::eval::eval_str_indexof("abc", "b", &huge),
        Some(BigInt::from(-1))
    );
}
// ── Derivative fast path + memoised fallback ───────────────────────
//
// The exact shared translation is checked against the prior recursive
// evaluator as a specification. Separate fallback tests keep pinning the memo
// itself: if translation or derivative limits decline, recursive descent must
// still terminate without changing an answer.

#[test]
fn derivative_translation_matches_recursive_fallback_spec() {
    let mut terms = TermStore::new();

    let none = mk_re_none(&mut terms);
    let all = mk_re_all(&mut terms);
    let allchar = mk_re_allchar(&mut terms);
    let range = mk_re_range(&mut terms, "a", "z");
    let reversed_range = mk_re_range(&mut terms, "z", "a");
    let malformed_range = mk_re_range(&mut terms, "ab", "z");
    let empty = mk_str_to_re(&mut terms, "");
    let a = mk_str_to_re(&mut terms, "a");
    let ab = mk_str_to_re(&mut terms, "ab");
    let unicode = mk_str_to_re(&mut terms, "éλ");
    let concat = mk_re_concat(&mut terms, vec![a, allchar]);
    let union = mk_re_union(&mut terms, vec![ab, range]);
    let inter = mk_re_inter(&mut terms, vec![all, union]);
    let star = mk_re_star(&mut terms, union);
    let plus = mk_re_plus(&mut terms, empty);
    let opt = mk_re_opt(&mut terms, ab);
    let comp = mk_re_comp(&mut terms, range);
    let diff = mk_re_diff(&mut terms, all, ab);
    let loop_small = mk_re_loop(&mut terms, opt, 2, 4);
    let loop_counter = mk_re_loop(&mut terms, a, 13, 20);
    let loop_degenerate = mk_re_loop(&mut terms, star, 4, 3);
    let comp_degenerate = mk_re_comp(&mut terms, loop_degenerate);

    let regexes = [
        none,
        all,
        allchar,
        range,
        reversed_range,
        malformed_range,
        empty,
        a,
        ab,
        unicode,
        concat,
        union,
        inter,
        star,
        plus,
        opt,
        comp,
        diff,
        loop_small,
        loop_counter,
        loop_degenerate,
        comp_degenerate,
    ];
    let subjects = ["", "a", "b", "ab", "aa", "az", "é", "éλ", "λé"];

    for regex in regexes {
        for subject in subjects {
            let mut budget = RegexWorkBudget::unlimited();
            let derivative =
                RegExpSolver::evaluate_derivative_with_budget(&terms, subject, regex, &mut budget);
            let fallback = RegExpSolver::evaluate_fallback(&terms, subject, regex);
            assert!(!budget.exhausted, "unlimited derivative budget exhausted");
            assert!(
                derivative.is_some(),
                "representative term failed exact translation: regex={regex:?}, subject={subject:?}"
            );
            assert_eq!(
                derivative, fallback,
                "derivative/fallback disagreement: regex={regex:?}, subject={subject:?}"
            );
        }
    }
}

#[test]
fn derivative_translation_limit_falls_back_without_losing_a_decision() {
    let mut terms = TermStore::new();
    let subject = "a".repeat(8 * 4096 + 8);
    let regex = mk_str_to_re(&mut terms, &subject);
    let mut budget = RegexWorkBudget::unlimited();

    assert_eq!(
        RegExpSolver::evaluate_derivative_with_budget(&terms, &subject, regex, &mut budget),
        None,
        "oversized exact translation must decline"
    );
    assert_eq!(
        RegExpSolver::evaluate_fallback(&terms, &subject, regex),
        Some(true)
    );
    assert_eq!(RegExpSolver::evaluate(&terms, &subject, regex), Some(true));
}

#[test]
fn derivative_transient_expansion_is_preflighted_before_fallback() {
    let mut terms = TermStore::new();
    let allchar = mk_re_allchar(&mut terms);
    let optional = mk_re_opt(&mut terms, allchar);
    let regex = mk_re_concat(&mut terms, vec![optional; 80]);
    let mut budget = RegexWorkBudget::unlimited();

    // Deriving a concat of nullable children clones and derives every suffix.
    // Its retained regex is small, but the candidate implementation could
    // transiently construct a quadratic number of nodes before checking size.
    assert_eq!(
        RegExpSolver::evaluate_derivative_with_budget(&terms, "x", regex, &mut budget),
        None,
        "transient expansion above the structural cap must decline pre-allocation"
    );
    assert!(!budget.exhausted);
    assert_eq!(
        RegExpSolver::evaluate_fallback(&terms, "x", regex),
        Some(true)
    );
    assert_eq!(RegExpSolver::evaluate(&terms, "x", regex), Some(true));
}

#[test]
fn derivative_preflight_traversal_obeys_a_tiny_work_budget() {
    let mut terms = TermStore::new();
    let allchar = mk_re_allchar(&mut terms);
    let optional = mk_re_opt(&mut terms, allchar);
    let term = mk_re_concat(&mut terms, vec![optional; 80]);
    let regex = crate::term_regex::translate(
        &terms,
        term,
        &crate::term_regex::TranslateLimits::for_ground_eval(),
    )
    .expect("wide nullable concat translates within the retained-size cap");

    let before = crate::regex_eval_work();
    let mut budget = RegexWorkBudget::limited(1);
    assert_eq!(
        derivative_transient_bound(&regex, 4096, &mut budget),
        None,
        "preflight must stop before traversing a wide nullable concat"
    );
    assert!(budget.exhausted);
    assert_eq!(crate::regex_eval_work().saturating_sub(before), 1);
}

#[test]
fn derivative_fast_path_obeys_the_in_evaluator_work_budget() {
    let mut terms = TermStore::new();
    let regex = mk_str_to_re(&mut terms, "abcdefgh");
    let before = crate::regex_eval_work();
    assert_eq!(
        RegExpSolver::evaluate(&terms, "abcdefgh", regex),
        Some(true)
    );
    let exact_work = crate::regex_eval_work().saturating_sub(before);
    assert!(
        exact_work > 1,
        "translation and derivatives must be charged"
    );

    assert_eq!(
        RegExpSolver::evaluate_with_work_limit(&terms, "abcdefgh", regex, exact_work - 1),
        Err(RegexWorkLimitExceeded)
    );
    assert_eq!(
        RegExpSolver::evaluate_with_work_limit(&terms, "abcdefgh", regex, exact_work),
        Ok(Some(true))
    );
}

#[test]
fn shared_translation_preserves_multi_witness_enumeration() {
    use crate::we_regex::{find_witnesses_bounded, WeRegex};

    let mut terms = TermStore::new();
    let b = mk_str_to_re(&mut terms, "b");
    let a = mk_str_to_re(&mut terms, "a");
    let c = mk_str_to_re(&mut terms, "c");
    let term = mk_re_union(&mut terms, vec![b, a, c]);
    let translated = crate::term_regex::translate(
        &terms,
        term,
        &crate::term_regex::TranslateLimits::for_ground_eval(),
    )
    .expect("ground union translates exactly");
    let direct = WeRegex::union(vec![
        WeRegex::lit("b"),
        WeRegex::lit("a"),
        WeRegex::lit("c"),
    ]);

    assert_eq!(
        find_witnesses_bounded(&[translated], None, 2, 3),
        find_witnesses_bounded(&[direct], None, 2, 3),
        "centralizing translation must not perturb W7 witness order or count"
    );
}

#[test]
fn shared_translation_is_exact_or_bail_at_policy_boundaries() {
    use crate::term_regex::{translate, TranslateLimits};
    use crate::we_regex::WeRegex;

    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let large_loop = mk_re_loop(&mut terms, a, 13, 20);
    let limits = TranslateLimits {
        max_size: 64,
        max_loop: 12,
        bounded_loop_node: false,
        max_depth: 32,
    };
    assert_eq!(
        translate(&terms, large_loop, &limits),
        None,
        "a disallowed exact loop representation must bail, not approximate"
    );

    let x = terms.mk_var("x", Sort::String);
    let non_ground = terms.mk_app(Symbol::named("str.to_re"), vec![x], Sort::RegLan);
    assert_eq!(translate(&terms, non_ground, &limits), None);

    // Preserve 54a8518a: lo > hi denotes the empty language without needing
    // to inspect the body, even when that body is non-ground.
    let degenerate = mk_re_loop(&mut terms, non_ground, 4, 3);
    assert_eq!(translate(&terms, degenerate, &limits), Some(WeRegex::None));

    let b = mk_str_to_re(&mut terms, "b");
    let c = mk_str_to_re(&mut terms, "c");
    let wide = mk_re_union(&mut terms, vec![a, b, c]);
    let narrow_limits = TranslateLimits {
        max_size: 2,
        max_loop: 8,
        bounded_loop_node: false,
        max_depth: 32,
    };
    assert_eq!(
        translate(&terms, wide, &narrow_limits),
        None,
        "source arity beyond the size policy must bail before reserving"
    );
    let epsilon = mk_str_to_re(&mut terms, "");
    let over_capacity_loop = mk_re_loop(&mut terms, epsilon, 0, 3);
    assert_eq!(
        translate(&terms, over_capacity_loop, &narrow_limits),
        None,
        "loop unrolling beyond the size policy must bail before reserving"
    );
}

/// `(a*)*` against a long all-`a` string that the trailing literal rejects —
/// the textbook exponential blow-up. Unmemoised this does not terminate in any
/// reasonable time; memoised it is instant and correctly `false`.
#[test]
fn nested_star_no_match_terminates() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let inner = mk_re_star(&mut terms, a);
    let outer = mk_re_star(&mut terms, inner);
    let b = mk_str_to_re(&mut terms, "b");
    let r = mk_re_concat(&mut terms, vec![outer, b]);
    let s = "a".repeat(40);
    assert_eq!(RegExpSolver::evaluate_fallback(&terms, &s, r), Some(false));
    let mut yes = s.clone();
    yes.push('b');
    assert_eq!(RegExpSolver::evaluate_fallback(&terms, &yes, r), Some(true));
}

/// `(a|aa)*` — every prefix has two decompositions, so the split tree is
/// exponential in |s| without a memo. The answer is `true` either way.
#[test]
fn ambiguous_star_alternation_terminates() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let aa = mk_str_to_re(&mut terms, "aa");
    let u = mk_re_union(&mut terms, vec![a, aa]);
    let r = mk_re_star(&mut terms, u);
    assert_eq!(
        RegExpSolver::evaluate_fallback(&terms, &"a".repeat(48), r),
        Some(true)
    );
}

/// A chain of `(re.opt allchar)` concatenations: each child may consume 0 or 1
/// characters, so the concat split loop branches at every position. Pins that
/// the `eval_concat` memo is keyed by `(node, idx, substring)` — a wrong key
/// would return one child's verdict for another and flip these answers.
#[test]
fn optional_chain_concat_lengths_are_exact() {
    let mut terms = TermStore::new();
    let ch = mk_re_allchar(&mut terms);
    let opt = mk_re_opt(&mut terms, ch);
    let lit = mk_str_to_re(&mut terms, "z");
    let mut children: Vec<TermId> = (0..12).map(|_| opt).collect();
    children.push(lit);
    let r = mk_re_concat(&mut terms, children);
    // Up to 12 optional characters, then a mandatory "z".
    assert_eq!(RegExpSolver::evaluate_fallback(&terms, "z", r), Some(true));
    assert_eq!(
        RegExpSolver::evaluate_fallback(&terms, &format!("{}z", "x".repeat(12)), r),
        Some(true)
    );
    assert_eq!(
        RegExpSolver::evaluate_fallback(&terms, &format!("{}z", "x".repeat(13)), r),
        Some(false)
    );
    assert_eq!(RegExpSolver::evaluate_fallback(&terms, "x", r), Some(false));
}

/// `((_ re.loop 2 4) (re.opt allchar))` — the loop memo key must carry `lo`
/// and `hi`, not just the body: the same `(body, substring)` pair has
/// different answers at different remaining-iteration counts.
#[test]
fn loop_memo_key_distinguishes_bounds() {
    let mut terms = TermStore::new();
    let ch = mk_re_allchar(&mut terms);
    let opt = mk_re_opt(&mut terms, ch);
    let r24 = terms.mk_app(
        Symbol::indexed("re.loop", vec![2, 4]),
        vec![opt],
        Sort::RegLan,
    );
    let r22 = terms.mk_app(
        Symbol::indexed("re.loop", vec![2, 2]),
        vec![opt],
        Sort::RegLan,
    );
    // 2..4 iterations of an optional char accept "", "x", "xx", "xxx", "xxxx".
    assert_eq!(
        RegExpSolver::evaluate_fallback(&terms, "xxxx", r24),
        Some(true)
    );
    assert_eq!(
        RegExpSolver::evaluate_fallback(&terms, "xxxxx", r24),
        Some(false)
    );
    // Exactly 2 iterations cannot reach 3 characters.
    assert_eq!(
        RegExpSolver::evaluate_fallback(&terms, "xx", r22),
        Some(true)
    );
    assert_eq!(
        RegExpSolver::evaluate_fallback(&terms, "xxx", r22),
        Some(false)
    );
}

/// The work counter is monotone and actually charged by an evaluation.
#[test]
fn regex_eval_work_counter_advances() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_star(&mut terms, a);
    let before = crate::regex_eval_work();
    assert_eq!(RegExpSolver::evaluate(&terms, "aaaa", r), Some(true));
    assert!(crate::regex_eval_work() > before);
}

/// A shared nullable DAG must be charged on every consultation but computed
/// once per distinct delta node. Without the delta memo this shape is
/// exponential; with it the exact cost is `2 * depth + 2` (top Eval, each
/// intersection miss + shared-child hit, and the leaf).
#[test]
fn bounded_nullable_shared_dag_is_memoised_and_exact() {
    const DEPTH: u64 = 24;
    let mut terms = TermStore::new();
    let mut body = mk_str_to_re(&mut terms, "");
    for _ in 0..DEPTH {
        body = mk_re_inter(&mut terms, vec![body, body]);
    }
    let plus = mk_re_plus(&mut terms, body);
    let exact = 2 * DEPTH + 2;

    assert_eq!(
        RegExpSolver::evaluate_fallback_with_work_limit(&terms, "", plus, exact - 1),
        Err(RegexWorkLimitExceeded)
    );
    assert_eq!(
        RegExpSolver::evaluate_fallback_with_work_limit(&terms, "", plus, exact),
        Ok(Some(true))
    );
}

/// A new miss at the memo cap fails closed before uncached recursive work can
/// restore catastrophic backtracking. This uses a zero-entry cap so the
/// regression is exercised without allocating the production million-entry
/// table.
#[test]
fn memo_cap_fails_closed_before_uncached_work() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_star(&mut terms, a);
    let mut budget = RegexWorkBudget::limited_with_memo_cap(4, 0);
    let before = crate::regex_eval_work();

    assert_eq!(
        RegExpSolver::evaluate_fallback_with_budget(&terms, "aaaa", r, &mut budget),
        None
    );
    assert_eq!(crate::regex_eval_work().saturating_sub(before), 1);
}

/// All substring probes in replace, and all repeated searches in replace-all,
/// consume one operation-wide budget instead of receiving fresh caps.
#[test]
fn bounded_regex_replacements_share_the_whole_operation_budget() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");

    let before_replace = crate::regex_eval_work();
    assert_eq!(
        crate::ground_eval_replace_re(&terms, "bbb", a, "x"),
        Some("bbb".to_string())
    );
    let replace_work = crate::regex_eval_work().saturating_sub(before_replace);
    assert!(replace_work > 1);
    assert_eq!(
        crate::ground_eval_replace_re_with_work_limit(&terms, "bbb", a, "x", replace_work - 1),
        Err(RegexWorkLimitExceeded)
    );
    assert_eq!(
        crate::ground_eval_replace_re_with_work_limit(&terms, "bbb", a, "x", replace_work),
        Ok(Some("bbb".to_string()))
    );

    let before_replace_all = crate::regex_eval_work();
    assert_eq!(
        crate::ground_eval_replace_re_all(&terms, "aaaa", a, "x"),
        Some("xxxx".to_string())
    );
    let replace_all_work = crate::regex_eval_work().saturating_sub(before_replace_all);
    assert!(replace_all_work > 1);
    assert_eq!(
        crate::ground_eval_replace_re_all_with_work_limit(
            &terms,
            "aaaa",
            a,
            "x",
            replace_all_work - 1,
        ),
        Err(RegexWorkLimitExceeded)
    );
    assert_eq!(
        crate::ground_eval_replace_re_all_with_work_limit(&terms, "aaaa", a, "x", replace_all_work),
        Ok(Some("xxxx".to_string()))
    );
}

// ── str.replace_re_all with a NULLABLE regex (#strings-replace_re_all-nullable)
//
// SMT-LIB 2.6 Unicode Strings defines
//   (str.replace_re_all s r t) = s                                   if s has no
//     decomposition s = x ++ w ++ z with w in [[r]] and w != "";
//   (str.replace_re_all s r t) = x ++ t ++ (str.replace_re_all z r t) otherwise,
//     for the decomposition with |x| minimal and then |w| minimal.
//
// The `w != ""` side condition is what makes the recursion terminate; it does
// NOT disable the operator on a nullable regex. AY used the empty-match-eligible
// leftmost-shortest matcher here, so for every nullable r the match found was
// the empty word at position 0, no replacement ever fired, and the operator
// silently became the identity — a wrong verdict in BOTH directions.

#[test]
fn find_first_nonempty_match_skips_the_empty_match() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let star = mk_re_star(&mut terms, a);
    let mut budget = RegexWorkBudget::unlimited();

    // The empty-match-eligible matcher (used by str.replace_re, whose clause
    // has NO `w != ""` condition) still reports the empty match at 0.
    assert!(matches!(
        RegExpSolver::find_first_match(&terms, "bab", star),
        MatchResult::Found(0, 0)
    ));

    // The non-empty matcher (used by str.replace_re_all) must skip past it and
    // report the leftmost, then shortest, NON-EMPTY match: "a" at index 1.
    assert!(matches!(
        RegExpSolver::find_first_nonempty_match_with_budget(&terms, "bab", star, &mut budget),
        Ok(MatchResult::Found(1, 2))
    ));
}

#[test]
fn find_first_nonempty_match_is_leftmost_then_shortest() {
    let mut terms = TermStore::new();
    // re.union(str.to_re("ab"), str.to_re("a")) — both start at index 1 in "xab";
    // the shortest non-empty one is "a".
    let ab = mk_str_to_re(&mut terms, "ab");
    let a = mk_str_to_re(&mut terms, "a");
    let r = mk_re_union(&mut terms, vec![ab, a]);
    let mut budget = RegexWorkBudget::unlimited();
    assert!(matches!(
        RegExpSolver::find_first_nonempty_match_with_budget(&terms, "xab", r, &mut budget),
        Ok(MatchResult::Found(1, 2))
    ));
}

#[test]
fn find_first_nonempty_match_none_when_only_epsilon_is_in_the_language() {
    let mut terms = TermStore::new();
    // L(str.to_re("")) = {ε}: no non-empty match exists anywhere.
    let eps = mk_str_to_re(&mut terms, "");
    let mut budget = RegexWorkBudget::unlimited();
    assert!(matches!(
        RegExpSolver::find_first_nonempty_match_with_budget(&terms, "abc", eps, &mut budget),
        Ok(MatchResult::NoMatch)
    ));
}

#[test]
fn replace_re_all_nullable_re_all_replaces_every_character() {
    let mut terms = TermStore::new();
    let all = mk_re_all(&mut terms);
    // Shortest non-empty match of re.all is one character, everywhere.
    assert_eq!(
        crate::ground_eval_replace_re_all(&terms, "a", all, "b"),
        Some("b".to_string())
    );
    assert_eq!(
        crate::ground_eval_replace_re_all(&terms, "abc", all, "-"),
        Some("---".to_string())
    );
}

#[test]
fn replace_re_all_star_and_plus_agree() {
    // L(a*) and L(a+) differ only by ε, which the `w != ""` side condition
    // filters out, so the two terms are provably equal for every s and t.
    // AY used to answer "XXb" for re.+ and "aab" for re.* — a self-contradiction.
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let star = mk_re_star(&mut terms, a);
    let plus = mk_re_plus(&mut terms, a);
    for subject in ["aab", "", "b", "aaa", "baa", "bab"] {
        assert_eq!(
            crate::ground_eval_replace_re_all(&terms, subject, star, "X"),
            crate::ground_eval_replace_re_all(&terms, subject, plus, "X"),
            "re.* and re.+ disagree on {subject:?}"
        );
    }
    assert_eq!(
        crate::ground_eval_replace_re_all(&terms, "aab", star, "X"),
        Some("XXb".to_string())
    );
}

#[test]
fn replace_re_all_re_opt_is_not_the_identity() {
    let mut terms = TermStore::new();
    let a = mk_str_to_re(&mut terms, "a");
    let opt = mk_re_opt(&mut terms, a); // nullable: L = {ε, "a"}
    assert_eq!(
        crate::ground_eval_replace_re_all(&terms, "bab", opt, "Z"),
        Some("bZb".to_string())
    );
}

#[test]
fn replace_re_all_epsilon_only_regex_is_the_identity() {
    // Guards the earlier fix (#strings-replace_re_all): a regex whose only word
    // is ε must NOT insert the replacement anywhere. That was a false-UNSAT.
    let mut terms = TermStore::new();
    let eps = mk_str_to_re(&mut terms, "");
    assert_eq!(
        crate::ground_eval_replace_re_all(&terms, "abc", eps, "X"),
        Some("abc".to_string())
    );
    assert_eq!(
        crate::ground_eval_replace_re_all(&terms, "", eps, "X"),
        Some(String::new())
    );
}

#[test]
fn replace_re_all_empty_subject_is_the_identity() {
    // "" admits no decomposition with a non-empty middle, so it is its own image
    // under every regex — including nullable ones.
    let mut terms = TermStore::new();
    let all = mk_re_all(&mut terms);
    let a = mk_str_to_re(&mut terms, "a");
    let star = mk_re_star(&mut terms, a);
    assert_eq!(
        crate::ground_eval_replace_re_all(&terms, "", all, "X"),
        Some(String::new())
    );
    assert_eq!(
        crate::ground_eval_replace_re_all(&terms, "", star, "X"),
        Some(String::new())
    );
}

#[test]
fn replace_re_all_re_none_is_the_identity() {
    let mut terms = TermStore::new();
    let none = mk_re_none(&mut terms);
    assert_eq!(
        crate::ground_eval_replace_re_all(&terms, "abc", none, "X"),
        Some("abc".to_string())
    );
}

#[test]
fn replace_re_all_nullable_is_char_indexed_not_byte_indexed() {
    // The matcher returns BYTE offsets from a CHARACTER-indexed scan; a nullable
    // regex over multi-byte characters must still slice on character boundaries.
    let mut terms = TermStore::new();
    let all = mk_re_all(&mut terms);
    assert_eq!(
        crate::ground_eval_replace_re_all(&terms, "\u{3b1}\u{3b2}", all, "-"),
        Some("--".to_string())
    );
    let alpha = mk_str_to_re(&mut terms, "\u{3b1}");
    let star = mk_re_star(&mut terms, alpha);
    assert_eq!(
        crate::ground_eval_replace_re_all(&terms, "x\u{3b1}\u{3b2}", star, "A"),
        Some("xA\u{3b2}".to_string())
    );
}

#[test]
fn replace_re_all_nullable_budget_is_still_threaded() {
    // The non-empty matcher always advances, so the loop cannot spin. An
    // exhausted budget must remain a resource abort, not a semantic answer.
    let mut terms = TermStore::new();
    let all = mk_re_all(&mut terms);
    assert_eq!(
        crate::ground_eval_replace_re_all_with_work_limit(&terms, "aaaa", all, "x", 0),
        Err(RegexWorkLimitExceeded)
    );
}

#[test]
fn replace_re_keeps_empty_match_eligibility() {
    // str.replace_re's SMT-LIB clause is not recursive, so it needs no
    // termination side condition and carries none: with a nullable regex the
    // minimal-|x|, then minimal-|w| decomposition is x = w = ε and t is
    // inserted at the front. That behaviour is pre-existing and was separately
    // adjudicated as correct; the replace_re_all fix must not disturb it.
    let mut terms = TermStore::new();
    let all = mk_re_all(&mut terms);
    assert_eq!(
        crate::ground_eval_replace_re(&terms, "a", all, "b"),
        Some("ba".to_string())
    );
    let a = mk_str_to_re(&mut terms, "a");
    let star = mk_re_star(&mut terms, a);
    assert_eq!(
        crate::ground_eval_replace_re(&terms, "bbb", star, "X"),
        Some("Xbbb".to_string())
    );
}

#[test]
fn membership_accepts_three_digit_conjunction_witness() {
    let mut terms = TermStore::new();
    let digits = (0..3).map(|_| mk_re_range(&mut terms, "0", "9")).collect();
    let exactly_three = mk_re_concat(&mut terms, digits);
    let digit = mk_re_range(&mut terms, "0", "9");
    let any_digits = mk_re_star(&mut terms, digit);

    assert_eq!(
        RegExpSolver::evaluate(&terms, "000", exactly_three),
        Some(true)
    );
    assert_eq!(
        RegExpSolver::evaluate(&terms, "000", any_digits),
        Some(true)
    );
}

#[test]
fn membership_accepts_literal_between_allchar_stars() {
    let mut terms = TermStore::new();
    let any_left = mk_re_allchar(&mut terms);
    let any_left = mk_re_star(&mut terms, any_left);
    let needle = mk_str_to_re(&mut terms, "\\<SCRIPT");
    let any_right = mk_re_allchar(&mut terms);
    let any_right = mk_re_star(&mut terms, any_right);
    let regex = mk_re_concat(&mut terms, vec![any_left, needle, any_right]);

    assert_eq!(
        RegExpSolver::evaluate(&terms, "xx\\<SCRIPTyy", regex),
        Some(true)
    );
}
