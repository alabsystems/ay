// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the string solver (lib.rs).

use super::*;
use ay_core::term::Symbol;
use ay_core::Sort;

#[test]
fn empty_check_returns_sat() {
    let terms = TermStore::new();
    let mut solver = StringSolver::new(&terms);
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn propagate_returns_empty() {
    let terms = TermStore::new();
    let mut solver = StringSolver::new(&terms);
    assert!(solver.propagate().is_empty());
}

#[test]
fn push_pop_sequence() {
    let terms = TermStore::new();
    let mut solver = StringSolver::new(&terms);
    solver.push();
    solver.push();
    solver.pop();
    solver.pop();
    // Extra pop beyond pushes — must not panic and solver must remain usable.
    solver.pop();
    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "empty solver after push/pop sequence should return Sat"
    );
}

#[test]
fn reset_then_check() {
    let mut terms = TermStore::new();
    let s1 = terms.mk_string("hello".to_string());
    let s2 = terms.mk_var("x", Sort::String);
    let eq = terms.mk_eq(s1, s2);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.reset();
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

/// Merged variables with disequality: x = y ∧ x ≠ y → UNSAT.
///
/// Note: mk_eq(x,x) simplifies to true_term (reflexive), so we use
/// two distinct variables and assert both equality and disequality.
#[test]
fn merged_disequality_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let eq = terms.mk_eq(x, y);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true); // x = y (merge)
    solver.assert_literal(eq, false); // x ≠ y (disequality)

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "x = y ∧ x ≠ y should be UNSAT, got {result:?}"
    );
}

#[test]
fn shared_equality_merges_string_eqcs() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let eq = terms.mk_eq(x, y);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, false); // x != y
    solver.assert_shared_equality(x, y, &[]);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "shared equality x = y must conflict with x != y, got {result:?}"
    );
}

#[test]
fn push_pop_restores_state() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let eq = terms.mk_eq(x, y);

    let mut solver = StringSolver::new(&terms);
    solver.push();
    solver.assert_literal(eq, true);
    // Variable-only formulas may return Unknown (incomplete) or Sat;
    // both are correct — the solver is not unsound.
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat | TheoryResult::Unknown),
        "x = y should be Sat or Unknown, got {result:?}"
    );

    solver.pop();
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn concat_normal_form() {
    let mut terms = TermStore::new();
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let ab = terms.mk_app(Symbol::named("str.++"), vec![a, b], Sort::String);
    let x = terms.mk_var("x", Sort::String);
    let eq = terms.mk_eq(x, ab);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn extract_model_assigns_string_var_from_constant_eqc() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let abc = terms.mk_string("abc".to_string());
    let eq = terms.mk_eq(x, abc);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let model = solver.extract_model();
    assert_eq!(model.values.get(&x), Some(&"abc".to_string()));
}

/// F2 regression: cycle detection with empty equivalent variable.
///
/// y = "" ∧ str.++(y, x) = x should NOT be a conflict because y is empty,
/// so the equation reduces to x = x.
#[test]
fn cycle_with_empty_equivalent_variable() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let empty = terms.mk_string(String::new());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![y, x], Sort::String);
    let eq_y_empty = terms.mk_eq(y, empty);
    let eq_concat_x = terms.mk_eq(concat, x);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq_y_empty, true); // y = ""
    solver.assert_literal(eq_concat_x, true); // str.++(y, x) = x

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "y=\"\" ∧ str.++(y,x)=x should be SAT, got {result:?}"
    );
}

// ── Proof coverage: gap documentation tests ─────────────────────────

/// Constant conflict: x = "abc" ∧ x = "def" → UNSAT.
///
/// merge() detects conflicting constants during union and sets
/// pending_conflict. check_init() converts it to a theory conflict.
#[test]
fn constant_conflict_detected() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let abc = terms.mk_string("abc".to_string());
    let def = terms.mk_string("def".to_string());
    let eq1 = terms.mk_eq(x, abc);
    let eq2 = terms.mk_eq(x, def);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq1, true); // x = "abc"
    solver.assert_literal(eq2, true); // x = "def"

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "x = \"abc\" ∧ x = \"def\" should be UNSAT, got {result:?}"
    );
}

/// Normal form equality: str.++("a","b") = "c" → UNSAT.
///
/// The concat NF [a, b] is compared against the EQC constant "c".
/// Position 0: "a" vs "c"[0:1] = "c" → mismatch → conflict.
#[test]
fn concat_constant_mismatch_detected() {
    let mut terms = TermStore::new();
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let ab = terms.mk_app(Symbol::named("str.++"), vec![a, b], Sort::String);
    let c = terms.mk_string("c".to_string());
    let eq = terms.mk_eq(ab, c);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true); // str.++("a","b") = "c"

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "str.++(\"a\",\"b\") = \"c\" should be UNSAT, got {result:?}"
    );
}

/// Normal form equality: str.++("a","b") = "ab" → SAT.
#[test]
fn concat_constant_match_is_sat() {
    let mut terms = TermStore::new();
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let ab = terms.mk_app(Symbol::named("str.++"), vec![a, b], Sort::String);
    let ab_const = terms.mk_string("ab".to_string());
    let eq = terms.mk_eq(ab, ab_const);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true); // str.++("a","b") = "ab"

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "str.++(\"a\",\"b\") = \"ab\" should be SAT, got {result:?}"
    );
}

/// Normal form equality: str.++("abc","def") = "abcde" → UNSAT (length mismatch).
#[test]
fn concat_constant_length_mismatch() {
    let mut terms = TermStore::new();
    let abc = terms.mk_string("abc".to_string());
    let def = terms.mk_string("def".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![abc, def], Sort::String);
    let target = terms.mk_string("abcde".to_string());
    let eq = terms.mk_eq(concat, target);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "str.++(\"abc\",\"def\") = \"abcde\" should be UNSAT, got {result:?}"
    );
}

/// Concat-vs-concat conflict: str.++("a","b") = str.++("c","d") → UNSAT.
///
/// Both NFs resolve to constants ("ab" vs "cd"), so the conflict is detected
/// by comparing resolved NF strings in check_normal_forms_eq Case B.
#[test]
fn concat_vs_concat_mismatch() {
    let mut terms = TermStore::new();
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let c = terms.mk_string("c".to_string());
    let d = terms.mk_string("d".to_string());
    let ab = terms.mk_app(Symbol::named("str.++"), vec![a, b], Sort::String);
    let cd = terms.mk_app(Symbol::named("str.++"), vec![c, d], Sort::String);
    let eq = terms.mk_eq(ab, cd);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true); // str.++("a","b") = str.++("c","d")

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "str.++(\"a\",\"b\") = str.++(\"c\",\"d\") should be UNSAT, got {result:?}"
    );
}

/// Disequality: str.++("a","b") != "ab" → UNSAT.
///
/// The concat NF resolves to `"ab"`, which equals the constant `"ab"`,
/// so the disequality is violated. Tests check_normal_forms_deq Check 3
/// (constant string resolution).
#[test]
fn deq_concat_resolves_to_same_constant() {
    let mut terms = TermStore::new();
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![a, b], Sort::String);
    let ab = terms.mk_string("ab".to_string());
    let eq = terms.mk_eq(concat, ab);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, false); // str.++("a","b") != "ab"

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "str.++(\"a\",\"b\") != \"ab\" should be UNSAT, got {result:?}"
    );
}

/// Disequality: str.++("a","b") != "cd" → SAT.
///
/// "ab" != "cd" is satisfiable.
#[test]
fn deq_concat_resolves_to_different_constant() {
    let mut terms = TermStore::new();
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![a, b], Sort::String);
    let cd = terms.mk_string("cd".to_string());
    let eq = terms.mk_eq(concat, cd);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, false); // str.++("a","b") != "cd"

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "str.++(\"a\",\"b\") != \"cd\" should be SAT, got {result:?}"
    );
}

/// processSimpleNEq Case 2+5: str.++(x,"a") = str.++(x,"b") → UNSAT.
///
/// x is a shared variable in both concat terms. process_simple_neq
/// advances past x (Case 2: same EQC rep), then compares "a" vs "b"
/// (Case 5: constant mismatch → conflict).
///
/// This test exercises the NF-pair comparison path that the old
/// nf_to_constant approach could NOT handle (because x is a variable).
#[test]
fn process_simple_neq_shared_variable_mismatch() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let xa = terms.mk_app(Symbol::named("str.++"), vec![x, a], Sort::String);
    let xb = terms.mk_app(Symbol::named("str.++"), vec![x, b], Sort::String);
    let eq = terms.mk_eq(xa, xb);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true); // str.++(x,"a") = str.++(x,"b")

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "str.++(x,\"a\") = str.++(x,\"b\") should be UNSAT, got {result:?}"
    );
}

/// processSimpleNEq Case 2+0: str.++(x,"a") = str.++(x,"a") → SAT.
///
/// Both NFs are identical (x, "a"). process_simple_neq advances past
/// both components and reaches Case 0 (both exhausted, consistent).
#[test]
fn process_simple_neq_shared_variable_match() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let a = terms.mk_string("a".to_string());
    let a2 = terms.mk_string("a".to_string());
    let xa1 = terms.mk_app(Symbol::named("str.++"), vec![x, a], Sort::String);
    let xa2 = terms.mk_app(Symbol::named("str.++"), vec![x, a2], Sort::String);
    let eq = terms.mk_eq(xa1, xa2);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true); // str.++(x,"a") = str.++(x,"a")

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "str.++(x,\"a\") = str.++(x,\"a\") should be SAT, got {result:?}"
    );
}

/// Concat-vs-concat match: str.++("a","b") = str.++("a","b") → SAT.
#[test]
fn concat_vs_concat_match() {
    let mut terms = TermStore::new();
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let ab1 = terms.mk_app(Symbol::named("str.++"), vec![a, b], Sort::String);
    let a2 = terms.mk_string("a".to_string());
    let b2 = terms.mk_string("b".to_string());
    let ab2 = terms.mk_app(Symbol::named("str.++"), vec![a2, b2], Sort::String);
    let eq = terms.mk_eq(ab1, ab2);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true); // str.++("a","b") = str.++("a","b")

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "str.++(\"a\",\"b\") = str.++(\"a\",\"b\") should be SAT, got {result:?}"
    );
}

/// Unicode safety: str.++("é","x") = str.++("ë","x") → UNSAT.
///
/// "é" (U+00E9) and "ë" (U+00EB) share first UTF-8 byte (0xC3) but
/// differ on second byte. process_simple_neq must use char-level
/// comparison (not byte-level) to avoid panics at non-character boundaries.
#[test]
fn unicode_multibyte_mismatch() {
    let mut terms = TermStore::new();
    let e_acute = terms.mk_string("é".to_string()); // U+00E9: [0xC3, 0xA9]
    let e_diaeresis = terms.mk_string("ë".to_string()); // U+00EB: [0xC3, 0xAB]
    let x_str = terms.mk_string("x".to_string());
    let x_str2 = terms.mk_string("x".to_string());
    let concat1 = terms.mk_app(Symbol::named("str.++"), vec![e_acute, x_str], Sort::String);
    let concat2 = terms.mk_app(
        Symbol::named("str.++"),
        vec![e_diaeresis, x_str2],
        Sort::String,
    );
    let eq = terms.mk_eq(concat1, concat2);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "str.++(\"é\",\"x\") = str.++(\"ë\",\"x\") should be UNSAT, got {result:?}"
    );
}

/// Phase C extf predicate evaluation:
/// str.contains(x, "hello") ∧ x = "goodbye" -> UNSAT.
#[test]
fn contains_with_resolved_constant_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let hello = terms.mk_string("hello".to_string());
    let goodbye = terms.mk_string("goodbye".to_string());
    let contains = terms.mk_app(Symbol::named("str.contains"), vec![x, hello], Sort::Bool);
    let eq = terms.mk_eq(x, goodbye);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(contains, true);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "str.contains(\"goodbye\",\"hello\") should be UNSAT, got {result:?}"
    );
}

/// Negated extf literal with true evaluated predicate is UNSAT.
///
/// str.contains("goodbye", "good") is true, so asserting it as false conflicts.
#[test]
fn contains_negated_true_predicate_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let good = terms.mk_string("good".to_string());
    let goodbye = terms.mk_string("goodbye".to_string());
    let contains = terms.mk_app(Symbol::named("str.contains"), vec![x, good], Sort::Bool);
    let eq = terms.mk_eq(x, goodbye);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(contains, false);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "not str.contains(\"goodbye\",\"good\") should be UNSAT, got {result:?}"
    );
}

/// str.prefixof("hello", x) ∧ x = "goodbye" -> UNSAT.
#[test]
fn prefixof_with_resolved_constant_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let hello = terms.mk_string("hello".to_string());
    let goodbye = terms.mk_string("goodbye".to_string());
    let prefixof = terms.mk_app(Symbol::named("str.prefixof"), vec![hello, x], Sort::Bool);
    let eq = terms.mk_eq(x, goodbye);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(prefixof, true);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "str.prefixof(\"hello\",\"goodbye\") should be UNSAT, got {result:?}"
    );
}

/// str.suffixof("hello", x) ∧ x = "goodbye" -> UNSAT.
#[test]
fn suffixof_with_resolved_constant_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let hello = terms.mk_string("hello".to_string());
    let goodbye = terms.mk_string("goodbye".to_string());
    let suffixof = terms.mk_app(Symbol::named("str.suffixof"), vec![hello, x], Sort::Bool);
    let eq = terms.mk_eq(x, goodbye);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(suffixof, true);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "str.suffixof(\"hello\",\"goodbye\") should be UNSAT, got {result:?}"
    );
}

#[test]
fn unresolved_replace_identity_negation_requests_split() {
    // With DEQ disequality processing (m2 merge), the solver now emits
    // a DeqEmptySplit lemma for unresolved replace disequalities instead
    // of returning Unknown.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let empty = terms.mk_string(String::new());
    let a = terms.mk_string("a".to_string());
    let replace = terms.mk_app(
        Symbol::named("str.replace"),
        vec![x, empty, a],
        Sort::String,
    );
    let concat = terms.mk_app(Symbol::named("str.++"), vec![a, x], Sort::String);
    let eq = terms.mk_eq(replace, concat);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, false);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::NeedStringLemma(_) | TheoryResult::Unknown
        ),
        "unresolved replace identity disequality must request split or be Unknown, got {result:?}"
    );
}

#[test]
fn unresolved_contains_transitivity_negation_is_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let a = terms.mk_string("a".to_string());
    let contains_xy = terms.mk_app(Symbol::named("str.contains"), vec![x, y], Sort::Bool);
    let contains_ya = terms.mk_app(Symbol::named("str.contains"), vec![y, a], Sort::Bool);
    let contains_xa = terms.mk_app(Symbol::named("str.contains"), vec![x, a], Sort::Bool);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(contains_xy, true);
    solver.assert_literal(contains_ya, true);
    solver.assert_literal(contains_xa, false);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "contains transitivity contradiction must be UNSAT, got {result:?}"
    );
}

#[test]
fn extf_equality_rewriter_replace_identity_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let z = terms.mk_var("z", Sort::String);
    let c = terms.mk_string("target".to_string());

    let eq_xy = terms.mk_eq(x, y);
    let replace = terms.mk_app(Symbol::named("str.replace"), vec![x, y, z], Sort::String);
    let eq_replace_c = terms.mk_eq(replace, c);
    let eq_z_c = terms.mk_eq(z, c);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq_xy, true);
    solver.assert_literal(eq_replace_c, true);
    solver.assert_literal(eq_z_c, false);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "str.replace(x,x,z)=c with z!=c must be UNSAT, got {result:?}"
    );
}

/// Regression for #3807: incompleteness must remain sticky across
/// internal-fact rounds so round-N+1 cannot incorrectly return Sat.
#[test]
fn prefix_sharing_word_equation_does_not_return_sat_after_round_reset() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let ab = terms.mk_string("ab".to_string());
    let a = terms.mk_string("a".to_string());
    let lhs = terms.mk_app(Symbol::named("str.++"), vec![ab, x], Sort::String);
    let rhs = terms.mk_app(Symbol::named("str.++"), vec![a, y], Sort::String);
    let eq = terms.mk_eq(lhs, rhs);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unknown | TheoryResult::NeedStringLemma(_)
        ),
        "prefix-sharing variable equation should not return Sat, got {result:?}"
    );
}

#[test]
fn unresolved_contains_self_tautology_is_sat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let contains_xx = terms.mk_app(Symbol::named("str.contains"), vec![x, x], Sort::Bool);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(contains_xx, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "contains(x, x) should stay SAT, got {result:?}"
    );
}

/// Variable-constant concat vs constant: str.++(x, "c") = "abc".
///
/// The concat NF is [x, "c"]. The EQC constant is "abc".
/// process_nf_against_constant cannot resolve x (variable), so it
/// falls through to process_simple_neq which emits a split lemma
/// (EmptySplit or ConstSplit on x). The solver must NOT return
/// Unknown — it must request a lemma to make progress.
///
/// This is the core test for #3319 (Phase B1): variable components
/// in NFs compared against constants must produce split lemmas.
#[test]
fn variable_concat_vs_constant_emits_split() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let c = terms.mk_string("c".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![x, c], Sort::String);
    let abc = terms.mk_string("abc".to_string());
    let eq = terms.mk_eq(concat, abc);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true); // str.++(x, "c") = "abc"

    let result = solver.check();
    // Must NOT be Unknown — should be a split lemma request.
    assert!(
        matches!(result, TheoryResult::NeedStringLemma(_)),
        "str.++(x,\"c\") = \"abc\" should request a split lemma, got {result:?}"
    );
}

/// Duplicate split requests in the same scope are suppressed.
///
/// We force the ConstSplit path with `x != ""` and check that the first
/// call requests a lemma while the second call does not re-emit it.
#[test]
fn duplicate_split_request_is_suppressed_in_scope() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let b = terms.mk_string("b".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![x, b], Sort::String);
    let ab = terms.mk_string("ab".to_string());
    let eq = terms.mk_eq(concat, ab);
    let empty = terms.mk_string(String::new());
    let x_eq_empty = terms.mk_eq(x, empty);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(x_eq_empty, false); // x != "" -> non-empty path

    let first = solver.check();
    assert!(
        matches!(first, TheoryResult::NeedStringLemma(_)),
        "first check should request split lemma, got {first:?}"
    );

    let second = solver.check();
    // After suppression, the solver should return Unknown (incomplete —
    // the split was already emitted but DPLL(T) hasn't acted on it yet).
    assert!(
        matches!(second, TheoryResult::Unknown),
        "second check should return Unknown (split already emitted), got {second:?}"
    );
}

/// Split dedup is scope-aware via StringSolver push/pop.
///
/// A split emitted in one pushed scope must be available again after pop.
#[test]
fn split_request_reappears_after_pop_scope() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let b = terms.mk_string("b".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![x, b], Sort::String);
    let ab = terms.mk_string("ab".to_string());
    let eq = terms.mk_eq(concat, ab);
    let empty = terms.mk_string(String::new());
    let x_eq_empty = terms.mk_eq(x, empty);

    let mut solver = StringSolver::new(&terms);

    solver.push();
    solver.assert_literal(eq, true);
    solver.assert_literal(x_eq_empty, false); // x != "" -> non-empty path

    let first = solver.check();
    assert!(
        matches!(first, TheoryResult::NeedStringLemma(_)),
        "first scoped check should request split lemma, got {first:?}"
    );
    let second = solver.check();
    assert!(
        !matches!(second, TheoryResult::NeedStringLemma(_)),
        "second scoped check should dedup split lemma, got {second:?}"
    );

    solver.pop();

    solver.push();
    solver.assert_literal(eq, true);
    solver.assert_literal(x_eq_empty, false);
    let third = solver.check();
    assert!(
        matches!(third, TheoryResult::NeedStringLemma(_)),
        "after pop, split lemma should be emittable again, got {third:?}"
    );
}

/// Variable-constant concat equals the constant suffix: str.++(x, "a") = "a".
///
/// This is SAT with x = "". The solver must emit EmptySplit on x (not
/// report a conflict). The concat NF is [x, "a"], the EQC constant is "a".
#[test]
fn variable_concat_suffix_equals_constant_not_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let a = terms.mk_string("a".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![x, a], Sort::String);
    let a2 = terms.mk_string("a".to_string());
    let eq = terms.mk_eq(concat, a2);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true); // str.++(x, "a") = "a"

    let result = solver.check();
    // SAT with x = "". The solver should emit a split lemma (EmptySplit/ConstSplit)
    // because it needs to case-split on x being empty vs non-empty.
    assert!(
        matches!(
            result,
            TheoryResult::NeedStringLemma(_) | TheoryResult::Sat | TheoryResult::Unknown
        ),
        "str.++(x,\"a\") = \"a\" expected NeedStringLemma/Sat/Unknown, got {result:?}"
    );
}

/// CEGAR iteration 2: str.++("a", x) = "a" with x = "" asserted.
///
/// Simulates what the executor CEGAR loop does after EmptySplit:
/// 1. Iteration 0: solver gets str.++("a", x) = "a", returns NeedStringLemma(EmptySplit(x)).
/// 2. Iteration 1: fresh solver gets str.++("a", x) = "a" AND x = "" from SAT model.
///    The solver should return Sat (NF simplifies to match constant).
#[test]
fn cegar_iteration_2_prefix_empty_split_resolves_to_sat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let a = terms.mk_string("a".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![a, x], Sort::String);
    let a2 = terms.mk_string("a".to_string());
    let eq = terms.mk_eq(concat, a2);
    let empty = terms.mk_string(String::new());
    let x_eq_empty = terms.mk_eq(x, empty);

    // Simulate CEGAR iteration 2: fresh solver with both assertions.
    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true); // str.++("a", x) = "a"
    solver.assert_literal(x_eq_empty, true); // x = "" (from SAT model)

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "With x=\"\" asserted, str.++(\"a\",x)=\"a\" should be Sat, got {result:?}"
    );
}

/// Same CEGAR test for suffix case: str.++(x, "a") = "a" with x = "".
#[test]
fn cegar_iteration_2_suffix_empty_split_resolves_to_sat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let a = terms.mk_string("a".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![x, a], Sort::String);
    let a2 = terms.mk_string("a".to_string());
    let eq = terms.mk_eq(concat, a2);
    let empty = terms.mk_string(String::new());
    let x_eq_empty = terms.mk_eq(x, empty);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(x_eq_empty, true); // x = ""

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "With x=\"\" asserted, str.++(x,\"a\")=\"a\" should be Sat, got {result:?}"
    );
}

/// Regression: str.++(x, "c") = str.++(y, "c") must NOT be unsat.
///
/// SAT with x=y="". If the cycle check or NF comparison reports false
/// unsat, there's a soundness bug.
#[test]
fn regression_3375_var_concat_suffix_equals_var_concat_suffix_not_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let c1 = terms.mk_string("c".to_string());
    let c2 = terms.mk_string("c".to_string());
    let concat_xc = terms.mk_app(Symbol::named("str.++"), vec![x, c1], Sort::String);
    let concat_yc = terms.mk_app(Symbol::named("str.++"), vec![y, c2], Sort::String);
    let eq = terms.mk_eq(concat_xc, concat_yc);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true);

    let result = solver.check();
    // Satisfiable (x=y=""), so must not be Unsat. Should request a split
    // or report Sat/Unknown — not silently pass for any non-Unsat result.
    assert!(
        matches!(
            result,
            TheoryResult::NeedStringLemma(_) | TheoryResult::Sat | TheoryResult::Unknown
        ),
        "str.++(x,\"c\") = str.++(y,\"c\") expected NeedStringLemma/Sat/Unknown, got {result:?}"
    );
}

/// Equal-length suffix mismatch is UNSAT: len(x)=len(y) ∧ x++"a"=y++"b".
///
/// The core solver should use length equality (Case 3b / N_UNIFY) to infer
/// x = y, then detect the endpoint constant clash "a" vs "b".
#[test]
fn equal_length_concat_suffix_mismatch_is_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let concat_xa = terms.mk_app(Symbol::named("str.++"), vec![x, a], Sort::String);
    let concat_yb = terms.mk_app(Symbol::named("str.++"), vec![y, b], Sort::String);
    let eq_concat = terms.mk_eq(concat_xa, concat_yb);
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = terms.mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
    let len_eq = terms.mk_eq(len_x, len_y);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(len_eq, true);
    solver.assert_literal(eq_concat, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "len(x)=len(y) ∧ x++\"a\"=y++\"b\" must be Unsat, got {result:?}"
    );
}

/// Constant prefix + variable vs constant: str.++("ab", x) = "abc".
///
/// NF is ["ab", x]. Compared against "abc": "ab" matches at offset 0-2,
/// then x is a variable at offset 2 with remaining constant "c".
/// Falls through to process_simple_neq, which should emit a split.
#[test]
fn const_prefix_variable_vs_constant_emits_split() {
    let mut terms = TermStore::new();
    let ab = terms.mk_string("ab".to_string());
    let x = terms.mk_var("x", Sort::String);
    let concat = terms.mk_app(Symbol::named("str.++"), vec![ab, x], Sort::String);
    let abc = terms.mk_string("abc".to_string());
    let eq = terms.mk_eq(concat, abc);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true); // str.++("ab", x) = "abc"

    let result = solver.check();
    // process_nf_against_constant hits x at offset 2 (remaining "c"),
    // falls through to process_simple_neq. It should emit either a
    // split lemma or infer x = "c" via endpoint equality. Either way,
    // the result must NOT be Unknown.
    assert!(
        !matches!(result, TheoryResult::Unknown),
        "str.++(\"ab\",x) = \"abc\" should not return Unknown, got {result:?}"
    );
}

/// Endpoint-empty inference works when empty string is pre-registered.
///
/// For (str.++ x "a") = "a", the reverse pass trims the shared "a" suffix,
/// leaving [x] vs []. Case 4 (endpoint-empty) should infer x = "" and
/// the internal fact loop converges to Sat.
///
/// This test verifies the fix for the empty_string_id gap: without
/// pre-registering "", the solver returned Unknown because it couldn't
/// emit the x="" inference.
#[test]
fn endpoint_empty_with_preregistered_empty_string() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let a = terms.mk_string("a".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![x, a], Sort::String);
    let a2 = terms.mk_string("a".to_string());
    let eq = terms.mk_eq(concat, a2);
    let empty = terms.mk_string(String::new());

    let mut solver = StringSolver::new(&terms);
    solver.set_empty_string_id(empty);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "str.++(x,\"a\") = \"a\" with pre-registered empty should be Sat, got {result:?}"
    );
}

/// Without pre-registered empty string, endpoint-empty returns Unknown
/// (not unsound — just incomplete).
#[test]
fn endpoint_empty_without_preregistered_empty_returns_unknown() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let a = terms.mk_string("a".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![x, a], Sort::String);
    let a2 = terms.mk_string("a".to_string());
    let eq = terms.mk_eq(concat, a2);
    // No empty string registered.

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true);

    let result = solver.check();
    // Without pre-registered empty string, solver may not be able to
    // construct the EmptySplit lemma. Must be NeedStringLemma, Sat, or Unknown.
    assert!(
            matches!(
                result,
                TheoryResult::NeedStringLemma(_) | TheoryResult::Sat | TheoryResult::Unknown
            ),
            "str.++(x,\"a\") = \"a\" without empty expected NeedStringLemma/Sat/Unknown, got {result:?}"
        );
}

/// Reverse pass trims shared suffix in var-var concat equations.
///
/// For (str.++ x "c") = (str.++ y "c"), the reverse pass trims "c",
/// leaving [x] vs [y]. The solver should emit a split lemma (not Unsat).
#[test]
fn reverse_pass_trims_shared_suffix_var_var() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let c = terms.mk_string("c".to_string());
    let concat_xc = terms.mk_app(Symbol::named("str.++"), vec![x, c], Sort::String);
    let concat_yc = terms.mk_app(Symbol::named("str.++"), vec![y, c], Sort::String);
    let eq = terms.mk_eq(concat_xc, concat_yc);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true);

    let result = solver.check();
    // After suffix trimming, [x] vs [y] with unknown lengths → LengthSplit.
    // Must request a split lemma (the solver needs external guidance on lengths).
    assert!(
        matches!(
            result,
            TheoryResult::NeedStringLemma(_) | TheoryResult::Sat | TheoryResult::Unknown
        ),
        "str.++(x,\"c\") = str.++(y,\"c\") expected NeedStringLemma/Sat/Unknown, got {result:?}"
    );
}

/// StringSolver push/pop restores SkolemCache split scope.
///
/// The same formula in the same scope first emits a split lemma, then
/// returns Unknown (duplicate split dedup). After pop+push with the same
/// assertion re-added, split emission should happen again.
#[test]
fn solver_push_pop_restores_split_emission_scope() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let c = terms.mk_string("c".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![x, c], Sort::String);
    let abc = terms.mk_string("abc".to_string());
    let eq = terms.mk_eq(concat, abc);

    let mut solver = StringSolver::new(&terms);

    solver.push();
    solver.assert_literal(eq, true);

    let first = solver.check();
    assert!(
        matches!(first, TheoryResult::NeedStringLemma(_)),
        "first check should emit split lemma, got {first:?}"
    );

    let second = solver.check();
    assert!(
        matches!(second, TheoryResult::Unknown),
        "second check in same scope should dedup to Unknown, got {second:?}"
    );

    solver.pop();

    solver.push();
    solver.assert_literal(eq, true);
    let third = solver.check();
    assert!(
        matches!(third, TheoryResult::NeedStringLemma(_)),
        "after pop+push, split should be emittable again, got {third:?}"
    );
}

/// Regression for #3807: prefix-sharing word equation must NOT return Sat.
///
/// `str.++("ab", x) = str.++("a", y)` has variable NF components that
/// cannot be resolved without external split lemmas. The solver must
/// return Unknown or NeedStringLemma — never Sat.
///
/// The `sticky_incomplete` latch prevents false Sat. This test verifies
/// the fix survives the `sticky_incomplete` reset on internal equality merge.
#[test]
fn regression_3807_prefix_sharing_not_false_sat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let ab = terms.mk_string("ab".to_string());
    let a = terms.mk_string("a".to_string());
    let concat_ab_x = terms.mk_app(Symbol::named("str.++"), vec![ab, x], Sort::String);
    let concat_a_y = terms.mk_app(Symbol::named("str.++"), vec![a, y], Sort::String);
    let eq = terms.mk_eq(concat_ab_x, concat_a_y);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true); // str.++("ab", x) = str.++("a", y)

    let result = solver.check();
    // Must NOT return Sat — requires VarSplit to make progress.
    assert!(
        !matches!(result, TheoryResult::Sat),
        "str.++(\"ab\",x) = str.++(\"a\",y) must not return Sat (soundness), got {result:?}"
    );
}

/// Regression for #3826: single woorpje-style equation is satisfiable.
///
/// This equation has a Z3 model `A = "c", F = "fafecefeeefac"` and must
/// never be concluded `Unsat` by the core string solver.
#[test]
fn regression_3826_single_woorpje_equation_not_unsat() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("A", Sort::String);
    let f = terms.mk_var("F", Sort::String);

    let cffcbdaa = terms.mk_string("cffcbdaa".to_string());
    let e = terms.mk_string("e".to_string());
    let fdceb = terms.mk_string("fdceb".to_string());
    let ffdbaf = terms.mk_string("ffdbaf".to_string());
    let cfdceb = terms.mk_string("cfdceb".to_string());
    let fafe = terms.mk_string("fafe".to_string());
    let efeeefa = terms.mk_string("efeeefa".to_string());
    let ffdbafce = terms.mk_string("ffdbafce".to_string());

    let lhs = terms.mk_app(
        Symbol::named("str.++"),
        vec![a, cffcbdaa, a, e, a, a, fdceb, a, f, ffdbaf, a, e],
        Sort::String,
    );
    let rhs = terms.mk_app(
        Symbol::named("str.++"),
        vec![
            a, cffcbdaa, a, e, a, cfdceb, a, fafe, a, efeeefa, a, ffdbafce,
        ],
        Sort::String,
    );
    let eq = terms.mk_eq(lhs, rhs);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(
        !matches!(result, TheoryResult::Unsat(_)),
        "woorpje-style single equation must not be Unsat, got {result:?}"
    );
}

/// Regression for #3826 (QF_S track01/01_track_48 shape): SAT equation
/// with repeated variables must not return Unsat.
#[test]
fn regression_3826_track01_shape_not_unsat() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("A", Sort::String);
    let f = terms.mk_var("F", Sort::String);
    let b = terms.mk_string("b".to_string());
    let cbc = terms.mk_string("cbc".to_string());
    let bc = terms.mk_string("bc".to_string());

    let lhs = terms.mk_app(Symbol::named("str.++"), vec![b, a, a, a, cbc], Sort::String);
    let rhs = terms.mk_app(Symbol::named("str.++"), vec![b, f, bc], Sort::String);
    let eq = terms.mk_eq(lhs, rhs);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(
        !matches!(result, TheoryResult::Unsat(_)),
        "track01 repeated-variable equation must not be Unsat, got {result:?}"
    );
}

/// Benchmark 130 scenario: str.contains(x, x++y)=T, x≠x++y, x=str.++(sk,x++y,sk2)
/// Theory must detect contradiction (y="" from self-concat → NF conflict on disequality).
#[test]
fn benchmark_130_case1_contains_true_eq_false() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let sk_pre = terms.mk_var("sk_pre", Sort::String);
    let sk_post = terms.mk_var("sk_post", Sort::String);
    let empty = terms.mk_string(String::new());

    // str.++(x, y)
    let xy = terms.mk_app(Symbol::named("str.++"), vec![x, y], Sort::String);
    // str.contains(x, str.++(x, y))
    let contains = terms.mk_app(Symbol::named("str.contains"), vec![x, xy], Sort::Bool);
    // (= x (str.++ x y))
    let eq_x_xy = terms.mk_eq(x, xy);
    // str.++(sk_pre, str.++(x, y), sk_post)
    let outer_concat = terms.mk_app(
        Symbol::named("str.++"),
        vec![sk_pre, xy, sk_post],
        Sort::String,
    );
    // (= x (str.++ sk_pre (str.++ x y) sk_post))
    let eq_decomp = terms.mk_eq(x, outer_concat);

    let mut solver = StringSolver::new(&terms);
    solver.set_empty_string_id(empty);

    // Assert: str.contains(x, x++y) = true
    solver.assert_literal(contains, true);
    // Assert: x ≠ x++y (Q=false)
    solver.assert_literal(eq_x_xy, false);
    // Assert: x = str.++(sk_pre, x++y, sk_post) (decomposition, R=true)
    solver.assert_literal(eq_decomp, true);

    let result = solver.check();
    assert!(
        !matches!(result, TheoryResult::Sat),
        "Case 1 (P=T, Q=F, R=T) must NOT be Sat: y=\"\" from self-concat makes x=x++y, \
             contradicting x≠x++y. Got {result:?}"
    );
}

/// Benchmark 130 scenario: str.contains(x, x++y)=F, x=x++y
/// Theory must detect contradiction (x=x++y → y="" → contains(x,x)=true, contradicting F).
#[test]
fn benchmark_130_case2_contains_false_eq_true() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let empty = terms.mk_string(String::new());

    // str.++(x, y)
    let xy = terms.mk_app(Symbol::named("str.++"), vec![x, y], Sort::String);
    // str.contains(x, str.++(x, y))
    let contains = terms.mk_app(Symbol::named("str.contains"), vec![x, xy], Sort::Bool);
    // (= x (str.++ x y))
    let eq_x_xy = terms.mk_eq(x, xy);

    let mut solver = StringSolver::new(&terms);
    solver.set_empty_string_id(empty);

    // Assert: str.contains(x, x++y) = false
    solver.assert_literal(contains, false);
    // Assert: x = x++y (Q=true)
    solver.assert_literal(eq_x_xy, true);

    let result = solver.check();
    assert!(
        !matches!(result, TheoryResult::Sat),
        "Case 2 (P=F, Q=T) must NOT be Sat: x=x++y makes contains(x,x)=true, \
             contradicting contains=false. Got {result:?}"
    );
}

/// Regression #3850 benchmark #15: str.contains("", x) ∧ x ≠ "" → UNSAT.
///
/// The empty string only contains the empty string, so positive
/// str.contains("", x) forces x = "". Combined with x ≠ "", this is UNSAT.
#[test]
fn contains_empty_haystack_with_nonempty_needle_is_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let empty = terms.mk_string(String::new());
    let contains = terms.mk_app(Symbol::named("str.contains"), vec![empty, x], Sort::Bool);
    let eq_x_empty = terms.mk_eq(x, empty);

    let mut solver = StringSolver::new(&terms);
    solver.set_empty_string_id(empty);
    solver.assert_literal(contains, true); // str.contains("", x) = true
    solver.assert_literal(eq_x_empty, false); // x ≠ ""

    let result = solver.check();
    assert!(
        !matches!(result, TheoryResult::Sat),
        "str.contains(\"\", x) ∧ x ≠ \"\" must NOT be Sat, got {result:?}"
    );
}

/// Positive case: str.contains("", x) ∧ x = "" → SAT.
#[test]
fn contains_empty_haystack_with_empty_needle_is_sat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let empty = terms.mk_string(String::new());
    let contains = terms.mk_app(Symbol::named("str.contains"), vec![empty, x], Sort::Bool);
    let eq_x_empty = terms.mk_eq(x, empty);

    let mut solver = StringSolver::new(&terms);
    solver.set_empty_string_id(empty);
    solver.assert_literal(contains, true); // str.contains("", x) = true
    solver.assert_literal(eq_x_empty, true); // x = ""

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "str.contains(\"\", x) ∧ x = \"\" should be Sat, got {result:?}"
    );
}

/// Regression #3850 benchmark #127: str.contains(x, x++x) ∧ x ≠ "" → UNSAT.
///
/// contains(x, x++x) means x contains a string twice its length.
/// Only possible when x = "". Combined with x ≠ "", this is UNSAT.
/// The `infer_eqs_from_contains` path detects haystack as a component
/// of needle and infers the extra components equal "".
#[test]
fn contains_self_concat_with_nonempty_var_is_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let empty = terms.mk_string(String::new());
    let xx = terms.mk_app(Symbol::named("str.++"), vec![x, x], Sort::String);
    let contains = terms.mk_app(Symbol::named("str.contains"), vec![x, xx], Sort::Bool);
    let eq_x_empty = terms.mk_eq(x, empty);

    let mut solver = StringSolver::new(&terms);
    solver.set_empty_string_id(empty);
    solver.assert_literal(contains, true);
    solver.assert_literal(eq_x_empty, false);

    let result = solver.check();
    assert!(
        !matches!(result, TheoryResult::Sat),
        "str.contains(x, x++x) ∧ x ≠ \"\" must NOT be Sat, got {result:?}"
    );
}

/// Regression #3850 benchmark #130 (partial): str.contains(x, x++y) ∧ x ≠ x++y → UNSAT.
///
/// str.contains(x, x++y) forces y = "" via infer_eqs_from_contains.
/// Then x++y = x, so x = x++y. Combined with x ≠ x++y, this is UNSAT.
#[test]
fn contains_x_concat_xy_with_diseq_is_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let empty = terms.mk_string(String::new());
    let xy = terms.mk_app(Symbol::named("str.++"), vec![x, y], Sort::String);
    let contains = terms.mk_app(Symbol::named("str.contains"), vec![x, xy], Sort::Bool);
    let eq_x_xy = terms.mk_eq(x, xy);

    let mut solver = StringSolver::new(&terms);
    solver.set_empty_string_id(empty);
    solver.assert_literal(contains, true);
    solver.assert_literal(eq_x_xy, false);

    let result = solver.check();
    assert!(
        !matches!(result, TheoryResult::Sat),
        "str.contains(x, x++y) ∧ x ≠ x++y must NOT be Sat, got {result:?}"
    );
}

/// #3899: After I_CYCLE infers y = "", the tautological
/// self-reference `str.++(y,x) = str.++("",x) = x` must not deadlock
/// NF computation. The NF for x must be `[x]`, allowing the NF
/// disequality check to detect that `str.++(x,y)` also has NF `[x]`,
/// conflicting with `x ≠ str.++(x,y)`.
#[test]
fn nf_tautological_self_ref_enables_deq_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let empty = terms.mk_string(String::new());

    // str.++(y, x)
    let yx = terms.mk_app(Symbol::named("str.++"), vec![y, x], Sort::String);
    // str.++(x, y)
    let xy = terms.mk_app(Symbol::named("str.++"), vec![x, y], Sort::String);
    // (= x (str.++ y x))
    let eq_x_yx = terms.mk_eq(x, yx);
    // (= x (str.++ x y))
    let eq_x_xy = terms.mk_eq(x, xy);

    let mut solver = StringSolver::new(&terms);
    solver.set_empty_string_id(empty);

    // SAT solver assigns: x = str.++(y,x) true, x = str.++(x,y) false
    // (one branch of the XOR). String theory must detect contradiction.
    solver.assert_literal(eq_x_yx, true);
    solver.assert_literal(eq_x_xy, false);

    let result = solver.check();
    assert!(
        !matches!(result, TheoryResult::Sat),
        "#3899: tautological self-ref must not block NF deq conflict. \
         After I_CYCLE y=\"\", x=str.++(y,x)=x and str.++(x,y)=x, \
         so x=str.++(x,y) should hold, contradicting the disequality. \
         Got {result:?}"
    );
}

/// #3762: take_warm_state() and import_warm_state() preserve statistics
/// and reduced terms across solver instances.
#[test]
fn warm_state_preserves_statistics_and_reduced_terms() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let abc = terms.mk_string("abc".to_string());
    let eq = terms.mk_eq(x, abc);
    let empty = terms.mk_string(String::new());

    // Build substr term without simultaneous mutable borrows.
    let zero = terms.mk_int(num_bigint::BigInt::from(0));
    let one = terms.mk_int(num_bigint::BigInt::from(1));
    let substr_term = terms.mk_app(
        Symbol::named("str.substr"),
        vec![x, zero, one],
        Sort::String,
    );

    // First solver: assert, check, accumulate statistics.
    let mut solver1 = StringSolver::new(&terms);
    solver1.set_empty_string_id(empty);
    solver1.assert_literal(eq, true);
    let _ = solver1.check(); // increments check_count

    // Mark a term as reduced.
    solver1.mark_reduced(substr_term);

    // Extract warm state.
    let warm = solver1.take_warm_state();
    assert!(warm.check_count >= 1, "check_count should be at least 1");
    assert!(
        !warm.reduced_terms.is_empty(),
        "reduced_terms should contain marked term"
    );

    // Create a second solver and import warm state.
    let mut solver2 = StringSolver::new(&terms);
    solver2.set_empty_string_id(empty);
    solver2.import_warm_state(&warm);

    // Verify statistics were imported.
    let warm2 = solver2.take_warm_state();
    assert_eq!(
        warm2.check_count, warm.check_count,
        "check_count should be preserved"
    );
    assert_eq!(
        warm2.conflict_count, warm.conflict_count,
        "conflict_count should be preserved"
    );
    assert_eq!(
        warm2.propagation_count, warm.propagation_count,
        "propagation_count should be preserved"
    );
    assert_eq!(
        warm2.reduced_terms.len(),
        warm.reduced_terms.len(),
        "reduced_terms should be preserved"
    );
}

/// #3762: soft_reset() preserves statistics and reduced terms.
#[test]
fn soft_reset_preserves_statistics_and_reduced_terms() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let abc = terms.mk_string("abc".to_string());
    let eq = terms.mk_eq(x, abc);
    let empty = terms.mk_string(String::new());

    // Build substr term without simultaneous mutable borrows.
    let zero = terms.mk_int(num_bigint::BigInt::from(0));
    let one = terms.mk_int(num_bigint::BigInt::from(1));
    let substr_term = terms.mk_app(
        Symbol::named("str.substr"),
        vec![x, zero, one],
        Sort::String,
    );

    let mut solver = StringSolver::new(&terms);
    solver.set_empty_string_id(empty);
    solver.assert_literal(eq, true);
    let _ = solver.check(); // increments check_count

    solver.mark_reduced(substr_term);

    let warm_before = solver.take_warm_state();
    assert!(warm_before.check_count >= 1);

    // Soft reset: clears assertion/EQC state, preserves statistics and reduced terms.
    solver.soft_reset();

    let warm_after = solver.take_warm_state();
    assert_eq!(
        warm_after.check_count, warm_before.check_count,
        "soft_reset must preserve check_count"
    );
    assert_eq!(
        warm_after.reduced_terms.len(),
        warm_before.reduced_terms.len(),
        "soft_reset must preserve reduced_terms"
    );

    // Solver should still be functional after soft_reset.
    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "empty solver after soft_reset should return Sat"
    );
}

/// NF-engine closure 5 is QUARANTINED: `AY_STR_NF=1` alone must NOT enable
/// it (measured wrong-UNSAT witness — see
/// `NF_CLOSURES_REQUIRING_EXPLICIT_OPT_IN`), while the closures that are
/// still trusted stay reachable. Naming it explicitly in
/// `--str-nf-closures` remains possible for repair work.
#[test]
fn nf_closure_5_is_not_enabled_by_the_master_switch_alone() {
    // No closure subset is installed in the test process, so the subset is
    // `None` and the quarantine list is the only thing that can exclude 5.
    STR_NF_TEST_OVERRIDE.with(|c| c.set(true));
    let five = str_nf_closure_enabled(5);
    let trusted: Vec<bool> = (1u8..=4)
        .chain(std::iter::once(6))
        .map(str_nf_closure_enabled)
        .collect();
    STR_NF_TEST_OVERRIDE.with(|c| c.set(false));

    assert!(
        !five,
        "closure 5 is quarantined: AY_STR_NF=1 alone must not enable it"
    );
    assert!(
        trusted.iter().all(|&t| t),
        "closures 1-4 and 6 must stay enabled under AY_STR_NF=1: {trusted:?}"
    );
    assert!(
        !str_nf_closure_enabled(6),
        "every closure must be off when the master switch is off"
    );
}

#[cfg(kani)]
mod verification {
    use super::*;
    use crate::normal_form::{ExplainEntry, NormalForm};

    // --- StringSolver contract proofs ---

    /// Empty solver must return Sat (no constraints = trivially satisfiable).
    #[kani::proof]
    fn proof_check_empty_sat() {
        let terms = TermStore::new();
        let mut solver = StringSolver::new(&terms);
        assert!(matches!(solver.check(), TheoryResult::Sat));
    }

    /// push/pop round-trip is safe and preserves Sat result.
    #[kani::proof]
    fn proof_push_pop_preserves_sat() {
        let terms = TermStore::new();
        let mut solver = StringSolver::new(&terms);
        assert!(matches!(solver.check(), TheoryResult::Sat));
        solver.push();
        assert!(matches!(solver.check(), TheoryResult::Sat));
        solver.pop();
        assert!(
            matches!(solver.check(), TheoryResult::Sat),
            "Sat must be preserved after push/pop on empty solver"
        );
    }

    /// reset restores to clean state.
    #[kani::proof]
    fn proof_reset_restores_sat() {
        let terms = TermStore::new();
        let mut solver = StringSolver::new(&terms);
        solver.push();
        solver.push();
        solver.reset();
        assert!(
            matches!(solver.check(), TheoryResult::Sat),
            "reset must restore to initial Sat state"
        );
    }

    // --- NormalForm invariant proofs ---

    /// Singleton NF has exactly one base term equal to the input, for all TermId values.
    #[kani::proof]
    fn proof_nf_singleton_invariant() {
        let id: u32 = kani::any();
        let t = TermId(id);
        let nf = NormalForm::singleton(t);
        assert_eq!(
            nf.base.len(),
            1,
            "singleton must have exactly one base term"
        );
        assert_eq!(nf.base[0], t, "singleton base[0] must equal input term");
        assert_eq!(nf.rep, Some(t), "singleton rep must be the input term");
        assert!(nf.deps.is_empty(), "singleton must have no deps");
    }

    /// add_dep preserves prior deps and appends new entry.
    #[kani::proof]
    fn proof_nf_add_dep_preserves() {
        let a: u32 = kani::any();
        let b: u32 = kani::any();
        let c: u32 = kani::any();
        let d: u32 = kani::any();

        let mut nf = NormalForm::singleton(TermId(a));
        nf.add_dep(TermId(a), TermId(b));
        assert_eq!(nf.deps.len(), 1);

        nf.add_dep(TermId(c), TermId(d));
        assert_eq!(nf.deps.len(), 2, "add_dep must append");
        assert_eq!(
            nf.deps[0],
            ExplainEntry {
                lhs: TermId(a),
                rhs: TermId(b)
            }
        );
        assert_eq!(
            nf.deps[1],
            ExplainEntry {
                lhs: TermId(c),
                rhs: TermId(d)
            }
        );
    }

    /// merge_deps concatenates exactly — total deps = |nf1.deps| + |nf2.deps|.
    #[kani::proof]
    fn proof_nf_merge_deps_preserves_all() {
        let a: u32 = kani::any();
        let b: u32 = kani::any();
        let c: u32 = kani::any();
        let d: u32 = kani::any();
        let e: u32 = kani::any();
        let f: u32 = kani::any();

        let mut nf1 = NormalForm::singleton(TermId(a));
        nf1.add_dep(TermId(a), TermId(b));

        let mut nf2 = NormalForm::singleton(TermId(c));
        nf2.add_dep(TermId(c), TermId(d));
        nf2.add_dep(TermId(e), TermId(f));

        let pre_count = nf1.deps.len();
        let other_count = nf2.deps.len();
        nf1.merge_deps(&nf2);

        assert_eq!(
            nf1.deps.len(),
            pre_count + other_count,
            "merge_deps must concatenate all deps"
        );
        // Verify nf2's deps are at the tail of nf1.
        assert_eq!(
            nf1.deps[1],
            ExplainEntry {
                lhs: TermId(c),
                rhs: TermId(d)
            }
        );
        assert_eq!(
            nf1.deps[2],
            ExplainEntry {
                lhs: TermId(e),
                rhs: TermId(f)
            }
        );
    }

    /// ExplainEntry equality is reflexive for all TermId pairs.
    #[kani::proof]
    fn proof_explain_entry_eq_reflexive() {
        let a: u32 = kani::any();
        let b: u32 = kani::any();
        let entry = ExplainEntry {
            lhs: TermId(a),
            rhs: TermId(b),
        };
        assert_eq!(entry, entry, "ExplainEntry equality must be reflexive");
    }

    /// str.contains("", x) iff x = "".
    ///
    /// The predicate evaluator should use emptiness facts from equalities and
    /// disequalities to detect contradictions without requiring concrete models.
    #[test]
    fn contains_empty_haystack_tracks_needle_emptiness() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::String);
        let empty = terms.mk_string(String::new());
        let contains = terms.mk_app(Symbol::named("str.contains"), vec![empty, x], Sort::Bool);
        let x_eq_empty = terms.mk_eq(x, empty);

        let mut solver = StringSolver::new(&terms);
        solver.assert_literal(contains, true);
        solver.assert_literal(x_eq_empty, false); // x != ""

        let result = solver.check();
        assert!(
            matches!(result, TheoryResult::Unsat(_)),
            "str.contains(\"\", x) with x != \"\" should be UNSAT, got {result:?}"
        );
    }
}
