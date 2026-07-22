// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the solver state module.

use super::*;
use ay_core::term::Symbol;
use ay_core::Sort;
use num_bigint::BigInt;

#[test]
fn new_state_is_empty() {
    let state = SolverState::new();
    assert!(state.disequalities().is_empty());
    assert_eq!(state.eqc_info.len(), 0);
}

#[test]
fn register_and_find() {
    let mut terms = TermStore::new();
    let s1 = terms.mk_string("hello".to_string());
    let s2 = terms.mk_string("world".to_string());

    let mut state = SolverState::new();
    state.register_term(&terms, s1);
    state.register_term(&terms, s2);

    assert_eq!(state.find(s1), s1);
    assert_eq!(state.find(s2), s2);
}

#[test]
fn merge_creates_equality() {
    let mut terms = TermStore::new();
    let s1 = terms.mk_string("hello".to_string());
    let s2 = terms.mk_var("x", Sort::String);
    let eq = terms.mk_eq(s1, s2);
    let lit = TheoryLit::new(eq, true);

    let mut state = SolverState::new();
    state.register_term(&terms, s1);
    state.register_term(&terms, s2);
    let _ = state.merge(s1, s2, lit);

    assert_eq!(state.find(s1), state.find(s2));
}

#[test]
fn constant_tracking() {
    let mut terms = TermStore::new();
    let s = terms.mk_string("hello".to_string());

    let mut state = SolverState::new();
    state.register_term(&terms, s);

    assert_eq!(state.get_constant(&s), Some("hello"));
}

#[test]
fn push_pop_restores_merge() {
    let mut terms = TermStore::new();
    let s1 = terms.mk_string("a".to_string());
    let s2 = terms.mk_var("x", Sort::String);
    let eq = terms.mk_eq(s1, s2);
    let lit = TheoryLit::new(eq, true);

    let mut state = SolverState::new();
    state.register_term(&terms, s1);
    state.register_term(&terms, s2);

    state.push();
    let _ = state.merge(s1, s2, lit);
    assert_eq!(state.find(s1), state.find(s2));

    state.pop();
    assert_ne!(state.find(s1), state.find(s2));
}

#[test]
fn push_pop_restores_eqc_info() {
    let mut terms = TermStore::new();
    let s = terms.mk_string("hello".to_string());

    let mut state = SolverState::new();
    state.push();
    state.register_term(&terms, s);
    assert_eq!(state.get_constant(&s), Some("hello"));
    assert_eq!(state.eqc_info.len(), 1);

    state.pop();
    // Trail-based backtracking properly restores EQC state.
    assert_eq!(state.eqc_info.len(), 0);
    assert!(state.get_constant(&s).is_none());
}

#[test]
fn assert_literal_equality() {
    let mut terms = TermStore::new();
    let s1 = terms.mk_string("hello".to_string());
    let s2 = terms.mk_var("x", Sort::String);
    let eq = terms.mk_eq(s1, s2);

    let mut state = SolverState::new();
    state.assert_literal(&terms, eq, true);

    assert_eq!(state.find(s1), state.find(s2));
}

#[test]
fn assert_literal_disequality() {
    let mut terms = TermStore::new();
    let s1 = terms.mk_string("hello".to_string());
    let s2 = terms.mk_var("x", Sort::String);
    let eq = terms.mk_eq(s1, s2);

    let mut state = SolverState::new();
    state.assert_literal(&terms, eq, false);

    assert_ne!(state.find(s1), state.find(s2));
    assert_eq!(state.disequalities().len(), 1);
}

#[test]
fn assert_literal_len_eq_constant_tracks_known_length() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let len_eq = terms.mk_eq(len_x, two);

    let mut state = SolverState::new();
    state.assert_literal(&terms, len_eq, true);

    assert_eq!(
        state.known_length_full(&terms, x),
        Some(2),
        "asserted len(x) = 2 must be visible to known_length_full"
    );
}

#[test]
fn reset_clears_everything() {
    let mut terms = TermStore::new();
    let s = terms.mk_string("hello".to_string());

    let mut state = SolverState::new();
    state.register_term(&terms, s);
    state.reset();

    assert!(state.disequalities().is_empty());
    assert_eq!(state.eqc_info.len(), 0);
}

#[test]
fn reset_clears_empty_string_id() {
    let mut terms = TermStore::new();
    let empty = terms.mk_string(String::new());

    let mut state = SolverState::new();
    state.register_term(&terms, empty);
    assert!(state.empty_string_id().is_some());

    state.reset();
    assert!(
        state.empty_string_id().is_none(),
        "reset() must clear empty_string_id to avoid stale term references"
    );
}

#[test]
fn pop_on_empty_stack_is_safe() {
    let mut state = SolverState::new();
    state.pop();
}

/// is_empty_string returns true for variables merged with "".
#[test]
fn is_empty_string_eqc_aware() {
    let mut terms = TermStore::new();
    let y = terms.mk_var("y", Sort::String);
    let empty = terms.mk_string(String::new());
    let eq = terms.mk_eq(y, empty);

    let mut state = SolverState::new();
    // Before merge: y is not empty.
    state.register_term(&terms, y);
    state.register_term(&terms, empty);
    assert!(!state.is_empty_string(&terms, y));
    assert!(state.is_empty_string(&terms, empty));

    // After merge: y is in the same EQC as "".
    state.assert_literal(&terms, eq, true);
    assert!(
        state.is_empty_string(&terms, y),
        "y merged with \"\" should be empty"
    );
    assert!(state.is_empty_string(&terms, empty));
}

/// Merging two EQCs with different constants sets pending_conflict.
#[test]
fn merge_constant_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let abc = terms.mk_string("abc".to_string());
    let def = terms.mk_string("def".to_string());
    let eq1 = terms.mk_eq(x, abc);
    let eq2 = terms.mk_eq(x, def);

    let mut state = SolverState::new();
    // x = "abc" → merge x and "abc"
    state.assert_literal(&terms, eq1, true);
    assert!(state.pending_conflict().is_none());
    // x = "def" → merge x (now same EQC as "abc") with "def"
    state.assert_literal(&terms, eq2, true);
    assert!(state.pending_conflict().is_some());
}

/// After push/merge/pop, the loser's EQC info is restored.
///
/// Scenario: register "a" and x, push, merge them, pop.
/// After pop, x's EQC info should be restored (x is its own class).
/// Previously F1 bug: eqc_info.remove(&loser) had no trail entry.
/// Fixed by saving loser EQC info in the Merge trail entry.
#[test]
fn push_pop_merge_restores_loser_eqc_info() {
    let mut terms = TermStore::new();
    let a = terms.mk_string("a".to_string());
    let x = terms.mk_var("x", Sort::String);
    let eq = terms.mk_eq(a, x);
    let lit = TheoryLit::new(eq, true);

    let mut state = SolverState::new();
    state.register_term(&terms, a);
    state.register_term(&terms, x);

    // Before push: both a and x have their own EQC info.
    assert!(state.get_eqc(&a).is_some(), "a should have EQC info");
    assert!(state.get_eqc(&x).is_some(), "x should have EQC info");
    assert_eq!(state.eqc_info.len(), 2);

    state.push();
    let _ = state.merge(a, x, lit);

    // After merge: only winner's EQC remains (loser absorbed).
    assert_eq!(state.eqc_info.len(), 1);

    state.pop();

    // After pop: both EQC infos are restored.
    assert_eq!(
        state.eqc_info.len(),
        2,
        "loser EQC info should be restored after pop"
    );
    assert!(
        state.get_eqc(&a).is_some(),
        "a should have EQC info after pop"
    );
    assert!(
        state.get_eqc(&x).is_some(),
        "x should have EQC info after pop"
    );
}

/// Regression: path compression must not corrupt push/pop.
///
/// Scenario: A → B → C (3-deep chain). With path compression, find(A)
/// would write A → C into parent without a trail entry. After pop, the
/// stale A → C pointer would survive, breaking the union-find.
///
/// With path compression removed, find() only reads the parent map.
#[test]
fn no_path_compression_corruption_on_pop() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::String);
    let b = terms.mk_var("b", Sort::String);
    let c = terms.mk_var("c", Sort::String);
    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let lit_ab = TheoryLit::new(eq_ab, true);
    let lit_bc = TheoryLit::new(eq_bc, true);

    let mut state = SolverState::new();
    state.register_term(&terms, a);
    state.register_term(&terms, b);
    state.register_term(&terms, c);

    // Create chain: merge a-b, then merge b-c → 3-deep chain.
    state.push();
    let _ = state.merge(a, b, lit_ab);
    let _ = state.merge(b, c, lit_bc);

    // All three should be in the same EQC.
    let rep = state.find(a);
    assert_eq!(rep, state.find(b));
    assert_eq!(rep, state.find(c));

    state.pop();

    // After pop: all three should be separate again.
    assert_ne!(state.find(a), state.find(b));
    assert_ne!(state.find(b), state.find(c));
    assert_ne!(state.find(a), state.find(c));
}

/// Pending conflict is undone on pop.
#[test]
fn push_pop_undoes_constant_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let abc = terms.mk_string("abc".to_string());
    let def = terms.mk_string("def".to_string());
    let eq1 = terms.mk_eq(x, abc);
    let eq2 = terms.mk_eq(x, def);

    let mut state = SolverState::new();
    state.assert_literal(&terms, eq1, true);

    state.push();
    state.assert_literal(&terms, eq2, true);
    assert!(state.pending_conflict().is_some());

    state.pop();
    assert!(state.pending_conflict().is_none());
}

/// R237 Finding 2 regression: register_term after pop must recreate EQC info.
///
/// Scenario:
/// 1. push()
/// 2. register_term(t) — creates parent[t] and eqc_info[t]
/// 3. pop() — must remove BOTH parent[t] and eqc_info[t]
/// 4. register_term(t) — must succeed and recreate eqc_info[t]
///
/// Before the fix, pop only removed eqc_info[t] but left parent[t],
/// causing register_term to early-return at the parent check.
#[test]
fn register_after_pop_recreates_eqc_info() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);

    let mut state = SolverState::new();

    state.push();
    state.register_term(&terms, x);
    assert!(
        state.get_eqc(&x).is_some(),
        "EQC info should exist after register"
    );

    state.pop();
    // After pop, both parent and eqc_info should be removed.
    assert!(
        state.get_eqc(&x).is_none(),
        "EQC info should be removed after pop"
    );

    // Re-register after pop must work.
    state.register_term(&terms, x);
    assert!(
        state.get_eqc(&x).is_some(),
        "EQC info should be recreated after re-registration"
    );
}

/// register_term for str.len(x) records length_term on x's EQC.
#[test]
fn register_strlen_records_length_term() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);

    let mut state = SolverState::new();
    state.register_term(&terms, len_x);

    // x should have been registered as a side effect.
    assert!(state.get_eqc(&x).is_some(), "x should be registered");
    assert_eq!(
        state.get_length_term(&x),
        Some(len_x),
        "x's EQC should have length_term = str.len(x)"
    );
}

/// Merge propagates length_term from loser to winner.
#[test]
fn merge_propagates_length_term() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let eq = terms.mk_eq(x, y);
    let lit = TheoryLit::new(eq, true);

    let mut state = SolverState::new();
    state.register_term(&terms, len_x); // registers x and sets length_term
    state.register_term(&terms, y);

    // Before merge: only x has length_term.
    assert!(state.get_length_term(&x).is_some());
    assert!(state.get_length_term(&y).is_none());

    let winner = state.merge(x, y, lit);
    // After merge: winner should have length_term.
    assert!(
        state.get_length_term(&winner).is_some(),
        "winner should have length_term after merge"
    );
}

/// Push/pop restores length_term correctly.
#[test]
fn push_pop_restores_length_term() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    assert!(state.get_length_term(&x).is_none());

    state.push();
    state.register_term(&terms, len_x);
    assert_eq!(state.get_length_term(&x), Some(len_x));

    state.pop();
    assert!(
        state.get_length_term(&x).is_none(),
        "length_term should be cleared after pop"
    );
}

/// are_lengths_equal: same EQC returns true.
#[test]
fn are_lengths_equal_same_eqc() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);

    let mut state = SolverState::new();
    state.register_term(&terms, x);

    assert!(state.are_lengths_equal(&terms, x, x));
}

/// are_lengths_equal: equal constant lengths.
#[test]
fn are_lengths_equal_constant_lengths() {
    let mut terms = TermStore::new();
    let abc = terms.mk_string("abc".to_string());
    let xyz = terms.mk_string("xyz".to_string());

    let mut state = SolverState::new();
    state.register_term(&terms, abc);
    state.register_term(&terms, xyz);

    assert!(
        state.are_lengths_equal(&terms, abc, xyz),
        "\"abc\" and \"xyz\" have equal length 3"
    );
}

/// are_lengths_equal: unequal constant lengths.
#[test]
fn are_lengths_equal_unequal_constant_lengths() {
    let mut terms = TermStore::new();
    let ab = terms.mk_string("ab".to_string());
    let xyz = terms.mk_string("xyz".to_string());

    let mut state = SolverState::new();
    state.register_term(&terms, ab);
    state.register_term(&terms, xyz);

    assert!(
        !state.are_lengths_equal(&terms, ab, xyz),
        "\"ab\" (2) and \"xyz\" (3) have different lengths"
    );
}

/// are_lengths_equal: unknown variable lengths.
#[test]
fn are_lengths_equal_unknown_variables() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, y);

    assert!(
        !state.are_lengths_equal(&terms, x, y),
        "unknown variables without length terms should not be equal"
    );
}

/// is_known_nonempty: variable with disequality to empty string.
///
/// CVC5 reference: `core_solver.cpp:1440-1480` (`explainNonEmpty`).
/// When `x != ""` is asserted, `is_known_nonempty(x)` should return true
/// even though x has no constant value.
#[test]
fn is_known_nonempty_via_disequality_with_empty() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let empty = terms.mk_string(String::new());
    let eq = terms.mk_eq(x, empty);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, empty);

    // Before disequality: x is not known nonempty.
    assert!(
        !state.is_known_nonempty(&terms, x),
        "x should not be known nonempty without constraints"
    );

    // Assert x != "".
    state.assert_literal(&terms, eq, false);

    // After disequality: x is known nonempty.
    assert!(
        state.is_known_nonempty(&terms, x),
        "x != \"\" should make x known nonempty"
    );
}

/// is_known_nonempty: push/pop restores disequality-based nonempty status.
#[test]
fn is_known_nonempty_disequality_push_pop() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let empty = terms.mk_string(String::new());
    let eq = terms.mk_eq(x, empty);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, empty);

    state.push();
    state.assert_literal(&terms, eq, false);
    assert!(state.is_known_nonempty(&terms, x));

    state.pop();
    assert!(
        !state.is_known_nonempty(&terms, x),
        "x should not be known nonempty after pop undoes disequality"
    );
}

/// is_known_nonempty: arithmetic lower-bound reasoning for concat terms.
///
/// `str.++(x, "a")` is always non-empty even when `x` is unconstrained.
/// ArithEntail proves `len(str.++(x, "a")) >= 1` from concat structure.
#[test]
fn is_known_nonempty_via_arith_lower_bound() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let a = terms.mk_string("a".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![x, a], Sort::String);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, a);
    state.register_term(&terms, concat);

    assert!(
        !state.is_known_nonempty(&terms, x),
        "unconstrained variable should remain unknown"
    );
    assert!(
        state.is_known_nonempty(&terms, concat),
        "concat with a non-empty constant suffix must be non-empty"
    );
}

/// are_lengths_disequal: different constant lengths.
#[test]
fn are_lengths_disequal_constant_lengths() {
    let mut terms = TermStore::new();
    let ab = terms.mk_string("ab".to_string());
    let xyz = terms.mk_string("xyz".to_string());

    let mut state = SolverState::new();
    state.register_term(&terms, ab);
    state.register_term(&terms, xyz);

    assert!(
        state.are_lengths_disequal(&terms, ab, xyz),
        "\"ab\" (2) and \"xyz\" (3) have different lengths"
    );
}

/// are_lengths_disequal: equal constant lengths should return false.
#[test]
fn are_lengths_disequal_equal_constant_lengths() {
    let mut terms = TermStore::new();
    let abc = terms.mk_string("abc".to_string());
    let xyz = terms.mk_string("xyz".to_string());

    let mut state = SolverState::new();
    state.register_term(&terms, abc);
    state.register_term(&terms, xyz);

    assert!(
        !state.are_lengths_disequal(&terms, abc, xyz),
        "\"abc\" and \"xyz\" both have length 3"
    );
}

/// are_lengths_disequal: same EQC returns false.
#[test]
fn are_lengths_disequal_same_eqc() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);

    let mut state = SolverState::new();
    state.register_term(&terms, x);

    assert!(
        !state.are_lengths_disequal(&terms, x, x),
        "same term should not have disequal lengths"
    );
}

/// are_lengths_disequal via length term disequality.
///
/// When `len(x) != len(y)` is asserted (as a negated equality on
/// Sort::Int length terms), `are_lengths_disequal(x, y)` should return true.
#[test]
fn are_lengths_disequal_via_length_term_disequality() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = terms.mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
    let len_eq = terms.mk_eq(len_x, len_y);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, y);
    state.register_term(&terms, len_x);
    state.register_term(&terms, len_y);

    // Before assertion: lengths unknown.
    assert!(
        !state.are_lengths_disequal(&terms, x, y),
        "unknown variables should not be disequal"
    );

    // Assert len(x) != len(y).
    state.assert_literal(&terms, len_eq, false);

    // After assertion: lengths are disequal.
    assert!(
        state.are_lengths_disequal(&terms, x, y),
        "len(x) != len(y) should make lengths disequal"
    );
}

/// assert_literal tracks Sort::Int length equalities.
///
/// When `len(x) = len(y)` is asserted, the length terms should be
/// merged in the union-find, enabling `are_lengths_equal`.
#[test]
fn assert_literal_tracks_length_equality() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = terms.mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
    let len_eq = terms.mk_eq(len_x, len_y);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, y);
    state.register_term(&terms, len_x);
    state.register_term(&terms, len_y);

    // Before assertion: lengths unknown.
    assert!(
        !state.are_lengths_equal(&terms, x, y),
        "unknown variable lengths should not be equal"
    );

    // Assert len(x) = len(y).
    state.assert_literal(&terms, len_eq, true);

    // After assertion: lengths are equal.
    assert!(
        state.are_lengths_equal(&terms, x, y),
        "len(x) = len(y) should make lengths equal"
    );
}

/// Bug #3375 regression: assert_literal registers length_term link.
///
/// When `len(x) = len(y)` arrives via assert_literal WITHOUT prior
/// register_term on the len() terms (simulating the executor's
/// LengthSplit clause path), the length_term link must still be
/// established so are_lengths_equal works.
///
/// Root cause: assert_literal used ensure_registered (parent-map only)
/// instead of register_term (which sets up EQC length_term link).
#[test]
fn regression_3375_assert_literal_registers_length_term_link() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = terms.mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
    let len_eq = terms.mk_eq(len_x, len_y);

    let mut state = SolverState::new();
    // Only register the string variables — NOT the len() terms.
    // This simulates the actual execution: the string solver sees x
    // and y from the original assertions, but the len() terms are
    // created by the executor's LengthSplit clause generation.
    state.register_term(&terms, x);
    state.register_term(&terms, y);

    // Before assertion: no length info.
    assert!(!state.are_lengths_equal(&terms, x, y));

    // Assert len(x) = len(y) via assert_literal (as the DPLL layer would).
    state.assert_literal(&terms, len_eq, true);

    // After assertion: lengths must be recognized as equal.
    // This is the bug #3375 regression: previously returned false because
    // ensure_registered didn't establish the length_term link.
    assert!(
        state.are_lengths_equal(&terms, x, y),
        "#3375: assert_literal must register length_term link for len() atoms"
    );
}

/// Bug #3375 regression (disequality path): assert_literal with negated
/// len() equality must also register the length_term link.
#[test]
fn regression_3375_assert_literal_registers_length_term_link_diseq() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = terms.mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
    let len_eq = terms.mk_eq(len_x, len_y);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, y);

    // Assert len(x) != len(y) via assert_literal.
    state.assert_literal(&terms, len_eq, false);

    assert!(
        state.are_lengths_disequal(&terms, x, y),
        "#3375: assert_literal must register length_term link for negated len() atoms"
    );
}

/// Push/pop correctly restores length term disequality tracking.
#[test]
fn are_lengths_disequal_push_pop() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = terms.mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
    let len_eq = terms.mk_eq(len_x, len_y);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, y);
    state.register_term(&terms, len_x);
    state.register_term(&terms, len_y);

    state.push();
    state.assert_literal(&terms, len_eq, false);
    assert!(state.are_lengths_disequal(&terms, x, y));

    state.pop();
    assert!(
        !state.are_lengths_disequal(&terms, x, y),
        "length disequality should be undone after pop"
    );
}

/// Memory safety: push/pop must restore exact state after complex merge
/// sequence involving multiple EQCs, constants, concat terms, and
/// length terms.
///
/// Verifies:
/// 1. EQC info maps are identical before push and after pop
/// 2. Union-find parent pointers are restored
/// 3. Assertions and disequalities are restored
/// 4. Pending conflict is cleared
/// 5. No memory leak from trail entries (trail truncated to push point)
#[test]
fn push_pop_restores_exact_state_after_complex_merges() {
    let mut terms = TermStore::new();

    // Create 4 variables + 2 constants + 1 concat
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let z = terms.mk_var("z", Sort::String);
    let w = terms.mk_var("w", Sort::String);
    let c_hello = terms.mk_string("hello".to_string());
    let c_world = terms.mk_string("world".to_string());
    let concat_xy = terms.mk_app(Symbol::named("str.++"), vec![x, y], Sort::String);
    let len_z = terms.mk_app(Symbol::named("str.len"), vec![z], Sort::Int);
    let len_w = terms.mk_app(Symbol::named("str.len"), vec![w], Sort::Int);

    // Create equality atoms
    let eq_xy = terms.mk_eq(x, y);
    let eq_xz = terms.mk_eq(x, z);
    let eq_wc = terms.mk_eq(w, c_hello);
    let len_eq_zw = terms.mk_eq(len_z, len_w);

    let mut state = SolverState::new();

    // Register all terms
    state.register_term(&terms, x);
    state.register_term(&terms, y);
    state.register_term(&terms, z);
    state.register_term(&terms, w);
    state.register_term(&terms, c_hello);
    state.register_term(&terms, c_world);
    state.register_term(&terms, concat_xy);
    state.register_term(&terms, len_z);
    state.register_term(&terms, len_w);

    // Assert a baseline equality (x = y) before the push scope
    state.assert_literal(&terms, eq_xy, true);

    // Snapshot pre-push state
    let pre_push_assertions_len = state.assertions().len();
    let pre_push_deq_len = state.disequalities().len();
    let pre_push_trail_len = state.trail.len();
    let pre_push_x_rep = state.find(x);
    let pre_push_y_rep = state.find(y);
    let pre_push_z_rep = state.find(z);
    let pre_push_w_rep = state.find(w);
    let pre_push_eqc_count = state.eqc_info.len();
    let pre_push_conflict = state.pending_conflict();

    // Now push and do a complex sequence of merges + disequalities
    state.push();

    // Merge x's EQC with z
    state.assert_literal(&terms, eq_xz, true);
    // Merge w with hello constant
    state.assert_literal(&terms, eq_wc, true);
    // Assert length disequality
    state.assert_literal(&terms, len_eq_zw, false);
    // Assert a string disequality
    let eq_yz = terms.mk_eq(y, z);
    state.assert_literal(&terms, eq_yz, false);

    // Verify intermediate state is modified
    assert_ne!(state.assertions().len(), pre_push_assertions_len);
    assert_ne!(state.disequalities().len(), pre_push_deq_len);

    // Pop should restore everything
    state.pop();

    // Verify exact state restoration
    assert_eq!(
        state.assertions().len(),
        pre_push_assertions_len,
        "assertions count mismatch after pop"
    );
    assert_eq!(
        state.disequalities().len(),
        pre_push_deq_len,
        "disequalities count mismatch after pop"
    );
    assert_eq!(
        state.trail.len(),
        pre_push_trail_len,
        "trail not truncated to push point"
    );
    assert_eq!(
        state.find(x),
        pre_push_x_rep,
        "x representative changed after pop"
    );
    assert_eq!(
        state.find(y),
        pre_push_y_rep,
        "y representative changed after pop"
    );
    assert_eq!(
        state.find(z),
        pre_push_z_rep,
        "z representative restored incorrectly"
    );
    assert_eq!(
        state.find(w),
        pre_push_w_rep,
        "w representative restored incorrectly"
    );
    assert_eq!(
        state.eqc_info.len(),
        pre_push_eqc_count,
        "EQC info map size changed after pop"
    );
    assert_eq!(
        state.pending_conflict(),
        pre_push_conflict,
        "pending conflict changed after pop"
    );

    // Verify w is NOT merged with c_hello anymore
    assert_ne!(
        state.find(w),
        state.find(c_hello),
        "w should not be in hello's EQC after pop"
    );

    // Verify length disequality is gone
    assert!(
        !state.are_lengths_disequal(&terms, z, w),
        "length disequality should be undone"
    );
}

/// Memory safety: nested push/pop scopes must not leak trail entries
/// or corrupt EQC metadata.
///
/// Tests: push → merge → push → merge → pop → verify inner → pop → verify outer
#[test]
fn nested_push_pop_no_leak() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::String);
    let b = terms.mk_var("b", Sort::String);
    let c = terms.mk_var("c", Sort::String);
    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);

    let mut state = SolverState::new();
    state.register_term(&terms, a);
    state.register_term(&terms, b);
    state.register_term(&terms, c);

    let initial_trail = state.trail.len();

    // Outer scope: merge a=b
    state.push();
    state.assert_literal(&terms, eq_ab, true);
    let after_outer_merge_a = state.find(a);
    let after_outer_merge_b = state.find(b);
    assert_eq!(after_outer_merge_a, after_outer_merge_b);

    // Inner scope: merge b=c
    state.push();
    state.assert_literal(&terms, eq_bc, true);
    // All three should be in same EQC
    let rep = state.find(a);
    assert_eq!(state.find(b), rep);
    assert_eq!(state.find(c), rep);

    // Pop inner: b=c undone, but a=b remains
    state.pop();
    assert_eq!(
        state.find(a),
        state.find(b),
        "a=b should persist after inner pop"
    );
    assert_ne!(state.find(a), state.find(c), "a!=c after inner pop");

    // Pop outer: everything undone
    state.pop();
    assert_ne!(state.find(a), state.find(b), "a!=b after outer pop");
    assert_ne!(state.find(b), state.find(c), "b!=c after outer pop");
    assert_eq!(
        state.trail.len(),
        initial_trail,
        "trail must return to initial length"
    );
}

/// Memory safety: pop on fresh state (no push) must not panic.
#[test]
fn pop_without_push_is_noop() {
    let mut state = SolverState::new();
    // Should not panic
    state.pop();
    // State should still be usable
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    state.register_term(&terms, x);
    assert_eq!(state.find(x), x);
}

/// Memory safety: push/pop correctly handles constant-constant merge
/// that creates a pending conflict. After pop, conflict must be cleared.
///
/// Uses a variable as bridge to avoid mk_eq constant folding:
/// x = "abc" and x = "def" → merge x with "abc", then merge x with "def"
/// → pending conflict because "abc" ≠ "def" in the same EQC.
#[test]
fn push_pop_clears_pending_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let c_abc = terms.mk_string("abc".to_string());
    let c_def = terms.mk_string("def".to_string());
    let eq_x_abc = terms.mk_eq(x, c_abc);
    let eq_x_def = terms.mk_eq(x, c_def);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, c_abc);
    state.register_term(&terms, c_def);

    assert!(state.pending_conflict().is_none());

    state.push();
    // First: merge x = "abc" (no conflict yet)
    state.assert_literal(&terms, eq_x_abc, true);
    assert!(
        state.pending_conflict().is_none(),
        "single merge should not create conflict"
    );

    // Second: merge x = "def" → pending conflict because "abc" ≠ "def"
    state.assert_literal(&terms, eq_x_def, true);
    assert!(
        state.pending_conflict().is_some(),
        "merging distinct constants via bridge variable must set pending conflict"
    );

    state.pop();
    assert!(
        state.pending_conflict().is_none(),
        "pending conflict must be cleared after pop"
    );
}

// ── explain() coverage ────────────────────────────────────────

/// explain: identical terms returns empty explanation.
#[test]
fn explain_same_term_returns_empty() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);

    let mut state = SolverState::new();
    state.register_term(&terms, x);

    let reasons = state.explain(x, x);
    assert!(reasons.is_empty(), "explain(x, x) should be empty");
}

/// explain: terms in different EQCs returns empty (#3826).
#[test]
fn explain_different_eqc_returns_empty() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let abc = terms.mk_string("abc".to_string());
    let eq_xa = terms.mk_eq(x, abc);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, y);
    state.assert_literal(&terms, eq_xa, true);

    // x and y are in different EQCs — explain returns empty (#3826).
    let reasons = state.explain(x, y);
    assert!(
        reasons.is_empty(),
        "explain for different EQCs should return empty (no proof path)"
    );

    // explain_or_all also returns empty for different EQCs (#3826).
    // The assertions fallback was removed to prevent false UNSAT.
    let reasons_or_all = state.explain_or_all(x, y);
    assert!(
        reasons_or_all.is_empty(),
        "explain_or_all for different EQCs should also return empty"
    );
}

/// explain: direct merge returns the single merge reason.
#[test]
fn explain_direct_merge_returns_reason() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let eq = terms.mk_eq(x, y);
    let lit = TheoryLit::new(eq, true);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, y);
    let _ = state.merge(x, y, lit);

    let reasons = state.explain(x, y);
    assert!(
        reasons.contains(&lit),
        "explain should include the merge reason"
    );
    assert_eq!(
        reasons.len(),
        1,
        "direct merge should have exactly one reason"
    );
}

/// explain: merge_with_explanation preserves all edge literals.
#[test]
fn explain_multi_literal_merge_preserves_all_reasons() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::String);
    let b = terms.mk_var("b", Sort::String);
    let c = terms.mk_var("c", Sort::String);
    let d = terms.mk_var("d", Sort::String);
    let eq_ab = terms.mk_eq(a, b);
    let eq_ad = terms.mk_eq(a, d);
    let eq_bc = terms.mk_eq(b, c);
    let lit_ab = TheoryLit::new(eq_ab, true);
    let lit_ad = TheoryLit::new(eq_ad, true);
    let lit_bc = TheoryLit::new(eq_bc, true);

    let mut state = SolverState::new();
    state.register_term(&terms, a);
    state.register_term(&terms, b);
    state.register_term(&terms, c);
    state.register_term(&terms, d);
    let _ = state.merge_with_explanation(a, b, &[lit_ab, lit_ad]);
    let _ = state.merge_with_explanation(b, c, &[lit_bc]);

    let reasons = state.explain(a, c);
    assert!(reasons.contains(&lit_ab), "expected a=b edge literal");
    assert!(
        reasons.contains(&lit_ad),
        "expected supplemental edge literal"
    );
    assert!(reasons.contains(&lit_bc), "expected b=c edge literal");
    assert_eq!(reasons.len(), 3, "expected all edge literals");
}

/// explain: transitive merge chain collects all intermediate reasons.
///
/// Merges a=b (reason1) then b=c (reason2). explain(a, c) should
/// return both reasons.
#[test]
fn explain_transitive_chain_collects_all_reasons() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::String);
    let b = terms.mk_var("b", Sort::String);
    let c = terms.mk_var("c", Sort::String);
    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let lit_ab = TheoryLit::new(eq_ab, true);
    let lit_bc = TheoryLit::new(eq_bc, true);

    let mut state = SolverState::new();
    state.register_term(&terms, a);
    state.register_term(&terms, b);
    state.register_term(&terms, c);
    let _ = state.merge(a, b, lit_ab);
    let _ = state.merge(b, c, lit_bc);

    let reasons = state.explain(a, c);
    assert!(
        reasons.contains(&lit_ab),
        "explain should include a=b reason"
    );
    assert!(
        reasons.contains(&lit_bc),
        "explain should include b=c reason"
    );
    assert_eq!(reasons.len(), 2, "chain of 2 merges should give 2 reasons");
}

/// explain: commutative — explain(a,b) and explain(b,a) give same reasons.
#[test]
fn explain_is_commutative() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::String);
    let b = terms.mk_var("b", Sort::String);
    let eq = terms.mk_eq(a, b);
    let lit = TheoryLit::new(eq, true);

    let mut state = SolverState::new();
    state.register_term(&terms, a);
    state.register_term(&terms, b);
    let _ = state.merge(a, b, lit);

    let reasons_ab = state.explain(a, b);
    let reasons_ba = state.explain(b, a);

    // Same set of reasons (order may differ).
    assert_eq!(reasons_ab.len(), reasons_ba.len());
    for r in &reasons_ab {
        assert!(reasons_ba.contains(r));
    }
}

/// explain: after pop, reverted merges no longer appear in explanations.
#[test]
fn explain_after_pop_reverts_merge() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::String);
    let b = terms.mk_var("b", Sort::String);
    let c = terms.mk_var("c", Sort::String);
    let d = terms.mk_var("d", Sort::String);
    let eq_ab = terms.mk_eq(a, b);
    let eq_cd = terms.mk_eq(c, d);
    let lit_ab = TheoryLit::new(eq_ab, true);
    let lit_cd = TheoryLit::new(eq_cd, true);

    let mut state = SolverState::new();
    state.register_term(&terms, a);
    state.register_term(&terms, b);
    state.assert_literal(&terms, eq_cd, true);
    assert!(
        state.assertions().contains(&lit_cd),
        "sanity: keep at least one unrelated asserted literal"
    );

    state.push();
    let _ = state.merge(a, b, lit_ab);
    assert_eq!(state.explain(a, b).len(), 1, "before pop: one reason");

    state.pop();
    // After pop, a and b are in different EQCs.
    assert_ne!(state.find(a), state.find(b), "after pop: different EQCs");
    let reasons = state.explain(a, b);
    assert!(
        reasons.is_empty(),
        "after pop: explain must return empty (no assertions fallback)"
    );
    assert!(
        !reasons.contains(&lit_ab),
        "after pop: reverted merge reason must not appear"
    );
}

/// explain: 4-term chain a=b=c=d collects all 3 intermediate reasons.
#[test]
fn explain_four_term_chain() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::String);
    let b = terms.mk_var("b", Sort::String);
    let c = terms.mk_var("c", Sort::String);
    let d = terms.mk_var("d", Sort::String);
    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_cd = terms.mk_eq(c, d);
    let lit_ab = TheoryLit::new(eq_ab, true);
    let lit_bc = TheoryLit::new(eq_bc, true);
    let lit_cd = TheoryLit::new(eq_cd, true);

    let mut state = SolverState::new();
    state.register_term(&terms, a);
    state.register_term(&terms, b);
    state.register_term(&terms, c);
    state.register_term(&terms, d);
    let _ = state.merge(a, b, lit_ab);
    let _ = state.merge(b, c, lit_bc);
    let _ = state.merge(c, d, lit_cd);

    let reasons = state.explain(a, d);
    assert!(reasons.contains(&lit_ab), "should include a=b");
    assert!(reasons.contains(&lit_bc), "should include b=c");
    assert!(reasons.contains(&lit_cd), "should include c=d");
    assert_eq!(reasons.len(), 3, "chain of 3 merges should give 3 reasons");
}

// ── known_length() coverage ───────────────────────────────────

/// known_length: constant string returns character count.
#[test]
fn known_length_constant_string() {
    let mut terms = TermStore::new();
    let abc = terms.mk_string("abc".to_string());

    let mut state = SolverState::new();
    state.register_term(&terms, abc);

    assert_eq!(state.known_length(&terms, abc), Some(3));
}

/// known_length: empty string returns 0.
#[test]
fn known_length_empty_string() {
    let mut terms = TermStore::new();
    let empty = terms.mk_string(String::new());

    let mut state = SolverState::new();
    state.register_term(&terms, empty);

    assert_eq!(state.known_length(&terms, empty), Some(0));
}

/// known_length: variable returns None.
#[test]
fn known_length_variable_returns_none() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);

    let mut state = SolverState::new();
    state.register_term(&terms, x);

    assert_eq!(state.known_length(&terms, x), None);
}

/// known_length: variable merged with constant gets constant's length.
#[test]
fn known_length_via_eqc_constant() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let hello = terms.mk_string("hello".to_string());
    let eq = terms.mk_eq(x, hello);

    let mut state = SolverState::new();
    state.assert_literal(&terms, eq, true);

    let rep = state.find(x);
    assert_eq!(state.known_length(&terms, rep), Some(5));
}

// ── resolve_int_constant() coverage ───────────────────────────

/// resolve_int_constant: integer constant returns its value.
#[test]
fn resolve_int_constant_literal() {
    let mut terms = TermStore::new();
    let n = terms.mk_int(BigInt::from(42));

    let state = SolverState::new();
    assert_eq!(state.resolve_int_constant(&terms, n), Some(42));
}

/// resolve_int_constant: string variable returns None.
#[test]
fn resolve_int_constant_variable_returns_none() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);

    let mut state = SolverState::new();
    state.register_term(&terms, x);

    assert_eq!(state.resolve_int_constant(&terms, x), None);
}

#[test]
fn resolve_int_constant_finds_constant_in_merged_eqc() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let len_eq = terms.mk_eq(len_x, two);

    let mut state = SolverState::new();
    state.assert_literal(&terms, len_eq, true);

    assert_eq!(state.resolve_int_constant(&terms, len_x), Some(2));
}

// ── eqc_representatives() coverage ────────────────────────────

/// eqc_representatives: returns all registered reps in sorted order.
#[test]
fn eqc_representatives_sorted() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let z = terms.mk_var("z", Sort::String);

    let mut state = SolverState::new();
    state.register_term(&terms, z);
    state.register_term(&terms, x);
    state.register_term(&terms, y);

    let reps = state.eqc_representatives();
    assert_eq!(reps.len(), 3);
    // Verify sorted order.
    for w in reps.windows(2) {
        assert!(w[0] <= w[1], "representatives should be sorted");
    }
}

/// eqc_representatives: merged EQCs reduce count.
#[test]
fn eqc_representatives_after_merge() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let eq = terms.mk_eq(x, y);
    let lit = TheoryLit::new(eq, true);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, y);
    assert_eq!(state.eqc_representatives().len(), 2);

    let _ = state.merge(x, y, lit);
    assert_eq!(
        state.eqc_representatives().len(),
        1,
        "merge should reduce representative count"
    );
}

// ── empty_string_id() / set_empty_string_id() coverage ───────

/// empty_string_id: returns None before set.
#[test]
fn empty_string_id_initially_none() {
    let state = SolverState::new();
    assert!(state.empty_string_id().is_none());
}

/// set_empty_string_id / empty_string_id roundtrip.
#[test]
fn set_and_get_empty_string_id() {
    let mut terms = TermStore::new();
    let empty = terms.mk_string(String::new());

    let mut state = SolverState::new();
    state.set_empty_string_id(&terms, empty);

    assert_eq!(state.empty_string_id(), Some(empty));
}

#[test]
fn empty_rep_detection_survives_missing_constant_metadata() {
    let mut terms = TermStore::new();
    let empty = terms.mk_string(String::new());
    let x = terms.mk_var("x", Sort::String);
    let eq = terms.mk_eq(x, empty);

    let mut state = SolverState::new();
    state.set_empty_string_id(&terms, empty);
    state.assert_literal(&terms, eq, true);

    let rep = state.find(x);
    state
        .eqc_info
        .get_mut(&rep)
        .expect("merged empty EQC should exist")
        .constant = None;

    assert!(
        state.is_empty_string(&terms, x),
        "registered empty-string representative should classify merged aliases as empty"
    );
    assert_eq!(
        state.find_constant_term_id(&terms, x),
        Some(empty),
        "registered empty-string term should still be returned as the concrete empty constant"
    );
}

// ── get_concat_children() coverage ────────────────────────────

/// get_concat_children: concat term returns its children.
#[test]
fn get_concat_children_returns_children() {
    let mut terms = TermStore::new();
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let ab = terms.mk_app(Symbol::named("str.++"), vec![a, b], Sort::String);

    let state = SolverState::new();
    let children = state.get_concat_children(&terms, ab).unwrap();
    assert_eq!(children, &[a, b]);
}

/// get_concat_children: non-concat term returns None.
#[test]
fn get_concat_children_non_concat_returns_none() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);

    let state = SolverState::new();
    assert!(state.get_concat_children(&terms, x).is_none());
}

// ── get_str_len_arg() coverage ────────────────────────────────

/// get_str_len_arg: str.len(x) returns Some(x).
#[test]
fn get_str_len_arg_returns_argument() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);

    let state = SolverState::new();
    assert_eq!(state.get_str_len_arg(&terms, len_x), Some(x));
}

/// get_str_len_arg: non-len term returns None.
#[test]
fn get_str_len_arg_non_len_returns_none() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);

    let state = SolverState::new();
    assert_eq!(state.get_str_len_arg(&terms, x), None);
}
