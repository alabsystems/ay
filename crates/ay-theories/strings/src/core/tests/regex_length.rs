// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regex length-set disjointness (`check_regex_length_disjoint`): the conflict
//! it learns must carry every literal behind the length it refutes.
//!
//! Regression for a false UNSAT: the explanation used to name only the asserted
//! equality `(= (str.len x) t)` whose int side `t` merely RESOLVED to the
//! refuted length through its equivalence class, dropping the literals that put
//! the constant there. The learned clause `¬in_re(x, R) ∨ ¬(len(x) = t)` is not
//! valid, and when `(= (str.len x) t)` is an axiom (the replace-result length
//! congruence `len(replace(..)) = len(sk_rep_res)`) it refuted the membership
//! outright: `(str.in_re (str.replace b "z" "") (re.union (str.to_re "u")
//! re.none))` answered `unsat` (b = "u" satisfies it), as did cvc5's
//! `regress0/strings/issue8481.smt2`.

use super::*;
use ay_core::TheoryResult;

fn str_to_re(terms: &mut TermStore, s: &str) -> TermId {
    let c = terms.mk_string(s.to_string());
    terms.mk_app(Symbol::named("str.to_re"), vec![c], Sort::RegLan)
}

/// `(re.union (str.to_re "ab") (str.to_re "cd"))`: accepted lengths `{2}`.
fn length_two_regex(terms: &mut TermStore) -> TermId {
    let ab = str_to_re(terms, "ab");
    let cd = str_to_re(terms, "cd");
    terms.mk_app(Symbol::named("re.union"), vec![ab, cd], Sort::RegLan)
}

fn str_len(terms: &mut TermStore, s: TermId) -> TermId {
    terms.mk_app(Symbol::named("str.len"), vec![s], Sort::Int)
}

fn conflict_of(terms: &TermStore, state: &SolverState) -> Option<Vec<TheoryLit>> {
    let mut infer = InferenceManager::new();
    let mut core = CoreSolver::new();
    if !core.check_regex_length_disjoint(terms, state, &mut infer) {
        return None;
    }
    match infer.to_theory_result() {
        TheoryResult::Unsat(lits) => Some(lits),
        other => panic!("a fired length-disjointness check must yield Unsat, got {other:?}"),
    }
}

/// `in_re(x, R)`, `len(x) = len(k)`, `len(k) = 0`: jointly UNSAT, but only
/// because of `len(k) = 0`. Without that literal the other two are satisfied by
/// `x = k = "ab"`, so a conflict that omits it refutes a satisfiable set.
#[test]
fn length_reached_through_an_int_eqc_explains_the_constant() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let k = terms.mk_var("k", Sort::String);
    let re = length_two_regex(&mut terms);
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![x, re], Sort::Bool);
    let len_x = str_len(&mut terms, x);
    let len_k = str_len(&mut terms, k);
    let zero = terms.mk_int(BigInt::from(0));
    let len_x_eq_len_k = terms.mk_eq(len_x, len_k);
    let len_k_eq_zero = terms.mk_eq(len_k, zero);

    let mut state = SolverState::new();
    state.assert_literal(&terms, in_re, true);
    state.assert_literal(&terms, len_x_eq_len_k, true);
    state.assert_literal(&terms, len_k_eq_zero, true);
    assert_eq!(state.known_length_full(&terms, x), Some(0));

    let conflict =
        conflict_of(&terms, &state).expect("len(x) = 0 is outside {2}: the conflict must fire");
    for (lit, what) in [
        (in_re, "the membership"),
        (len_x_eq_len_k, "len(x) = len(k)"),
        (len_k_eq_zero, "len(k) = 0"),
    ] {
        assert!(
            conflict.contains(&TheoryLit::new(lit, true)),
            "the conflict must name {what}; without it the explained set is \
             satisfiable and the learned clause is a false refutation: {conflict:?}"
        );
    }
}

/// The documented strong clause survives: a directly asserted
/// `(= (str.len x) 3)` is the whole length reason.
#[test]
fn directly_asserted_length_is_the_whole_reason() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let re = length_two_regex(&mut terms);
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![x, re], Sort::Bool);
    let len_x = str_len(&mut terms, x);
    let three = terms.mk_int(BigInt::from(3));
    let len_x_eq_three = terms.mk_eq(len_x, three);

    let mut state = SolverState::new();
    state.assert_literal(&terms, in_re, true);
    state.assert_literal(&terms, len_x_eq_three, true);

    let mut conflict = conflict_of(&terms, &state).expect("len(x) = 3 is outside {2}");
    conflict.sort_by_key(|lit| lit.term);
    let mut expected = vec![
        TheoryLit::new(in_re, true),
        TheoryLit::new(len_x_eq_three, true),
    ];
    expected.sort_by_key(|lit| lit.term);
    assert_eq!(conflict, expected);
}

/// `Σ*·"Z"·Σ*` ("contains Z").
fn contains_z_regex(terms: &mut TermStore) -> TermId {
    let allchar = terms.mk_app(Symbol::named("re.allchar"), vec![], Sort::RegLan);
    let star = terms.mk_app(Symbol::named("re.*"), vec![allchar], Sort::RegLan);
    let z = str_to_re(terms, "Z");
    let zstar = terms.mk_app(Symbol::named("re.++"), vec![z, star], Sort::RegLan);
    terms.mk_app(Symbol::named("re.++"), vec![star, zstar], Sort::RegLan)
}

fn membership_conflict_of(terms: &TermStore, state: &SolverState) -> Option<Vec<TheoryLit>> {
    let mut infer = InferenceManager::new();
    let mut core = CoreSolver::new();
    if !core.check_regex_membership_violations(terms, state, &mut infer) {
        return None;
    }
    match infer.to_theory_result() {
        TheoryResult::Unsat(lits) => Some(lits),
        other => panic!("a fired membership check must yield Unsat, got {other:?}"),
    }
}

/// The slog shape (minimised `slog_stranger_2391_sink`): `x`'s EQC has
/// NO constant — its value exists only through the concat member
/// `"ab"·v·"cd"` once the SAT layer decides `v = ""`. The ground
/// membership check must still refute `x ∈ Σ*·"Z"·Σ*`, and the
/// conflict must name every literal behind `x = "abcd"`.
#[test]
fn membership_violation_fires_through_eqc_concat_member() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let v = terms.mk_var("v", Sort::String);
    let ab = terms.mk_string("ab".to_string());
    let cd = terms.mk_string("cd".to_string());
    let empty = terms.mk_string(String::new());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![ab, v, cd], Sort::String);
    let x_eq_concat = terms.mk_eq(x, concat);
    let v_eq_empty = terms.mk_eq(v, empty);
    let re = contains_z_regex(&mut terms);
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![x, re], Sort::Bool);

    let mut state = SolverState::new();
    state.assert_literal(&terms, x_eq_concat, true);
    state.assert_literal(&terms, v_eq_empty, true);
    state.assert_literal(&terms, in_re, true);

    let conflict = membership_conflict_of(&terms, &state)
        .expect("x = \"abcd\" is outside Sigma*.Z.Sigma*: the conflict must fire");
    for (lit, what) in [
        (in_re, "the membership"),
        (x_eq_concat, "x = concat"),
        (v_eq_empty, "v = \"\""),
    ] {
        assert!(
            conflict.contains(&TheoryLit::new(lit, true)),
            "the conflict must name {what}; without it the explained set is \
             satisfiable and the learned clause is a false refutation: {conflict:?}"
        );
    }
}

/// Same shape with `v = "Z"`: `x = "abZcd"` satisfies the membership,
/// so no conflict may fire.
#[test]
fn membership_through_concat_member_does_not_fire_when_satisfied() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let v = terms.mk_var("v", Sort::String);
    let ab = terms.mk_string("ab".to_string());
    let cd = terms.mk_string("cd".to_string());
    let z = terms.mk_string("Z".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![ab, v, cd], Sort::String);
    let x_eq_concat = terms.mk_eq(x, concat);
    let v_eq_z = terms.mk_eq(v, z);
    let re = contains_z_regex(&mut terms);
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![x, re], Sort::Bool);

    let mut state = SolverState::new();
    state.assert_literal(&terms, x_eq_concat, true);
    state.assert_literal(&terms, v_eq_z, true);
    state.assert_literal(&terms, in_re, true);

    assert_eq!(membership_conflict_of(&terms, &state), None);
}

/// With `v` unresolved there is no ground value for `x` at all.
#[test]
fn membership_through_concat_member_does_not_fire_when_unresolved() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let v = terms.mk_var("v", Sort::String);
    let ab = terms.mk_string("ab".to_string());
    let cd = terms.mk_string("cd".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![ab, v, cd], Sort::String);
    let x_eq_concat = terms.mk_eq(x, concat);
    let re = contains_z_regex(&mut terms);
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![x, re], Sort::Bool);

    let mut state = SolverState::new();
    state.assert_literal(&terms, x_eq_concat, true);
    state.assert_literal(&terms, in_re, true);

    assert_eq!(membership_conflict_of(&terms, &state), None);
}

/// A length that is not known does not fire at all.
#[test]
fn unknown_length_does_not_fire() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let k = terms.mk_var("k", Sort::String);
    let re = length_two_regex(&mut terms);
    let in_re = terms.mk_app(Symbol::named("str.in_re"), vec![x, re], Sort::Bool);
    let len_x = str_len(&mut terms, x);
    let len_k = str_len(&mut terms, k);
    let len_x_eq_len_k = terms.mk_eq(len_x, len_k);

    let mut state = SolverState::new();
    state.assert_literal(&terms, in_re, true);
    state.assert_literal(&terms, len_x_eq_len_k, true);

    assert_eq!(conflict_of(&terms, &state), None);
}
