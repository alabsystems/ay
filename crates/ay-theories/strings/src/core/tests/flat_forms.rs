// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Flat-form tests: constant containment, pairwise unification, endpoint inference.

use super::*;
use ay_core::term::Symbol;
use ay_core::Sort;

/// Flat form constant containment: when an EQC has a constant and a concat
/// member whose flat form has a constant component not found in order,
/// the mismatch is deferred to the full NF pass (not raised as a flat
/// form conflict). This avoids over-approximate explanations.
///
/// The actual conflict ("d" not in "abc") is detected by
/// `check_normal_forms_eq` with a sound explanation.
#[test]
fn flat_form_constant_containment_conflict() {
    let mut terms = TermStore::new();
    let d = terms.mk_string("d".to_string());
    let x = terms.mk_var("x", Sort::String);
    // str.++(x, "d")
    let concat = terms.mk_app(Symbol::named("str.++"), vec![x, d], Sort::String);
    // "abc"
    let abc = terms.mk_string("abc".to_string());
    // str.++(x, "d") = "abc"
    let eq = terms.mk_eq(concat, abc);

    let mut state = SolverState::new();
    state.assert_literal(&terms, eq, true);

    let mut core = CoreSolver::new();
    core.build_flat_forms(&terms, &state);

    // Flat form of concat = [x_rep, d_rep].
    // EQC of concat has constant "abc". "d" is not found in "abc".
    // Flat forms defer this to the full NF pass for sound explanations.
    let mut infer = InferenceManager::new();
    let result = core.check_flat_forms(&terms, &state, &mut infer);
    assert!(!result, "flat forms defer constant mismatch to NF pass");
    assert!(!infer.has_conflict());
}

/// Flat form pairwise unify: when two concat terms in the same EQC have
/// components at the same index with equal known lengths but different
/// representatives, infer they are equal.
#[test]
fn flat_form_pairwise_unify() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    // str.++(x, "a")
    let concat1 = terms.mk_app(Symbol::named("str.++"), vec![x, a], Sort::String);
    // str.++(y, "b")
    let concat2 = terms.mk_app(Symbol::named("str.++"), vec![y, b], Sort::String);
    // str.++(x, "a") = str.++(y, "b")
    let eq_concats = terms.mk_eq(concat1, concat2);
    // len(x) = len(y)
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = terms.mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
    let len_eq = terms.mk_eq(len_x, len_y);

    let mut state = SolverState::new();
    state.assert_literal(&terms, len_eq, true);
    state.assert_literal(&terms, eq_concats, true);

    let mut core = CoreSolver::new();
    core.build_flat_forms(&terms, &state);

    let mut infer = InferenceManager::new();
    let conflict = core.check_flat_forms(&terms, &state, &mut infer);
    // Not a conflict — but should produce an internal equality x = y.
    assert!(
        !conflict,
        "should not be a conflict, but an internal equality"
    );
    assert!(
        infer.has_internal_equalities(),
        "flat form should infer x = y via F_UNIFY"
    );
    let eqs = infer.drain_internal_equalities();
    assert_eq!(eqs.len(), 1);
    // The equality is between x and y (or their reps).
    let (lhs, rhs) = (eqs[0].lhs, eqs[0].rhs);
    let lhs_rep = state.find(lhs);
    let rhs_rep = state.find(rhs);
    assert!(
        (lhs_rep == state.find(x) && rhs_rep == state.find(y))
            || (lhs_rep == state.find(y) && rhs_rep == state.find(x)),
        "expected equality between x and y reps"
    );
}

/// Flat form endpoint empty: when one flat form is longer than the other
/// in the same EQC, excess components must be empty.
#[test]
fn flat_form_endpoint_empty() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let empty = terms.mk_string(String::new());
    // str.++(x)
    let concat1 = terms.mk_app(Symbol::named("str.++"), vec![x], Sort::String);
    // str.++(x, y)
    let concat2 = terms.mk_app(Symbol::named("str.++"), vec![x, y], Sort::String);
    // str.++(x) = str.++(x, y)
    let eq = terms.mk_eq(concat1, concat2);

    let mut state = SolverState::new();
    state.set_empty_string_id(&terms, empty);
    state.assert_literal(&terms, eq, true);

    let mut core = CoreSolver::new();
    core.build_flat_forms(&terms, &state);

    let mut infer = InferenceManager::new();
    let conflict = core.check_flat_forms(&terms, &state, &mut infer);
    assert!(
        !conflict,
        "should not be a conflict, but an internal equality (y = empty)"
    );
    assert!(
        infer.has_internal_equalities(),
        "flat form should infer y = '' via F_ENDPOINT_EMP"
    );
    let eqs = infer.drain_internal_equalities();
    assert_eq!(eqs.len(), 1);
    assert_eq!(state.find(eqs[0].rhs), state.find(empty));
}

/// Flat form constant prefix bailout: when two constant components at the
/// same index are in a prefix relationship (one starts with the other),
/// compare_flat_forms should bail (return false) without conflict.
/// The full NF computation handles this case.
#[test]
fn flat_form_constant_prefix_bails_no_conflict() {
    let mut terms = TermStore::new();
    let ab = terms.mk_string("ab".to_string());
    let abc = terms.mk_string("abc".to_string());
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    // str.++(ab, x)
    let concat1 = terms.mk_app(Symbol::named("str.++"), vec![ab, x], Sort::String);
    // str.++(abc, y)
    let concat2 = terms.mk_app(Symbol::named("str.++"), vec![abc, y], Sort::String);
    // str.++(ab, x) = str.++(abc, y)
    let eq = terms.mk_eq(concat1, concat2);

    let mut state = SolverState::new();
    state.assert_literal(&terms, eq, true);

    let mut core = CoreSolver::new();
    core.build_flat_forms(&terms, &state);

    let mut infer = InferenceManager::new();
    let conflict = core.check_flat_forms(&terms, &state, &mut infer);
    assert!(
        !conflict,
        "prefix relationship (\"ab\" vs \"abc\") should not be a conflict"
    );
    // No internal equalities either — bailed out.
    assert!(
        !infer.has_internal_equalities(),
        "prefix bailout should not produce internal equalities"
    );
}

/// Flat form constant incompatibility at same index: "ab" vs "cd" are
/// neither prefixes of each other. Flat forms defer this mismatch to
/// the full NF pass for sound conflict explanations.
#[test]
fn flat_form_constant_incompatible_is_conflict() {
    let mut terms = TermStore::new();
    let ab = terms.mk_string("ab".to_string());
    let cd = terms.mk_string("cd".to_string());
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    // str.++(ab, x)
    let concat1 = terms.mk_app(Symbol::named("str.++"), vec![ab, x], Sort::String);
    // str.++(cd, y)
    let concat2 = terms.mk_app(Symbol::named("str.++"), vec![cd, y], Sort::String);
    // str.++(ab, x) = str.++(cd, y)
    let eq = terms.mk_eq(concat1, concat2);

    let mut state = SolverState::new();
    state.assert_literal(&terms, eq, true);

    let mut core = CoreSolver::new();
    core.build_flat_forms(&terms, &state);

    let mut infer = InferenceManager::new();
    let conflict = core.check_flat_forms(&terms, &state, &mut infer);
    assert!(!conflict, "flat forms defer constant mismatch to NF pass");
    assert!(!infer.has_conflict());
}

/// Flat form constant containment: when multiple constants appear in
/// order within the EQC constant, no conflict is raised.
#[test]
fn flat_form_constant_containment_no_conflict_when_in_order() {
    let mut terms = TermStore::new();
    let a = terms.mk_string("a".to_string());
    let c = terms.mk_string("c".to_string());
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    // str.++(a, x, c, y)
    let concat = terms.mk_app(Symbol::named("str.++"), vec![a, x, c, y], Sort::String);
    // "abcd"
    let abcd = terms.mk_string("abcd".to_string());
    // str.++(a, x, c, y) = "abcd"
    let eq = terms.mk_eq(concat, abcd);

    let mut state = SolverState::new();
    state.assert_literal(&terms, eq, true);

    let mut core = CoreSolver::new();
    core.build_flat_forms(&terms, &state);

    let mut infer = InferenceManager::new();
    let conflict = core.check_flat_forms(&terms, &state, &mut infer);
    assert!(
        !conflict,
        "'a' at pos 0 and 'c' at pos 2 in 'abcd' — in order, no conflict"
    );
}

/// Flat form endpoint equality: when both flat forms have exactly one
/// remaining component at the end with different reps, infer equality.
#[test]
fn flat_form_endpoint_eq_inference() {
    let mut terms = TermStore::new();
    let a = terms.mk_string("a".to_string());
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    // str.++("a", x)
    let concat1 = terms.mk_app(Symbol::named("str.++"), vec![a, x], Sort::String);
    // Create a second "a" constant to share the same value.
    let a2 = terms.mk_string("a".to_string());
    // str.++("a", y)
    let concat2 = terms.mk_app(Symbol::named("str.++"), vec![a2, y], Sort::String);
    // str.++("a", x) = str.++("a", y)
    let eq = terms.mk_eq(concat1, concat2);

    let mut state = SolverState::new();
    state.assert_literal(&terms, eq, true);

    let mut core = CoreSolver::new();
    core.build_flat_forms(&terms, &state);

    let mut infer = InferenceManager::new();
    let conflict = core.check_flat_forms(&terms, &state, &mut infer);
    assert!(
        !conflict,
        "endpoint-eq is not a conflict, just an equality inference"
    );
    assert!(
        infer.has_internal_equalities(),
        "should infer x = y via F_ENDPOINT_EQ"
    );
    let eqs = infer.drain_internal_equalities();
    assert_eq!(eqs.len(), 1);
    let (lhs, rhs) = (eqs[0].lhs, eqs[0].rhs);
    let lhs_rep = state.find(lhs);
    let rhs_rep = state.find(rhs);
    assert!(
        (lhs_rep == state.find(x) && rhs_rep == state.find(y))
            || (lhs_rep == state.find(y) && rhs_rep == state.find(x)),
        "expected equality between x and y reps"
    );
}

/// Flat form endpoint-eq: two single-component flat forms with different
/// reps in the same EQC should infer equality (F_ENDPOINT_EQ).
#[test]
fn flat_form_endpoint_eq_single_component() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    // Build concat terms: str.++(x) and str.++(y)
    let cx = terms.mk_app(Symbol::named("str.++"), vec![x], Sort::String);
    let cy = terms.mk_app(Symbol::named("str.++"), vec![y], Sort::String);
    let eq = terms.mk_eq(cx, cy);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, y);
    state.register_term(&terms, cx);
    state.register_term(&terms, cy);
    state.assert_literal(&terms, eq, true); // cx = cy

    let mut core = CoreSolver::new();
    core.build_flat_forms(&terms, &state);
    let mut infer = InferenceManager::new();
    let conflict = core.check_flat_forms(&terms, &state, &mut infer);

    assert!(!conflict, "no conflict expected from endpoint-eq");
    assert!(
        infer.has_internal_equalities(),
        "endpoint-eq should produce an internal equality (x = y)"
    );
}

/// Flat form endpoint-empty: a 2-component flat form vs a 1-component flat
/// form in the same EQC should infer the extra component is empty.
#[test]
fn flat_form_endpoint_empty_infers_empty() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let empty = terms.mk_string(String::new());
    // str.++(x) vs str.++(x, y)
    let cx = terms.mk_app(Symbol::named("str.++"), vec![x], Sort::String);
    let cxy = terms.mk_app(Symbol::named("str.++"), vec![x, y], Sort::String);
    let eq = terms.mk_eq(cx, cxy);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, y);
    state.register_term(&terms, empty); // register empty so empty_string_id is set
    state.register_term(&terms, cx);
    state.register_term(&terms, cxy);
    state.assert_literal(&terms, eq, true);

    let mut core = CoreSolver::new();
    core.build_flat_forms(&terms, &state);
    let mut infer = InferenceManager::new();
    let conflict = core.check_flat_forms(&terms, &state, &mut infer);

    assert!(!conflict, "no conflict expected from endpoint-empty");
    // The flat form of cx is [x], the flat form of cxy is [x, y].
    // After matching x==x, y should be inferred empty.
    assert!(
        infer.has_internal_equalities(),
        "endpoint-empty should infer y = \"\""
    );
}

/// Flat form same-rep components: when flat forms match exactly, no
/// inferences or conflicts are produced.
#[test]
fn flat_form_same_rep_no_inference() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    // str.++(x, y) and str.++(x, y) — same structure in same EQC
    let c1 = terms.mk_app(Symbol::named("str.++"), vec![x, y], Sort::String);
    let c2 = terms.mk_app(Symbol::named("str.++"), vec![x, y], Sort::String);
    let eq = terms.mk_eq(c1, c2);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, y);
    state.register_term(&terms, c1);
    state.register_term(&terms, c2);
    state.assert_literal(&terms, eq, true);

    let mut core = CoreSolver::new();
    core.build_flat_forms(&terms, &state);
    let mut infer = InferenceManager::new();
    let conflict = core.check_flat_forms(&terms, &state, &mut infer);

    assert!(!conflict, "identical flat forms should not conflict");
    assert!(
        !infer.has_internal_equalities(),
        "identical flat forms need no inferences"
    );
}

/// Flat form constant mismatch: two constants with incompatible prefixes
/// should defer to NF (no conflict at flat form level).
#[test]
fn flat_form_constant_mismatch_defers_to_nf() {
    let mut terms = TermStore::new();
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let x = terms.mk_var("x", Sort::String);
    // str.++(a, x) and str.++(b, x) in same EQC
    let cax = terms.mk_app(Symbol::named("str.++"), vec![a, x], Sort::String);
    let cbx = terms.mk_app(Symbol::named("str.++"), vec![b, x], Sort::String);
    let eq = terms.mk_eq(cax, cbx);

    let mut state = SolverState::new();
    state.register_term(&terms, a);
    state.register_term(&terms, b);
    state.register_term(&terms, x);
    state.register_term(&terms, cax);
    state.register_term(&terms, cbx);
    state.assert_literal(&terms, eq, true);

    let mut core = CoreSolver::new();
    core.build_flat_forms(&terms, &state);
    let mut infer = InferenceManager::new();
    let conflict = core.check_flat_forms(&terms, &state, &mut infer);

    // Flat forms defer constant mismatches to full NF checks.
    assert!(
        !conflict,
        "constant mismatch should not conflict at flat form level"
    );
    assert!(
        !infer.has_internal_equalities(),
        "constant mismatch should not produce inferences at flat form level"
    );
}
