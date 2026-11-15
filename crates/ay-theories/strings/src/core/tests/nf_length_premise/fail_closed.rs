// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Negative twins of the `nf_length_premise` tests: when a premise an NF,
//! flat-form or `str.to_code` inference reads is known only through a merge
//! the proof forest cannot explain (an empty-reason merge or a pure
//! `ArithEntail` bound), the inference must not fire. Falling back to the
//! alignment alone would learn a clause that refutes a satisfiable input,
//! the laundering pattern upstream 0eb3642a4 removed from the regex length
//! check.

use super::*;

/// Negative twin of `n_unify_carries_the_decided_length`: here `len(x) = 1`
/// holds only through `len(x) = len(w) + 1` and `w = ""`, which `ArithEntail`
/// derives from bounds but the proof forest cannot explain as one length
/// fact. N_UNIFY must then stay silent (the splits decide) rather than fall
/// back to the alignment alone, as the `--str-nf` closure-2 path did.
#[test]
fn n_unify_on_an_unexplainable_length_does_not_fire() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let z = terms.mk_var("z", Sort::String);
    let w = terms.mk_var("w", Sort::String);
    let a = terms.mk_string("a".to_string());
    let empty = terms.mk_string(String::new());
    let one = terms.mk_int(BigInt::from(1));
    // Built before len(x) so it wins the union-find tie and represents the
    // length class: ArithEntail bounds only the representative.
    let len_w = str_len(&mut terms, w);
    let len_w_plus_one = terms.mk_app(Symbol::named("+"), vec![len_w, one], Sort::Int);
    let lhs = concat(&mut terms, vec![x, y]);
    let rhs = concat(&mut terms, vec![a, z]);
    let input = terms.mk_eq(lhs, rhs);
    let len_x = str_len(&mut terms, x);
    let len_a = str_len(&mut terms, a);
    let w_is_empty = terms.mk_eq(w, empty);
    let len_x_is_len_w_plus_one = terms.mk_eq(len_w_plus_one, len_x);
    let len_a_is_one = terms.mk_eq(len_a, one);

    let mut state = SolverState::new();
    state.assert_literal(&terms, input, true);
    state.assert_literal(&terms, len_a_is_one, true);
    state.assert_literal(&terms, w_is_empty, true);
    state.assert_literal(&terms, len_x_is_len_w_plus_one, true);
    assert!(
        CoreSolver::are_lengths_equal_with_entail(&terms, &state, x, a),
        "precondition: len(x) = len(\"a\") must be entailed, or this test is vacuous"
    );
    let (nf1, nf2) = nf_pair(lhs, vec![x, y], rhs, vec![a, z]);

    let mut infer = InferenceManager::new();
    let result = simple_neq(&terms, &state, &nf1, &nf2, &mut infer);
    for eq in infer.drain_internal_equalities() {
        assert!(
            eq.explanation.contains(&pos(len_x_is_len_w_plus_one))
                && eq.explanation.contains(&pos(w_is_empty)),
            "no unify may rest on the alignment alone: {:?} = {:?} by {:?}",
            eq.lhs,
            eq.rhs,
            eq.explanation
        );
    }
    if let NfCheckResult::NeedLemma(StringLemma {
        kind: StringLemmaKind::ConstUnify,
        reason,
        ..
    }) = result
    {
        panic!("ConstUnify on an unexplainable length: {reason:?}");
    }
}

/// Negative twin of `flat_form_unify_carries_the_length`: `len(x) = len(w)`
/// holds only through an empty-reason merge of the length terms (an N-O
/// bridge equality with no literals behind it). F_UNIFY must then stay
/// silent rather than infer `x = w` on the concat equality alone.
#[test]
fn flat_form_unify_on_an_unexplainable_length_does_not_fire() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let w = terms.mk_var("w", Sort::String);
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let lhs = concat(&mut terms, vec![x, a]);
    let rhs = concat(&mut terms, vec![w, b]);
    let input = terms.mk_eq(lhs, rhs);
    let len_x = str_len(&mut terms, x);
    let len_w = str_len(&mut terms, w);

    let mut state = SolverState::new();
    state.assert_literal(&terms, input, true);
    state.register_term(&terms, len_x);
    state.register_term(&terms, len_w);
    let _ = state.merge_with_explanation(len_x, len_w, &[]);
    assert!(
        CoreSolver::are_lengths_equal_with_entail(&terms, &state, x, w),
        "precondition: len(x) = len(w) must be known, or this test is vacuous"
    );
    let mut core = CoreSolver::new();
    core.build_flat_forms(&terms, &state);
    let mut infer = InferenceManager::new();
    core.check_flat_forms(&terms, &state, &mut infer);
    let eqs = infer.drain_internal_equalities();
    assert!(
        eqs.is_empty(),
        "no flat-form unify may rest on an unexplained length: {eqs:?}"
    );
}

/// Negative twin of `to_code_range_conflict_names_the_length`: `len(x) = 1`
/// is known only through an empty-reason merge, so the narrowing to
/// `[0, 196607]` must not apply. A conflict drawn from it could name only
/// `str.to_code(x) = -1`, which `x = ""` satisfies.
#[test]
fn to_code_narrowing_needs_an_explained_length() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let code = terms.mk_app(Symbol::named("str.to_code"), vec![x], Sort::Int);
    let minus_one = terms.mk_int(BigInt::from(-1));
    let one = terms.mk_int(BigInt::from(1));
    let input = terms.mk_eq(code, minus_one);
    let len_x = str_len(&mut terms, x);

    let mut state = SolverState::new();
    state.assert_literal(&terms, input, true);
    state.register_term(&terms, len_x);
    state.register_term(&terms, one);
    let _ = state.merge_with_explanation(one, len_x, &[]);
    assert_eq!(
        state.known_length_full(&terms, x),
        Some(1),
        "precondition: len(x) = 1 must be known, or this test is vacuous"
    );
    let mut core = CoreSolver::new();
    let mut infer = InferenceManager::new();
    core.check_extf_int_reductions(&terms, &state, &mut infer);
    if let TheoryResult::Unsat(conflict) = infer.to_theory_result() {
        panic!("range conflict on an unexplained len(x) = 1: {conflict:?}");
    }
}

/// Negative twin of `flat_form_endpoint_carries_the_child_to_representative_merge`:
/// `x`'s class is represented by `k` through an empty-reason merge, so
/// `explain(x, k)` is empty. F_ENDPOINT_EQ must then stay silent rather than
/// infer `k = w` on the concat equality alone.
#[test]
fn flat_form_endpoint_on_an_unexplained_child_merge_does_not_fire() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::String);
    let x = terms.mk_var("x", Sort::String);
    let w = terms.mk_var("w", Sort::String);
    let k = terms.mk_var("k", Sort::String);
    let lhs = concat(&mut terms, vec![p, x]);
    let rhs = concat(&mut terms, vec![p, w]);
    let input = terms.mk_eq(lhs, rhs);

    let mut state = SolverState::new();
    state.register_term(&terms, k);
    state.register_term(&terms, x);
    let _ = state.merge_with_explanation(k, x, &[]);
    state.assert_literal(&terms, input, true);
    assert_ne!(
        state.find(x),
        x,
        "precondition: x must not represent its class"
    );
    assert!(
        state.explain(x, state.find(x)).is_empty(),
        "precondition: x = rep is unexplained"
    );
    let mut core = CoreSolver::new();
    core.build_flat_forms(&terms, &state);
    let mut infer = InferenceManager::new();
    core.check_flat_forms(&terms, &state, &mut infer);
    let eqs = infer.drain_internal_equalities();
    assert!(
        eqs.is_empty(),
        "no flat-form inference may rest on an unexplained child merge: {eqs:?}"
    );
}

/// The same fail-closed rule for a child the flat form DROPS as empty:
/// `e = ""` by an empty-reason merge leaves `p ++ e ++ x = p ++ w` without a
/// premise for the dropped `e`, so F_ENDPOINT_EQ must not infer `x = w`.
#[test]
fn flat_form_endpoint_on_an_unexplained_empty_child_does_not_fire() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::String);
    let e = terms.mk_var("e", Sort::String);
    let x = terms.mk_var("x", Sort::String);
    let w = terms.mk_var("w", Sort::String);
    let empty = terms.mk_string(String::new());
    let lhs = concat(&mut terms, vec![p, e, x]);
    let rhs = concat(&mut terms, vec![p, w]);
    let input = terms.mk_eq(lhs, rhs);

    let mut state = SolverState::new();
    state.register_term(&terms, empty);
    state.register_term(&terms, e);
    // `e` represents the class, so only the dropped-child check can catch it.
    let _ = state.merge_with_explanation(e, empty, &[]);
    state.assert_literal(&terms, input, true);
    assert_eq!(state.find(e), e, "precondition: e represents its class");
    assert!(state.is_empty_string(&terms, e), "precondition: e = \"\"");
    let mut core = CoreSolver::new();
    core.build_flat_forms(&terms, &state);
    let mut infer = InferenceManager::new();
    core.check_flat_forms(&terms, &state, &mut infer);
    let eqs = infer.drain_internal_equalities();
    assert!(
        eqs.is_empty(),
        "no flat-form inference may rest on an unexplained dropped child: {eqs:?}"
    );
}

/// ConstUnify on a length known only through an empty-reason merge: the
/// lemma could not name the length, so it must not be emitted.
#[test]
fn const_unify_on_an_unexplained_length_does_not_fire() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let z = terms.mk_var("z", Sort::String);
    let ab = terms.mk_string("ab".to_string());
    let one = terms.mk_int(BigInt::from(1));
    let lhs = concat(&mut terms, vec![x, y]);
    let rhs = concat(&mut terms, vec![ab, z]);
    let input = terms.mk_eq(lhs, rhs);
    let len_x = str_len(&mut terms, x);

    let mut state = SolverState::new();
    state.assert_literal(&terms, input, true);
    state.register_term(&terms, len_x);
    state.register_term(&terms, one);
    let _ = state.merge_with_explanation(one, len_x, &[]);
    assert_eq!(state.known_length_full(&terms, x), Some(1), "precondition");
    let (nf1, nf2) = nf_pair(lhs, vec![x, y], rhs, vec![ab, z]);

    let mut infer = InferenceManager::new();
    let result = simple_neq(&terms, &state, &nf1, &nf2, &mut infer);
    if let NfCheckResult::NeedLemma(StringLemma {
        kind: StringLemmaKind::ConstUnify,
        reason,
        ..
    }) = result
    {
        panic!("ConstUnify on an unexplained length: {reason:?}");
    }
}
