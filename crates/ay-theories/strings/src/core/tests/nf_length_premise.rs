// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! NF and flat-form inferences must carry every premise they read from an
//! equivalence class (`core/nf_equality_simpleq/nf_length_premise.rs`).
//!
//! Each test builds a state where the inference fires, and checks that the
//! literal the inference READ is in its explanation. The inferences are
//! N_UNIFY, ConstUnify (offset 0 and partial offset), the partial-offset
//! length conflict, F_UNIFY, F_ENDPOINT_EQ and the `str.to_code` range and
//! no-witness conflicts. Without that literal, the learned clause holds only
//! on the current branch, and when the rest of the explanation is input
//! literals it refutes a satisfiable input: the false UNSAT `ay-dpll`
//! `group_strings::regex_length_false_unsat::length_decided_unify_is_not_unsat`
//! pins at the solver level. The negative twins in `fail_closed` pin the other
//! half of the rule: a premise the proof forest cannot explain keeps the
//! inference from firing.

use super::*;
use crate::normal_form::ExplainEntry;
use ay_core::term::Symbol;
use ay_core::{Sort, TheoryResult};

mod fail_closed;

fn str_len(terms: &mut TermStore, s: TermId) -> TermId {
    terms.mk_app(Symbol::named("str.len"), vec![s], Sort::Int)
}

fn concat(terms: &mut TermStore, parts: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named("str.++"), parts, Sort::String)
}

fn pos(t: TermId) -> TheoryLit {
    TheoryLit::new(t, true)
}

/// The NF pair of an asserted `lhs = rhs` concat equation: the pair's only
/// dependency is that input equality.
fn nf_pair(
    lhs: TermId,
    lhs_base: Vec<TermId>,
    rhs: TermId,
    rhs_base: Vec<TermId>,
) -> (NormalForm, NormalForm) {
    let dep = vec![ExplainEntry { lhs, rhs }];
    (
        NormalForm {
            base: lhs_base,
            rep: Some(lhs),
            source: Some(lhs),
            deps: dep.clone(),
        },
        NormalForm {
            base: rhs_base,
            rep: Some(rhs),
            source: Some(rhs),
            deps: dep,
        },
    )
}

fn simple_neq(
    terms: &TermStore,
    state: &SolverState,
    nf1: &NormalForm,
    nf2: &NormalForm,
    infer: &mut InferenceManager,
) -> NfCheckResult {
    CoreSolver::process_simple_neq(terms, state, nf1, nf2, infer, &mut SkolemCache::new())
}

/// `x ++ y = "a" ++ z` (input) with `len(x) = 1` DECIDED: N_UNIFY infers
/// `x = "a"`. The input alone does not entail it (`x = "ab"`, `z = "b" ++ y`
/// satisfies the input), so the equality must also carry `len(x) = 1`.
#[test]
fn n_unify_carries_the_decided_length() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let z = terms.mk_var("z", Sort::String);
    let a = terms.mk_string("a".to_string());
    let one = terms.mk_int(BigInt::from(1));
    let lhs = concat(&mut terms, vec![x, y]);
    let rhs = concat(&mut terms, vec![a, z]);
    let input = terms.mk_eq(lhs, rhs);
    let len_x = str_len(&mut terms, x);
    let len_a = str_len(&mut terms, a);
    let len_x_is_one = terms.mk_eq(len_x, one);
    let len_a_is_one = terms.mk_eq(len_a, one);

    let mut state = SolverState::new();
    state.assert_literal(&terms, input, true);
    state.assert_literal(&terms, len_a_is_one, true);
    state.assert_literal(&terms, len_x_is_one, true);
    let (nf1, nf2) = nf_pair(lhs, vec![x, y], rhs, vec![a, z]);

    let mut infer = InferenceManager::new();
    assert!(matches!(
        simple_neq(&terms, &state, &nf1, &nf2, &mut infer),
        NfCheckResult::Incomplete
    ));
    let eqs = infer.drain_internal_equalities();
    assert_eq!(eqs.len(), 1, "N_UNIFY must still fire: {eqs:?}");
    assert_eq!((eqs[0].lhs, eqs[0].rhs), (x, a));
    for (lit, what) in [(input, "the input equation"), (len_x_is_one, "len(x) = 1")] {
        assert!(
            eqs[0].explanation.contains(&pos(lit)),
            "x = \"a\" must name {what}: {:?}",
            eqs[0].explanation
        );
    }
}

/// Same shape, but `"ab"` against `x`: the lengths are not equal, so the
/// variable-vs-constant branch emits ConstUnify `x = "a"` for `len(x) = 1`.
/// The lemma's guard must include `len(x) = 1`, or it pins `x = "a"` for good.
#[test]
fn const_unify_is_guarded_by_the_length() {
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
    let len_x_is_one = terms.mk_eq(len_x, one);

    let mut state = SolverState::new();
    state.assert_literal(&terms, input, true);
    state.assert_literal(&terms, len_x_is_one, true);
    let (nf1, nf2) = nf_pair(lhs, vec![x, y], rhs, vec![ab, z]);

    let mut infer = InferenceManager::new();
    match simple_neq(&terms, &state, &nf1, &nf2, &mut infer) {
        NfCheckResult::NeedLemma(StringLemma {
            kind: StringLemmaKind::ConstUnify,
            x: lx,
            y: ly,
            char_offset,
            start_offset,
            reason,
        }) => {
            assert_eq!((lx, ly, start_offset, char_offset), (x, ab, 0, 1));
            for (lit, what) in [(input, "the input equation"), (len_x_is_one, "len(x) = 1")] {
                assert!(
                    reason.contains(&pos(lit)),
                    "ConstUnify must be guarded by {what}: {reason:?}"
                );
            }
        }
        other => panic!("expected ConstUnify x = \"a\", got {other:?}"),
    }
}

/// `"a" ++ x = "ab"` (input) with `len(x) = 2` DECIDED: after `"a"`, one
/// character of the last constant remains, so the partial-offset branch
/// refutes the length. The conflict is about `len(x) = 2`, not the input
/// (`x = "b"` satisfies it), so it must name the length literal.
#[test]
fn partial_offset_length_conflict_names_the_length() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let a = terms.mk_string("a".to_string());
    let ab = terms.mk_string("ab".to_string());
    let two = terms.mk_int(BigInt::from(2));
    let lhs = concat(&mut terms, vec![a, x]);
    let input = terms.mk_eq(lhs, ab);
    let len_x = str_len(&mut terms, x);
    let len_x_is_two = terms.mk_eq(len_x, two);

    let mut state = SolverState::new();
    state.assert_literal(&terms, input, true);
    state.assert_literal(&terms, len_x_is_two, true);
    let (nf1, nf2) = nf_pair(lhs, vec![a, x], ab, vec![ab]);

    let mut infer = InferenceManager::new();
    assert!(matches!(
        simple_neq(&terms, &state, &nf1, &nf2, &mut infer),
        NfCheckResult::Conflict
    ));
    let TheoryResult::Unsat(conflict) = infer.to_theory_result() else {
        panic!("a conflict was reported");
    };
    for (lit, what) in [(input, "the input equation"), (len_x_is_two, "len(x) = 2")] {
        assert!(
            conflict.contains(&pos(lit)),
            "the conflict must name {what}: {conflict:?}"
        );
    }
}

/// F_UNIFY on `x ++ "a" = w ++ "b"` with `len(x) = len(w)` decided: the
/// inferred `x = w` must carry the length literal.
#[test]
fn flat_form_unify_carries_the_length() {
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
    let len_eq = terms.mk_eq(len_x, len_w);

    let mut state = SolverState::new();
    state.assert_literal(&terms, len_eq, true);
    state.assert_literal(&terms, input, true);
    let mut core = CoreSolver::new();
    core.build_flat_forms(&terms, &state);
    let mut infer = InferenceManager::new();
    assert!(!core.check_flat_forms(&terms, &state, &mut infer));

    let eqs = infer.drain_internal_equalities();
    assert_eq!(eqs.len(), 1, "F_UNIFY must still fire: {eqs:?}");
    for (lit, what) in [(input, "the input equation"), (len_eq, "len(x) = len(w)")] {
        assert!(
            eqs[0].explanation.contains(&pos(lit)),
            "F_UNIFY must name {what}: {:?}",
            eqs[0].explanation
        );
    }
}

/// F_ENDPOINT_EQ on `p ++ x = p ++ w` where `x`'s class is represented by
/// `k` (`x = k` decided after `k = m`): the flat form reads `k` for `x`, so
/// the inferred `k = w` must carry `x = k`. The input gives only `x = w`.
#[test]
fn flat_form_endpoint_carries_the_child_to_representative_merge() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::String);
    let x = terms.mk_var("x", Sort::String);
    let w = terms.mk_var("w", Sort::String);
    let k = terms.mk_var("k", Sort::String);
    let m = terms.mk_var("m", Sort::String);
    let lhs = concat(&mut terms, vec![p, x]);
    let rhs = concat(&mut terms, vec![p, w]);
    let input = terms.mk_eq(lhs, rhs);
    let k_is_m = terms.mk_eq(k, m);
    let x_is_k = terms.mk_eq(x, k);

    let mut state = SolverState::new();
    state.assert_literal(&terms, k_is_m, true);
    state.assert_literal(&terms, x_is_k, true);
    state.assert_literal(&terms, input, true);
    assert_ne!(state.find(x), x, "x must not represent its own class here");
    let mut core = CoreSolver::new();
    core.build_flat_forms(&terms, &state);
    let mut infer = InferenceManager::new();
    assert!(!core.check_flat_forms(&terms, &state, &mut infer));

    let eqs = infer.drain_internal_equalities();
    assert_eq!(eqs.len(), 1, "F_ENDPOINT_EQ must still fire: {eqs:?}");
    for (lit, what) in [(input, "the input equation"), (x_is_k, "x = k")] {
        assert!(
            eqs[0].explanation.contains(&pos(lit)),
            "F_ENDPOINT_EQ must name {what}: {:?}",
            eqs[0].explanation
        );
    }
}

/// `str.to_code(x) = -1` (input) with `len(x) = 1` DECIDED: the range check
/// narrows `str.to_code(x)` to `[0, 196607]` because of the length, so its
/// conflict must name `len(x) = 1`; `x = "ab"` satisfies the input.
#[test]
fn to_code_range_conflict_names_the_length() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let code = terms.mk_app(Symbol::named("str.to_code"), vec![x], Sort::Int);
    let minus_one = terms.mk_int(BigInt::from(-1));
    let one = terms.mk_int(BigInt::from(1));
    let input = terms.mk_eq(code, minus_one);
    let len_x = str_len(&mut terms, x);
    let len_x_is_one = terms.mk_eq(len_x, one);

    let mut state = SolverState::new();
    state.assert_literal(&terms, input, true);
    state.assert_literal(&terms, len_x_is_one, true);
    let mut core = CoreSolver::new();
    let mut infer = InferenceManager::new();
    assert!(core.check_extf_int_reductions(&terms, &state, &mut infer));
    let TheoryResult::Unsat(conflict) = infer.to_theory_result() else {
        panic!("a conflict was reported");
    };
    for (lit, what) in [(input, "the input relation"), (len_x_is_one, "len(x) = 1")] {
        assert!(
            conflict.contains(&pos(lit)),
            "the range conflict must name {what}: {conflict:?}"
        );
    }
}

/// `"a" ++ x ++ y = "abc"` (input) with `len(x) = 1` DECIDED: after `"a"`, `x`
/// sits at offset 1 of `"abc"` and fits, so the partial-offset branch emits
/// ConstUnify `x = "b"`. The input alone does not entail it (`x = "bc"`,
/// `y = ""` satisfies the input), so the lemma's guard must include
/// `len(x) = 1`.
#[test]
fn partial_offset_const_unify_is_guarded_by_the_length() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let a = terms.mk_string("a".to_string());
    let abc = terms.mk_string("abc".to_string());
    let one = terms.mk_int(BigInt::from(1));
    let lhs = concat(&mut terms, vec![a, x, y]);
    let input = terms.mk_eq(lhs, abc);
    let len_x = str_len(&mut terms, x);
    let len_x_is_one = terms.mk_eq(len_x, one);

    let mut state = SolverState::new();
    state.assert_literal(&terms, input, true);
    state.assert_literal(&terms, len_x_is_one, true);
    let (nf1, nf2) = nf_pair(lhs, vec![a, x, y], abc, vec![abc]);

    let mut infer = InferenceManager::new();
    match simple_neq(&terms, &state, &nf1, &nf2, &mut infer) {
        NfCheckResult::NeedLemma(StringLemma {
            kind: StringLemmaKind::ConstUnify,
            x: lx,
            y: ly,
            char_offset,
            start_offset,
            reason,
        }) => {
            assert_eq!((lx, ly, start_offset, char_offset), (x, abc, 1, 2));
            for (lit, what) in [(input, "the input equation"), (len_x_is_one, "len(x) = 1")] {
                assert!(
                    reason.contains(&pos(lit)),
                    "partial-offset ConstUnify must be guarded by {what}: {reason:?}"
                );
            }
        }
        other => panic!("expected ConstUnify x = \"b\", got {other:?}"),
    }
}

/// `str.to_code(x) < 0` (input) with `len(x) = 1` DECIDED: the narrowed range
/// `[0, 196607]` has no witness below 0, so the `<` branch conflicts. That
/// rests on the length (`x = ""` gives -1 and satisfies the input), so the
/// conflict must name `len(x) = 1`.
#[test]
fn to_code_no_witness_conflict_names_the_length() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let code = terms.mk_app(Symbol::named("str.to_code"), vec![x], Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let input = terms.mk_lt(code, zero);
    let len_x = str_len(&mut terms, x);
    let len_x_is_one = terms.mk_eq(len_x, one);

    let mut state = SolverState::new();
    state.assert_literal(&terms, input, true);
    state.assert_literal(&terms, len_x_is_one, true);
    let mut core = CoreSolver::new();
    let mut infer = InferenceManager::new();
    assert!(core.check_extf_int_reductions(&terms, &state, &mut infer));
    let TheoryResult::Unsat(conflict) = infer.to_theory_result() else {
        panic!("a conflict was reported");
    };
    for (lit, what) in [(input, "the input relation"), (len_x_is_one, "len(x) = 1")] {
        assert!(
            conflict.contains(&pos(lit)),
            "the no-witness conflict must name {what}: {conflict:?}"
        );
    }
}
