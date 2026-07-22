// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Normal-form disequality tests: process_simple_deq, length entailment, nfs_equal.

use super::*;
use ay_core::term::Symbol;
use ay_core::Sort;

#[test]
fn lengths_equal_with_entail_handles_unit_terms() {
    let mut terms = TermStore::new();
    let c1 = terms.mk_int(BigInt::from(97));
    let c2 = terms.mk_int(BigInt::from(98));
    let u1 = terms.mk_app(Symbol::named("str.unit"), vec![c1], Sort::String);
    let u2 = terms.mk_app(Symbol::named("str.unit"), vec![c2], Sort::String);
    let len_u1 = terms.mk_app(Symbol::named("str.len"), vec![u1], Sort::Int);
    let len_u2 = terms.mk_app(Symbol::named("str.len"), vec![u2], Sort::Int);

    let mut state = SolverState::new();
    state.register_term(&terms, u1);
    state.register_term(&terms, u2);
    state.register_term(&terms, len_u1);
    state.register_term(&terms, len_u2);

    assert!(
        !state.are_lengths_equal(&terms, u1, u2),
        "raw EQC metadata has no explicit len(u1)=len(u2) fact"
    );
    assert!(
        CoreSolver::are_lengths_equal_with_entail(&terms, &state, u1, u2),
        "arith entail should prove len(str.unit(_)) = 1 on both sides"
    );
}

/// Trivially satisfied split-branch disequalities must not force incomplete.
///
/// Example: x = "" and x != str.++("b", k) is already satisfied because the
/// rhs is guaranteed non-empty.
#[test]
fn check_normal_forms_deq_trivial_split_disequality_is_resolved() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let k = terms.mk_var("k", Sort::String);
    let empty = terms.mk_string(String::new());
    let b = terms.mk_string("b".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![b, k], Sort::String);
    let eq_x_empty = terms.mk_eq(x, empty);
    let eq_x_concat = terms.mk_eq(x, concat);

    let mut state = SolverState::new();
    state.assert_literal(&terms, eq_x_empty, true);
    state.assert_literal(&terms, eq_x_concat, false);

    let mut core = CoreSolver::new();
    core.compute_normal_forms(&terms, &state);
    let mut infer = InferenceManager::new();
    let mut skolems = SkolemCache::new();
    let result = core.check_normal_forms_deq(&terms, &state, &mut infer, &mut skolems);

    assert!(
        matches!(result, NfCheckResult::Ok),
        "trivial disequality should be resolved, got {result:?}"
    );
    assert!(!infer.has_conflict());
}

/// process_simple_deq: shared suffix reduction should request a split on
/// the reduced prefix components (x vs y), not on the original full terms.
#[test]
fn process_simple_deq_suffix_trim_requests_component_length_split() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let a = terms.mk_string("a".to_string());
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = terms.mk_app(Symbol::named("str.len"), vec![y], Sort::Int);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, y);
    state.register_term(&terms, a);
    // Register str.len terms so has_length_info(x/y) is true.
    state.register_term(&terms, len_x);
    state.register_term(&terms, len_y);

    let nf1 = NormalForm {
        base: vec![x, a],
        rep: Some(x),
        source: Some(x),
        deps: Vec::new(),
    };
    let nf2 = NormalForm {
        base: vec![y, a],
        rep: Some(y),
        source: Some(y),
        deps: Vec::new(),
    };

    let diseq = terms.mk_eq(x, y);
    let diseq_lit = TheoryLit {
        term: diseq,
        value: false,
    };
    let result = CoreSolver::process_simple_deq(
        &terms,
        &state,
        &nf1,
        &nf2,
        diseq_lit,
        &mut SkolemCache::new(),
    );
    match result {
        NfCheckResult::NeedLemma(StringLemma {
            kind: StringLemmaKind::LengthSplit,
            x: lhs,
            y: rhs,
            ..
        }) => {
            assert_eq!(lhs, x, "split should target reduced lhs prefix component");
            assert_eq!(rhs, y, "split should target reduced rhs prefix component");
        }
        other => panic!("expected LengthSplit on reduced prefix components, got {other:?}"),
    }
}

/// process_simple_deq: without length metadata, two different variable
/// components return Incomplete (cannot certify disequality without
/// equality split lemma). CVC5 returns false and the caller issues an
/// equality split. CVC5 emits DEQ_STRINGS_EQ here (#4119).
#[test]
fn process_simple_deq_suffix_trim_without_length_info_requests_equality_split() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let a = terms.mk_string("a".to_string());

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, y);
    state.register_term(&terms, a);

    let nf1 = NormalForm {
        base: vec![x, a],
        rep: Some(x),
        source: Some(x),
        deps: Vec::new(),
    };
    let nf2 = NormalForm {
        base: vec![y, a],
        rep: Some(y),
        source: Some(y),
        deps: Vec::new(),
    };

    let diseq = terms.mk_eq(x, y);
    let diseq_lit = TheoryLit {
        term: diseq,
        value: false,
    };
    let result = CoreSolver::process_simple_deq(
        &terms,
        &state,
        &nf1,
        &nf2,
        diseq_lit,
        &mut SkolemCache::new(),
    );
    // After suffix trimming, [x] vs [y] with no length info.
    // CVC5 returns false from processSimpleDeq, and the caller emits
    // an equality split (x = y v x != y) to force the SAT solver to
    // decide. This drives completeness for diseq + shared-prefix patterns.
    // Ref: CVC5 core_solver.cpp:2280-2300 (DEQ_STRINGS_EQ).
    assert!(
        matches!(
            result,
            NfCheckResult::NeedLemma(StringLemma {
                kind: StringLemmaKind::EqualitySplit,
                ..
            })
        ),
        "after suffix trim, unresolved deq requests EqualitySplit, got {result:?}"
    );
}

/// check_normal_forms_deq: disequality conflict via nf_to_constant.
///
/// x = str.++("a","b"), x != "ab". NF of x resolves to "ab", which equals "ab".
/// Should detect the disequality violation via Check 3 (constant resolution).
#[test]
fn deq_conflict_via_nf_to_constant() {
    let mut terms = TermStore::new();
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());
    let concat = terms.mk_app(Symbol::named("str.++"), vec![a, b], Sort::String);
    let ab_const = terms.mk_string("ab".to_string());

    let mut state = SolverState::new();
    let eq_lit = terms.mk_eq(concat, ab_const);
    state.assert_literal(&terms, eq_lit, false); // str.++("a","b") != "ab"

    let mut infer = InferenceManager::new();
    let mut core = CoreSolver::new();
    assert!(
        core.check(&terms, &state, &mut infer, &mut SkolemCache::new()),
        "str.++(\"a\",\"b\") != \"ab\" should be UNSAT"
    );
    assert!(infer.has_conflict());
}

/// nfs_equal: different-length NFs are not equal.
#[test]
fn nfs_equal_different_lengths() {
    let state = SolverState::new();
    let core = CoreSolver::new();

    let nf1 = NormalForm {
        base: vec![TermId::new(1)],
        rep: Some(TermId::new(1)),
        source: Some(TermId::new(1)),
        deps: Vec::new(),
    };
    let nf2 = NormalForm {
        base: vec![TermId::new(1), TermId::new(2)],
        rep: Some(TermId::new(1)),
        source: Some(TermId::new(1)),
        deps: Vec::new(),
    };

    assert!(!core.nfs_equal(&state, &nf1, &nf2));
}

/// nfs_equal: same components via EQC representatives.
#[test]
fn nfs_equal_same_components_via_eqc() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::String);
    let b = terms.mk_var("b", Sort::String);
    let eq = terms.mk_eq(a, b);

    let mut state = SolverState::new();
    state.assert_literal(&terms, eq, true); // merge a and b

    let core = CoreSolver::new();
    let nf1 = NormalForm {
        base: vec![a],
        rep: Some(a),
        source: Some(a),
        deps: Vec::new(),
    };
    let nf2 = NormalForm {
        base: vec![b],
        rep: Some(b),
        source: Some(b),
        deps: Vec::new(),
    };

    assert!(
        core.nfs_equal(&state, &nf1, &nf2),
        "a and b are in same EQC, NFs should be equal"
    );
}

/// process_simple_deq: direct character mismatch between two constants
/// witnesses disequality immediately (returns Ok).
#[test]
fn process_simple_deq_character_mismatch_returns_ok() {
    let mut terms = TermStore::new();
    let abc = terms.mk_string("abc".to_string());
    let abd = terms.mk_string("abd".to_string());

    let mut state = SolverState::new();
    state.register_term(&terms, abc);
    state.register_term(&terms, abd);

    let nf1 = NormalForm {
        base: vec![abc],
        rep: Some(abc),
        source: Some(abc),
        deps: Vec::new(),
    };
    let nf2 = NormalForm {
        base: vec![abd],
        rep: Some(abd),
        source: Some(abd),
        deps: Vec::new(),
    };

    let diseq = terms.mk_eq(abc, abd);
    let diseq_lit = TheoryLit {
        term: diseq,
        value: false,
    };
    let result = CoreSolver::process_simple_deq(
        &terms,
        &state,
        &nf1,
        &nf2,
        diseq_lit,
        &mut SkolemCache::new(),
    );
    assert!(
        matches!(result, NfCheckResult::Ok),
        "character mismatch at position 2 witnesses disequality, got {result:?}"
    );
}

/// process_simple_deq: multi-component with offset advancement.
/// NF1 = `["ab", x]`, NF2 = `["a", "cd"]`, offset advances through `"a"` prefix.
#[test]
fn process_simple_deq_offset_advancement_finds_mismatch() {
    let mut terms = TermStore::new();
    let ab = terms.mk_string("ab".to_string());
    let a = terms.mk_string("a".to_string());
    let cd = terms.mk_string("cd".to_string());
    let x = terms.mk_var("x", Sort::String);

    let mut state = SolverState::new();
    state.register_term(&terms, ab);
    state.register_term(&terms, a);
    state.register_term(&terms, cd);
    state.register_term(&terms, x);

    // NF1 = ["ab", x], NF2 = ["a", "cd"]
    // After matching "a" prefix: off1=1 in "ab", advance j.
    // Then compare "b" (ab[1..]) vs "cd" => mismatch at position 0.
    let nf1 = NormalForm {
        base: vec![ab, x],
        rep: Some(ab),
        source: Some(ab),
        deps: Vec::new(),
    };
    let nf2 = NormalForm {
        base: vec![a, cd],
        rep: Some(a),
        source: Some(a),
        deps: Vec::new(),
    };

    let diseq = terms.mk_eq(ab, a);
    let diseq_lit = TheoryLit {
        term: diseq,
        value: false,
    };
    let result = CoreSolver::process_simple_deq(
        &terms,
        &state,
        &nf1,
        &nf2,
        diseq_lit,
        &mut SkolemCache::new(),
    );
    assert!(
        matches!(result, NfCheckResult::Ok),
        "offset advancement should find 'b' vs 'c' mismatch, got {result:?}"
    );
}

/// process_simple_deq: identical constant NFs return Incomplete (cannot
/// certify disequality when forms are identical).
#[test]
fn process_simple_deq_identical_constants_returns_incomplete() {
    let mut terms = TermStore::new();
    let abc = terms.mk_string("abc".to_string());

    let mut state = SolverState::new();
    state.register_term(&terms, abc);

    let nf1 = NormalForm {
        base: vec![abc],
        rep: Some(abc),
        source: Some(abc),
        deps: Vec::new(),
    };
    let nf2 = NormalForm {
        base: vec![abc],
        rep: Some(abc),
        source: Some(abc),
        deps: Vec::new(),
    };

    let diseq = terms.mk_eq(abc, abc);
    let diseq_lit = TheoryLit {
        term: diseq,
        value: false,
    };
    let result = CoreSolver::process_simple_deq(
        &terms,
        &state,
        &nf1,
        &nf2,
        diseq_lit,
        &mut SkolemCache::new(),
    );
    assert!(
        matches!(result, NfCheckResult::Incomplete),
        "identical NFs cannot certify disequality, got {result:?}"
    );
}

/// process_simple_deq: one side exhausted with leftover offset characters
/// witnesses disequality (returns Ok).
#[test]
fn process_simple_deq_exhausted_with_leftover_offset_returns_ok() {
    let mut terms = TermStore::new();
    let abc = terms.mk_string("abc".to_string());
    let ab = terms.mk_string("ab".to_string());

    let mut state = SolverState::new();
    state.register_term(&terms, abc);
    state.register_term(&terms, ab);

    // NF1 = ["abc"], NF2 = ["ab"]
    // Character walk: "ab" prefix matches, then "c" vs nothing.
    // j exhausted with off1 > 0 → leftover concrete → Ok.
    let nf1 = NormalForm {
        base: vec![abc],
        rep: Some(abc),
        source: Some(abc),
        deps: Vec::new(),
    };
    let nf2 = NormalForm {
        base: vec![ab],
        rep: Some(ab),
        source: Some(ab),
        deps: Vec::new(),
    };

    let diseq = terms.mk_eq(abc, ab);
    let diseq_lit = TheoryLit {
        term: diseq,
        value: false,
    };
    let result = CoreSolver::process_simple_deq(
        &terms,
        &state,
        &nf1,
        &nf2,
        diseq_lit,
        &mut SkolemCache::new(),
    );
    assert!(
        matches!(result, NfCheckResult::Ok),
        "leftover offset after exhaustion witnesses disequality, got {result:?}"
    );
}

/// process_simple_deq Case 2: equal-length disequal variables return Ok.
#[test]
fn process_simple_deq_equal_length_disequal_vars_returns_ok() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = terms.mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
    let len_eq = terms.mk_eq(len_x, len_y);
    let x_ne_y = terms.mk_eq(x, y);

    let mut state = SolverState::new();
    state.register_term(&terms, x);
    state.register_term(&terms, y);
    state.register_term(&terms, len_x);
    state.register_term(&terms, len_y);
    state.assert_literal(&terms, len_eq, true); // len(x) = len(y)
    state.assert_literal(&terms, x_ne_y, false); // x != y

    let nf1 = NormalForm {
        base: vec![x],
        rep: Some(x),
        source: Some(x),
        deps: Vec::new(),
    };
    let nf2 = NormalForm {
        base: vec![y],
        rep: Some(y),
        source: Some(y),
        deps: Vec::new(),
    };

    let diseq_lit = TheoryLit {
        term: x_ne_y,
        value: false,
    };
    let result = CoreSolver::process_simple_deq(
        &terms,
        &state,
        &nf1,
        &nf2,
        diseq_lit,
        &mut SkolemCache::new(),
    );
    assert!(
        matches!(result, NfCheckResult::Ok),
        "equal-length disequal variables should certify disequality, got {result:?}"
    );
}
