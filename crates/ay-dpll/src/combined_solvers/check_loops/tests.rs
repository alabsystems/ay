// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{EqualityPropagationResult, Sort, TheoryConflict, TheoryLit, TheoryPropagation};
use num_bigint::BigInt;
use num_rational::BigRational;

/// Test-only version of triage_lra_result (non-deferred).
/// Production code uses `triage_lra_result_deferred` instead.
fn triage_lra_result(result: TheoryResult) -> (bool, Option<TheoryResult>) {
    match result {
        TheoryResult::Sat => (false, None),
        TheoryResult::Unknown => (true, None),
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => (false, Some(result)),
        // LRA produces disequality/expression splits for (x != c) constraints.
        // Propagate to the outer split-loop pipeline (#6020).
        TheoryResult::NeedDisequalitySplit(_) | TheoryResult::NeedExpressionSplit(_) => {
            (false, Some(result))
        }
        TheoryResult::NeedSplit(_) => {
            unreachable!("BUG: LRA solver returned NeedSplit (should only come from LIA)");
        }
        TheoryResult::NeedStringLemma(_) => {
            unreachable!("BUG: LRA solver returned NeedStringLemma");
        }
        TheoryResult::NeedLemmas(_) => {
            unreachable!("BUG: LRA solver returned NeedLemmas");
        }
        // LRA returns NeedModelEquality/NeedModelEqualities when fixed-term
        // equalities are discovered (lib.rs:7182-7194). Propagate as early
        // return so the outer pipeline can handle them (#6812).
        TheoryResult::NeedModelEquality(_) | TheoryResult::NeedModelEqualities(_) => {
            (false, Some(result))
        }
        // All current TheoryResult variants handled above (#4906, #6149, #6303).
        // Wildcard covers future variants from #[non_exhaustive].
        _ => unreachable!("unhandled TheoryResult variant — update this match"),
    }
}

/// UnsatWithFarkas must be returned as an early-return, not deferred
/// as a split request. Before the fix, UnsatWithFarkas fell into the
/// catch-all arm of triage_lia_result and was treated as a split.
#[test]
fn test_triage_lia_result_unsat_with_farkas_is_early_return() {
    let conflict = TheoryConflict::new(vec![TheoryLit::new(TermId(1), true)]);
    let result = TheoryResult::UnsatWithFarkas(conflict);
    let (deferred, early) = triage_lia_result(result);
    assert!(
        deferred.is_none(),
        "UnsatWithFarkas must not be deferred as a split request"
    );
    assert!(
        early.is_some(),
        "UnsatWithFarkas must be returned as an early-return"
    );
    assert!(
        matches!(early.unwrap(), TheoryResult::UnsatWithFarkas(_)),
        "early-return must preserve the UnsatWithFarkas variant"
    );
}

#[test]
fn test_triage_lia_result_unsat_is_early_return() {
    let reasons = vec![TheoryLit::new(TermId(1), true)];
    let result = TheoryResult::Unsat(reasons);
    let (deferred, early) = triage_lia_result(result);
    assert!(deferred.is_none());
    assert!(matches!(early.unwrap(), TheoryResult::Unsat(_)));
}

#[test]
fn test_triage_lia_result_sat_is_no_action() {
    let (deferred, early) = triage_lia_result(TheoryResult::Sat);
    assert!(deferred.is_none());
    assert!(early.is_none());
}

#[test]
fn test_triage_lia_result_unknown_is_no_action() {
    let (deferred, early) = triage_lia_result(TheoryResult::Unknown);
    assert!(deferred.is_none());
    assert!(early.is_none());
}

#[test]
fn test_triage_lia_result_need_split_is_deferred() {
    let split = ay_core::SplitRequest {
        variable: TermId(1),
        value: BigRational::from(BigInt::from(1)),
        floor: BigInt::from(0),
        ceil: BigInt::from(1),
    };
    let result = TheoryResult::NeedSplit(split);
    let (deferred, early) = triage_lia_result(result);
    assert!(
        deferred.is_some(),
        "NeedSplit must be deferred, not early-returned"
    );
    assert!(early.is_none());
}

// -----------------------------------------------------------------------
// Tests for forward_non_sat
// -----------------------------------------------------------------------

#[test]
fn test_forward_non_sat_returns_none_for_sat() {
    assert!(forward_non_sat(TheoryResult::Sat).is_none());
}

#[test]
fn test_forward_non_sat_forwards_unsat() {
    let reasons = vec![TheoryLit::new(TermId(1), true)];
    let result = forward_non_sat(TheoryResult::Unsat(reasons));
    assert!(matches!(result, Some(TheoryResult::Unsat(_))));
}

#[test]
fn test_forward_non_sat_forwards_unsat_with_farkas() {
    let conflict = TheoryConflict::new(vec![TheoryLit::new(TermId(1), true)]);
    let result = forward_non_sat(TheoryResult::UnsatWithFarkas(conflict));
    assert!(matches!(result, Some(TheoryResult::UnsatWithFarkas(_))));
}

#[test]
fn test_forward_non_sat_forwards_unknown() {
    let result = forward_non_sat(TheoryResult::Unknown);
    assert!(matches!(result, Some(TheoryResult::Unknown)));
}

#[test]
fn test_forward_non_sat_forwards_need_model_equality() {
    let eq = ay_core::ModelEqualityRequest {
        lhs: TermId(1),
        rhs: TermId(2),
        reason: Vec::new(),
        implied: false,
    };
    let result = forward_non_sat(TheoryResult::NeedModelEquality(eq));
    assert!(matches!(result, Some(TheoryResult::NeedModelEquality(_))));
}

#[test]
fn test_forward_non_sat_forwards_need_model_equalities() {
    let requests = vec![
        ay_core::ModelEqualityRequest {
            lhs: TermId(1),
            rhs: TermId(2),
            reason: Vec::new(),
            implied: false,
        },
        ay_core::ModelEqualityRequest {
            lhs: TermId(3),
            rhs: TermId(4),
            reason: Vec::new(),
            implied: false,
        },
    ];
    let result = forward_non_sat(TheoryResult::NeedModelEqualities(requests));
    assert!(matches!(
        result,
        Some(TheoryResult::NeedModelEqualities(ref eqs)) if eqs.len() == 2
    ));
}

// -----------------------------------------------------------------------
// Tests for triage_lra_result
// -----------------------------------------------------------------------

#[test]
fn test_triage_lra_result_sat_continues() {
    let (is_unknown, early) = triage_lra_result(TheoryResult::Sat);
    assert!(!is_unknown);
    assert!(early.is_none());
}

#[test]
fn test_triage_lra_result_unknown_sets_flag() {
    let (is_unknown, early) = triage_lra_result(TheoryResult::Unknown);
    assert!(is_unknown);
    assert!(early.is_none());
}

#[test]
fn test_triage_lra_result_unsat_is_early_return() {
    let reasons = vec![TheoryLit::new(TermId(1), true)];
    let (is_unknown, early) = triage_lra_result(TheoryResult::Unsat(reasons));
    assert!(!is_unknown);
    assert!(matches!(early, Some(TheoryResult::Unsat(_))));
}

#[test]
fn test_triage_lra_result_diseq_split_is_early_return() {
    let split = ay_core::DisequalitySplitRequest {
        variable: TermId(1),
        excluded_value: BigRational::from(BigInt::from(3)),
        disequality_term: Some(TermId(2)),
        is_distinct: false,
    };
    let (is_unknown, early) = triage_lra_result(TheoryResult::NeedDisequalitySplit(split));
    assert!(!is_unknown);
    assert!(matches!(early, Some(TheoryResult::NeedDisequalitySplit(_))));
}

// -----------------------------------------------------------------------
// Tests for triage_lra_result_deferred
// -----------------------------------------------------------------------

#[test]
fn test_triage_lra_result_deferred_sat_is_no_action() {
    let (deferred, early) = triage_lra_result_deferred(TheoryResult::Sat);
    assert!(deferred.is_none());
    assert!(early.is_none());
}

#[test]
fn test_triage_lra_result_deferred_unsat_is_early_return() {
    let reasons = vec![TheoryLit::new(TermId(1), true)];
    let (deferred, early) = triage_lra_result_deferred(TheoryResult::Unsat(reasons));
    assert!(deferred.is_none());
    assert!(matches!(early, Some(TheoryResult::Unsat(_))));
}

#[test]
fn test_triage_lra_result_deferred_diseq_split_is_deferred() {
    let split = ay_core::DisequalitySplitRequest {
        variable: TermId(1),
        excluded_value: BigRational::from(BigInt::from(3)),
        disequality_term: Some(TermId(2)),
        is_distinct: false,
    };
    let (deferred, early) = triage_lra_result_deferred(TheoryResult::NeedDisequalitySplit(split));
    assert!(
        deferred.is_some(),
        "NeedDisequalitySplit must be deferred in deferred mode"
    );
    assert!(early.is_none());
}

// -----------------------------------------------------------------------
// Tests for triage_lia_result with NeedModelEquality (#4906)
// -----------------------------------------------------------------------

#[test]
fn test_triage_lia_result_need_model_equality_is_deferred() {
    let eq = ay_core::ModelEqualityRequest {
        lhs: TermId(10),
        rhs: TermId(20),
        reason: Vec::new(),
        implied: false,
    };
    let result = TheoryResult::NeedModelEquality(eq);
    let (deferred, early) = triage_lia_result(result);
    assert!(
        deferred.is_some(),
        "NeedModelEquality must be deferred (same as NeedSplit)"
    );
    assert!(early.is_none());
    assert!(
        matches!(deferred.unwrap(), TheoryResult::NeedModelEquality(_)),
        "deferred result must preserve NeedModelEquality variant"
    );
}

// -----------------------------------------------------------------------
// Tests for discover_model_equality (#4906)
// -----------------------------------------------------------------------

/// Helper: create a TermStore with N integer variables and return their TermIds.
fn make_int_terms(n: usize) -> (TermStore, Vec<TermId>) {
    let mut store = TermStore::new();
    let ids: Vec<TermId> = (0..n)
        .map(|i| store.mk_var(format!("x{i}"), Sort::Int))
        .collect();
    (store, ids)
}

#[test]
fn test_discover_model_equality_empty_iterator() {
    let (store, _) = make_int_terms(0);
    let euf = EufSolver::new(&store);
    let get_val = |_: TermId| -> Option<BigInt> { None };
    let result = discover_model_equality(
        std::iter::empty(),
        &store,
        &euf,
        &get_val,
        &[Sort::Int],
        false,
        "test",
    );
    assert!(result.is_none(), "empty iterator should yield None");
}

#[test]
fn test_discover_model_equality_single_term_per_value() {
    let (store, ids) = make_int_terms(3);
    let euf = EufSolver::new(&store);
    // Each term has a distinct value — no group has 2+ terms.
    let values: Vec<BigInt> = vec![BigInt::from(1), BigInt::from(2), BigInt::from(3)];
    let get_val = |t: TermId| -> Option<BigInt> {
        ids.iter()
            .position(|&id| id == t)
            .map(|i| values[i].clone())
    };
    let result = discover_model_equality(
        ids.iter().copied(),
        &store,
        &euf,
        &get_val,
        &[Sort::Int],
        false,
        "test",
    );
    assert!(
        result.is_none(),
        "no group has 2+ terms, so no model equality needed"
    );
}

#[test]
fn test_discover_model_equality_two_terms_same_value_not_euf_equal() {
    let (store, ids) = make_int_terms(2);
    let euf = EufSolver::new(&store);
    // Both terms have value 42, but are NOT EUF-equal (fresh solver).
    let get_val = |_: TermId| -> Option<BigInt> { Some(BigInt::from(42)) };
    let result = discover_model_equality(
        ids.iter().copied(),
        &store,
        &euf,
        &get_val,
        &[Sort::Int],
        false,
        "test",
    );
    match result {
        Some(TheoryResult::NeedModelEquality(req)) => {
            assert_eq!(req.lhs, ids[0]);
            assert_eq!(req.rhs, ids[1]);
            assert!(req.reason.is_empty());
        }
        other => panic!("expected NeedModelEquality, got {other:?}"),
    }
}

#[test]
fn test_discover_model_equality_two_terms_same_value_euf_equal() {
    let (mut store, ids) = make_int_terms(2);
    // Create an equality term and assert it to make the terms EUF-equal.
    let eq_term = store.mk_eq(ids[0], ids[1]);
    let mut euf = EufSolver::new(&store);
    euf.assert_literal(eq_term, true);
    euf.check(); // Process the merge.

    let get_val = |_: TermId| -> Option<BigInt> { Some(BigInt::from(42)) };
    let result = discover_model_equality(
        ids.iter().copied(),
        &store,
        &euf,
        &get_val,
        &[Sort::Int],
        false,
        "test",
    );
    assert!(
        result.is_none(),
        "terms are EUF-equal, so no model equality needed"
    );
}

#[test]
fn test_discover_model_equality_three_terms_two_equal_one_not() {
    let (mut store, ids) = make_int_terms(3);
    // Make ids[0] and ids[1] EUF-equal, but ids[2] is different.
    let eq_01 = store.mk_eq(ids[0], ids[1]);
    let mut euf = EufSolver::new(&store);
    euf.assert_literal(eq_01, true);
    euf.check();

    // All three have the same model value.
    let get_val = |_: TermId| -> Option<BigInt> { Some(BigInt::from(7)) };
    let result = discover_model_equality(
        ids.iter().copied(),
        &store,
        &euf,
        &get_val,
        &[Sort::Int],
        false,
        "test",
    );
    match result {
        Some(TheoryResult::NeedModelEquality(req)) => {
            // Should find a pair where one side is not EUF-equal to the other.
            // ids[0] == ids[1] (EUF), so the pair must involve ids[2].
            assert!(
                req.lhs == ids[2] || req.rhs == ids[2],
                "the non-EUF-equal term must be part of the pair"
            );
        }
        other => panic!("expected NeedModelEquality, got {other:?}"),
    }
}

#[test]
fn test_discover_model_equality_terms_with_no_value_are_skipped() {
    let (store, ids) = make_int_terms(3);
    let euf = EufSolver::new(&store);
    // Only ids[0] has a value; ids[1] and ids[2] return None.
    let get_val = |t: TermId| -> Option<BigInt> {
        if t == ids[0] {
            Some(BigInt::from(5))
        } else {
            None
        }
    };
    let result = discover_model_equality(
        ids.iter().copied(),
        &store,
        &euf,
        &get_val,
        &[Sort::Int],
        false,
        "test",
    );
    assert!(
        result.is_none(),
        "only one term has a value, so no pair can form"
    );
}

#[test]
fn test_discover_model_equality_multiple_value_groups() {
    let (store, ids) = make_int_terms(4);
    let euf = EufSolver::new(&store);
    // ids[0], ids[1] have value 10; ids[2], ids[3] have value 20.
    let get_val = |t: TermId| -> Option<BigInt> {
        if t == ids[0] || t == ids[1] {
            Some(BigInt::from(10))
        } else {
            Some(BigInt::from(20))
        }
    };
    let result = discover_model_equality(
        ids.iter().copied(),
        &store,
        &euf,
        &get_val,
        &[Sort::Int],
        false,
        "test",
    );
    match result {
        Some(TheoryResult::NeedModelEqualities(reqs)) => {
            assert_eq!(
                reqs.len(),
                2,
                "one unresolved pair should be emitted per value group"
            );
            assert_eq!(reqs[0].lhs, ids[0]);
            assert_eq!(reqs[0].rhs, ids[1]);
            assert_eq!(reqs[1].lhs, ids[2]);
            assert_eq!(reqs[1].rhs, ids[3]);
        }
        other => panic!("expected NeedModelEqualities, got {other:?}"),
    }
}

#[test]
fn test_discover_model_equality_batches_anchor_pairs_for_one_value_group() {
    let (store, ids) = make_int_terms(3);
    let euf = EufSolver::new(&store);
    // All three have the same value — batching should use ids[0] as the anchor
    // and request equality with each other term.
    let get_val = |_: TermId| -> Option<BigInt> { Some(BigInt::from(99)) };
    let result = discover_model_equality(
        ids.iter().copied(),
        &store,
        &euf,
        &get_val,
        &[Sort::Int],
        false,
        "test",
    );
    match result {
        Some(TheoryResult::NeedModelEqualities(reqs)) => {
            assert_eq!(reqs.len(), 2);
            assert_eq!(reqs[0].lhs, ids[0]);
            assert_eq!(reqs[0].rhs, ids[1]);
            assert_eq!(reqs[1].lhs, ids[0]);
            assert_eq!(reqs[1].rhs, ids[2]);
        }
        other => panic!("expected NeedModelEqualities, got {other:?}"),
    }
}

#[test]
fn test_discover_model_equality_filters_non_int_sorted_terms() {
    // Regression test: Array-sorted variables in interface_arith_terms
    // must be filtered out to avoid sort-mismatched (= Int Array) panics.
    let mut store = TermStore::new();
    let int_var = store.mk_var("x".to_string(), Sort::Int);
    let arr_var = store.mk_var(
        "a".to_string(),
        Sort::Array(Box::new(ay_core::ArraySort {
            index_sort: Sort::Int,
            element_sort: Sort::Int,
        })),
    );
    let ids = [int_var, arr_var];
    let euf = EufSolver::new(&store);
    // Both return a value, but arr_var should be filtered by sort check.
    let get_val = |_: TermId| -> Option<BigInt> { Some(BigInt::from(42)) };
    let result = discover_model_equality(
        ids.iter().copied(),
        &store,
        &euf,
        &get_val,
        &[Sort::Int],
        false,
        "test",
    );
    assert!(
        result.is_none(),
        "Array-sorted term must be filtered out; only one Int term remains, so no pair"
    );
}

// -----------------------------------------------------------------------
// Tests for propagate_equalities_to empty-conflict handling (#6197)
// -----------------------------------------------------------------------

/// Minimal mock theory solver that returns an empty conflict from
/// `propagate_equalities` to test the graceful-degradation path.
struct EmptyConflictSolver;

impl TheorySolver for EmptyConflictSolver {
    fn assert_literal(&mut self, _literal: TermId, _value: bool) {}
    fn check(&mut self) -> TheoryResult {
        TheoryResult::Sat
    }
    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        Vec::new()
    }
    fn push(&mut self) {}
    fn pop(&mut self) {}
    fn reset(&mut self) {}
    fn propagate_equalities(&mut self) -> EqualityPropagationResult {
        EqualityPropagationResult {
            equalities: Vec::new(),
            conflict: Some(Vec::new()), // empty-reason conflict (the bug)
            ..Default::default()
        }
    }
}

/// A no-op target solver for the equality propagation target side.
struct NoopSolver;

impl TheorySolver for NoopSolver {
    fn assert_literal(&mut self, _literal: TermId, _value: bool) {}
    fn check(&mut self) -> TheoryResult {
        TheoryResult::Sat
    }
    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        Vec::new()
    }
    fn push(&mut self) {}
    fn pop(&mut self) {}
    fn reset(&mut self) {}
}

#[test]
fn test_propagate_equalities_to_empty_conflict_returns_unknown() {
    // Regression: an empty-reason conflict used to panic (#6197).
    // After the fix, it should return Err(TheoryResult::Unknown).
    let mut source = EmptyConflictSolver;
    let mut target = NoopSolver;
    let result = propagate_equalities_to(&mut source, &mut target, false, "test", 0);
    assert!(
        matches!(result, Err(TheoryResult::Unknown)),
        "empty-reason conflict should return Unknown, not panic; got: {result:?}",
    );
}

#[test]
fn test_propagate_equalities_to_nonempty_conflict_returns_unsat() {
    // Non-empty conflict should still return Err(Unsat) as before.
    struct NonEmptyConflictSolver;
    impl TheorySolver for NonEmptyConflictSolver {
        fn assert_literal(&mut self, _literal: TermId, _value: bool) {}
        fn check(&mut self) -> TheoryResult {
            TheoryResult::Sat
        }
        fn propagate(&mut self) -> Vec<TheoryPropagation> {
            Vec::new()
        }
        fn push(&mut self) {}
        fn pop(&mut self) {}
        fn reset(&mut self) {}
        fn propagate_equalities(&mut self) -> EqualityPropagationResult {
            EqualityPropagationResult {
                equalities: Vec::new(),
                conflict: Some(vec![TheoryLit::new(TermId(1), true)]),
                ..Default::default()
            }
        }
    }

    let mut source = NonEmptyConflictSolver;
    let mut target = NoopSolver;
    let result = propagate_equalities_to(&mut source, &mut target, false, "test", 0);
    assert!(
        matches!(result, Err(TheoryResult::Unsat(_))),
        "non-empty conflict should return Unsat; got: {result:?}",
    );
}

#[test]
fn test_array_equality_propagation_empty_conflict_returns_unknown() {
    let result = array_equality_propagation_conflict_result(Vec::new());
    assert!(
        matches!(result, TheoryResult::Unknown),
        "empty-reason array conflict should return Unknown, not panic; got: {result:?}",
    );
}

#[test]
fn test_array_equality_propagation_nonempty_conflict_returns_unsat() {
    let result = array_equality_propagation_conflict_result(vec![TheoryLit::new(TermId(1), true)]);
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "non-empty array conflict should return Unsat; got: {result:?}",
    );
}

// --- distinct_by_affine_offset tests (#5970 coverage gap) ---
//
// The affine module (126 lines) was extracted from check_loops.rs with zero tests.
// `distinct_by_affine_offset` is soundness-critical: a false positive (claiming
// two terms are distinct when they aren't) would produce unsound array index
// disequality conflicts at check_loops.rs:332.

use ay_core::term::Symbol;

fn make_add(store: &mut TermStore, args: Vec<TermId>) -> TermId {
    store.mk_app(Symbol::Named("+".into()), args, Sort::Int)
}

fn make_sub(store: &mut TermStore, args: Vec<TermId>) -> TermId {
    store.mk_app(Symbol::Named("-".into()), args, Sort::Int)
}

fn make_mul(store: &mut TermStore, args: Vec<TermId>) -> TermId {
    store.mk_app(Symbol::Named("*".into()), args, Sort::Int)
}

/// Two different integer constants are provably distinct.
#[test]
fn test_affine_distinct_different_constants() {
    let mut store = TermStore::new();
    let a = store.mk_int(BigInt::from(1));
    let b = store.mk_int(BigInt::from(2));
    assert!(distinct_by_affine_offset(&store, a, b));
}

/// Same integer constant is NOT distinct.
#[test]
fn test_affine_same_constant_not_distinct() {
    let mut store = TermStore::new();
    let a = store.mk_int(BigInt::from(5));
    let b = store.mk_int(BigInt::from(5));
    assert!(!distinct_by_affine_offset(&store, a, b));
}

/// (x + 1) vs (x + 2): same variable coefficient, different constant offset.
#[test]
fn test_affine_x_plus_1_vs_x_plus_2() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let c1 = store.mk_int(BigInt::from(1));
    let c2 = store.mk_int(BigInt::from(2));
    let lhs = make_add(&mut store, vec![x, c1]);
    let rhs = make_add(&mut store, vec![x, c2]);
    assert!(distinct_by_affine_offset(&store, lhs, rhs));
}

/// Same affine expression is NOT distinct.
#[test]
fn test_affine_same_expression_not_distinct() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let c = store.mk_int(BigInt::from(1));
    let lhs = make_add(&mut store, vec![x, c]);
    let x2 = store.mk_var("x", Sort::Int);
    let c2 = store.mk_int(BigInt::from(1));
    let rhs = make_add(&mut store, vec![x2, c2]);
    assert!(!distinct_by_affine_offset(&store, lhs, rhs));
}

/// Different variables (x vs y) are NOT provably distinct via affine offset.
/// (They could be equal at runtime.)
#[test]
fn test_affine_different_variables_not_distinct() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    assert!(!distinct_by_affine_offset(&store, x, y));
}

/// Non-linear term (x*y) is not parseable — must return false, not panic.
#[test]
fn test_affine_nonlinear_returns_false() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let prod = make_mul(&mut store, vec![x, y]);
    let c = store.mk_int(BigInt::from(1));
    assert!(!distinct_by_affine_offset(&store, prod, c));
}

/// Unknown function f(x) is not parseable — must return false.
#[test]
fn test_affine_unknown_function_returns_false() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let f_x = store.mk_app(Symbol::Named("f".into()), vec![x], Sort::Int);
    let c = store.mk_int(BigInt::from(1));
    assert!(!distinct_by_affine_offset(&store, f_x, c));
}

/// Multi-variable: (x + y + 3) vs (x + y + 5) — same coefficients, different offset.
#[test]
fn test_affine_complex_multivar_offset() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let c3 = store.mk_int(BigInt::from(3));
    let c5 = store.mk_int(BigInt::from(5));
    let lhs = make_add(&mut store, vec![x, y, c3]);
    let x2 = store.mk_var("x", Sort::Int);
    let y2 = store.mk_var("y", Sort::Int);
    let rhs = make_add(&mut store, vec![x2, y2, c5]);
    assert!(distinct_by_affine_offset(&store, lhs, rhs));
}

/// Scalar multiplication: 2*x vs 2*x — same expression, NOT distinct.
#[test]
fn test_affine_scaled_same_offset_not_distinct() {
    let mut store = TermStore::new();
    let c2 = store.mk_int(BigInt::from(2));
    let x = store.mk_var("x", Sort::Int);
    let lhs = make_mul(&mut store, vec![c2, x]);
    let c2b = store.mk_int(BigInt::from(2));
    let x2 = store.mk_var("x", Sort::Int);
    let rhs = make_mul(&mut store, vec![c2b, x2]);
    assert!(!distinct_by_affine_offset(&store, lhs, rhs));
}

/// Subtraction: (x - 1) vs (x - 3) — same coefficients, different offset.
#[test]
fn test_affine_subtraction_different_offset() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let c1 = store.mk_int(BigInt::from(1));
    let lhs = make_sub(&mut store, vec![x, c1]);
    let x2 = store.mk_var("x", Sort::Int);
    let c3 = store.mk_int(BigInt::from(3));
    let rhs = make_sub(&mut store, vec![x2, c3]);
    assert!(distinct_by_affine_offset(&store, lhs, rhs));
}

/// Negation: (-x + 1) vs (-x + 2) — same coefficients (x has coeff -1), different offset.
#[test]
fn test_affine_negation_different_offset() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let neg_x = make_sub(&mut store, vec![x]);
    let c1 = store.mk_int(BigInt::from(1));
    let lhs = make_add(&mut store, vec![neg_x, c1]);
    let x2 = store.mk_var("x", Sort::Int);
    let neg_x2 = make_sub(&mut store, vec![x2]);
    let c2 = store.mk_int(BigInt::from(2));
    let rhs = make_add(&mut store, vec![neg_x2, c2]);
    assert!(distinct_by_affine_offset(&store, lhs, rhs));
}

/// Zero offset: (x + 0) vs x — same expression semantically, NOT distinct.
#[test]
fn test_affine_zero_offset_not_distinct() {
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let c0 = store.mk_int(BigInt::from(0));
    let lhs = make_add(&mut store, vec![x, c0]);
    let x2 = store.mk_var("x", Sort::Int);
    assert!(!distinct_by_affine_offset(&store, lhs, x2));
}
