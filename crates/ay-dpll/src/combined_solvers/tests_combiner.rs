// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for TheoryCombiner — validates behavioral correctness of the
//! generic Nelson-Oppen combiner across all supported logic combinations.

use super::combiner::TheoryCombiner;
use ay_core::{Sort, Symbol, TermStore, TheoryResult, TheorySolver};
use num_bigint::BigInt;

fn setup_term_store() -> TermStore {
    TermStore::new()
}

// ============================================================
// TheoryCombiner::uf_lia
// ============================================================

#[test]
fn test_combiner_uf_lia_new() {
    let terms = setup_term_store();
    let _solver = TheoryCombiner::uf_lia(&terms);
}

#[test]
fn test_combiner_uf_lia_check_empty() {
    let terms = setup_term_store();
    let mut combiner = TheoryCombiner::uf_lia(&terms);
    let cr = combiner.check();
    assert!(matches!(cr, TheoryResult::Sat));
}

#[test]
fn test_combiner_uf_lia_push_pop() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lia(&terms);
    solver.push();
    solver.push();
    solver.pop();
    solver.pop();
}

#[test]
fn test_combiner_uf_lia_reset() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lia(&terms);
    solver.reset();
}

#[test]
fn test_combiner_uf_lia_soft_reset() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lia(&terms);
    solver.soft_reset();
}

#[test]
fn test_combiner_uf_lia_pop_underflow_returns() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lia(&terms);
    // Pop at depth 0 is a graceful no-op (early return), not a panic.
    solver.pop();
    // Solver remains usable after underflow.
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
#[should_panic(expected = "BUG: TheoryCombiner(UFLIA)::reset() called with non-zero scope depth")]
fn test_combiner_uf_lia_reset_with_open_scope_panics() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lia(&terms);
    solver.push();
    solver.reset();
}

#[test]
fn test_combiner_uf_lia_assert_int_constraint() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let constraint = terms.mk_gt(x, five);

    let mut combiner = TheoryCombiner::uf_lia(&terms);
    combiner.assert_literal(constraint, true);
    let cr = combiner.check();

    assert!(
        !matches!(
            cr,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "single positive constraint should not be UNSAT"
    );
}

#[test]
fn test_combiner_uf_lia_detects_unsat() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));
    let gt_one = terms.mk_gt(x, one);
    let lt_zero = terms.mk_lt(x, zero);

    let mut combiner = TheoryCombiner::uf_lia(&terms);
    combiner.assert_literal(gt_one, true);
    combiner.assert_literal(lt_zero, true);
    let cr = combiner.check();

    assert!(
        matches!(
            cr,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x>1 AND x<0 should be UNSAT"
    );
}

#[test]
fn test_combiner_uf_lia_push_pop_isolates_state() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));
    let gt_one = terms.mk_gt(x, one);
    let lt_zero = terms.mk_lt(x, zero);

    let mut solver = TheoryCombiner::uf_lia(&terms);

    solver.assert_literal(gt_one, true);
    let r1 = solver.check();
    assert!(
        !matches!(
            r1,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x > 1 alone should not be UNSAT"
    );

    solver.push();
    solver.assert_literal(lt_zero, true);
    let r2 = solver.check();
    assert!(
        matches!(
            r2,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x > 1 AND x < 0 should be UNSAT"
    );

    solver.pop();
    let r3 = solver.check();
    assert!(
        !matches!(
            r3,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "After pop, x > 1 alone should not be UNSAT"
    );
}

// ============================================================
// TheoryCombiner::uf_lra
// ============================================================

#[test]
fn test_combiner_uf_lra_new() {
    let terms = setup_term_store();
    let _solver = TheoryCombiner::uf_lra(&terms);
}

#[test]
fn test_combiner_uf_lra_check_empty() {
    let terms = setup_term_store();
    let mut combiner = TheoryCombiner::uf_lra(&terms);
    let cr = combiner.check();
    assert!(matches!(cr, TheoryResult::Sat));
}

#[test]
fn test_combiner_uf_lra_assert_real_constraint() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Real);
    let half = terms.mk_rational(num_rational::Ratio::new(BigInt::from(1), BigInt::from(2)));
    let constraint = terms.mk_gt(x, half);

    let mut combiner = TheoryCombiner::uf_lra(&terms);
    combiner.assert_literal(constraint, true);
    let cr = combiner.check();

    assert!(
        !matches!(
            cr,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x > 0.5: single constraint should not be UNSAT"
    );
}

#[test]
fn test_combiner_uf_lra_supports_farkas() {
    let terms = setup_term_store();
    let combiner = TheoryCombiner::uf_lra(&terms);
    assert!(combiner.supports_farkas_semantic_check());
}

// ============================================================
// TheoryCombiner::array_euf
// ============================================================

#[test]
fn test_combiner_array_euf_new() {
    let terms = setup_term_store();
    let _solver = TheoryCombiner::array_euf(&terms);
}

#[test]
fn test_combiner_array_euf_check_empty() {
    let terms = setup_term_store();
    let mut combiner = TheoryCombiner::array_euf(&terms);
    let cr = combiner.check();
    assert!(matches!(cr, TheoryResult::Sat));
}

#[test]
fn test_combiner_array_euf_push_pop() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::array_euf(&terms);
    solver.push();
    solver.push();
    solver.pop();
    solver.pop();
}

#[test]
fn test_combiner_array_euf_theory_aware_branching() {
    let terms = setup_term_store();
    let combiner = TheoryCombiner::array_euf(&terms);
    assert!(combiner.supports_theory_aware_branching());
}

// ============================================================
// TheoryCombiner::auf_lia
// ============================================================

#[test]
fn test_combiner_auf_lia_new() {
    let terms = setup_term_store();
    let _solver = TheoryCombiner::auf_lia(&terms);
}

#[test]
fn test_combiner_auf_lia_check_empty() {
    let terms = setup_term_store();
    let mut combiner = TheoryCombiner::auf_lia(&terms);
    let cr = combiner.check();
    assert!(matches!(cr, TheoryResult::Sat));
}

#[test]
fn test_combiner_auf_lia_theory_aware_branching() {
    let terms = setup_term_store();
    let combiner = TheoryCombiner::auf_lia(&terms);
    assert!(combiner.supports_theory_aware_branching());
}

#[cfg(debug_assertions)]
#[test]
fn test_combiner_auf_lia_rebind_preserves_array_request_progress() {
    let mut terms = setup_term_store();
    let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(Sort::Int, Sort::Int)));
    let array = terms.mk_fresh_var("a", array_sort);
    let store_index = terms.mk_fresh_var("i", Sort::Int);
    let select_index = terms.mk_fresh_var("j", Sort::Int);
    let value = terms.mk_fresh_var("v", Sort::Int);
    let stored = terms.mk_store(array, store_index, value);
    let _stored_select = terms.mk_select(stored, select_index);
    let _base_select = terms.mk_select(array, select_index);
    let mut grown_terms = terms.clone();
    let _new_term = grown_terms.mk_fresh_var("new_after_round", Sort::Int);
    let mut combiner = TheoryCombiner::auf_lia(&terms);

    let mut exact_request_source = ay_arrays::ArraySolver::new(&terms);
    let exact_result = exact_request_source.check();
    assert!(
        matches!(
            exact_result,
            TheoryResult::NeedModelEquality(_) | TheoryResult::NeedModelEqualities(_)
        ),
        "ROW2 should create exact-select request keys, got {exact_result:?}"
    );
    let exact_select_requests = exact_request_source.export_exact_select_model_eq_keys();
    assert!(
        !exact_select_requests.is_empty(),
        "ROW2 exact-select request generation must be non-vacuous"
    );

    let interface_requests = [(terms.true_term(), terms.false_term())]
        .into_iter()
        .collect();
    let model_requests = [(terms.false_term(), terms.true_term())]
        .into_iter()
        .collect();
    combiner.import_array_requested_interface_eqs(&interface_requests);
    combiner.import_array_requested_model_eqs(&model_requests);
    combiner.import_array_exact_select_model_eq_keys(&exact_select_requests);

    combiner.rebind_terms(&grown_terms);

    assert_eq!(
        combiner.export_array_requested_interface_eqs(),
        interface_requests
    );
    assert_eq!(combiner.export_array_requested_model_eqs(), model_requests);
    assert_eq!(
        combiner.export_array_exact_select_model_eq_keys(),
        exact_select_requests
    );
}

// ============================================================
// TheoryCombiner::auf_lra
// ============================================================

#[test]
fn test_combiner_auf_lra_new() {
    let terms = setup_term_store();
    let _solver = TheoryCombiner::auf_lra(&terms);
}

#[test]
fn test_combiner_auf_lra_check_empty() {
    let terms = setup_term_store();
    let mut combiner = TheoryCombiner::auf_lra(&terms);
    let cr = combiner.check();
    assert!(matches!(cr, TheoryResult::Sat));
}

#[test]
fn test_combiner_auf_lra_supports_farkas() {
    let terms = setup_term_store();
    let combiner = TheoryCombiner::auf_lra(&terms);
    assert!(combiner.supports_farkas_semantic_check());
    assert!(combiner.supports_theory_aware_branching());
}

// ============================================================
// Cross-combination property tests
// ============================================================

#[test]
fn test_combiner_propagate_empty_all_variants() {
    let terms = setup_term_store();

    let mut variants: Vec<(&str, Box<dyn TheorySolver + '_>)> = vec![
        ("uf_lia", Box::new(TheoryCombiner::uf_lia(&terms))),
        ("uf_lra", Box::new(TheoryCombiner::uf_lra(&terms))),
        ("array_euf", Box::new(TheoryCombiner::array_euf(&terms))),
        ("auf_lia", Box::new(TheoryCombiner::auf_lia(&terms))),
        ("auf_lra", Box::new(TheoryCombiner::auf_lra(&terms))),
    ];

    for (name, solver) in &mut variants {
        let props = solver.propagate();
        assert!(
            props.is_empty(),
            "{name}: expected empty propagation on fresh solver"
        );
    }
}

// ============================================================
// Nelson-Oppen fixpoint loop tests (#6611)
//
// These tests exercise the cross-theory equality propagation
// that is the core of the N-O combination procedure. Each test
// requires at least one theory to discover an equality that a
// different theory needs to detect a conflict or reach SAT.
// ============================================================

/// Verify that the N-O loop propagates LIA equalities to EUF.
///
/// Formula: x = y AND f(x) != f(y)
/// Expected: UNSAT
/// Reasoning:
///   1. x = y is asserted (routed to both LIA and EUF)
///   2. EUF derives f(x) = f(y) by congruence closure on x = y
///   3. Conflicts with f(x) != f(y)
///
/// This exercises the combined theory check path where both LIA and
/// EUF must cooperate on the same equality to detect the conflict.
#[test]
fn test_combiner_no_lia_euf_equality_congruence() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let y = terms.mk_fresh_var("y", Sort::Int);
    let fx = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let fy = terms.mk_app(Symbol::named("f"), vec![y], Sort::Int);

    // x = y (arithmetic equality, routed to EUF + LIA)
    let x_eq_y = terms.mk_eq(x, y);
    // f(x) = f(y) — will be negated
    let fx_eq_fy = terms.mk_eq(fx, fy);

    let mut combiner = TheoryCombiner::uf_lia(&terms);
    combiner.register_atom(x_eq_y);
    combiner.register_atom(fx_eq_fy);
    combiner.assert_literal(x_eq_y, true); // x = y
    combiner.assert_literal(fx_eq_fy, false); // f(x) != f(y)

    let result = combiner.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x=y AND f(x)!=f(y) must be UNSAT — requires EUF congruence on shared equality"
    );
}

/// Verify that the N-O loop propagates EUF equalities to LIA.
///
/// Formula: a = b (UF equality on Int vars) AND a > 5 AND b < 3
/// Expected: UNSAT
/// Reasoning:
///   1. EUF knows a = b from the direct assertion
///   2. N-O propagates a = b to LIA as a shared equality
///   3. LIA has a > 5 and b < 3; with a = b, this gives a > 5 AND a < 3
///   4. Contradiction
///
/// This exercises the propagate_equalities_to(euf → lia) path.
/// The equality a = b is routed to EUF (and LIA via is_uf_int_equality routing),
/// but the arithmetic constraints are only in LIA, so the conflict requires
/// both theories cooperating.
#[test]
fn test_combiner_no_euf_to_lia_propagation() {
    let mut terms = setup_term_store();
    let a = terms.mk_fresh_var("a", Sort::Int);
    let b = terms.mk_fresh_var("b", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let three = terms.mk_int(BigInt::from(3));

    // a = b (Int-sorted equality)
    let a_eq_b = terms.mk_eq(a, b);
    // a > 5 (arithmetic)
    let a_gt_5 = terms.mk_gt(a, five);
    // b < 3 (arithmetic)
    let b_lt_3 = terms.mk_lt(b, three);

    let mut combiner = TheoryCombiner::uf_lia(&terms);
    combiner.register_atom(a_eq_b);
    combiner.register_atom(a_gt_5);
    combiner.register_atom(b_lt_3);
    combiner.assert_literal(a_eq_b, true); // a = b
    combiner.assert_literal(a_gt_5, true); // a > 5
    combiner.assert_literal(b_lt_3, true); // b < 3

    let result = combiner.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "a=b AND a>5 AND b<3 must be UNSAT — requires EUF+LIA cooperation"
    );
}

/// Verify that a satisfiable LIA formula with UF is not falsely UNSAT.
///
/// Formula: x >= 0 AND x <= 2 AND 2*y = x
/// Expected: not UNSAT (satisfiable by x=0, y=0 or x=2, y=1)
/// The combiner should return SAT or NeedSplit, but never UNSAT.
#[test]
fn test_combiner_no_deferred_lia_split() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let y = terms.mk_fresh_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let two_val = terms.mk_int(BigInt::from(2));

    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_2 = terms.mk_le(x, two_val);
    let two_const = terms.mk_int(BigInt::from(2));
    let two_y = terms.mk_mul(vec![two_const, y]);
    let two_y_eq_x = terms.mk_eq(two_y, x);

    let mut combiner = TheoryCombiner::uf_lia(&terms);
    combiner.register_atom(x_ge_0);
    combiner.register_atom(x_le_2);
    combiner.register_atom(two_y_eq_x);
    combiner.assert_literal(x_ge_0, true);
    combiner.assert_literal(x_le_2, true);
    combiner.assert_literal(two_y_eq_x, true);

    let result = combiner.check();
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x>=0 AND x<=2 AND 2y=x is satisfiable — should not be UNSAT"
    );
}

/// Verify push/pop correctly isolates cross-theory N-O state.
///
/// 1. Assert x > 5, check → not UNSAT
/// 2. Push, assert x = y AND f(x) != f(y), check → UNSAT via congruence
/// 3. Pop, check → not UNSAT (the UNSAT constraints are gone)
/// 4. Push, assert y < 3, check → not UNSAT (x > 5, y < 3 with no x=y)
#[test]
fn test_combiner_no_push_pop_cross_theory_isolation() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let y = terms.mk_fresh_var("y", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let three = terms.mk_int(BigInt::from(3));
    let fx = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let fy = terms.mk_app(Symbol::named("f"), vec![y], Sort::Int);

    let x_gt_5 = terms.mk_gt(x, five);
    let x_eq_y = terms.mk_eq(x, y);
    let fx_eq_fy = terms.mk_eq(fx, fy);
    let y_lt_3 = terms.mk_lt(y, three);

    let mut combiner = TheoryCombiner::uf_lia(&terms);
    combiner.register_atom(x_gt_5);
    combiner.register_atom(x_eq_y);
    combiner.register_atom(fx_eq_fy);
    combiner.register_atom(y_lt_3);

    // Level 0: x > 5 → not UNSAT
    combiner.assert_literal(x_gt_5, true);
    let r1 = combiner.check();
    assert!(
        !matches!(
            r1,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x > 5 alone should not be UNSAT"
    );

    // Level 1: add x = y AND f(x) != f(y) → UNSAT via congruence
    combiner.push();
    combiner.assert_literal(x_eq_y, true);
    combiner.assert_literal(fx_eq_fy, false);
    let r2 = combiner.check();
    assert!(
        matches!(
            r2,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x=y AND f(x)!=f(y) should be UNSAT via EUF congruence"
    );

    // Pop: back to just x > 5 → not UNSAT
    combiner.pop();
    let r3 = combiner.check();
    assert!(
        !matches!(
            r3,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "After pop, x > 5 alone should not be UNSAT"
    );

    // Level 1 again: add y < 3 (no x=y) → not UNSAT
    combiner.push();
    combiner.assert_literal(y_lt_3, true);
    let r4 = combiner.check();
    assert!(
        !matches!(
            r4,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x > 5 AND y < 3 (without x=y) should not be UNSAT"
    );
    combiner.pop();
}

/// Verify array theory participates in the N-O fixpoint loop.
///
/// Formula: a[i] != a[j] AND i = j
/// Expected: UNSAT (array read-over-write: i=j → a[i]=a[j], contradicts a[i]!=a[j])
///
/// This test uses the array_euf combiner which has EUF + Arrays.
/// The equality i = j is handled by EUF, which tells the array solver
/// about the index equality, triggering the ROW axiom.
#[test]
fn test_combiner_no_array_euf_select_equality() {
    let mut terms = setup_term_store();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    let a = terms.mk_fresh_var("a", arr_sort);
    let i = terms.mk_fresh_var("i", Sort::Int);
    let j = terms.mk_fresh_var("j", Sort::Int);

    let a_i = terms.mk_select(a, i);
    let a_j = terms.mk_select(a, j);
    let i_eq_j = terms.mk_eq(i, j);
    let ai_eq_aj = terms.mk_eq(a_i, a_j);

    let mut combiner = TheoryCombiner::array_euf(&terms);
    combiner.register_atom(i_eq_j);
    combiner.register_atom(ai_eq_aj);
    combiner.assert_literal(i_eq_j, true); // i = j
    combiner.assert_literal(ai_eq_aj, false); // a[i] != a[j]

    let result = combiner.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "i=j AND a[i]!=a[j] must be UNSAT — requires array ROW axiom"
    );
}

/// Verify three-theory N-O fixpoint: EUF + LIA + Arrays.
///
/// Formula: a[i] > 10 AND a[j] < 5 AND i = j
/// Expected: UNSAT
/// Reasoning chain:
///   1. i = j asserted to EUF and (via shared equality) to arrays
///   2. Arrays: i = j → a[i] = a[j] (ROW axiom)
///   3. a[i] = a[j] propagated back to EUF, then to LIA as shared equality
///   4. LIA: a[i] > 10 AND a[j] < 5 with a[i] = a[j] → contradiction
///
/// This exercises the full EUF ↔ Arrays ↔ LIA propagation chain.
#[test]
fn test_combiner_no_auflia_three_theory_fixpoint() {
    let mut terms = setup_term_store();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    let a = terms.mk_fresh_var("a", arr_sort);
    let i = terms.mk_fresh_var("i", Sort::Int);
    let j = terms.mk_fresh_var("j", Sort::Int);

    let a_i = terms.mk_select(a, i);
    let a_j = terms.mk_select(a, j);
    let ten = terms.mk_int(BigInt::from(10));
    let five = terms.mk_int(BigInt::from(5));

    let i_eq_j = terms.mk_eq(i, j);
    let ai_gt_10 = terms.mk_gt(a_i, ten);
    let aj_lt_5 = terms.mk_lt(a_j, five);

    let mut combiner = TheoryCombiner::auf_lia(&terms);
    combiner.register_atom(i_eq_j);
    combiner.register_atom(ai_gt_10);
    combiner.register_atom(aj_lt_5);
    combiner.assert_literal(i_eq_j, true); // i = j
    combiner.assert_literal(ai_gt_10, true); // a[i] > 10
    combiner.assert_literal(aj_lt_5, true); // a[j] < 5

    let result = combiner.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "i=j AND a[i]>10 AND a[j]<5 must be UNSAT — requires EUF+Arrays+LIA propagation"
    );
}
