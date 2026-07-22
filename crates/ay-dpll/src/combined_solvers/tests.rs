// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::combiner::TheoryCombiner;
use super::*;
use ay_core::term::Symbol;
use ay_core::{ArraySort, Sort, TermId, TermStore, TheoryResult, TheorySolver};
use num_bigint::BigInt;

// Helper to create a term store with common test variables
fn setup_term_store() -> TermStore {
    TermStore::new()
}
// ============================================================
// TheoryCombiner::array_euf tests (replaces ArrayEufSolver)
// ============================================================

#[test]
fn test_array_euf_solver_new() {
    let terms = setup_term_store();
    let _solver = TheoryCombiner::array_euf(&terms);
}

#[test]
fn test_array_euf_solver_reset() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::array_euf(&terms);
    solver.reset();
}

#[test]
fn test_array_euf_solver_push_pop() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::array_euf(&terms);
    solver.push();
    solver.push();
    solver.pop();
    solver.pop();
}

#[test]
fn test_array_euf_solver_check_empty() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::array_euf(&terms);
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));
}

#[test]
fn test_array_euf_solver_propagate_empty() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::array_euf(&terms);
    let props = solver.propagate();
    assert!(props.is_empty());
}

#[test]
fn test_array_euf_solver_soft_reset_clears_conflict_state() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let eq = terms.mk_eq(x, zero);

    let mut solver = TheoryCombiner::array_euf(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(eq, false);
    assert!(
        matches!(
            solver.check(),
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "expected contradiction before soft_reset"
    );

    solver.soft_reset();
    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "soft_reset should clear ArrayEUF conflict state"
    );
}

#[test]
fn test_array_euf_solver_pop_underflow_returns() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::array_euf(&terms);
    // Pop at depth 0 is a graceful no-op (early return), not a panic.
    solver.pop();
    // Solver remains usable after underflow.
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
#[should_panic(expected = "BUG: TheoryCombiner(AX)::reset() called with non-zero scope depth")]
fn test_array_euf_solver_reset_with_open_scope_panics() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::array_euf(&terms);
    solver.push();
    solver.reset();
}

#[test]
#[should_panic(expected = "BUG: TheoryCombiner(AX)::soft_reset() called with non-zero scope depth")]
fn test_array_euf_solver_soft_reset_with_open_scope_panics() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::array_euf(&terms);
    solver.push();
    solver.soft_reset();
}

// ============================================================
// TheoryCombiner::uf_lia tests (replaces UfLiaSolver)
// ============================================================

#[test]
fn test_uf_lia_solver_new() {
    let terms = setup_term_store();
    let _solver = TheoryCombiner::uf_lia(&terms);
}

#[test]
fn test_uf_lia_solver_reset() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lia(&terms);
    solver.reset();
}

#[test]
fn test_uf_lia_solver_push_pop() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lia(&terms);
    solver.push();
    solver.push();
    solver.pop();
    solver.pop();
}

#[test]
fn test_uf_lia_solver_check_empty() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lia(&terms);
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));
}

#[test]
fn test_uf_lia_solver_propagate_empty() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lia(&terms);
    let props = solver.propagate();
    assert!(props.is_empty());
}

#[test]
fn test_uf_lia_solver_pop_underflow_returns() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lia(&terms);
    // Pop at depth 0 is a graceful no-op (early return), not a panic.
    solver.pop();
    // Solver remains usable after underflow.
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
#[should_panic(expected = "BUG: TheoryCombiner(UFLIA)::reset() called with non-zero scope depth")]
fn test_uf_lia_solver_reset_with_open_scope_panics() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lia(&terms);
    solver.push();
    solver.reset();
}

#[test]
#[should_panic(
    expected = "BUG: TheoryCombiner(UFLIA)::soft_reset() called with non-zero scope depth"
)]
fn test_uf_lia_solver_soft_reset_with_open_scope_panics() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lia(&terms);
    solver.push();
    solver.soft_reset();
}

// ============================================================
// TheoryCombiner::uf_lra tests (replaces UfLraSolver)
// ============================================================

#[test]
fn test_uf_lra_solver_new() {
    let terms = setup_term_store();
    let _solver = TheoryCombiner::uf_lra(&terms);
}

#[test]
fn test_uf_lra_solver_reset() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lra(&terms);
    solver.reset();
}

#[test]
fn test_uf_lra_solver_push_pop() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lra(&terms);
    solver.push();
    solver.pop();
}

#[test]
fn test_uf_lra_solver_check_empty() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lra(&terms);
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));
}

#[test]
fn test_uf_lra_solver_supports_farkas() {
    let terms = setup_term_store();
    let solver = TheoryCombiner::uf_lra(&terms);
    assert!(solver.supports_farkas_semantic_check());
}

#[test]
fn test_uf_lra_solver_extract_models_empty() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lra(&terms);
    let (euf_model, lra_model) = solver.extract_euf_lra_models();
    // Empty solver should have empty models
    assert!(euf_model.term_values.is_empty());
    assert!(lra_model.values.is_empty());
}

#[test]
fn test_uf_lra_solver_soft_reset_clears_conflict_state() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Real);
    let one = terms.mk_rational(num_rational::Ratio::new(BigInt::from(1), BigInt::from(1)));
    let zero = terms.mk_rational(num_rational::Ratio::new(BigInt::from(0), BigInt::from(1)));
    let gt_one = terms.mk_gt(x, one);
    let lt_zero = terms.mk_lt(x, zero);

    let mut solver = TheoryCombiner::uf_lra(&terms);
    solver.assert_literal(gt_one, true);
    solver.assert_literal(lt_zero, true);
    assert!(
        matches!(
            solver.check(),
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "expected contradiction before soft_reset"
    );

    solver.soft_reset();
    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "soft_reset should clear UFLRA conflict state"
    );
}

#[test]
fn test_uf_lra_solver_pop_underflow_returns() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lra(&terms);
    // Pop at depth 0 is a graceful no-op (early return), not a panic.
    solver.pop();
    // Solver remains usable after underflow.
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
#[should_panic(expected = "BUG: TheoryCombiner(UFLRA)::reset() called with non-zero scope depth")]
fn test_uf_lra_solver_reset_with_open_scope_panics() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lra(&terms);
    solver.push();
    solver.reset();
}

#[test]
#[should_panic(
    expected = "BUG: TheoryCombiner(UFLRA)::soft_reset() called with non-zero scope depth"
)]
fn test_uf_lra_solver_soft_reset_with_open_scope_panics() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::uf_lra(&terms);
    solver.push();
    solver.soft_reset();
}

// ============================================================
// TheoryCombiner::auf_lia tests (replaces AufLiaSolver)
// ============================================================

#[test]
fn test_auf_lia_solver_new() {
    let terms = setup_term_store();
    let _solver = TheoryCombiner::auf_lia(&terms);
}

#[test]
fn test_auf_lia_solver_reset() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::auf_lia(&terms);
    solver.reset();
}

#[test]
fn test_auf_lia_solver_push_pop() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::auf_lia(&terms);
    solver.push();
    solver.push();
    solver.pop();
    solver.pop();
}

#[test]
fn test_auf_lia_solver_check_empty() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::auf_lia(&terms);
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));
}

#[test]
fn test_auf_lia_solver_pop_underflow_returns() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::auf_lia(&terms);
    // Pop at depth 0 is a graceful no-op (early return), not a panic.
    solver.pop();
    // Solver remains usable after underflow.
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
#[should_panic(expected = "BUG: TheoryCombiner(AUFLIA)::reset() called with non-zero scope depth")]
fn test_auf_lia_solver_reset_with_open_scope_panics() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::auf_lia(&terms);
    solver.push();
    solver.reset();
}

#[test]
#[should_panic(
    expected = "BUG: TheoryCombiner(AUFLIA)::soft_reset() called with non-zero scope depth"
)]
fn test_auf_lia_solver_soft_reset_with_open_scope_panics() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::auf_lia(&terms);
    solver.push();
    solver.soft_reset();
}

// ============================================================
// TheoryCombiner::auf_lra tests (replaces AufLraSolver)
// ============================================================

#[test]
fn test_auf_lra_solver_new() {
    let terms = setup_term_store();
    let _solver = TheoryCombiner::auf_lra(&terms);
}

#[test]
fn test_auf_lra_solver_reset() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::auf_lra(&terms);
    solver.reset();
}

#[test]
fn test_auf_lra_solver_push_pop() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::auf_lra(&terms);
    solver.push();
    solver.pop();
}

#[test]
fn test_auf_lra_solver_check_empty() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::auf_lra(&terms);
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));
}

#[test]
fn test_auf_lra_solver_pop_underflow_returns() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::auf_lra(&terms);
    // Pop at depth 0 is a graceful no-op (early return), not a panic.
    solver.pop();
    // Solver remains usable after underflow.
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
#[should_panic(expected = "BUG: TheoryCombiner(AUFLRA)::reset() called with non-zero scope depth")]
fn test_auf_lra_solver_reset_with_open_scope_panics() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::auf_lra(&terms);
    solver.push();
    solver.reset();
}

#[test]
#[should_panic(
    expected = "BUG: TheoryCombiner(AUFLRA)::soft_reset() called with non-zero scope depth"
)]
fn test_auf_lra_solver_soft_reset_with_open_scope_panics() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::auf_lra(&terms);
    solver.push();
    solver.soft_reset();
}

// ============================================================
// LiraSolver tests (still a bespoke adapter)
// ============================================================

#[test]
fn test_lira_solver_new() {
    let terms = setup_term_store();
    let _solver = LiraSolver::new(&terms);
}

#[test]
fn test_lira_solver_reset() {
    let terms = setup_term_store();
    let mut solver = LiraSolver::new(&terms);
    solver.reset();
}

#[test]
fn test_lira_solver_push_pop() {
    let terms = setup_term_store();
    let mut solver = LiraSolver::new(&terms);
    solver.push();
    solver.push();
    solver.pop();
    solver.pop();
}

#[test]
fn test_lira_solver_check_empty() {
    let terms = setup_term_store();
    let mut solver = LiraSolver::new(&terms);
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));
}

#[test]
fn test_lira_solver_propagate_empty() {
    let terms = setup_term_store();
    let mut solver = LiraSolver::new(&terms);
    let props = solver.propagate();
    assert!(props.is_empty());
}

#[test]
fn test_lira_solver_pop_underflow_returns() {
    let terms = setup_term_store();
    let mut solver = LiraSolver::new(&terms);
    // Pop at depth 0 is a graceful no-op (early return), not a panic.
    solver.pop();
    // Solver remains usable after underflow.
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
#[should_panic(expected = "BUG: LiraSolver::reset() called with non-zero scope depth")]
fn test_lira_solver_reset_with_open_scope_panics() {
    let terms = setup_term_store();
    let mut solver = LiraSolver::new(&terms);
    solver.push();
    solver.reset();
}

#[test]
#[should_panic(expected = "BUG: LiraSolver::soft_reset() called with non-zero scope depth")]
fn test_lira_solver_soft_reset_with_open_scope_panics() {
    let terms = setup_term_store();
    let mut solver = LiraSolver::new(&terms);
    solver.push();
    solver.soft_reset();
}

#[test]
fn test_strings_lia_equal_length_suffix_mismatch_unsat() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::String);
    let y = terms.mk_fresh_var("y", Sort::String);
    let a = terms.mk_string("a".to_string());
    let b = terms.mk_string("b".to_string());

    let concat_xa = terms.mk_app(Symbol::named("str.++"), vec![x, a], Sort::String);
    let concat_yb = terms.mk_app(Symbol::named("str.++"), vec![y, b], Sort::String);
    let concat_eq = terms.mk_eq(concat_xa, concat_yb);

    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = terms.mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
    let len_eq = terms.mk_eq(len_x, len_y);

    let mut solver = StringsLiaSolver::new(&terms);
    solver.assert_literal(len_eq, true);
    solver.assert_literal(concat_eq, true);

    let result = solver.check();
    // After #6261 soundness guard: the initial string check's Unsat is
    // converted to Unknown (strings_incomplete=true) because the NF
    // comparison can produce spurious conflicts on multi-variable word
    // equations. The CEGAR loop at the DPLL(T) level will eventually
    // prove this Unsat via split lemmas. At the theory-solver level,
    // Unknown is the correct conservative answer.
    assert!(
        matches!(result, TheoryResult::Unsat(_) | TheoryResult::Unknown),
        "len(x)=len(y) ∧ x++\"a\"=y++\"b\" should be Unsat or Unknown in StringsLiaSolver, got {result:?}"
    );
}

/// Test that StringsLiaSolver iterates interface terms in deterministic (sorted) order.
///
/// Regression test for #3674: interface_arith_terms was iterated as a HashSet
/// (nondeterministic), while UfLiaSolver and TheoryCombiner::auf_lia correctly sorted first.
///
/// Sets up multiple interface arithmetic terms and asserts exact sorted order.
#[test]
fn test_strings_lia_interface_term_deterministic_order() {
    let mut terms = setup_term_store();
    let c = terms.mk_fresh_var("c", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let three = terms.mk_int(BigInt::from(3));

    // Create two interface arithmetic terms: (* c 2) and (* c 3)
    let c_times_2 = terms.mk_app(Symbol::named("*"), vec![c, two], Sort::Int);
    let c_times_3 = terms.mk_app(Symbol::named("*"), vec![c, three], Sort::Int);

    // (f c) - uninterpreted function for EUF side
    let f_c = terms.mk_app(Symbol::named("f"), vec![c], Sort::Int);

    // Create string variable so StringsLiaSolver has string content
    let s = terms.mk_fresh_var("s", Sort::String);
    let len_s = terms.mk_app(Symbol::named("str.len"), vec![s], Sort::Int);

    // (= (f c) (* c 2)) and (= (str.len s) (* c 3)) - two interface equalities
    let eq_fc_c2 = terms.mk_app(Symbol::named("="), vec![f_c, c_times_2], Sort::Bool);
    let eq_lens_c3 = terms.mk_app(Symbol::named("="), vec![len_s, c_times_3], Sort::Bool);

    let mut solver = StringsLiaSolver::new(&terms);
    solver.assert_literal(eq_fc_c2, true);
    solver.assert_literal(eq_lens_c3, true);

    // Both interface terms should be registered
    assert!(
        solver.has_interface_term(c_times_2),
        "interface term (* c 2) should be tracked"
    );
    assert!(
        solver.has_interface_term(c_times_3),
        "interface term (* c 3) should be tracked"
    );

    let ordered_terms = solver.sorted_interface_terms();
    assert_eq!(
        ordered_terms,
        vec![c_times_2, c_times_3],
        "interface arithmetic terms must be propagated in sorted TermId order"
    );
}

#[test]
fn test_strings_lia_solver_pop_underflow_returns() {
    let terms = setup_term_store();
    let mut solver = StringsLiaSolver::new(&terms);
    // Pop at depth 0 is a graceful no-op (early return), not a panic.
    solver.pop();
    // Solver remains usable after underflow.
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
#[should_panic(expected = "BUG: StringsLiaSolver::reset() called with non-zero scope depth")]
fn test_strings_lia_solver_reset_with_open_scope_panics() {
    let terms = setup_term_store();
    let mut solver = StringsLiaSolver::new(&terms);
    solver.push();
    solver.reset();
}

#[test]
#[should_panic(expected = "BUG: StringsLiaSolver::soft_reset() called with non-zero scope depth")]
fn test_strings_lia_solver_soft_reset_with_open_scope_panics() {
    let terms = setup_term_store();
    let mut solver = StringsLiaSolver::new(&terms);
    solver.push();
    solver.soft_reset();
}

#[test]
fn test_lira_solver_extract_models_empty() {
    let terms = setup_term_store();
    let mut solver = LiraSolver::new(&terms);
    let (lia_model, lra_model) = solver.extract_models();
    // Empty solver should have empty LIA/LRA models.
    assert!(
        matches!(lia_model.as_ref(), Some(m) if m.values.is_empty()),
        "expected Some(empty) LIA model for empty solver"
    );
    assert!(lra_model.values.is_empty());
}

// ============================================================
// AufLiraSolver tests (still a bespoke adapter)
// ============================================================

#[test]
fn test_auf_lira_solver_new() {
    let terms = setup_term_store();
    let _solver = AufLiraSolver::new(&terms);
}

#[test]
fn test_auf_lira_solver_reset() {
    let terms = setup_term_store();
    let mut solver = AufLiraSolver::new(&terms);
    solver.reset();
}

#[test]
fn test_auf_lira_solver_push_pop() {
    let terms = setup_term_store();
    let mut solver = AufLiraSolver::new(&terms);
    solver.push();
    solver.push();
    solver.pop();
    solver.pop();
}

#[test]
fn test_auf_lira_solver_check_empty() {
    let terms = setup_term_store();
    let mut solver = AufLiraSolver::new(&terms);
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));
}

#[test]
fn test_auf_lira_solver_propagate_empty() {
    let terms = setup_term_store();
    let mut solver = AufLiraSolver::new(&terms);
    let props = solver.propagate();
    assert!(props.is_empty());
}

#[test]
fn test_auf_lira_solver_extract_all_models_empty() {
    let terms = setup_term_store();
    let mut solver = AufLiraSolver::new(&terms);
    let (euf_model, array_model, lia_model, lra_model) = solver.extract_all_models();
    assert!(euf_model.term_values.is_empty());
    assert!(array_model.array_values.is_empty());
    assert!(
        matches!(lia_model.as_ref(), Some(m) if m.values.is_empty()),
        "expected Some(empty) LIA model for empty solver"
    );
    assert!(lra_model.values.is_empty());
}

#[test]
fn test_auf_lira_solver_pop_underflow_returns() {
    let terms = setup_term_store();
    let mut solver = AufLiraSolver::new(&terms);
    // Pop at depth 0 is a graceful no-op (early return), not a panic.
    solver.pop();
    // Solver remains usable after underflow.
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
#[should_panic(expected = "BUG: AufLiraSolver::reset() called with non-zero scope depth")]
fn test_auf_lira_solver_reset_with_open_scope_panics() {
    let terms = setup_term_store();
    let mut solver = AufLiraSolver::new(&terms);
    solver.push();
    solver.reset();
}

#[test]
#[should_panic(expected = "BUG: AufLiraSolver::soft_reset() called with non-zero scope depth")]
fn test_auf_lira_solver_soft_reset_with_open_scope_panics() {
    let terms = setup_term_store();
    let mut solver = AufLiraSolver::new(&terms);
    solver.push();
    solver.soft_reset();
}

// ============================================================
// Assert literal routing tests
// ============================================================

#[test]
fn test_uf_lia_assert_literal_with_int_constraint() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    // x > 5 - this involves Int arithmetic
    let constraint = terms.mk_gt(x, five);

    let mut solver = TheoryCombiner::uf_lia(&terms);
    solver.assert_literal(constraint, true);
    let result = solver.check();
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Single positive constraint should not be UNSAT"
    );
}

#[test]
fn test_uf_lra_assert_literal_with_real_constraint() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Real);
    let half = terms.mk_rational(num_rational::Ratio::new(BigInt::from(1), BigInt::from(2)));
    // x > 0.5 - this involves Real arithmetic
    let constraint = terms.mk_gt(x, half);

    let mut solver = TheoryCombiner::uf_lra(&terms);
    solver.assert_literal(constraint, true);
    let result = solver.check();
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Single positive constraint should not be UNSAT"
    );
}

#[test]
fn test_lira_routes_int_to_lia() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let constraint = terms.mk_gt(x, one);

    let mut solver = LiraSolver::new(&terms);
    solver.assert_literal(constraint, true);
    let result = solver.check();
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Single positive constraint should not be UNSAT"
    );
}

#[test]
fn test_lira_routes_real_to_lra() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Real);
    let one = terms.mk_rational(num_rational::Ratio::new(BigInt::from(1), BigInt::from(1)));
    let constraint = terms.mk_gt(x, one);

    let mut solver = LiraSolver::new(&terms);
    solver.assert_literal(constraint, true);
    let result = solver.check();
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Single positive constraint should not be UNSAT"
    );
}

// ============================================================
// Conflict detection tests
// ============================================================

#[test]
fn test_uf_lia_detects_unsat() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));

    // x > 1 AND x < 0 - contradiction
    let gt_one = terms.mk_gt(x, one);
    let lt_zero = terms.mk_lt(x, zero);

    let mut solver = TheoryCombiner::uf_lia(&terms);
    solver.assert_literal(gt_one, true);
    solver.assert_literal(lt_zero, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Expected UNSAT for contradictory constraints"
    );
}

#[test]
fn test_lira_detects_int_unsat() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));

    let gt_one = terms.mk_gt(x, one);
    let lt_zero = terms.mk_lt(x, zero);

    let mut solver = LiraSolver::new(&terms);
    solver.assert_literal(gt_one, true);
    solver.assert_literal(lt_zero, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Expected UNSAT for contradictory Int constraints"
    );
}

// ============================================================
// Push/pop state isolation tests
// ============================================================

#[test]
fn test_uf_lia_push_pop_isolates_state() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));

    let gt_one = terms.mk_gt(x, one);
    let lt_zero = terms.mk_lt(x, zero);

    let mut solver = TheoryCombiner::uf_lia(&terms);

    solver.assert_literal(gt_one, true);
    let result1 = solver.check();
    assert!(
        !matches!(
            result1,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Single positive constraint should not be UNSAT"
    );

    solver.push();
    solver.assert_literal(lt_zero, true);
    let result2 = solver.check();
    assert!(
        matches!(
            result2,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Inner scope should be UNSAT"
    );

    solver.pop();
}

#[test]
fn test_array_euf_push_pop_isolates_state() {
    let terms = setup_term_store();
    let mut solver = TheoryCombiner::array_euf(&terms);

    assert!(matches!(solver.check(), TheoryResult::Sat));

    solver.push();
    solver.push();
    solver.pop();
    solver.pop();

    assert!(matches!(solver.check(), TheoryResult::Sat));
}

// ============================================================
// Nelson-Oppen interface term propagation tests (#1893)
// ============================================================

/// Test for #1893: Nelson-Oppen theory combination must propagate interface term values.
#[test]
fn test_nelson_oppen_interface_term_evaluation() {
    let mut terms = setup_term_store();
    let c = terms.mk_fresh_var("c", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let c_times_2 = terms.mk_app(Symbol::named("*"), vec![c, two], Sort::Int);
    let f_c = terms.mk_app(Symbol::named("f"), vec![c], Sort::Int);
    let eq_fc_c2 = terms.mk_app(Symbol::named("="), vec![f_c, c_times_2], Sort::Bool);
    let eq_c_5 = terms.mk_app(Symbol::named("="), vec![c, five], Sort::Bool);
    let eq_fc_10 = terms.mk_app(Symbol::named("="), vec![f_c, ten], Sort::Bool);
    let not_eq_fc_10 = terms.mk_not(eq_fc_10);

    let mut solver = TheoryCombiner::uf_lia(&terms);
    solver.assert_literal(eq_fc_c2, true);
    solver.assert_literal(eq_c_5, true);
    solver.assert_literal(not_eq_fc_10, true);

    let result = solver.check();
    // UnsatWithFarkas accepted since #rank-4 increment 2: the LIA affine
    // path certifies this equality-implication conflict.
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Expected UNSAT from Nelson-Oppen interface term propagation, got {result:?}"
    );
}

/// Test that push/pop correctly saves and restores interface term tracking state.
#[test]
fn test_uflia_push_pop_clears_interface_terms() {
    let mut terms = setup_term_store();
    let c = terms.mk_fresh_var("c", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let five = terms.mk_int(BigInt::from(5));

    let c_times_2 = terms.mk_app(Symbol::named("*"), vec![c, two], Sort::Int);
    let f_c = terms.mk_app(Symbol::named("f"), vec![c], Sort::Int);
    let eq_fc_c2 = terms.mk_app(Symbol::named("="), vec![f_c, c_times_2], Sort::Bool);
    let eq_c_5 = terms.mk_app(Symbol::named("="), vec![c, five], Sort::Bool);

    let mut solver = TheoryCombiner::uf_lia(&terms);

    solver.push();
    solver.assert_literal(eq_fc_c2, true);

    assert!(
        solver.has_interface_term(c_times_2),
        "Interface term should be tracked after assertion"
    );

    solver.pop();

    assert!(
        !solver.has_interface_term(c_times_2),
        "Interface term should be cleared after pop"
    );

    solver.assert_literal(eq_c_5, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "Expected SAT after pop removed interface term, got {result:?}"
    );
}

/// Test Nelson-Oppen interface term propagation for TheoryCombiner::auf_lia (#1926).
#[test]
fn test_auflia_nelson_oppen_interface_term_evaluation() {
    let mut terms = setup_term_store();
    let c = terms.mk_fresh_var("c", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let c_times_2 = terms.mk_app(Symbol::named("*"), vec![c, two], Sort::Int);
    let f_c = terms.mk_app(Symbol::named("f"), vec![c], Sort::Int);
    let eq_fc_c2 = terms.mk_app(Symbol::named("="), vec![f_c, c_times_2], Sort::Bool);
    let eq_c_5 = terms.mk_app(Symbol::named("="), vec![c, five], Sort::Bool);
    let eq_fc_10 = terms.mk_app(Symbol::named("="), vec![f_c, ten], Sort::Bool);
    let not_eq_fc_10 = terms.mk_not(eq_fc_10);

    let mut solver = TheoryCombiner::auf_lia(&terms);
    solver.assert_literal(eq_fc_c2, true);
    solver.assert_literal(eq_c_5, true);
    solver.assert_literal(not_eq_fc_10, true);

    let result = solver.check();
    // UnsatWithFarkas accepted since #rank-4 increment 2: the LIA affine
    // path certifies this equality-implication conflict.
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Expected UNSAT from AufLia Nelson-Oppen interface term propagation (#1926), got {result:?}"
    );
}

#[test]
fn test_auflia_tracks_bare_int_uf_apps_as_interface_terms_6846() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let y = terms.mk_fresh_var("y", Sort::Int);
    let rf_x = terms.mk_app(Symbol::named("RF"), vec![x], Sort::Int);
    let rf_y = terms.mk_app(Symbol::named("RF"), vec![y], Sort::Int);
    let eq_rf_x_rf_y = terms.mk_eq(rf_x, rf_y);

    let mut solver = TheoryCombiner::auf_lia(&terms);
    solver.assert_literal(eq_rf_x_rf_y, true);

    assert!(
        solver.has_interface_term(rf_x),
        "left bare UF application should be tracked as an interface term"
    );
    assert!(
        solver.has_interface_term(rf_y),
        "right bare UF application should be tracked as an interface term"
    );
}

#[test]
fn test_auflia_combiner_catches_disjunctive_store_equality_regression_6885() {
    let mut terms = setup_term_store();
    let arr_sort = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));

    let a = terms.mk_fresh_var("a", arr_sort.clone());
    let b = terms.mk_fresh_var("b", arr_sort);
    let x = terms.mk_fresh_var("x", Sort::Int);
    let y = terms.mk_fresh_var("y", Sort::Int);
    let v = terms.mk_fresh_var("v", Sort::Int);
    let w = terms.mk_fresh_var("w", Sort::Int);
    let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let f_y = terms.mk_app(Symbol::named("f"), vec![y], Sort::Int);
    let g_a = terms.mk_app(Symbol::named("g"), vec![a], Sort::Int);
    let g_b = terms.mk_app(Symbol::named("g"), vec![b], Sort::Int);

    let store_x = terms.mk_store(a, x, v);
    let store_y = terms.mk_store(a, y, w);
    let eq_fx_fy = terms.mk_eq(f_x, f_y);
    let eq_ga_gb = terms.mk_eq(g_a, g_b);
    let eq_store_x_b = terms.mk_eq(store_x, b);
    let eq_store_y_b = terms.mk_eq(store_y, b);
    let not_eq_fx_fy = terms.mk_not(eq_fx_fy);
    let not_eq_ga_gb = terms.mk_not(eq_ga_gb);

    let mut solver = TheoryCombiner::auf_lia(&terms);
    solver.assert_literal(eq_store_x_b, true);
    solver.assert_literal(eq_store_y_b, true);
    solver.assert_literal(not_eq_fx_fy, true);
    solver.assert_literal(not_eq_ga_gb, true);

    let result = solver.check();
    assert!(
        !matches!(result, TheoryResult::Sat),
        "AUFLIA combiner must not accept the #6885 disjunctive-store formula as SAT: {result:?}"
    );
}

/// Test that push/pop correctly saves and restores interface term tracking state
/// for TheoryCombiner::auf_lia (#1926).
#[test]
fn test_auflia_push_pop_clears_interface_terms() {
    let mut terms = setup_term_store();
    let c = terms.mk_fresh_var("c", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let five = terms.mk_int(BigInt::from(5));

    let c_times_2 = terms.mk_app(Symbol::named("*"), vec![c, two], Sort::Int);
    let f_c = terms.mk_app(Symbol::named("f"), vec![c], Sort::Int);
    let eq_fc_c2 = terms.mk_app(Symbol::named("="), vec![f_c, c_times_2], Sort::Bool);
    let eq_c_5 = terms.mk_app(Symbol::named("="), vec![c, five], Sort::Bool);

    let mut solver = TheoryCombiner::auf_lia(&terms);
    solver.push();

    solver.assert_literal(eq_fc_c2, true);

    assert!(
        solver.has_interface_term(c_times_2),
        "Interface term should be tracked after assert_literal"
    );

    solver.pop();

    assert!(
        !solver.has_interface_term(c_times_2),
        "Interface term should be cleared after pop"
    );

    solver.assert_literal(eq_c_5, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "Expected SAT after pop removed interface term, got {result:?}"
    );
}

#[test]
fn test_combined_solvers_need_final_check_after_sat() {
    let terms = setup_term_store();

    assert!(TheoryCombiner::uf_lia(&terms).needs_final_check_after_sat());
    assert!(TheoryCombiner::uf_lra(&terms).needs_final_check_after_sat());
    assert!(LiraSolver::new(&terms).needs_final_check_after_sat());
    assert!(AufLiraSolver::new(&terms).needs_final_check_after_sat());
    assert!(UfNraSolver::new(&terms).needs_final_check_after_sat());
}

#[test]
fn test_uflia_check_during_propagate_defers_interface_bridge_unsat() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let three = terms.mk_int(BigInt::from(3));
    let ten = terms.mk_int(BigInt::from(10));

    let x_plus_one = terms.mk_app(Symbol::named("+"), vec![x, one], Sort::Int);
    let f_x_plus_one = terms.mk_app(Symbol::named("f"), vec![x_plus_one], Sort::Int);
    let f_three = terms.mk_app(Symbol::named("f"), vec![three], Sort::Int);
    let x_eq_two = terms.mk_eq(x, two);
    let f_three_eq_ten = terms.mk_eq(f_three, ten);
    let f_x_plus_one_eq_ten = terms.mk_eq(f_x_plus_one, ten);

    let mut solver = TheoryCombiner::uf_lia(&terms);
    solver.assert_literal(x_eq_two, true);
    solver.assert_literal(f_three_eq_ten, true);
    solver.assert_literal(f_x_plus_one_eq_ten, false);

    assert!(
        matches!(solver.check_during_propagate(), TheoryResult::Sat),
        "BCP-time UFLIA check should defer interface-bridge UNSAT to the final check"
    );

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Full UFLIA check should still find the deferred interface-bridge conflict, got {result:?}"
    );
}

#[test]
fn test_uflia_ground_definitional_uf_arith_chain_unsat_7884() {
    let mut terms = setup_term_store();
    let i = terms.mk_fresh_var("i", Sort::Int);
    let acc = terms.mk_fresh_var("acc", Sort::Int);
    let i_prime = terms.mk_fresh_var("i_prime", Sort::Int);
    let acc_prime = terms.mk_fresh_var("acc_prime", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));

    let double_i = terms.mk_app(Symbol::named("logic_double"), vec![i], Sort::Int);
    let double_i_prime = terms.mk_app(Symbol::named("logic_double"), vec![i_prime], Sort::Int);
    let i_plus_i = terms.mk_app(Symbol::named("+"), vec![i, i], Sort::Int);
    let ip_plus_ip = terms.mk_app(Symbol::named("+"), vec![i_prime, i_prime], Sort::Int);
    let i_plus_one = terms.mk_app(Symbol::named("+"), vec![i, one], Sort::Int);
    let acc_plus_two = terms.mk_app(Symbol::named("+"), vec![acc, two], Sort::Int);

    let double_i_eq_i_plus_i = terms.mk_eq(double_i, i_plus_i);
    let double_ip_eq_ip_plus_ip = terms.mk_eq(double_i_prime, ip_plus_ip);
    let acc_eq_double_i = terms.mk_eq(acc, double_i);
    let ip_eq_i_plus_one = terms.mk_eq(i_prime, i_plus_one);
    let accp_eq_acc_plus_two = terms.mk_eq(acc_prime, acc_plus_two);
    let accp_eq_double_ip = terms.mk_eq(acc_prime, double_i_prime);

    let mut solver = TheoryCombiner::uf_lia(&terms);
    solver.assert_literal(double_i_eq_i_plus_i, true);
    solver.assert_literal(double_ip_eq_ip_plus_ip, true);
    solver.assert_literal(acc_eq_double_i, true);
    solver.assert_literal(ip_eq_i_plus_one, true);
    solver.assert_literal(accp_eq_acc_plus_two, true);
    solver.assert_literal(accp_eq_double_ip, false);

    let result = solver.check();
    let targets_preservation_refinement = |lhs: TermId, rhs: TermId| {
        let late_chain = [i_prime, acc_prime, double_i_prime, ip_plus_ip];
        late_chain.contains(&lhs)
            && late_chain.contains(&rhs)
            && (lhs == acc_prime
                || rhs == acc_prime
                || lhs == double_i_prime
                || rhs == double_i_prime)
    };
    match result {
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => {}
        TheoryResult::NeedModelEquality(req) => {
            assert!(
                targets_preservation_refinement(req.lhs, req.rhs),
                "Expected model equality in the late preservation chain, got {req:?}"
            );
        }
        TheoryResult::NeedModelEqualities(reqs) => {
            assert!(
                reqs.iter()
                    .any(|req| targets_preservation_refinement(req.lhs, req.rhs)),
                "Expected a model equality in the late preservation chain, got {reqs:?}"
            );
        }
        other => panic!(
            "Expected UNSAT or a model-equality refinement before arithmetic expression split, got {other:?}"
        ),
    }
}

#[test]
fn test_uflra_check_during_propagate_defers_interface_bridge_unsat() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Real);
    let one = terms.mk_rational(num_rational::Ratio::new(BigInt::from(1), BigInt::from(1)));
    let two = terms.mk_rational(num_rational::Ratio::new(BigInt::from(2), BigInt::from(1)));
    let three = terms.mk_rational(num_rational::Ratio::new(BigInt::from(3), BigInt::from(1)));
    let ten = terms.mk_rational(num_rational::Ratio::new(BigInt::from(10), BigInt::from(1)));

    let x_plus_one = terms.mk_app(Symbol::named("+"), vec![x, one], Sort::Real);
    let f_x_plus_one = terms.mk_app(Symbol::named("f"), vec![x_plus_one], Sort::Real);
    let f_three = terms.mk_app(Symbol::named("f"), vec![three], Sort::Real);
    let x_eq_two = terms.mk_eq(x, two);
    let f_three_eq_ten = terms.mk_eq(f_three, ten);
    let f_x_plus_one_eq_ten = terms.mk_eq(f_x_plus_one, ten);

    let mut solver = TheoryCombiner::uf_lra(&terms);
    solver.assert_literal(x_eq_two, true);
    solver.assert_literal(f_three_eq_ten, true);
    solver.assert_literal(f_x_plus_one_eq_ten, false);

    assert!(
        matches!(solver.check_during_propagate(), TheoryResult::Sat),
        "BCP-time UFLRA check should defer interface-bridge UNSAT to the final check"
    );

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Full UFLRA check should still find the deferred interface-bridge conflict, got {result:?}"
    );
}

#[test]
fn test_lira_check_during_propagate_keeps_local_unsat() {
    let mut terms = setup_term_store();
    let x = terms.mk_fresh_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));

    let x_gt_one = terms.mk_gt(x, one);
    let x_lt_zero = terms.mk_lt(x, zero);

    let mut solver = LiraSolver::new(&terms);
    solver.assert_literal(x_gt_one, true);
    solver.assert_literal(x_lt_zero, true);

    let result = solver.check_during_propagate();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "BCP-time LIRA check must still report local arithmetic conflicts, got {result:?}"
    );
}

#[test]
fn test_lira_check_during_propagate_defers_cross_sort_unsat() {
    let mut terms = setup_term_store();
    let relu = terms.mk_fresh_var("relu", Sort::Real);
    let phase = terms.mk_fresh_var("phase", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_rational(num_rational::Ratio::new(BigInt::from(1), BigInt::from(1)));

    let phase_real = terms.mk_to_real(phase);
    let phase_eq_zero = terms.mk_eq(phase, zero);
    let relu_le_phase = terms.mk_le(relu, phase_real);
    let relu_ge_one = terms.mk_ge(relu, one);

    let mut solver = LiraSolver::new(&terms);
    solver.assert_literal(phase_eq_zero, true);
    solver.assert_literal(relu_le_phase, true);
    solver.assert_literal(relu_ge_one, true);

    assert!(
        matches!(solver.check_during_propagate(), TheoryResult::Sat),
        "BCP-time LIRA check should defer cross-sort UNSAT to the final check"
    );

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Full LIRA check should still find the deferred cross-sort conflict, got {result:?}"
    );
}

#[test]
fn test_auflira_check_during_propagate_defers_interface_bridge_unsat() {
    let mut terms = setup_term_store();
    let y = terms.mk_fresh_var("y", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let three = terms.mk_int(BigInt::from(3));
    let ten = terms.mk_int(BigInt::from(10));

    let y_plus_one = terms.mk_app(Symbol::named("+"), vec![y, one], Sort::Int);
    let g_y_plus_one = terms.mk_app(Symbol::named("g"), vec![y_plus_one], Sort::Int);
    let g_three = terms.mk_app(Symbol::named("g"), vec![three], Sort::Int);
    let y_eq_two = terms.mk_eq(y, two);
    let g_three_eq_ten = terms.mk_eq(g_three, ten);
    let g_y_plus_one_eq_ten = terms.mk_eq(g_y_plus_one, ten);

    let mut solver = AufLiraSolver::new(&terms);
    solver.assert_literal(y_eq_two, true);
    solver.assert_literal(g_three_eq_ten, true);
    solver.assert_literal(g_y_plus_one_eq_ten, false);

    assert!(
        matches!(solver.check_during_propagate(), TheoryResult::Sat),
        "BCP-time AUFLIRA check should defer interface-bridge UNSAT to the final check"
    );

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Full AUFLIRA check should still find the deferred interface-bridge conflict, got {result:?}"
    );
}

/// Test that negated UF-int equalities are forwarded to LIA as shared
/// disequalities, enabling conflict detection (#5228).
#[test]
fn test_uflia_shared_disequality_propagation_5228() {
    let mut terms = setup_term_store();
    let zero = terms.mk_int(BigInt::from(0));
    let five = terms.mk_int(BigInt::from(5));

    let g_0 = terms.mk_app(Symbol::named("g"), vec![zero], Sort::Int);
    let ge_g0_5 = terms.mk_app(Symbol::named(">="), vec![g_0, five], Sort::Bool);
    let le_g0_5 = terms.mk_app(Symbol::named("<="), vec![g_0, five], Sort::Bool);
    let eq_g0_5 = terms.mk_app(Symbol::named("="), vec![g_0, five], Sort::Bool);

    let mut solver = TheoryCombiner::uf_lia(&terms);

    solver.assert_literal(ge_g0_5, true);
    solver.assert_literal(le_g0_5, true);
    solver.assert_literal(eq_g0_5, false);

    let result = solver.check();
    assert!(
        !matches!(result, TheoryResult::Sat),
        "Expected non-Sat for UNSAT formula with disequality propagation (#5228), got {result:?}"
    );
}

/// Shared disequality trail push/pop correctness (#5228).
#[test]
fn test_uflia_shared_disequality_push_pop_isolation_5228() {
    let mut terms = setup_term_store();
    let zero = terms.mk_int(BigInt::from(0));
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let g_0 = terms.mk_app(Symbol::named("g"), vec![zero], Sort::Int);
    let ge_g0_5 = terms.mk_app(Symbol::named(">="), vec![g_0, five], Sort::Bool);
    let le_g0_5 = terms.mk_app(Symbol::named("<="), vec![g_0, five], Sort::Bool);
    let eq_g0_5 = terms.mk_app(Symbol::named("="), vec![g_0, five], Sort::Bool);
    let le_g0_10 = terms.mk_app(Symbol::named("<="), vec![g_0, ten], Sort::Bool);

    let mut solver = TheoryCombiner::uf_lia(&terms);

    solver.push();
    solver.assert_literal(ge_g0_5, true);
    solver.assert_literal(le_g0_5, true);
    solver.assert_literal(eq_g0_5, false);
    let result1 = solver.check();
    assert!(
        !matches!(result1, TheoryResult::Sat),
        "Scope 1: expected non-Sat for UNSAT formula, got {result1:?}"
    );
    solver.pop();

    solver.push();
    solver.assert_literal(ge_g0_5, true);
    solver.assert_literal(le_g0_10, true);
    let result2 = solver.check();
    // The combiner may return Sat directly, or NeedModelEquality if
    // discover_model_equality finds UF app g(0) and LIA constant 5 with
    // matching values but no EUF equality. Both are correct combiner-level
    // results — the pipeline handles NeedModelEquality by encoding the
    // equality and re-solving.
    assert!(
        matches!(
            result2,
            TheoryResult::Sat | TheoryResult::NeedModelEquality(_)
        ),
        "Scope 2: expected Sat or NeedModelEquality for satisfiable formula, got {result2:?}"
    );
    solver.pop();
}

/// Test that shared disequality propagation works with TheoryCombiner::auf_lia (#5228).
#[test]
fn test_auflia_shared_disequality_propagation_5228() {
    let mut terms = setup_term_store();
    let zero = terms.mk_int(BigInt::from(0));
    let five = terms.mk_int(BigInt::from(5));

    let g_0 = terms.mk_app(Symbol::named("g"), vec![zero], Sort::Int);
    let ge_g0_5 = terms.mk_app(Symbol::named(">="), vec![g_0, five], Sort::Bool);
    let le_g0_5 = terms.mk_app(Symbol::named("<="), vec![g_0, five], Sort::Bool);
    let eq_g0_5 = terms.mk_app(Symbol::named("="), vec![g_0, five], Sort::Bool);

    let mut solver = TheoryCombiner::auf_lia(&terms);

    solver.assert_literal(ge_g0_5, true);
    solver.assert_literal(le_g0_5, true);
    solver.assert_literal(eq_g0_5, false);

    let result = solver.check();
    assert!(
        !matches!(result, TheoryResult::Sat),
        "Expected non-Sat for UNSAT formula with disequality propagation (#5228), got {result:?}"
    );
}
