// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::term::TermStore;
use ay_core::{Sort, Symbol, TheoryResult, TheorySolver};
use ay_dt::DtSolver;

#[test]
fn test_disequality_conflict_from_transitive_equalities() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);

    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);

    let mut solver = DtSolver::new(&terms);
    solver.assert_literal(eq_ab, true);
    solver.assert_literal(eq_bc, true);
    solver.assert_literal(eq_ac, false);

    let result = solver.check();
    assert!(matches!(result, TheoryResult::Unsat(_)));
}

#[test]
fn test_disequality_no_conflict_when_not_equal() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);

    let eq_ab = terms.mk_eq(a, b);

    let mut solver = DtSolver::new(&terms);
    solver.assert_literal(eq_ab, false);

    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));
}

/// Regression test for #3657: tester_results must be restored on pop().
/// After push -> assert is-Cons(x) -> pop, the tester result for x should
/// not persist. This exercises the scope-based tester undo.
#[test]
fn test_tester_results_restored_on_pop() {
    let mut terms = TermStore::new();
    let list_sort = Sort::Uninterpreted("List".to_string());
    let x = terms.mk_var("x", list_sort);

    // Create all terms before solver (solver borrows terms immutably)
    let is_cons_x = terms.mk_app(Symbol::Named("is-Cons".to_string()), vec![x], Sort::Bool);
    let is_nil_x = terms.mk_app(Symbol::Named("is-Nil".to_string()), vec![x], Sort::Bool);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("List", &["Cons".to_string(), "Nil".to_string()]);

    // Scope 0: push, assert is-Cons(x)=true, check, pop
    solver.push();
    solver.assert_literal(is_cons_x, true);
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));
    solver.pop();

    // After pop, tester_results for x should be cleared.
    // Scope 1: assert is-Nil(x)=true -- must not clash with stale Cons.
    solver.push();
    solver.assert_literal(is_nil_x, true);
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));
    solver.pop();
}

/// Regression test for #3656: union-find must be restored on pop().
///
/// After push -> assert (= a b) -> pop, terms a and b should no longer be
/// in the same equivalence class. Without the fix, union() merges persist
/// and a disequality (not (= a b)) incorrectly reports UNSAT.
#[test]
fn test_union_find_restored_on_pop_3656() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);

    let eq_ab = terms.mk_eq(a, b);

    let mut solver = DtSolver::new(&terms);

    // Push scope and merge a = b
    solver.push();
    solver.assert_literal(eq_ab, true);
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));
    solver.pop();

    // After pop, a and b should NOT be merged.
    // Assert a != b — must be SAT because the equality was popped.
    solver.assert_literal(eq_ab, false);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "After pop, a=b should be undone. a!=b alone is SAT, got {result:?}"
    );
}

/// Regression test for #3656: pre-push equalities must survive pop().
///
/// Assert (= a b) at base scope, then push, add (= b c), pop.
/// After pop, a and b should still be equal (base scope), but b and c
/// should no longer be equal (scoped).
#[test]
fn test_pre_push_equalities_survive_pop_3656() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);

    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);

    let mut solver = DtSolver::new(&terms);

    // Base scope: a = b
    solver.assert_literal(eq_ab, true);
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));

    // Push and add b = c
    solver.push();
    solver.assert_literal(eq_bc, true);
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));
    solver.pop();

    // After pop: a=b still holds, but b=c was undone.
    // Assert a != c — should be SAT because b=c was popped.
    solver.assert_literal(eq_ac, false);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "After pop, b=c should be undone. a=b holds but a!=c is SAT, got {result:?}"
    );
}

/// Verify that pop() doesn't over-undo: base-scope equalities must survive.
///
/// The weaker `test_pre_push_equalities_survive_pop_3656` test passes even if
/// pop() clears base-scope equalities (because a!=c is trivially SAT when no
/// equalities hold). This test explicitly checks that a=b still holds by
/// asserting a!=b after pop, which must be UNSAT.
#[test]
fn test_base_scope_equality_survives_pop() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);

    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);

    let mut solver = DtSolver::new(&terms);

    // Base scope: a = b
    solver.assert_literal(eq_ab, true);
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));

    // Push and add b = c
    solver.push();
    solver.assert_literal(eq_bc, true);
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));
    solver.pop();

    // After pop: a=b MUST still hold. Assert a!=b → must be UNSAT.
    // This catches an over-undo bug where pop() clears base-scope equalities.
    solver.assert_literal(eq_ab, false);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "Base-scope equality a=b must survive pop. a!=b should be UNSAT, got {result:?}"
    );
}

/// Document that tester-tester disjointness is NOT handled by DtSolver alone.
///
/// The DT solver's `check_tester_conflicts()` only checks testers against
/// constructors in the same equivalence class. Tester-tester disjointness
/// (e.g., is-Cons(x) AND is-Nil(x)) requires the executor's axiom (C)
/// scheme which converts `is-C(x)=true → x = C(sel_1(x),...)`, producing
/// constructor terms that then clash. This is tested at the integration
/// level in `qf_dt_integration.rs::test_dt_bv_constructor_clash_unsat`.
///
/// This test documents the DT solver's behavior: conflicting testers
/// without constructor terms in the equivalence class are NOT detected.
#[test]
fn test_tester_only_conflict_not_detected_by_solver_alone() {
    let mut terms = TermStore::new();
    let list_sort = Sort::Uninterpreted("List".to_string());
    let x = terms.mk_var("x", list_sort);

    let is_cons_x = terms.mk_app(Symbol::Named("is-Cons".to_string()), vec![x], Sort::Bool);
    let is_nil_x = terms.mk_app(Symbol::Named("is-Nil".to_string()), vec![x], Sort::Bool);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("List", &["Cons".to_string(), "Nil".to_string()]);

    solver.assert_literal(is_cons_x, true);
    solver.assert_literal(is_nil_x, true);

    // DtSolver alone returns Sat — tester disjointness requires executor axiom (C).
    // The integrated system (solve_dt, solve_dt_ufbv, etc.) handles this correctly
    // because axiom (C) generates constructor terms from tester truth values.
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "DtSolver alone does not detect tester-only conflicts (needs axiom C), got {result:?}"
    );
}
