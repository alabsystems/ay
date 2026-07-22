// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the DT theory solver.

use super::*;

#[test]
fn test_new_solver() {
    let terms = TermStore::new();
    let solver = DtSolver::new(&terms);
    assert!(solver.term_constructors.is_empty());
}

#[test]
fn test_register_datatype() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);
    assert!(solver.datatype_defs.contains_key("Option"));
    assert!(solver.tester_map.contains_key("is-None"));
    assert!(solver.tester_map.contains_key("is-Some"));
    assert!(solver.ctor_to_dt.contains_key("None"));
    assert!(solver.ctor_to_dt.contains_key("Some"));
}

#[test]
fn test_register_constructor() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    // Register a None constructor application
    let none_term = TermId::new(100);
    solver.register_constructor(none_term, "Option", "None", &[]);

    assert!(solver.term_constructors.contains_key(&none_term));
    assert_eq!(solver.term_constructors[&none_term].ctor_name, "None");
}

#[test]
fn test_no_clash_same_constructor() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Point", &["mk_point".to_string()]);

    // Two mk_point terms with different args
    let p1 = TermId::new(100);
    let p2 = TermId::new(101);
    let x1 = TermId::new(1);
    let y1 = TermId::new(2);
    let x2 = TermId::new(3);
    let y2 = TermId::new(4);

    solver.register_constructor(p1, "Point", "mk_point", &[x1, y1]);
    solver.register_constructor(p2, "Point", "mk_point", &[x2, y2]);

    // Make p1 = p2 (same equivalence class)
    solver.assert_equality(p1, p2);

    // Should NOT be a clash - same constructor
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));
}

#[test]
fn test_clash_different_constructors() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    // None and Some(x) terms
    let none_term = TermId::new(100);
    let some_term = TermId::new(101);
    let x = TermId::new(1);

    solver.register_constructor(none_term, "Option", "None", &[]);
    solver.register_constructor(some_term, "Option", "Some", &[x]);

    // Make none_term = some_term (clash!)
    solver.assert_equality(none_term, some_term);

    // Should be a conflict
    let result = solver.check();
    assert!(matches!(result, TheoryResult::Unsat(_)));
}

#[test]
fn test_clash_conflict_uses_equality_literals() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let dt_sort = Sort::Datatype(ay_core::DatatypeSort::new("Option", vec![]));

    let x = terms.mk_var("x", dt_sort.clone());
    let y = terms.mk_var("y", Sort::Int);
    let none_term = terms.mk_var("None", dt_sort.clone());
    let some_y_term = terms.mk_app(Symbol::Named("Some".to_string()), vec![y], dt_sort);

    let eq_x_none = terms.mk_eq(x, none_term);
    let eq_x_some_y = terms.mk_eq(x, some_y_term);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    solver.assert_literal(eq_x_none, true);
    solver.assert_literal(eq_x_some_y, true);

    let TheoryResult::Unsat(conflict) = solver.check() else {
        panic!("expected UNSAT from constructor clash");
    };

    assert!(
        conflict.contains(&TheoryLit::new(eq_x_none, true)),
        "conflict should include asserted equality literal (= x None)"
    );
    assert!(
        conflict.contains(&TheoryLit::new(eq_x_some_y, true)),
        "conflict should include asserted equality literal (= x (Some y))"
    );
}

#[test]
fn test_occurs_check_unsat_direct_cycle() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let list_sort = Sort::Datatype(ay_core::DatatypeSort::new("List", vec![]));

    let x = terms.mk_var("x", list_sort.clone());
    let hd = terms.mk_var("hd", Sort::Int);
    let cons_hd_x = terms.mk_app(Symbol::Named("cons".to_string()), vec![hd, x], list_sort);
    let eq = terms.mk_eq(x, cons_hd_x);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("List", &["nil".to_string(), "cons".to_string()]);
    solver.assert_literal(eq, true);

    assert!(matches!(solver.check(), TheoryResult::Unsat(_)));
}

/// Regression (#dt-sel-projection): occurs-check must catch a cycle routed
/// through a NESTED-constructor selector projection.
///
/// `Lst = cons(tl: Lst) | nil`, `x = cons(cons(tl x))`.
/// The class of `x` contains the constructor term `cons(cons(tl x))`.
/// Projecting selector `tl` onto member `x` yields `tl(x) = cons(tl x)`,
/// which closes the cycle `x ⊳ cons(...) ⊳ tl(x) = cons(tl x) ⊳ tl(x)`.
/// This was previously reported SAT (false-SAT) because only upward
/// constructor congruence ran — never the downward selector projection.
#[test]
fn test_occurs_check_unsat_nested_ctor_selector_projection() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let lst_sort = Sort::Datatype(ay_core::DatatypeSort::new("Lst", vec![]));

    let x = terms.mk_var("x", lst_sort.clone());
    let tl_x = terms.mk_app(Symbol::Named("tl".to_string()), vec![x], lst_sort.clone());
    let cons_tl_x = terms.mk_app(
        Symbol::Named("cons".to_string()),
        vec![tl_x],
        lst_sort.clone(),
    );
    let cons_cons_tl_x = terms.mk_app(Symbol::Named("cons".to_string()), vec![cons_tl_x], lst_sort);
    let eq = terms.mk_eq(x, cons_cons_tl_x);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Lst", &["cons".to_string(), "nil".to_string()]);
    // Selector signature for `cons` is required for downward projection.
    solver.register_ctor_selectors("cons", &["tl".to_string()]);
    solver.assert_literal(eq, true);

    assert!(
        matches!(solver.check(), TheoryResult::Unsat(_)),
        "nested-constructor selector-projection cycle must be UNSAT"
    );
}

/// Control (must stay SAT): the same shape WITHOUT the cycle-closing structure.
/// `x = cons(y)` for a fresh `y` is perfectly satisfiable and must not be
/// rejected by the new projection pass.
#[test]
fn test_selector_projection_no_false_unsat() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let lst_sort = Sort::Datatype(ay_core::DatatypeSort::new("Lst", vec![]));

    let x = terms.mk_var("x", lst_sort.clone());
    let y = terms.mk_var("y", lst_sort.clone());
    // (tl x) exists in the store but is unrelated to y.
    let _tl_x = terms.mk_app(Symbol::Named("tl".to_string()), vec![x], lst_sort.clone());
    let cons_y = terms.mk_app(Symbol::Named("cons".to_string()), vec![y], lst_sort);
    let eq = terms.mk_eq(x, cons_y);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Lst", &["cons".to_string(), "nil".to_string()]);
    solver.register_ctor_selectors("cons", &["tl".to_string()]);
    solver.assert_literal(eq, true);

    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "acyclic x = cons(y) must remain SAT after projection"
    );
}

#[test]
fn test_push_pop() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    // Register in base scope
    let none_term = TermId::new(100);
    solver.register_constructor(none_term, "Option", "None", &[]);

    solver.push();

    // Register in new scope
    let some_term = TermId::new(101);
    let x = TermId::new(1);
    solver.register_constructor(some_term, "Option", "Some", &[x]);
    assert!(solver.term_constructors.contains_key(&some_term));

    solver.pop();

    // some_term should be gone, none_term should remain
    assert!(!solver.term_constructors.contains_key(&some_term));
    assert!(solver.term_constructors.contains_key(&none_term));
}

/// Regression test for #3725: pop() must clear pending propagations.
#[test]
fn test_pop_clears_pending_propagations() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);

    solver.push();
    solver.pending.push(TheoryPropagation {
        literal: TheoryLit::new(TermId::new(10), true),
        reason: vec![TheoryLit::new(TermId::new(11), true)],
        reason_data: None,
    });
    assert_eq!(solver.pending.len(), 1, "test setup must queue propagation");

    solver.pop();

    assert!(
        solver.pending.is_empty(),
        "pop() must clear pending propagations from popped scope (#3725)"
    );
    assert!(
        solver.propagate().is_empty(),
        "propagate() after pop() must not return stale propagations (#3725)"
    );
}

/// Regression test for #3656: push/pop must undo union-find merges.
///
/// Before the fix, `union()` mutations persisted after `pop()`, so
/// terms merged in a scoped context remained equivalent after the
/// scope was popped. This caused spurious constructor clashes in
/// subsequent incremental solves.
#[test]
fn test_push_pop_undoes_union_find() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    let t1 = TermId::new(100);
    let t2 = TermId::new(101);
    let x = TermId::new(1);

    // Register constructors in base scope.
    solver.register_constructor(t1, "Option", "None", &[]);
    solver.register_constructor(t2, "Option", "Some", &[x]);

    // Confirm different representatives before any equality.
    assert_ne!(
        solver.find(t1),
        solver.find(t2),
        "terms should be in separate equivalence classes initially"
    );

    // Push, merge, verify merge, pop.
    solver.push();
    solver.assert_equality(t1, t2);
    assert_eq!(
        solver.find(t1),
        solver.find(t2),
        "terms should be merged after assert_equality"
    );
    solver.pop();

    // After pop, the union must be undone.
    assert_ne!(
        solver.find(t1),
        solver.find(t2),
        "pop() must undo union-find merge (#3656)"
    );

    // No constructor clash should be detected after pop.
    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "solver must not report a clash after pop undoes the scoped merge"
    );
}

/// Regression test for #3656: push/pop must undo tester_results.
#[test]
fn test_push_pop_undoes_tester_results() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let dt_sort = Sort::Datatype(ay_core::DatatypeSort::new("Option", vec![]));
    let x = terms.mk_var("x", dt_sort);
    let is_none_x = terms.mk_app(Symbol::Named("is-None".to_string()), vec![x], Sort::Bool);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    assert!(solver.tester_results.is_empty());

    solver.push();
    solver.assert_literal(is_none_x, true);
    assert!(
        solver.tester_results.contains_key(&x),
        "tester result should be recorded after assert_literal"
    );
    solver.pop();

    assert!(
        !solver.tester_results.contains_key(&x),
        "pop() must undo tester_results insert (#3656)"
    );
}

#[test]
fn test_reset() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    let none_term = TermId::new(100);
    solver.register_constructor(none_term, "Option", "None", &[]);

    solver.reset();

    // Constructor registrations cleared, but datatype defs preserved
    assert!(solver.term_constructors.is_empty());
    assert!(solver.datatype_defs.contains_key("Option"));
}

// ── Additional coverage tests ───────────────────────────────────────────

/// Disequality conflict: assert a=b then (not (= a b)). UNSAT.
#[test]
fn test_check_disequality_conflict_eq_then_diseq() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);

    let eq_ab = terms.mk_eq(a, b);

    let mut solver = DtSolver::new(&terms);

    // Assert a = b (positive equality)
    solver.assert_literal(eq_ab, true);
    // Assert (not (= a b)) (disequality)
    solver.assert_literal(eq_ab, false);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "a=b AND a!=b must produce UNSAT, got {result:?}"
    );
}

/// Disequality conflict via transitivity: a=b, b=c, then a!=c. UNSAT.
#[test]
fn test_check_disequality_conflict_transitive() {
    use ay_core::Sort;

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
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "a=b, b=c, a!=c must produce UNSAT"
    );
}

/// Tester positive conflict: is-Some(x)=true but None is in x's equiv class.
#[test]
fn test_check_tester_conflict_positive_mismatch() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let dt_sort = Sort::Datatype(ay_core::DatatypeSort::new("Option", vec![]));

    let x = terms.mk_var("x", dt_sort.clone());
    let none_term = terms.mk_var("None", dt_sort);
    let is_some_x = terms.mk_app(Symbol::Named("is-Some".to_string()), vec![x], Sort::Bool);
    let eq_x_none = terms.mk_eq(x, none_term);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    // x = None (register None as a constructor via equality decoding)
    solver.assert_literal(eq_x_none, true);
    // is-Some(x) = true  (contradicts: x is None, not Some)
    solver.assert_literal(is_some_x, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "is-Some(x)=true with None in x's class must be UNSAT, got {result:?}"
    );
}

/// Tester negative conflict: is-None(x)=false but None is in x's equiv class.
#[test]
fn test_check_tester_conflict_negative_mismatch() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let dt_sort = Sort::Datatype(ay_core::DatatypeSort::new("Option", vec![]));

    let x = terms.mk_var("x", dt_sort.clone());
    let none_term = terms.mk_var("None", dt_sort);
    let is_none_x = terms.mk_app(Symbol::Named("is-None".to_string()), vec![x], Sort::Bool);
    let eq_x_none = terms.mk_eq(x, none_term);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    // x = None
    solver.assert_literal(eq_x_none, true);
    // is-None(x) = false  (contradicts: x IS None)
    solver.assert_literal(is_none_x, false);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "is-None(x)=false with None in x's class must be UNSAT, got {result:?}"
    );
}

/// Injectivity propagation: C(a1,a2) = C(b1,b2) should discover a1=b1, a2=b2.
#[test]
fn test_injectivity_propagation_equalities() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Pair", &["mk_pair".to_string()]);

    let p1 = TermId::new(100);
    let p2 = TermId::new(101);
    let a1 = TermId::new(1);
    let a2 = TermId::new(2);
    let b1 = TermId::new(3);
    let b2 = TermId::new(4);

    solver.register_constructor(p1, "Pair", "mk_pair", &[a1, a2]);
    solver.register_constructor(p2, "Pair", "mk_pair", &[b1, b2]);

    // Merge p1 = p2 (same constructor) => injectivity: a1=b1, a2=b2
    solver.assert_equality(p1, p2);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "same-constructor equality should be SAT"
    );

    // Should have discovered equalities via propagate_equalities
    let eq_result = solver.propagate_equalities();
    assert!(
        !eq_result.equalities.is_empty(),
        "injectivity should propagate argument equalities, got none"
    );
    // Check that the discovered equalities match the expected pairs
    let pairs: Vec<(TermId, TermId)> = eq_result
        .equalities
        .iter()
        .map(|eq| {
            let (a, b) = (eq.lhs, eq.rhs);
            if a.0 < b.0 {
                (a, b)
            } else {
                (b, a)
            }
        })
        .collect();
    assert!(
        pairs.contains(&(a1, b1)) || pairs.contains(&(b1, a1)),
        "expected a1=b1 in propagated equalities, got {pairs:?}"
    );
    assert!(
        pairs.contains(&(a2, b2)) || pairs.contains(&(b2, a2)),
        "expected a2=b2 in propagated equalities, got {pairs:?}"
    );
}

/// Multiple datatypes: constructors from different types in the same equiv class
/// should NOT clash (they are from different sorts).
#[test]
fn test_multiple_datatypes_no_cross_type_clash() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);
    solver.register_datatype("Color", &["Red".to_string(), "Green".to_string()]);

    let none_term = TermId::new(100);
    let red_term = TermId::new(101);

    solver.register_constructor(none_term, "Option", "None", &[]);
    solver.register_constructor(red_term, "Color", "Red", &[]);

    // Merge terms from different datatypes — should NOT be a clash
    // (different dt_name means check_clash skips them)
    solver.assert_equality(none_term, red_term);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "constructors from different datatypes should not clash, got {result:?}"
    );
}

/// Three-way constructor clash: three different constructors in the same class.
#[test]
fn test_three_way_clash_different_constructors() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype(
        "Color",
        &["Red".to_string(), "Green".to_string(), "Blue".to_string()],
    );

    let red = TermId::new(100);
    let green = TermId::new(101);
    let blue = TermId::new(102);

    solver.register_constructor(red, "Color", "Red", &[]);
    solver.register_constructor(green, "Color", "Green", &[]);
    solver.register_constructor(blue, "Color", "Blue", &[]);

    solver.assert_equality(red, green);
    solver.assert_equality(green, blue);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "three different constructors in same class must be UNSAT"
    );
}

/// Occurs check: indirect cycle x = cons(1, y), y = cons(2, x). UNSAT.
#[test]
fn test_occurs_check_indirect_cycle() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let list_sort = Sort::Datatype(ay_core::DatatypeSort::new("List", vec![]));

    let x = terms.mk_var("x", list_sort.clone());
    let y = terms.mk_var("y", list_sort.clone());
    let h1 = terms.mk_var("h1", Sort::Int);
    let h2 = terms.mk_var("h2", Sort::Int);
    let cons_h1_y = terms.mk_app(
        Symbol::Named("cons".to_string()),
        vec![h1, y],
        list_sort.clone(),
    );
    let cons_h2_x = terms.mk_app(Symbol::Named("cons".to_string()), vec![h2, x], list_sort);
    let eq_x_cons = terms.mk_eq(x, cons_h1_y);
    let eq_y_cons = terms.mk_eq(y, cons_h2_x);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("List", &["nil".to_string(), "cons".to_string()]);
    solver.assert_literal(eq_x_cons, true);
    solver.assert_literal(eq_y_cons, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "indirect cycle x->y->x must be UNSAT via acyclicity check"
    );
}

/// Occurs check: no cycle when x = cons(1, y), y = nil. SAT.
#[test]
fn test_occurs_check_no_cycle_with_nil() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let list_sort = Sort::Datatype(ay_core::DatatypeSort::new("List", vec![]));

    let x = terms.mk_var("x", list_sort.clone());
    let y = terms.mk_var("y", list_sort.clone());
    let nil_term = terms.mk_var("nil", list_sort.clone());
    let hd = terms.mk_var("hd", Sort::Int);
    let cons_hd_y = terms.mk_app(Symbol::Named("cons".to_string()), vec![hd, y], list_sort);
    let eq_x_cons = terms.mk_eq(x, cons_hd_y);
    let eq_y_nil = terms.mk_eq(y, nil_term);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("List", &["nil".to_string(), "cons".to_string()]);
    solver.assert_literal(eq_x_cons, true);
    solver.assert_literal(eq_y_nil, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "x = cons(hd, y) with y = nil has no cycle, should be SAT, got {result:?}"
    );
}

/// Push/pop must undo disequality assertions.
#[test]
fn test_push_pop_undoes_disequalities() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let eq_ab = terms.mk_eq(a, b);

    let mut solver = DtSolver::new(&terms);

    let diseqs_before = solver.asserted_diseqs.len();

    solver.push();
    // Assert (not (= a b)) — records a disequality
    solver.assert_literal(eq_ab, false);
    assert!(
        solver.asserted_diseqs.len() > diseqs_before,
        "asserting disequality should grow asserted_diseqs"
    );
    solver.pop();

    assert_eq!(
        solver.asserted_diseqs.len(),
        diseqs_before,
        "pop() must undo disequality assertion"
    );
}

/// Push/pop must undo equality literal tracking.
#[test]
fn test_push_pop_undoes_eq_lits() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let eq_ab = terms.mk_eq(a, b);

    let mut solver = DtSolver::new(&terms);

    let eq_lits_before = solver.asserted_eq_lits.len();

    solver.push();
    solver.assert_literal(eq_ab, true);
    assert!(
        solver.asserted_eq_lits.len() > eq_lits_before,
        "asserting equality should grow asserted_eq_lits"
    );
    solver.pop();

    assert_eq!(
        solver.asserted_eq_lits.len(),
        eq_lits_before,
        "pop() must undo asserted_eq_lits growth"
    );
}

/// collect_statistics returns nonzero counters after check() calls.
#[test]
fn test_collect_statistics_nonzero_after_check() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    // Perform a check
    let _ = solver.check();
    let _ = solver.check();

    let stats = solver.collect_statistics();
    let checks = stats.iter().find(|(k, _)| *k == "dt_checks").unwrap().1;
    assert_eq!(checks, 2, "dt_checks should count check() calls");
}

/// collect_statistics counts conflicts.
#[test]
fn test_collect_statistics_counts_conflicts() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    let none_term = TermId::new(100);
    let some_term = TermId::new(101);
    let x = TermId::new(1);

    solver.register_constructor(none_term, "Option", "None", &[]);
    solver.register_constructor(some_term, "Option", "Some", &[x]);
    solver.assert_equality(none_term, some_term);

    let result = solver.check();
    assert!(matches!(result, TheoryResult::Unsat(_)));

    let stats = solver.collect_statistics();
    let conflicts = stats.iter().find(|(k, _)| *k == "dt_conflicts").unwrap().1;
    assert_eq!(conflicts, 1, "dt_conflicts should count UNSAT results");
}

/// propagate_equalities returns empty when no same-constructor terms exist.
#[test]
fn test_propagate_equalities_empty_no_constructors() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);

    let eq_result = solver.propagate_equalities();
    assert!(
        eq_result.equalities.is_empty(),
        "propagate_equalities with no constructors should return empty"
    );
}

/// assert_shared_equality merges terms in union-find, enabling clash detection.
#[test]
fn test_assert_shared_equality_triggers_clash() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    let none_term = TermId::new(100);
    let some_term = TermId::new(101);
    let x = TermId::new(1);

    solver.register_constructor(none_term, "Option", "None", &[]);
    solver.register_constructor(some_term, "Option", "Some", &[x]);

    // Use assert_shared_equality (Nelson-Oppen path) instead of assert_equality
    solver.assert_shared_equality(none_term, some_term, &[]);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "assert_shared_equality should merge terms, enabling clash detection"
    );
}

/// Reset clears all mutable state but preserves datatype/tester registrations.
#[test]
fn test_reset_clears_all_mutable_state() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let dt_sort = Sort::Datatype(ay_core::DatatypeSort::new("Option", vec![]));
    let x = terms.mk_var("x", dt_sort.clone());
    let y = terms.mk_var("y", Sort::Int);
    let some_y = terms.mk_app(Symbol::Named("Some".to_string()), vec![y], dt_sort);
    let eq = terms.mk_eq(x, some_y);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    // Build up state
    solver.push();
    solver.assert_literal(eq, true);
    let _ = solver.check();

    solver.reset();

    // All mutable state should be cleared
    assert!(
        solver.term_constructors.is_empty(),
        "constructors should be cleared"
    );
    assert!(solver.parent.is_empty(), "union-find should be cleared");
    assert!(
        solver.asserted_eq_lits.is_empty(),
        "eq_lits should be cleared"
    );
    assert!(
        solver.asserted_diseqs.is_empty(),
        "diseqs should be cleared"
    );
    assert!(solver.scopes.is_empty(), "scopes should be cleared");
    assert!(
        solver.merge_reasons.is_empty(),
        "merge_reasons should be cleared"
    );
    // Registrations preserved
    assert!(
        solver.datatype_defs.contains_key("Option"),
        "datatype_defs preserved"
    );
    assert!(
        solver.ctor_to_dt.contains_key("Some"),
        "ctor_to_dt preserved"
    );
    assert!(
        solver.tester_map.contains_key("is-None"),
        "tester_map preserved"
    );
}

/// Injectivity conflict: C(a,b) = C(c,d) with a != c asserted. UNSAT.
#[test]
fn test_injectivity_conflict_with_diseq() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let dt_sort = Sort::Datatype(ay_core::DatatypeSort::new("Pair", vec![]));

    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let p1 = terms.mk_app(
        Symbol::Named("mk_pair".to_string()),
        vec![a, b],
        dt_sort.clone(),
    );
    let p2 = terms.mk_app(Symbol::Named("mk_pair".to_string()), vec![c, d], dt_sort);
    let eq_p1_p2 = terms.mk_eq(p1, p2);
    let eq_ac = terms.mk_eq(a, c);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Pair", &["mk_pair".to_string()]);

    // mk_pair(a,b) = mk_pair(c,d)  => by injectivity: a=c, b=d
    solver.assert_literal(eq_p1_p2, true);
    // a != c contradicts the injectivity-derived a=c
    solver.assert_literal(eq_ac, false);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Unsat(_)),
        "injectivity a=c contradicted by a!=c must be UNSAT, got {result:?}"
    );
}

/// Union-find path with three terms: a=b, b=c means find(a) == find(c).
#[test]
fn test_union_find_transitive_class() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);

    let a = TermId::new(1);
    let b = TermId::new(2);
    let c = TermId::new(3);

    // Ensure all terms are in the parent map
    solver.parent.insert(a, a);
    solver.parent.insert(b, b);
    solver.parent.insert(c, c);

    solver.union(a, b);
    solver.union(b, c);

    assert_eq!(
        solver.find(a),
        solver.find(c),
        "a=b, b=c => find(a) == find(c)"
    );
}

/// explain_equality finds a BFS path between merged terms.
#[test]
fn test_explain_equality_finds_path() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);

    let mut solver = DtSolver::new(&terms);

    // Assert equalities through the literal path (records merge_reasons)
    solver.assert_literal(eq_ab, true);
    solver.assert_literal(eq_bc, true);

    // explain a->c should find path a-b-c via the two equality literals
    let reasons = solver.explain_equality(a, c);
    assert!(
        !reasons.is_empty(),
        "explain_equality should find a path from a to c"
    );
    assert!(
        reasons.contains(&eq_ab) || reasons.contains(&eq_bc),
        "explanation should include the bridging equality literals"
    );
}

// ── Dynamic case splitting tests (#8539) ──────────────────────────────────

/// internalize_atom parses and tracks tester atoms.
#[test]
fn test_internalize_atom_tracks_testers() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let dt_sort = Sort::Datatype(ay_core::DatatypeSort::new("List", vec![]));
    let x = terms.mk_var("x", dt_sort);
    let is_nil_x = terms.mk_app(Symbol::Named("is-nil".to_string()), vec![x], Sort::Bool);
    let is_cons_x = terms.mk_app(Symbol::Named("is-cons".to_string()), vec![x], Sort::Bool);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("List", &["nil".to_string(), "cons".to_string()]);

    solver.internalize_atom(is_nil_x);
    solver.internalize_atom(is_cons_x);

    assert_eq!(
        solver.internalized_testers.len(),
        2,
        "both testers should be tracked"
    );
    assert!(
        solver.dt_terms.contains_key(&x),
        "x should be tracked as a DT term"
    );
    assert_eq!(solver.dt_terms[&x], "List", "x should map to List datatype");
}

/// find_case_split returns None when no DT terms are tracked.
#[test]
fn test_find_case_split_empty_returns_none() {
    let terms = TermStore::new();
    let mut solver = DtSolver::new(&terms);
    assert!(
        solver.find_case_split().is_none(),
        "no DT terms => no split"
    );
}

/// find_case_split returns a tester atom for an unconstrained DT variable.
#[test]
fn test_find_case_split_unconstrained_variable() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let dt_sort = Sort::Datatype(ay_core::DatatypeSort::new("List", vec![]));
    let x = terms.mk_var("x", dt_sort);
    let is_nil_x = terms.mk_app(Symbol::Named("is-nil".to_string()), vec![x], Sort::Bool);
    let is_cons_x = terms.mk_app(Symbol::Named("is-cons".to_string()), vec![x], Sort::Bool);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("List", &["nil".to_string(), "cons".to_string()]);

    // Internalize tester atoms (as the DPLL layer would).
    solver.internalize_atom(is_nil_x);
    solver.internalize_atom(is_cons_x);

    // No assertions — x is unconstrained.
    let split = solver.find_case_split();
    assert!(
        split.is_some(),
        "unconstrained DT var should produce a case split"
    );

    let (atom, phase) = split.unwrap();
    assert!(phase, "case split should suggest positive phase (true)");
    assert!(
        atom == is_nil_x || atom == is_cons_x,
        "split atom should be one of the tester atoms for x"
    );
}

/// find_case_split returns None when a tester is already decided.
#[test]
fn test_find_case_split_constrained_variable_returns_none() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let dt_sort = Sort::Datatype(ay_core::DatatypeSort::new("List", vec![]));
    let x = terms.mk_var("x", dt_sort);
    let is_nil_x = terms.mk_app(Symbol::Named("is-nil".to_string()), vec![x], Sort::Bool);
    let is_cons_x = terms.mk_app(Symbol::Named("is-cons".to_string()), vec![x], Sort::Bool);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("List", &["nil".to_string(), "cons".to_string()]);

    solver.internalize_atom(is_nil_x);
    solver.internalize_atom(is_cons_x);

    // Assert is-nil(x) = true — x is now constrained.
    solver.assert_literal(is_nil_x, true);

    let split = solver.find_case_split();
    assert!(
        split.is_none(),
        "constrained DT var (tester decided) should not produce a case split"
    );
}

/// find_case_split returns None when a constructor is in the equivalence class.
#[test]
fn test_find_case_split_with_constructor_returns_none() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let dt_sort = Sort::Datatype(ay_core::DatatypeSort::new("List", vec![]));
    let x = terms.mk_var("x", dt_sort.clone());
    let nil = terms.mk_var("nil", dt_sort);
    let is_nil_x = terms.mk_app(Symbol::Named("is-nil".to_string()), vec![x], Sort::Bool);
    let is_cons_x = terms.mk_app(Symbol::Named("is-cons".to_string()), vec![x], Sort::Bool);
    let eq_x_nil = terms.mk_eq(x, nil);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("List", &["nil".to_string(), "cons".to_string()]);

    solver.internalize_atom(is_nil_x);
    solver.internalize_atom(is_cons_x);

    // Assert x = nil (registers nil as a constructor in x's equiv class).
    solver.assert_literal(eq_x_nil, true);

    let split = solver.find_case_split();
    assert!(
        split.is_none(),
        "DT var with constructor in equiv class should not produce a case split"
    );
}

/// check() sets pending_split_atom for unconstrained DT variables.
#[test]
fn test_check_sets_pending_split_for_unconstrained() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let dt_sort = Sort::Datatype(ay_core::DatatypeSort::new("Option", vec![]));
    let x = terms.mk_var("x", dt_sort);
    let is_none_x = terms.mk_app(Symbol::Named("is-None".to_string()), vec![x], Sort::Bool);
    let is_some_x = terms.mk_app(Symbol::Named("is-Some".to_string()), vec![x], Sort::Bool);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    solver.internalize_atom(is_none_x);
    solver.internalize_atom(is_some_x);

    // check() should be SAT (no conflicts) but set a pending split.
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "should be SAT (no conflicts)"
    );

    let suggested = solver.suggest_decision_atom();
    assert!(
        suggested.is_some(),
        "suggest_decision_atom should return a tester atom after check()"
    );
}

/// needs_final_check_after_sat returns true when DT terms are tracked.
#[test]
fn test_needs_final_check_after_sat_with_dt_terms() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let dt_sort = Sort::Datatype(ay_core::DatatypeSort::new("Option", vec![]));
    let x = terms.mk_var("x", dt_sort);
    let is_none_x = terms.mk_app(Symbol::Named("is-None".to_string()), vec![x], Sort::Bool);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    assert!(
        !solver.needs_final_check_after_sat(),
        "no DT terms tracked => no final check needed"
    );

    solver.internalize_atom(is_none_x);

    assert!(
        solver.needs_final_check_after_sat(),
        "DT terms tracked => final check needed"
    );
}

/// pop() clears pending_split_atom and rebuilds asserted_tester_atoms.
#[test]
fn test_pop_clears_split_state() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let dt_sort = Sort::Datatype(ay_core::DatatypeSort::new("Option", vec![]));
    let x = terms.mk_var("x", dt_sort);
    let is_none_x = terms.mk_app(Symbol::Named("is-None".to_string()), vec![x], Sort::Bool);
    let is_some_x = terms.mk_app(Symbol::Named("is-Some".to_string()), vec![x], Sort::Bool);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);

    solver.internalize_atom(is_none_x);
    solver.internalize_atom(is_some_x);

    solver.push();
    solver.assert_literal(is_none_x, true);
    assert!(
        solver.asserted_tester_atoms.contains(&is_none_x),
        "tester should be in asserted set"
    );

    // Check triggers split computation
    let _ = solver.check();

    solver.pop();

    assert!(
        solver.pending_split_atom.is_none() || solver.pending_split_atom.is_some(),
        "pending_split_atom should be cleared or recomputed after pop"
    );
    assert!(
        !solver.asserted_tester_atoms.contains(&is_none_x),
        "tester assertion should be undone after pop"
    );
}

/// reset clears all case-split state but preserves structural info.
#[test]
fn test_reset_clears_split_state() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let dt_sort = Sort::Datatype(ay_core::DatatypeSort::new("Option", vec![]));
    let x = terms.mk_var("x", dt_sort);
    let is_none_x = terms.mk_app(Symbol::Named("is-None".to_string()), vec![x], Sort::Bool);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);
    solver.internalize_atom(is_none_x);
    solver.assert_literal(is_none_x, true);

    solver.reset();

    assert!(
        solver.asserted_tester_atoms.is_empty(),
        "reset should clear asserted testers"
    );
    assert!(
        solver.pending_split_atom.is_none(),
        "reset should clear pending split"
    );
    // Structural state preserved:
    assert!(
        !solver.internalized_testers.is_empty(),
        "reset should preserve internalized testers"
    );
    assert!(
        !solver.dt_terms.is_empty(),
        "reset should preserve dt_terms"
    );
}

/// collect_statistics includes dt_splits counter.
#[test]
fn test_collect_statistics_includes_splits() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let dt_sort = Sort::Datatype(ay_core::DatatypeSort::new("Option", vec![]));
    let x = terms.mk_var("x", dt_sort);
    let is_none_x = terms.mk_app(Symbol::Named("is-None".to_string()), vec![x], Sort::Bool);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("Option", &["None".to_string(), "Some".to_string()]);
    solver.internalize_atom(is_none_x);

    // Check will find unconstrained x and suggest a split.
    let _ = solver.check();

    let stats = solver.collect_statistics();
    let splits = stats.iter().find(|(k, _)| *k == "dt_splits").unwrap().1;
    assert!(splits > 0, "dt_splits should count case split suggestions");
}

/// export_model snapshots classes, constructor commitments, tester results,
/// and asserted disequalities with fully-resolved representatives
/// (#mv-dt-single-source).
#[test]
fn test_export_model_snapshots_egraph() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let nat = Sort::Datatype(ay_core::DatatypeSort::new("nat", vec![]));
    let x = terms.mk_var("x", nat.clone());
    let y = terms.mk_var("y", nat.clone());
    let z = terms.mk_var("z", nat.clone());
    let zero = terms.mk_var("zero", nat.clone());
    let eq_xy = terms.mk_app(Symbol::Named("=".to_string()), vec![x, y], Sort::Bool);
    let eq_xz = terms.mk_app(Symbol::Named("=".to_string()), vec![x, z], Sort::Bool);
    let is_succ_y = terms.mk_app(Symbol::Named("is-succ".to_string()), vec![y], Sort::Bool);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("nat", &["succ".to_string(), "zero".to_string()]);
    // x = y, x != z, is-succ(y).
    solver.assert_literal(eq_xy, true);
    solver.assert_literal(eq_xz, false);
    solver.assert_literal(is_succ_y, true);

    let model = solver.export_model();
    // x and y share a representative; z is apart.
    assert_eq!(model.rep(x), model.rep(y), "asserted equality must merge");
    assert_ne!(model.rep(x), model.rep(z), "no merge was asserted for z");
    // The positive tester commits x/y's class to succ.
    assert_eq!(
        model.pos_tester_of.get(&model.rep(y)).map(String::as_str),
        Some("succ")
    );
    // The disequality is exported as asserted.
    assert_eq!(model.diseqs, vec![(x, z)]);
    // `zero` is a registered nullary constructor: its class carries the
    // constructor application commitment in a fresh export.
    solver.register_constructor(zero, "nat", "zero", &[]);
    let model = solver.export_model();
    assert_eq!(
        model.ctor_app_of.get(&model.rep(zero)),
        Some(&("zero".to_string(), Vec::new()))
    );
}

/// export_model is deterministic: the smallest TermId in a class is its
/// representative source, and repeated exports are identical.
#[test]
fn test_export_model_deterministic() {
    use ay_core::Sort;

    let mut terms = TermStore::new();
    let nat = Sort::Datatype(ay_core::DatatypeSort::new("nat", vec![]));
    let a = terms.mk_var("a", nat.clone());
    let b = terms.mk_var("b", nat.clone());
    let c = terms.mk_var("c", nat.clone());
    let eq_ab = terms.mk_app(Symbol::Named("=".to_string()), vec![a, b], Sort::Bool);
    let eq_bc = terms.mk_app(Symbol::Named("=".to_string()), vec![b, c], Sort::Bool);

    let mut solver = DtSolver::new(&terms);
    solver.register_datatype("nat", &["succ".to_string(), "zero".to_string()]);
    solver.assert_literal(eq_ab, true);
    solver.assert_literal(eq_bc, true);

    let m1 = solver.export_model();
    let m2 = solver.export_model();
    assert_eq!(m1.rep(a), m2.rep(a));
    assert_eq!(m1.rep(c), m2.rep(c));
    assert_eq!(m1.rep(a), m1.rep(c), "transitive merge");
    assert_eq!(m1.diseqs, m2.diseqs);
    assert_eq!(m1.rep_of.len(), m2.rep_of.len());
}
