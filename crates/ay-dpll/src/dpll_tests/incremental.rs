// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Gap 9: DpllT push/pop incremental solving tests.

use super::*;

/// Test basic push/pop scope depth tracking
#[test]
fn test_dpllt_push_pop_scope_depth() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(3, theory);

    assert_eq!(dpll.scope_depth(), 0, "Initial scope depth should be 0");

    dpll.push();
    assert_eq!(dpll.scope_depth(), 1, "After push, scope depth should be 1");

    dpll.push();
    assert_eq!(
        dpll.scope_depth(),
        2,
        "After second push, scope depth should be 2"
    );

    let ok = dpll.pop();
    assert!(ok, "Pop should succeed");
    assert_eq!(dpll.scope_depth(), 1, "After pop, scope depth should be 1");

    let ok = dpll.pop();
    assert!(ok, "Pop should succeed");
    assert_eq!(
        dpll.scope_depth(),
        0,
        "After second pop, scope depth should be 0"
    );

    let ok = dpll.pop();
    assert!(!ok, "Pop on empty should return false");
    assert_eq!(dpll.scope_depth(), 0, "Scope depth should remain 0");
}

/// Test that clauses added after push are disabled after pop
#[test]
fn test_dpllt_push_pop_clause_scoping() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(2, theory);

    // Add a base clause that makes formula SAT: (x ∨ y)
    dpll.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);

    // Solve - should be SAT
    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Sat(_)));

    // Push and add a conflicting clause
    dpll.push();

    // Add ¬x and ¬y unit clauses - combined with (x ∨ y), this is UNSAT
    dpll.add_clause(vec![Literal::negative(Variable::new(0))]);
    dpll.add_clause(vec![Literal::negative(Variable::new(1))]);

    // Should now be UNSAT
    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Unsat(_)));

    // Pop - the ¬x and ¬y clauses should be disabled
    let ok = dpll.pop();
    assert!(ok);

    // Should be SAT again (only base clause (x ∨ y) is active)
    let result = dpll.solve().unwrap();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "After pop, formula should be SAT again"
    );
}

/// Test incremental solving with multiple push/pop cycles
#[test]
fn test_dpllt_incremental_multiple_cycles() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(3, theory);

    // Base clause: (x ∨ y ∨ z)
    dpll.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]);

    // First cycle: force x=false, y=false - only z can be true
    dpll.push();
    dpll.add_clause(vec![Literal::negative(Variable::new(0))]); // ¬x
    dpll.add_clause(vec![Literal::negative(Variable::new(1))]); // ¬y

    let result = dpll.solve().unwrap();
    match result {
        SatResult::Sat(model) => {
            // z must be true
            assert!(model.get(2).copied().unwrap_or(false), "z should be true");
        }
        _ => panic!("Should be SAT with z=true"),
    }

    dpll.pop();

    // Second cycle: force x=false, z=false - only y can be true
    dpll.push();
    dpll.add_clause(vec![Literal::negative(Variable::new(0))]); // ¬x
    dpll.add_clause(vec![Literal::negative(Variable::new(2))]); // ¬z

    let result = dpll.solve().unwrap();
    match result {
        SatResult::Sat(model) => {
            // y must be true
            assert!(model.get(1).copied().unwrap_or(false), "y should be true");
        }
        _ => panic!("Should be SAT with y=true"),
    }

    dpll.pop();

    // After all pops, should be SAT with any of x, y, z
    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Sat(_)));
}

/// Test nested push/pop scopes
#[test]
fn test_dpllt_nested_push_pop() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(3, theory);

    // Base: (x ∨ y ∨ z)
    dpll.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
        Literal::positive(Variable::new(2)),
    ]);

    // Level 1: add ¬x
    dpll.push();
    dpll.add_clause(vec![Literal::negative(Variable::new(0))]);
    assert_eq!(dpll.scope_depth(), 1);

    // Level 2: add ¬y
    dpll.push();
    dpll.add_clause(vec![Literal::negative(Variable::new(1))]);
    assert_eq!(dpll.scope_depth(), 2);

    // At level 2: only z can be true
    let result = dpll.solve().unwrap();
    match result {
        SatResult::Sat(model) => {
            assert!(!model.first().copied().unwrap_or(true), "x should be false");
            assert!(!model.get(1).copied().unwrap_or(true), "y should be false");
            assert!(model.get(2).copied().unwrap_or(false), "z should be true");
        }
        _ => panic!("Should be SAT"),
    }

    // Pop level 2 - ¬y is removed
    dpll.pop();
    assert_eq!(dpll.scope_depth(), 1);

    // At level 1: x is false, y or z can be true
    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Sat(_)));

    // Pop level 1 - ¬x is removed
    dpll.pop();
    assert_eq!(dpll.scope_depth(), 0);

    // At base level: any of x, y, z can be true
    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Sat(_)));
}

/// Test that sync_theory tracks assertion count and skips identical models (#2138).
#[test]
fn test_sync_theory_tracks_assertion_count() {
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::Arc;

    /// A theory solver that counts `assert_literal` calls via shared atomic.
    #[derive(Clone)]
    struct CountingTheory {
        count: Arc<AtomicU64>,
    }
    impl TheorySolver for CountingTheory {
        fn assert_literal(&mut self, _term: TermId, _value: bool) {
            self.count.fetch_add(1, Ordering::Relaxed);
        }
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

    let count = Arc::new(AtomicU64::new(0));
    let theory = CountingTheory {
        count: count.clone(),
    };
    let mut dpll = DpllT::new(4, theory);

    // Register 2 theory atoms: terms 10,11 mapped to vars 0,1.
    let t0 = TermId::new(10);
    let t1 = TermId::new(11);
    dpll.register_theory_atom(t0, 0);
    dpll.register_theory_atom(t1, 1);

    // Reset counter after internalize_atom calls from register_theory_atom.
    count.store(0, Ordering::Relaxed);

    // First sync: should assert both atoms.
    let model = vec![true, false, true, false];
    dpll.sync_theory(&model);
    assert_eq!(
        count.load(Ordering::Relaxed),
        2,
        "first sync asserts 2 atoms"
    );
    assert_eq!(dpll.sync_atoms_asserted(), 2);
    assert_eq!(dpll.sync_skipped_identical(), 0);

    // Second sync with identical theory atom values (vars 0,1 unchanged, var 2 changes).
    let model2 = vec![true, false, false, true];
    dpll.sync_theory(&model2);
    // Theory atoms at vars 0,1 are the same, so this should be skipped.
    assert_eq!(
        count.load(Ordering::Relaxed),
        2,
        "identical model skips re-assertion"
    );
    assert_eq!(dpll.sync_skipped_identical(), 1);

    // Third sync with changed theory atom value.
    let model3 = vec![false, false, false, true];
    dpll.sync_theory(&model3);
    // Var 0 changed from true to false, so full re-assertion happens.
    assert_eq!(count.load(Ordering::Relaxed), 4, "changed model re-asserts");
    assert_eq!(dpll.sync_atoms_asserted(), 4);
    assert_eq!(dpll.sync_skipped_identical(), 1);
    // Delta stats: 1 atom changed (var 0: true->false), 1 unchanged (var 1: false->false).
    assert_eq!(
        dpll.sync_delta_changed(),
        1,
        "one atom changed in third sync"
    );
    assert_eq!(
        dpll.sync_delta_unchanged(),
        1,
        "one atom unchanged in third sync"
    );

    // Clean up: exit model scope.
    dpll.exit_model_scope_if_active();
}

/// Test that sync_theory delta statistics track changed vs unchanged atoms (#2138).
#[test]
fn test_sync_theory_delta_statistics() {
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::Arc;

    #[derive(Clone)]
    struct CountingTheory {
        count: Arc<AtomicU64>,
    }
    impl TheorySolver for CountingTheory {
        fn assert_literal(&mut self, _term: TermId, _value: bool) {
            self.count.fetch_add(1, Ordering::Relaxed);
        }
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

    let count = Arc::new(AtomicU64::new(0));
    let theory = CountingTheory {
        count: count.clone(),
    };
    let mut dpll = DpllT::new(8, theory);

    // Register 4 theory atoms: terms 10..13 mapped to vars 0..3.
    for i in 0u32..4 {
        dpll.register_theory_atom(TermId::new(10 + i), i);
    }
    count.store(0, Ordering::Relaxed);

    // First sync: no delta stats (no previous model).
    let model1 = vec![true, false, true, false, false, false, false, false];
    dpll.sync_theory(&model1);
    assert_eq!(dpll.sync_delta_changed(), 0, "no delta on first sync");
    assert_eq!(dpll.sync_delta_unchanged(), 0, "no delta on first sync");
    assert_eq!(dpll.sync_atoms_asserted(), 4);

    // Second sync: change 2 atoms (vars 0,2), keep 2 unchanged (vars 1,3).
    let model2 = vec![false, false, false, false, false, false, false, false];
    dpll.sync_theory(&model2);
    assert_eq!(dpll.sync_delta_changed(), 2, "2 atoms changed");
    assert_eq!(dpll.sync_delta_unchanged(), 2, "2 atoms unchanged");
    assert_eq!(dpll.sync_atoms_asserted(), 8);

    // Third sync: identical to model2 -> skipped entirely.
    let model3 = vec![false, false, false, false, true, true, true, true];
    dpll.sync_theory(&model3);
    assert_eq!(dpll.sync_skipped_identical(), 1, "identical model skipped");
    // Delta stats unchanged since skip bypasses the delta tracking.
    assert_eq!(dpll.sync_delta_changed(), 2);
    assert_eq!(dpll.sync_delta_unchanged(), 2);

    dpll.exit_model_scope_if_active();
}

/// Test that pop on empty scope returns false and is safe
#[test]
fn test_dpllt_pop_empty_safe() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(2, theory);

    // Pop without any push should be safe and return false
    assert!(!dpll.pop());
    assert!(!dpll.pop());
    assert_eq!(dpll.scope_depth(), 0);

    // Solver should still work
    dpll.add_clause(vec![Literal::positive(Variable::new(0))]);
    let result = dpll.solve().unwrap();
    assert!(matches!(result, SatResult::Sat(_)));
}
