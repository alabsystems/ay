// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// =======================================================================
// Tests for ExtPropagateResult - #1656
// =======================================================================

#[test]
fn ext_propagate_result_none_is_empty() {
    let result = ExtPropagateResult::none();
    assert!(result.clauses.is_empty());
    assert!(result.conflict.is_none());
}

#[test]
fn ext_propagate_result_clause_contains_single_clause() {
    let lit_a = Literal::positive(Variable(1));
    let lit_b = Literal::negative(Variable(2));
    let clause = vec![lit_a, lit_b];

    let result = ExtPropagateResult::clause(clause.clone());
    assert_eq!(result.clauses.len(), 1);
    assert_eq!(result.clauses[0], clause);
    assert!(result.conflict.is_none());
}

#[test]
fn ext_propagate_result_clauses_contains_multiple_clauses() {
    let lit_a = Literal::positive(Variable(1));
    let lit_b = Literal::negative(Variable(2));
    let clause1 = vec![lit_a];
    let clause2 = vec![lit_b];

    let result = ExtPropagateResult::clauses(vec![clause1.clone(), clause2.clone()]);
    assert_eq!(result.clauses.len(), 2);
    assert_eq!(result.clauses[0], clause1);
    assert_eq!(result.clauses[1], clause2);
    assert!(result.conflict.is_none());
}

#[test]
fn ext_propagate_result_conflict_sets_conflict_clause() {
    let lit_a = Literal::positive(Variable(1));
    let lit_b = Literal::negative(Variable(2));
    let conflict_clause = vec![lit_a, lit_b];

    let result = ExtPropagateResult::conflict(conflict_clause.clone());
    assert!(result.clauses.is_empty());
    assert_eq!(result.conflict, Some(conflict_clause));
}

// =======================================================================
// Tests for SolverContext default methods - #1656
// =======================================================================

#[test]
fn solver_context_lit_value_propagates_variable_value() {
    struct ContextWithValues;
    impl SolverContext for ContextWithValues {
        fn value(&self, var: Variable) -> Option<bool> {
            // Variable(0) is true, Variable(1) is false
            match var.index() {
                0 => Some(true),
                1 => Some(false),
                _ => None,
            }
        }
        fn decision_level(&self) -> u32 {
            0
        }
        fn var_level(&self, _var: Variable) -> Option<u32> {
            None
        }
        fn trail(&self) -> &[Literal] {
            &[]
        }
    }

    let ctx = ContextWithValues;

    // Positive literal of true variable (index 0) should be true
    let lit_pos_true = Literal::positive(Variable(0));
    assert_eq!(ctx.lit_value(lit_pos_true), Some(true));

    // Negative literal of true variable (index 0) should be false
    let lit_neg_true = Literal::negative(Variable(0));
    assert_eq!(ctx.lit_value(lit_neg_true), Some(false));

    // Positive literal of false variable (index 1) should be false
    let lit_pos_false = Literal::positive(Variable(1));
    assert_eq!(ctx.lit_value(lit_pos_false), Some(false));

    // Negative literal of false variable (index 1) should be true
    let lit_neg_false = Literal::negative(Variable(1));
    assert_eq!(ctx.lit_value(lit_neg_false), Some(true));

    // Unassigned variable (index 100) returns None
    let lit_unassigned = Literal::positive(Variable(100));
    assert_eq!(ctx.lit_value(lit_unassigned), None);
}

#[test]
fn solver_context_new_assignments_returns_correct_slice() {
    struct ContextWithTrail {
        trail: Vec<Literal>,
    }
    impl SolverContext for ContextWithTrail {
        fn value(&self, _var: Variable) -> Option<bool> {
            None
        }
        fn decision_level(&self) -> u32 {
            0
        }
        fn var_level(&self, _var: Variable) -> Option<u32> {
            None
        }
        fn trail(&self) -> &[Literal] {
            &self.trail
        }
    }

    let trail = vec![
        Literal::positive(Variable(1)),
        Literal::negative(Variable(2)),
        Literal::positive(Variable(3)),
    ];
    let ctx = ContextWithTrail { trail };

    // From position 0: all assignments
    assert_eq!(ctx.new_assignments(0).len(), 3);

    // From position 1: last 2 assignments
    assert_eq!(ctx.new_assignments(1).len(), 2);

    // From position 3: empty (caught up)
    assert_eq!(ctx.new_assignments(3).len(), 0);

    // From position beyond trail: empty
    assert_eq!(ctx.new_assignments(10).len(), 0);
}

// =======================================================================
// Tests for SolverContext stats and activity methods - #8425, #8420
// =======================================================================

#[test]
fn solver_context_defaults_return_zero() {
    struct MinimalContext;
    impl SolverContext for MinimalContext {
        fn value(&self, _var: Variable) -> Option<bool> {
            None
        }
        fn decision_level(&self) -> u32 {
            0
        }
        fn var_level(&self, _var: Variable) -> Option<u32> {
            None
        }
        fn trail(&self) -> &[Literal] {
            &[]
        }
    }

    let ctx = MinimalContext;
    assert_eq!(ctx.conflicts(), 0);
    assert_eq!(ctx.decisions(), 0);
    assert_eq!(ctx.restarts(), 0);
    assert_eq!(ctx.propagations(), 0);
    assert_eq!(ctx.activity(Variable(0)), 0.0);
    assert_eq!(ctx.activity(Variable(42)), 0.0);
}

#[test]
fn solver_context_activity_for_solver_uses_bounded_solver_api() {
    let mut solver = crate::Solver::new(2);
    let cold = Variable::new(0);
    let hot = Variable::new(1);
    let out_of_range = Variable::new(99);

    assert_eq!(SolverContext::activity(&solver, hot), 0.0);

    solver.bump_variable_activity(hot);

    let direct = solver.activity(hot);
    let through_context = SolverContext::activity(&solver, hot);
    assert_eq!(through_context, direct);
    assert!(through_context > SolverContext::activity(&solver, cold));

    assert_eq!(solver.activity(out_of_range), 0.0);
    assert_eq!(SolverContext::activity(&solver, out_of_range), 0.0);
}
