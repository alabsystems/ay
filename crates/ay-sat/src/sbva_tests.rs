// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::clause_arena::ClauseArena;
use crate::literal::{Literal, Variable};
use crate::occ_list::OccList;
use crate::solver::lifecycle::VarState;

fn pos(var: u32) -> Literal {
    Literal::positive(Variable(var))
}

/// Build a test clause database and occurrence list from clause sets.
fn build_test_db(num_vars: usize, clauses: &[Vec<Literal>]) -> (ClauseArena, OccList) {
    let mut arena = ClauseArena::new();
    let mut occ = OccList::new(num_vars);
    for clause in clauses {
        let ci = arena.add(clause, false);
        occ.add_clause(ci, clause);
    }
    (arena, occ)
}

#[test]
fn test_sbva_basic_group_detection() {
    // 3 clauses sharing {b, c} as common subset besides pivot a:
    // {a, b, c, d}  => shared={b,c}, tail={d}
    // {a, b, c, e}  => shared={b,c}, tail={e}
    // {a, b, c, f}  => shared={b,c}, tail={f}
    let a = pos(0);
    let b = pos(1);
    let c = pos(2);
    let d = pos(3);
    let e = pos(4);
    let f = pos(5);

    let num_vars = 10;
    let clauses = vec![vec![a, b, c, d], vec![a, b, c, e], vec![a, b, c, f]];

    let (arena, occ) = build_test_db(num_vars, &clauses);
    let vals = vec![0i8; num_vars * 2];
    let var_states = vec![VarState::Active; num_vars];
    let config = SbvaConfig {
        next_var_id: num_vars,
        effort_limit: 100_000,
    };

    let mut engine = Sbva::new(num_vars);
    let result = engine.run(&arena, &occ, &vals, &var_states, &config);

    assert!(
        result.groups_applied >= 1,
        "SBVA should find at least one compressible group, got {}",
        result.groups_applied
    );
    assert!(
        result.extension_vars_needed >= 1,
        "SBVA should introduce extension variables"
    );
    assert!(
        !result.to_delete.is_empty(),
        "SBVA should delete original clauses"
    );
    assert!(
        !result.new_clauses.is_empty(),
        "SBVA should create new clauses"
    );
}

#[test]
fn test_sbva_no_group_when_shared_too_small() {
    // 3 clauses with only 1 shared literal besides pivot.
    // shared={b} only, which is < MIN_SHARED_SIZE=2.
    let a = pos(0);
    let b = pos(1);
    let c = pos(2);
    let d = pos(3);
    let e = pos(4);

    let num_vars = 8;
    let clauses = vec![vec![a, b, c], vec![a, b, d], vec![a, b, e]];

    let (arena, occ) = build_test_db(num_vars, &clauses);
    let vals = vec![0i8; num_vars * 2];
    let var_states = vec![VarState::Active; num_vars];
    let config = SbvaConfig {
        next_var_id: num_vars,
        effort_limit: 100_000,
    };

    let mut engine = Sbva::new(num_vars);
    let result = engine.run(&arena, &occ, &vals, &var_states, &config);

    assert_eq!(
        result.groups_applied, 0,
        "SBVA should not apply when shared subset is too small or not profitable"
    );
}

#[test]
fn test_sbva_literal_savings() {
    // 4 clauses sharing {b,c,d} with different tails:
    // {a, b, c, d, e}
    // {a, b, c, d, f}
    // {a, b, c, d, g}
    // {a, b, c, d, h}
    //
    // Original: 4 * 5 = 20 literals
    // New: 1 def (5 lits: x,a,b,c,d) + 4 tails (2 lits each: ¬x,tail) = 13
    // Savings: 7 literals
    let num_vars = 12;
    let clauses = vec![
        vec![pos(0), pos(1), pos(2), pos(3), pos(4)],
        vec![pos(0), pos(1), pos(2), pos(3), pos(5)],
        vec![pos(0), pos(1), pos(2), pos(3), pos(6)],
        vec![pos(0), pos(1), pos(2), pos(3), pos(7)],
    ];

    let (arena, occ) = build_test_db(num_vars, &clauses);
    let vals = vec![0i8; num_vars * 2];
    let var_states = vec![VarState::Active; num_vars];
    let config = SbvaConfig {
        next_var_id: num_vars,
        effort_limit: 100_000,
    };

    let mut engine = Sbva::new(num_vars);
    let result = engine.run(&arena, &occ, &vals, &var_states, &config);

    assert!(
        result.groups_applied >= 1,
        "SBVA should compress 4 clauses sharing large common subset"
    );

    for app in &result.applications {
        assert!(
            app.definition_clause.len() >= 3,
            "definition clause too short: {:?}",
            app.definition_clause
        );
        assert_eq!(
            app.blocked_clause.len(),
            app.shared_subset.len() + 1,
            "blocked clause length mismatch"
        );
        for tail in &app.tail_clauses {
            assert!(tail.len() >= 2, "tail clause too short");
        }
    }
}

#[test]
fn test_sbva_effort_limit_respected() {
    let num_vars = 20;
    let a = pos(0);
    let b = pos(1);
    let c = pos(2);
    let mut clauses = Vec::new();
    for v in 3..15u32 {
        clauses.push(vec![a, b, c, pos(v)]);
    }

    let (arena, occ) = build_test_db(num_vars, &clauses);
    let vals = vec![0i8; num_vars * 2];
    let var_states = vec![VarState::Active; num_vars];
    let config = SbvaConfig {
        next_var_id: num_vars,
        effort_limit: 5,
    };

    let mut engine = Sbva::new(num_vars);
    let result = engine.run(&arena, &occ, &vals, &var_states, &config);

    assert!(
        !result.completed,
        "SBVA should report incomplete when effort limit is hit"
    );
}

#[test]
fn test_sbva_proof_structure() {
    let num_vars = 10;
    let clauses = vec![
        vec![pos(0), pos(1), pos(2), pos(3)],
        vec![pos(0), pos(1), pos(2), pos(4)],
        vec![pos(0), pos(1), pos(2), pos(5)],
    ];

    let (arena, occ) = build_test_db(num_vars, &clauses);
    let vals = vec![0i8; num_vars * 2];
    let var_states = vec![VarState::Active; num_vars];
    let config = SbvaConfig {
        next_var_id: num_vars,
        effort_limit: 100_000,
    };

    let mut engine = Sbva::new(num_vars);
    let result = engine.run(&arena, &occ, &vals, &var_states, &config);

    for app in &result.applications {
        let fresh_pos = Literal::positive(app.fresh_var);
        let fresh_neg = Literal::negative(app.fresh_var);

        assert_eq!(
            app.definition_clause[0], fresh_pos,
            "definition clause should start with fresh positive literal"
        );
        assert_eq!(
            app.blocked_clause[0], fresh_neg,
            "blocked clause should start with fresh negative literal"
        );
        for tail in &app.tail_clauses {
            assert_eq!(
                tail[0], fresh_neg,
                "tail clause should start with fresh negative literal"
            );
        }
        // Blocked clause: negations of shared subset.
        for i in 1..app.blocked_clause.len() {
            let negated_shared = app.blocked_clause[i];
            assert!(
                app.shared_subset
                    .iter()
                    .any(|&s| s.negated() == negated_shared),
                "blocked clause literal {} should be negation of a shared literal, shared={:?}",
                negated_shared.0,
                app.shared_subset
            );
        }
    }
}

#[test]
fn test_sbva_empty_result_on_no_eligible() {
    // Only binary clauses -- too short for SBVA (need >= 3 literals).
    let num_vars = 6;
    let clauses = vec![
        vec![pos(0), pos(1)],
        vec![pos(0), pos(2)],
        vec![pos(0), pos(3)],
    ];

    let (arena, occ) = build_test_db(num_vars, &clauses);
    let vals = vec![0i8; num_vars * 2];
    let var_states = vec![VarState::Active; num_vars];
    let config = SbvaConfig {
        next_var_id: num_vars,
        effort_limit: 100_000,
    };

    let mut engine = Sbva::new(num_vars);
    let result = engine.run(&arena, &occ, &vals, &var_states, &config);

    assert_eq!(result.groups_applied, 0);
    assert!(result.new_clauses.is_empty());
    assert!(result.to_delete.is_empty());
}

#[test]
fn test_sbva_deleted_clauses_not_reused() {
    // Multiple groups possible: ensure deleted clauses from first group
    // are not reused in second group.
    let num_vars = 16;
    // Group 1: pivot=a(0), shared={b(1),c(2)}, tails={d(3),e(4),f(5)}
    // Group 2: pivot=g(6), shared={h(7),i(8)}, tails={j(9),k(10),l(11)}
    let clauses = vec![
        // Group 1
        vec![pos(0), pos(1), pos(2), pos(3)],
        vec![pos(0), pos(1), pos(2), pos(4)],
        vec![pos(0), pos(1), pos(2), pos(5)],
        // Group 2
        vec![pos(6), pos(7), pos(8), pos(9)],
        vec![pos(6), pos(7), pos(8), pos(10)],
        vec![pos(6), pos(7), pos(8), pos(11)],
    ];

    let (arena, occ) = build_test_db(num_vars, &clauses);
    let vals = vec![0i8; num_vars * 2];
    let var_states = vec![VarState::Active; num_vars];
    let config = SbvaConfig {
        next_var_id: num_vars,
        effort_limit: 100_000,
    };

    let mut engine = Sbva::new(num_vars);
    let result = engine.run(&arena, &occ, &vals, &var_states, &config);

    // Both groups should be detected and applied independently.
    assert!(
        result.groups_applied >= 2,
        "Should detect 2 independent groups, got {}",
        result.groups_applied
    );
    assert_eq!(
        result.to_delete.len(),
        6,
        "Should delete all 6 original clauses"
    );
}
