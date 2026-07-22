// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Test that minimize_learned_clause removes a truly redundant literal.
///
/// Constructs a scenario where literal L is implied by the reason chain of
/// other literals in the learned clause. After minimization, L should be removed.
#[test]
fn test_minimize_learned_clause_removes_redundant_literal() {
    // Create a formula where conflict analysis produces a learned clause with
    // a redundant literal. We set up the solver state manually:
    //
    // Variables: v0..v4
    // Level assignments:
    //   v0 @ level 1 (decision)
    //   v1 @ level 1 (propagated from clause C1: v0 => v1)
    //   v2 @ level 2 (decision)
    //   v3 @ level 2 (propagated from clause C2: v2 => v3)
    //
    // Learned clause before minimization: [!v2, !v1, !v0]
    // v1 is redundant because its reason clause is (v0, v1), and v0 is already
    // in the learned clause. So v1 can be derived from the other learned literals.
    //
    // Expected after minimization: [!v2, !v0] (v1 removed)
    let mut solver = Solver::new(5);

    // Add some clauses to populate the clause DB
    // C0: (v0, v1) — reason for v1 if v0 is true
    let reason_for_v1 = ClauseRef(solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    ) as u32);

    // Set up assignments (required by is_redundant_cached debug_assert)
    solver.vals[Literal::positive(Variable(0)).index()] = 1; // v0 = true
    solver.vals[Literal::negative(Variable(0)).index()] = -1;
    solver.vals[Literal::positive(Variable(1)).index()] = 1; // v1 = true (propagated from v0)
    solver.vals[Literal::negative(Variable(1)).index()] = -1;
    solver.vals[Literal::positive(Variable(2)).index()] = 1; // v2 = true
    solver.vals[Literal::negative(Variable(2)).index()] = -1;
    solver.vals[Literal::positive(Variable(3)).index()] = 1; // v3 = true
    solver.vals[Literal::negative(Variable(3)).index()] = -1;

    // Set up levels (simulate state after decisions + propagation)
    solver.var_data[0].level = 1; // v0 @ level 1 (decision)
    solver.var_data[1].level = 1; // v1 @ level 1 (propagated)
    solver.var_data[2].level = 2; // v2 @ level 2 (decision)
    solver.var_data[3].level = 2; // v3 @ level 2 (propagated)

    // Set up trail positions (ascending order of assignment)
    solver.var_data[0].trail_pos = 0; // v0 assigned first (decision @ level 1)
    solver.var_data[1].trail_pos = 1; // v1 assigned second (propagated @ level 1)
    solver.var_data[2].trail_pos = 2; // v2 assigned third (decision @ level 2)
    solver.var_data[3].trail_pos = 3; // v3 assigned fourth (propagated @ level 2)

    // Set up reasons
    solver.var_data[0].reason = NO_REASON; // v0 is a decision
    solver.var_data[1].reason = reason_for_v1.0; // v1 is propagated from C0
    solver.var_data[2].reason = NO_REASON; // v2 is a decision
    solver.var_data[3].reason = NO_REASON; // v3 is a decision

    // Set up conflict state: learned clause is [!v2, !v1, !v0]
    // UIP is some literal at the current decision level (not part of minimize test)
    solver.conflict.clear(&mut solver.var_data);
    solver
        .conflict
        .set_asserting_literal(Literal::negative(Variable(3)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(2)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(1)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(0)));

    // Run minimization
    solver.minimize_learned_clause();

    // Check result: v1 should be removed because its reason (C0: v0 => v1)
    // means v1 can be derived from v0, which is already in the clause.
    let asserting = solver.conflict.asserting_literal();
    let learned_count = solver.conflict.learned_count();
    let mut learned_vars: Vec<usize> = Vec::new();
    for i in 0..learned_count {
        learned_vars.push(solver.conflict.learned_at(i).variable().index());
    }

    assert!(
        !learned_vars.contains(&1),
        "v1 should be removed by minimization (redundant: implied by v0 via C0). Learned vars: {learned_vars:?}"
    );
    assert!(
        learned_vars.contains(&0),
        "v0 must remain in learned clause. Learned vars: {learned_vars:?}"
    );
    assert!(
        learned_vars.contains(&2),
        "v2 must remain in learned clause (decision, not redundant). Learned vars: {learned_vars:?}"
    );
    assert_eq!(
        asserting,
        Literal::negative(Variable(3)),
        "asserting literal should be unchanged by minimization"
    );
}

/// Test that minimize_learned_clause does NOT remove a non-redundant decision literal.
#[test]
fn test_minimize_learned_clause_preserves_decisions() {
    let mut solver = Solver::new(4);

    // All learned literals are decisions — none can be removed
    solver.vals[Literal::positive(Variable(0)).index()] = 1;
    solver.vals[Literal::negative(Variable(0)).index()] = -1;
    solver.vals[Literal::positive(Variable(1)).index()] = 1;
    solver.vals[Literal::negative(Variable(1)).index()] = -1;
    solver.vals[Literal::positive(Variable(2)).index()] = 1;
    solver.vals[Literal::negative(Variable(2)).index()] = -1;

    solver.var_data[0].level = 1;
    solver.var_data[1].level = 2;
    solver.var_data[2].level = 3;

    solver.var_data[0].reason = NO_REASON;
    solver.var_data[1].reason = NO_REASON;
    solver.var_data[2].reason = NO_REASON;

    solver.conflict.clear(&mut solver.var_data);
    solver
        .conflict
        .set_asserting_literal(Literal::negative(Variable(2)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(0)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(1)));

    solver.minimize_learned_clause();

    let learned_count = solver.conflict.learned_count();
    assert_eq!(
        learned_count, 2,
        "decision literals cannot be minimized away: expected 2, got {learned_count}"
    );
}

/// #5060 AC-2: Knuth single-literal abort in `is_redundant_cached`.
/// When a literal at depth 0 has `minimize_level_count[var_level] < 2`
/// (only one literal from its level in the clause), the abort fires
/// and the literal is not removed — even though it has a reason clause.
#[test]
fn test_minimize_knuth_single_literal_abort() {
    // Setup:
    //   v0 @ level 1 (decision, trail_pos=0)
    //   v1 @ level 1 (propagated from C0: v0 ∨ v1, trail_pos=1)
    //   v2 @ level 2 (decision, trail_pos=2)
    //
    // Learned clause: [!v2 (asserting), !v1]
    // Level 1 has only 1 literal (v1) → minimize_level_count[1] == 1 < 2
    // Knuth abort fires → v1 stays.
    let mut solver = Solver::new(4);

    // C0: (v0, v1) — reason for v1's propagation
    let reason_for_v1 = ClauseRef(solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    ) as u32);

    // Assignments
    solver.vals[Literal::positive(Variable(0)).index()] = 1;
    solver.vals[Literal::negative(Variable(0)).index()] = -1;
    solver.vals[Literal::positive(Variable(1)).index()] = 1;
    solver.vals[Literal::negative(Variable(1)).index()] = -1;
    solver.vals[Literal::positive(Variable(2)).index()] = 1;
    solver.vals[Literal::negative(Variable(2)).index()] = -1;

    // Levels: v0, v1 @ level 1; v2 @ level 2
    solver.var_data[0].level = 1; // v0 (decision)
    solver.var_data[1].level = 1; // v1 (propagated)
    solver.var_data[2].level = 2; // v2 (decision)

    // Trail positions
    solver.var_data[0].trail_pos = 0;
    solver.var_data[1].trail_pos = 1;
    solver.var_data[2].trail_pos = 2;

    // Reasons
    solver.var_data[0].reason = NO_REASON; // decision
    solver.var_data[1].reason = reason_for_v1.0; // propagated
    solver.var_data[2].reason = NO_REASON; // decision

    // Learned clause: asserting = !v2, learned = [!v1]
    solver.conflict.clear(&mut solver.var_data);
    solver
        .conflict
        .set_asserting_literal(Literal::negative(Variable(2)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(1)));

    solver.decision_level = 2;
    solver.minimize_learned_clause();

    // v1 should stay: only 1 literal from level 1 → Knuth abort
    let learned_count = solver.conflict.learned_count();
    assert_eq!(
        learned_count, 1,
        "Knuth single-literal abort: v1 should stay (only literal at level 1). Got {learned_count}"
    );
    assert_eq!(
        solver.conflict.learned_at(0),
        Literal::negative(Variable(1)),
        "The remaining literal should be !v1"
    );
}

/// #5060 AC-3: Trail-position abort in `is_redundant_cached`.
/// When `trail_pos[var_idx] <= minimize_level_trail[var_level]`, the
/// literal was assigned at or before the earliest clause literal on its
/// level, so it cannot be resolved away.
#[test]
fn test_minimize_trail_position_abort() {
    // Setup:
    //   v0 @ level 1 (decision, trail_pos=0)
    //   v1 @ level 1 (propagated from C0: v0 ∨ v1, trail_pos=1)
    //   v2 @ level 1 (propagated from C1: v1 ∨ v2, trail_pos=2)
    //   v3 @ level 2 (decision, trail_pos=3)
    //
    // Learned clause: [!v3 (asserting), !v2, !v1]
    // Level 1 has 2 literals (v1, v2) → Knuth abort does NOT fire.
    // minimize_level_trail[1] = min(trail_pos[1], trail_pos[2]) = 1
    //
    // For v1: trail_pos[1]=1 <= minimize_level_trail[1]=1 → abort → stays
    // For v2: trail_pos[2]=2 > minimize_level_trail[1]=1 → no abort
    //   v2's reason C1=(v1,v2): v1 is VISITED (in clause) → redundant → v2 removed
    let mut solver = Solver::new(5);

    // C0: (v0, v1) — reason for v1
    let reason_for_v1 = ClauseRef(solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    ) as u32);

    // C1: (v1, v2) — reason for v2
    let reason_for_v2 = ClauseRef(solver.add_clause_db(
        &[
            Literal::positive(Variable(1)),
            Literal::positive(Variable(2)),
        ],
        false,
    ) as u32);

    // Assignments: v0..v3 all true
    for v in 0..4 {
        solver.vals[Literal::positive(Variable(v)).index()] = 1;
        solver.vals[Literal::negative(Variable(v)).index()] = -1;
    }

    // Levels: v0, v1, v2 @ level 1; v3 @ level 2
    solver.var_data[0].level = 1;
    solver.var_data[1].level = 1;
    solver.var_data[2].level = 1;
    solver.var_data[3].level = 2;

    // Trail positions (ascending)
    solver.var_data[0].trail_pos = 0;
    solver.var_data[1].trail_pos = 1;
    solver.var_data[2].trail_pos = 2;
    solver.var_data[3].trail_pos = 3;

    // Reasons
    solver.var_data[0].reason = NO_REASON; // decision
    solver.var_data[1].reason = reason_for_v1.0;
    solver.var_data[2].reason = reason_for_v2.0;
    solver.var_data[3].reason = NO_REASON; // decision

    // Learned clause: asserting = !v3, learned = [!v2, !v1]
    solver.conflict.clear(&mut solver.var_data);
    solver
        .conflict
        .set_asserting_literal(Literal::negative(Variable(3)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(2)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(1)));

    solver.decision_level = 2;
    solver.minimize_learned_clause();

    // v1 stays (trail-position abort), v2 removed (redundant via v1)
    let learned_count = solver.conflict.learned_count();
    assert_eq!(
        learned_count, 1,
        "Trail-position abort: v1 stays, v2 removed. Expected 1 learned literal, got {learned_count}"
    );

    let remaining = solver.conflict.learned_at(0);
    assert_eq!(
        remaining,
        Literal::negative(Variable(1)),
        "The remaining literal should be !v1 (earliest at level 1, trail-pos abort)"
    );
}

#[test]
fn test_shrink_skips_singleton_level_learned_clause() {
    let mut solver = Solver::new(4);

    for v in 0..3 {
        solver.vals[Literal::positive(Variable(v)).index()] = 1;
        solver.vals[Literal::negative(Variable(v)).index()] = -1;
        solver.var_data[v as usize].level = v + 1;
        solver.var_data[v as usize].trail_pos = v;
        solver.var_data[v as usize].reason = NO_REASON;
        solver.trail.push(Literal::positive(Variable(v)));
    }
    solver.decision_level = 3;

    solver.conflict.clear(&mut solver.var_data);
    solver
        .conflict
        .set_asserting_literal(Literal::negative(Variable(2)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(1)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(0)));

    solver.shrink_and_minimize_learned_clause();

    assert_eq!(
        solver.conflict.learned_count(),
        2,
        "singleton-level learned literals must be kept"
    );
    assert_eq!(
        solver.conflict.learned_at(0),
        Literal::negative(Variable(1))
    );
    assert_eq!(
        solver.conflict.learned_at(1),
        Literal::negative(Variable(0))
    );
    assert_eq!(
        solver.stats.shrink_block_attempts, 0,
        "no repeated non-UIP level means block shrink cannot be attempted"
    );
    assert_eq!(
        solver.stats.shrink_singleton_fast_path_skips, 1,
        "singleton-level learned clauses should be counted as fast-path skips"
    );
    assert!(
        solver.min.minimize_to_clear.is_empty() && solver.min.minimize_levels_to_clear.is_empty(),
        "fast path must not leave minimization scratch pending"
    );
}

#[test]
fn test_lrat_singleton_shrink_skips_original_snapshot_gate() {
    let mut solver = Solver::new(4);
    solver.enable_lrat();

    assert!(
        !solver.should_snapshot_lrat_original_learned(3, false),
        "LRAT shrink mode must skip the original learned snapshot when the repeated-level guard is false"
    );
    assert!(
        solver.should_snapshot_lrat_original_learned(3, true),
        "LRAT shrink mode still needs the snapshot when shrink/minimize can remove literals"
    );
    assert!(
        !solver.should_snapshot_lrat_original_learned(2, true),
        "binary clauses skip minimization and therefore do not need an original snapshot"
    );

    solver.set_shrink_enabled(false);
    assert!(
        solver.should_snapshot_lrat_original_learned(3, false),
        "plain minimization can still remove literals, so LRAT must keep the original snapshot"
    );

    let no_lrat_solver = Solver::new(4);
    assert!(
        !no_lrat_solver.should_snapshot_lrat_original_learned(3, true),
        "non-LRAT solving must not pay for an LRAT-only original snapshot"
    );
}

#[test]
fn test_lrat_removed_literal_chain_call_counter() {
    let mut solver = Solver::new(2);
    solver.enable_lrat();
    solver.conflict.clear(&mut solver.var_data);
    solver
        .conflict
        .set_asserting_literal(Literal::negative(Variable(1)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(0)));

    assert_eq!(solver.learned_lrat_snapshot_stats().4, 0);
    let minimize_level0 =
        solver.compute_lrat_chain_for_removed_literals(&[Literal::negative(Variable(0))]);

    assert!(
        minimize_level0.is_empty(),
        "identical original/final learned clause has no removed literals"
    );
    assert_eq!(
        solver.learned_lrat_snapshot_stats().4,
        1,
        "removed-literal LRAT chain calls should be counted even when no literal was removed"
    );
}

#[test]
fn test_lrat_snapshot_counter_skips_unchanged_minimize_clause() {
    let mut solver = Solver::new(3);
    solver.enable_lrat();
    solver.set_shrink_enabled(false);

    for v in 0..3 {
        let var = Variable(v);
        solver.vals[Literal::positive(var).index()] = 1;
        solver.vals[Literal::negative(var).index()] = -1;
        solver.var_data[v as usize].level = v + 1;
        solver.var_data[v as usize].trail_pos = v;
        solver.var_data[v as usize].reason = NO_REASON;
        solver.trail.push(Literal::positive(var));
    }
    solver.decision_level = 3;

    solver.conflict.clear(&mut solver.var_data);
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(0)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(1)));

    let result = solver.finalize_conflict_analysis(Literal::negative(Variable(2)), Vec::new());

    assert_eq!(
        result.learned_clause,
        vec![
            Literal::negative(Variable(2)),
            Literal::negative(Variable(1)),
            Literal::negative(Variable(0)),
        ],
        "decision literals must survive minimize unchanged"
    );
    assert_eq!(
        solver.learned_lrat_snapshot_stats(),
        (0, 0, 0, 0, 0),
        "LRAT snapshot counters should only charge actual removed-literal snapshots"
    );
}

#[test]
fn test_plain_minimize_collect_removed_records_only_dropped_literals() {
    let mut solver = Solver::new(4);
    solver.set_shrink_enabled(false);

    let reason_for_v1 = ClauseRef(solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    ) as u32);

    for v in 0..3 {
        solver.vals[Literal::positive(Variable(v)).index()] = 1;
        solver.vals[Literal::negative(Variable(v)).index()] = -1;
        solver.var_data[v as usize].trail_pos = v;
        solver.trail.push(Literal::positive(Variable(v)));
    }
    solver.var_data[0].level = 1;
    solver.var_data[1].level = 1;
    solver.var_data[2].level = 2;
    solver.var_data[0].reason = NO_REASON;
    solver.var_data[1].reason = reason_for_v1.0;
    solver.var_data[2].reason = NO_REASON;
    solver.decision_level = 2;

    solver.conflict.clear(&mut solver.var_data);
    solver
        .conflict
        .set_asserting_literal(Literal::negative(Variable(2)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(1)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(0)));

    let mut removed = Vec::new();
    solver.minimize_learned_clause_collect_removed(Some(&mut removed));

    assert_eq!(
        removed,
        vec![Literal::negative(Variable(1))],
        "removed-only LRAT collection must not copy kept learned literals"
    );
    assert_eq!(solver.conflict.learned_count(), 1);
    assert_eq!(
        solver.conflict.learned_at(0),
        Literal::negative(Variable(0))
    );
}

#[test]
fn test_shrink_collect_removed_records_replaced_block_literals() {
    let mut solver = Solver::new(4);

    let reason_for_v1 = ClauseRef(solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    ) as u32);

    for v in 0..3 {
        solver.vals[Literal::positive(Variable(v)).index()] = 1;
        solver.vals[Literal::negative(Variable(v)).index()] = -1;
        solver.var_data[v as usize].trail_pos = v;
        solver.trail.push(Literal::positive(Variable(v)));
    }
    solver.var_data[0].level = 1;
    solver.var_data[1].level = 1;
    solver.var_data[2].level = 2;
    solver.var_data[0].reason = NO_REASON;
    solver.var_data[1].reason = reason_for_v1.0;
    solver.var_data[2].reason = NO_REASON;
    solver.decision_level = 2;

    solver.conflict.clear(&mut solver.var_data);
    solver
        .conflict
        .set_asserting_literal(Literal::negative(Variable(2)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(1)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(0)));

    let mut removed = Vec::new();
    solver.shrink_and_minimize_repeated_level_learned_clause_collect_removed(2, Some(&mut removed));

    assert_eq!(
        removed,
        vec![Literal::negative(Variable(1))],
        "block-UIP shrink must record only literals replaced out of the learned clause"
    );
    assert_eq!(solver.conflict.learned_count(), 1);
    assert_eq!(
        solver.conflict.learned_at(0),
        Literal::negative(Variable(0))
    );
    assert_eq!(solver.stats.shrink_block_successes, 1);
}

#[test]
fn test_shrink_repeated_level_still_enters_block_path() {
    let mut solver = Solver::new(4);

    for v in 0..3 {
        solver.vals[Literal::positive(Variable(v)).index()] = 1;
        solver.vals[Literal::negative(Variable(v)).index()] = -1;
        solver.var_data[v as usize].trail_pos = v;
        solver.var_data[v as usize].reason = NO_REASON;
        solver.trail.push(Literal::positive(Variable(v)));
    }
    solver.var_data[0].level = 1;
    solver.var_data[1].level = 1;
    solver.var_data[2].level = 2;
    solver.decision_level = 2;

    solver.conflict.clear(&mut solver.var_data);
    solver
        .conflict
        .set_asserting_literal(Literal::negative(Variable(2)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(1)));
    solver
        .conflict
        .add_to_learned(Literal::negative(Variable(0)));

    solver.shrink_and_minimize_learned_clause();

    assert_eq!(
        solver.stats.shrink_block_attempts, 1,
        "same-level learned literals must not take the singleton fast path"
    );
    assert_eq!(
        solver.stats.shrink_singleton_fast_path_skips, 0,
        "repeated-level learned literals must not be counted as singleton skips"
    );
    assert_eq!(
        solver.conflict.learned_count(),
        2,
        "decision literals in the repeated block must be kept when no block UIP exists"
    );
    assert!(
        solver.min.minimize_to_clear.is_empty() && solver.min.minimize_levels_to_clear.is_empty(),
        "normal block path must clean minimization scratch"
    );
}

// ========================================================================
// lit_val (branch-free literal value) Tests
// ========================================================================

/// lit_val returns 0 for all literals in a fresh solver.
#[test]
fn test_lit_val_fresh_solver_all_unassigned() {
    let solver: Solver = Solver::new(5);
    for var_idx in 0..5u32 {
        let var = Variable(var_idx);
        assert_eq!(solver.lit_val(Literal::positive(var)), 0);
        assert_eq!(solver.lit_val(Literal::negative(var)), 0);
    }
}

/// After enqueue(positive), lit_val returns +1 for positive and -1 for negative.
#[test]
fn test_lit_val_after_enqueue_positive() {
    let mut solver: Solver = Solver::new(3);
    let var = Variable(1);
    let pos = Literal::positive(var);
    let neg = Literal::negative(var);

    solver.enqueue(pos, None);
    assert_eq!(solver.lit_val(pos), 1, "positive literal should be true");
    assert_eq!(solver.lit_val(neg), -1, "negative literal should be false");
    // lit_value must agree
    assert_eq!(solver.lit_value(pos), Some(true));
    assert_eq!(solver.lit_value(neg), Some(false));
}

/// After enqueue(negative), lit_val returns +1 for negative and -1 for positive.
#[test]
fn test_lit_val_after_enqueue_negative() {
    let mut solver: Solver = Solver::new(3);
    let var = Variable(2);
    let pos = Literal::positive(var);
    let neg = Literal::negative(var);

    solver.enqueue(neg, None);
    assert_eq!(solver.lit_val(neg), 1, "negative literal should be true");
    assert_eq!(solver.lit_val(pos), -1, "positive literal should be false");
    // lit_value must agree
    assert_eq!(solver.lit_value(neg), Some(true));
    assert_eq!(solver.lit_value(pos), Some(false));
}

/// After backtrack, lit_val returns 0 for unassigned variables.
#[test]
fn test_lit_val_after_backtrack_is_zero() {
    let mut solver: Solver = Solver::new(3);

    // Decide at level 1 (propagate between decides to advance qhead)
    solver.decide(Literal::positive(Variable(0)));
    solver.propagate();
    assert_eq!(solver.lit_val(Literal::positive(Variable(0))), 1);

    // Decide at level 2
    solver.decide(Literal::negative(Variable(1)));
    assert_eq!(solver.lit_val(Literal::negative(Variable(1))), 1);
    assert_eq!(solver.lit_val(Literal::positive(Variable(1))), -1);

    // Backtrack to level 1: variable 1 should be unassigned
    solver.backtrack(1);
    assert_eq!(
        solver.lit_val(Literal::positive(Variable(1))),
        0,
        "var 1 should be unassigned after backtracking past its level"
    );
    assert_eq!(
        solver.lit_val(Literal::negative(Variable(1))),
        0,
        "~var 1 should be unassigned after backtracking past its level"
    );
    // Variable 0 should still be assigned
    assert_eq!(solver.lit_val(Literal::positive(Variable(0))), 1);
}

/// lit_val and lit_value agree for all variables through assign/backtrack cycles.
#[test]
fn test_lit_val_agrees_with_lit_value_through_cycles() {
    let mut solver: Solver = Solver::new(4);

    // Assign all variables at different levels (propagate between decides to advance qhead)
    solver.decide(Literal::positive(Variable(0)));
    solver.propagate();
    solver.decide(Literal::negative(Variable(1)));
    solver.propagate();
    solver.decide(Literal::positive(Variable(2)));
    solver.propagate();
    solver.decide(Literal::negative(Variable(3)));

    // Verify agreement
    for var_idx in 0..4u32 {
        let var = Variable(var_idx);
        let pos = Literal::positive(var);
        let neg = Literal::negative(var);
        let val = solver.lit_val(pos);
        let value = solver.lit_value(pos);
        match val {
            1 => assert_eq!(value, Some(true)),
            -1 => assert_eq!(value, Some(false)),
            0 => assert_eq!(value, None),
            _ => panic!("unexpected lit_val: {val}"),
        }
        // Negative literal must be opposite
        assert_eq!(solver.lit_val(neg), -val);
    }

    // Backtrack all the way
    solver.backtrack(0);
    for var_idx in 0..4u32 {
        let var = Variable(var_idx);
        assert_eq!(solver.lit_val(Literal::positive(var)), 0);
        assert_eq!(solver.lit_val(Literal::negative(var)), 0);
        assert_eq!(solver.lit_value(Literal::positive(var)), None);
    }
}
