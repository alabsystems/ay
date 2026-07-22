// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_reason_clause_marks_refresh_clears_stale_entries() {
    let mut solver: Solver = Solver::new(2);
    let c0_off = solver.arena.len();
    let x0 = Literal::positive(Variable(0));
    solver.add_clause(vec![x0]);
    let c1_off = solver.arena.len();
    let x1 = Literal::positive(Variable(1));
    solver.add_clause(vec![x1]);

    solver.vals[x0.index()] = 1;
    solver.vals[x0.negated().index()] = -1;
    solver.var_data[0].level = 0;
    solver.var_data[0].reason = c0_off as u32;
    solver.trail.push(x0);

    solver.vals[x1.index()] = 1;
    solver.vals[x1.negated().index()] = -1;
    solver.var_data[1].level = 0;
    solver.var_data[1].reason = c1_off as u32;
    solver.trail.push(x1);
    solver.refresh_reason_clause_marks();

    assert!(solver.is_reason_clause_marked(c0_off));
    assert!(solver.is_reason_clause_marked(c1_off));

    solver.var_data[1].reason = NO_REASON;
    solver.refresh_reason_clause_marks();

    assert!(solver.is_reason_clause_marked(c0_off));
    assert!(!solver.is_reason_clause_marked(c1_off));
}

/// Two `ensure_reason_clause_marks_current()` calls without intervening
/// invalidation must produce exactly one rebuild.
#[test]
fn test_ensure_reason_marks_skips_redundant_rebuild() {
    let mut solver: Solver = Solver::new(2);
    let c0_off = solver.arena.len();
    let x0 = Literal::positive(Variable(0));
    solver.add_clause(vec![x0]);
    let c1_off = solver.arena.len();
    let x1 = Literal::positive(Variable(1));
    solver.add_clause(vec![x1]);

    solver.vals[x0.index()] = 1;
    solver.vals[x0.negated().index()] = -1;
    solver.var_data[0].level = 0;
    solver.var_data[0].reason = c0_off as u32;
    solver.trail.push(x0);

    solver.vals[x1.index()] = 1;
    solver.vals[x1.negated().index()] = -1;
    solver.var_data[1].level = 0;
    solver.var_data[1].reason = c1_off as u32;
    solver.trail.push(x1);
    // Invalidate so ensure will trigger a rebuild on the first call.
    solver.invalidate_reason_clause_marks();

    let epoch_before = solver.reason_clause_epoch;
    solver.ensure_reason_clause_marks_current();
    let epoch_after_first = solver.reason_clause_epoch;
    // First call must have rebuilt (epoch incremented).
    assert_eq!(
        epoch_after_first,
        epoch_before + 1,
        "first ensure must rebuild"
    );

    // Second call with no intervening invalidation — should be a no-op.
    solver.ensure_reason_clause_marks_current();
    let epoch_after_second = solver.reason_clause_epoch;
    assert_eq!(
        epoch_after_second, epoch_after_first,
        "second ensure without invalidation must skip rebuild"
    );

    // Marks must still be correct after the skipped rebuild.
    assert!(solver.is_reason_clause_marked(c0_off));
    assert!(solver.is_reason_clause_marked(c1_off));

    // Now invalidate and verify ensure rebuilds again.
    solver.var_data[1].reason = NO_REASON;
    solver.invalidate_reason_clause_marks();
    solver.ensure_reason_clause_marks_current();
    let epoch_after_third = solver.reason_clause_epoch;
    assert_eq!(
        epoch_after_third,
        epoch_after_second + 1,
        "ensure after invalidation must rebuild"
    );
    assert!(solver.is_reason_clause_marked(c0_off));
    assert!(
        !solver.is_reason_clause_marked(c1_off),
        "cleared reason must not be marked"
    );
}

/// `invalidate_reason_clause_marks` is idempotent and cleared by `ensure`.
#[test]
fn test_invalidate_reason_clause_marks_is_idempotent() {
    let mut solver: Solver = Solver::new(1);

    // Starts non-invalidated.
    assert!(!solver.reason_marks_invalidated);

    solver.invalidate_reason_clause_marks();
    assert!(solver.reason_marks_invalidated);

    // Repeated invalidation is idempotent.
    solver.invalidate_reason_clause_marks();
    assert!(solver.reason_marks_invalidated);

    // After ensure, invalidation is cleared.
    solver.ensure_reason_clause_marks_current();
    assert!(!solver.reason_marks_invalidated);

    solver.invalidate_reason_clause_marks();
    assert!(solver.reason_marks_invalidated);
}

/// Incremental mark/unmark: marks set by mark_reason_clause() are visible
/// immediately without needing ensure_reason_clause_marks_current().
#[test]
fn test_incremental_mark_unmark_reason_clause() {
    let mut solver: Solver = Solver::new(2);
    let c0_off = solver.arena.len();
    let x0 = Literal::positive(Variable(0));
    solver.add_clause(vec![x0]);
    let c1_off = solver.arena.len();
    let x1 = Literal::positive(Variable(1));
    solver.add_clause(vec![x1]);

    // Initially not marked.
    assert!(!solver.is_reason_clause_marked(c0_off));
    assert!(!solver.is_reason_clause_marked(c1_off));

    // Mark c0 incrementally.
    solver.mark_reason_clause(c0_off);
    assert!(solver.is_reason_clause_marked(c0_off));
    assert!(!solver.is_reason_clause_marked(c1_off));

    // Mark c1 incrementally.
    solver.mark_reason_clause(c1_off);
    assert!(solver.is_reason_clause_marked(c0_off));
    assert!(solver.is_reason_clause_marked(c1_off));

    // Unmark c0.
    solver.unmark_reason_clause(c0_off);
    assert!(!solver.is_reason_clause_marked(c0_off));
    assert!(solver.is_reason_clause_marked(c1_off));

    // Unmark c1.
    solver.unmark_reason_clause(c1_off);
    assert!(!solver.is_reason_clause_marked(c0_off));
    assert!(!solver.is_reason_clause_marked(c1_off));
}

#[test]
fn test_reason_clause_marks_ignore_unassigned_stale_reason() {
    let mut solver: Solver = Solver::new(2);
    let c0_off = solver.arena.len();
    let x0 = Literal::positive(Variable(0));
    solver.add_clause(vec![x0]);
    let c1_off = solver.arena.len();
    let x1 = Literal::positive(Variable(1));
    solver.add_clause(vec![x1]);

    // Unassigned variable with a stale reason should not keep the clause marked.
    solver.var_data[0].level = 1;
    solver.var_data[0].reason = c0_off as u32;

    // Assigned variable with a live reason should still be marked.
    solver.vals[x1.index()] = 1;
    solver.vals[x1.negated().index()] = -1;
    solver.var_data[1].level = 0;
    solver.var_data[1].reason = c1_off as u32;
    solver.trail.push(x1); // Only assigned vars go on the trail.

    solver.refresh_reason_clause_marks();
    assert!(
        !solver.is_reason_clause_marked(c0_off),
        "unassigned stale reason must not mark clause as active"
    );
    assert!(solver.is_reason_clause_marked(c1_off));
}

#[test]
fn test_delete_clause_checked_respects_reason_marks() {
    // Unit clauses are now enqueued with reason=None (#6257), so they are NOT
    // reason-marked. This test verifies that a binary clause used as a
    // propagation reason IS protected from deletion.
    let mut solver: Solver = Solver::new(2);
    let lit0 = Literal::positive(Variable(0));
    let lit1 = Literal::positive(Variable(1));
    // Add a unit clause (neg x0) and a binary clause (x0 v x1).
    // Processing enqueues neg_x0 (reason=None for unit), then propagate()
    // triggers BCP: x0 is false, so binary clause forces x1 true
    // with reason=Some(binary_ref).
    solver.add_clause(vec![Literal::negative(Variable(0))]);
    solver.add_clause(vec![lit0, lit1]);
    // Set up watches (normally done in init_solve) so BCP can find the binary clause.
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    // Run BCP to propagate x1 via the binary clause.
    assert!(solver.propagate().is_none(), "expected no conflict");

    // Find the binary clause's arena index from x1's reason.
    let x1_var = lit1.variable().index();
    let binary_ref = solver
        .var_reason(x1_var)
        .expect("x1 should be propagated with a reason");
    let binary_idx = binary_ref.0 as usize;
    assert!(
        solver.arena.is_active(binary_idx),
        "binary clause must be active"
    );
    assert_eq!(
        solver.arena.len_of(binary_idx),
        2,
        "reason must be a binary clause"
    );

    solver.refresh_reason_clause_marks();
    assert!(
        solver.is_reason_clause_marked(binary_idx),
        "binary clause must be reason-marked"
    );
    let result = solver.delete_clause_checked(binary_idx, mutate::ReasonPolicy::Skip);
    assert_eq!(result, mutate::DeleteResult::Skipped);
    assert!(solver.arena.is_active(binary_idx));
}

/// Unit clauses with reason=None (#6257) are not reason-marked
/// and can be deleted via `delete_clause_checked`.
#[test]
fn test_unit_clause_reason_none_not_reason_marked() {
    let mut solver: Solver = Solver::new(1);
    let lit = Literal::positive(Variable(0));
    solver.add_clause(vec![lit]);
    assert!(solver.process_initial_clauses().is_none());

    solver.refresh_reason_clause_marks();
    // Unit clause (index 0) was enqueued with reason=None (#6257),
    // so it is NOT reason-marked and CAN be deleted.
    assert!(!solver.is_reason_clause_marked(0));
}

/// T4 (#4674): `delete_clause_unchecked` must panic (via debug_assert) when
/// called on a reason-protected clause with `ReasonPolicy::Skip`. This guards
/// against silent trail corruption where a reason clause is deleted while still
/// referenced by conflict analysis.
///
/// Only fires in debug builds (`debug_assert` is compiled out in release).
#[test]
#[should_panic(expected = "BUG: delete_clause_unchecked called on reason clause")]
#[cfg(debug_assertions)]
fn test_delete_clause_unchecked_panics_on_reason_clause() {
    let mut solver: Solver = Solver::new(2);
    // Add a clause so clause index 0 exists.
    let x0 = Literal::positive(Variable(0));
    solver.add_clause(vec![x0, Literal::positive(Variable(1))]);

    // Directly mark clause 0 as a reason (same pattern as
    // test_reason_clause_marks_refresh_clears_stale_entries).
    solver.vals[x0.index()] = 1;
    solver.vals[x0.negated().index()] = -1;
    solver.var_data[0].level = 0;
    solver.var_data[0].reason = 0;
    solver.trail.push(x0);
    solver.refresh_reason_clause_marks();
    assert!(solver.is_reason_clause_marked(0));

    // This must panic: deleting a reason clause with Skip policy.
    solver.delete_clause_unchecked(0, mutate::ReasonPolicy::Skip);
}
