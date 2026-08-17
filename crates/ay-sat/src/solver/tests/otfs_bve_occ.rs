// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for OTFS BVE occ list notification correctness (#8363).
//!
//! OTFS (on-the-fly self-subsumption) modifies clauses during CDCL search
//! without going through the inprocessing `replace_clause_impl` path. This
//! test module verifies that all three OTFS code paths properly notify the
//! BVE occurrence lists so they remain consistent.
//!
//! The three paths are:
//! 1. `otfs_strengthen`: in-place clause replacement (removes pivot literal)
//! 2. `otfs_subsume` deletion: garbage-marks the subsumed clause
//! 3. `otfs_subsume` promotion: promotes learned->irredundant
//!
//! Without these notifications, BVE occ lists retain stale entries that
//! corrupt elimination decisions. This was the primary cause of #8223
//! (P0 soundness bug) that forced the revert of incremental occ lists.

#[cfg(debug_assertions)]
use super::*;

/// OTFS BVE occ list notification (#8363): after OTFS strengthening an
/// irredundant clause, the BVE occurrence lists must be updated to reflect
/// the removed literal. Without this notification, occ lists retain stale
/// entries that corrupt BVE elimination decisions (primary cause of #8223).
#[cfg(debug_assertions)]
#[test]
fn test_otfs_strengthen_notifies_bve_occ_lists() {
    let mut solver = Solver::new(5);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let x3 = Literal::positive(Variable(3));
    let x4 = Literal::positive(Variable(4));

    // Add irredundant clauses (is_learned=false)
    let clause_idx = solver.add_clause_db(&[x0, x1, x2, x3], false);
    let clause_ref = ClauseRef(clause_idx as u32);
    // Add another irredundant clause so occ list has multiple entries
    let _c2 = solver.add_clause_db(&[x1, x2, x4], false);

    solver.initialize_watches();
    let _ = solver.process_initial_clauses();

    // Populate BVE occ lists
    solver
        .inproc
        .bve
        .rebuild_with_vals(&solver.arena, &solver.vals);
    assert!(
        solver.inproc.bve.is_occ_populated(),
        "occ lists must be populated after rebuild_with_vals"
    );

    // Verify occ list consistency before OTFS
    solver
        .inproc
        .bve
        .debug_verify_occ_against_rebuild(&solver.arena, &solver.vals);

    // Simulate OTFS state: x0 = propagated (true at level 1), rest falsified.
    solver.decide(x0);
    solver.propagate();
    solver.decide(x1.negated());
    solver.propagate();
    solver.decide(x2.negated());
    solver.propagate();
    solver.decide(x3.negated());
    solver.propagate();

    // OTFS strengthen: remove pivot x0 from the irredundant clause
    assert!(solver.otfs_strengthen(clause_ref, x0));
    assert_eq!(solver.otfs_strengthened(), 1);

    // After OTFS, the BVE occ lists must be consistent: the old literal
    // x0 must be removed and the remaining literals must be present.
    //
    // Pass empty vals to disable satisfied-clause filtering. During search,
    // some clauses may be satisfied by decision-level assignments, but
    // incremental occ maintenance does not filter satisfied clauses (that
    // cleanup happens in refresh_incremental at the start of the next BVE
    // round at level 0). The invariant we verify here: structural consistency
    // (correct clause→literal mapping), not val-filtered equivalence.
    solver
        .inproc
        .bve
        .debug_verify_occ_against_rebuild(&solver.arena, &[]);
}

/// OTFS subsume BVE occ list notification (#8363): after OTFS subsumes an
/// irredundant clause, the BVE occurrence lists must remove the subsumed
/// clause's entries. If the subsuming clause is learned and promoted to
/// irredundant, the occ lists must add the promoted clause.
#[cfg(debug_assertions)]
#[test]
fn test_otfs_subsume_notifies_bve_occ_lists() {
    // Use enough variables to avoid BCP triggering unit propagation on the
    // learned clause. With a 5-literal learned clause [x0..x4], deciding
    // x0=F and x1=F still leaves 3 unassigned — no unit propagation.
    let mut solver = Solver::new(6);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let x3 = Literal::positive(Variable(3));
    let x4 = Literal::positive(Variable(4));
    let x5 = Literal::positive(Variable(5));

    // Irredundant clause (to be subsumed): {x0, x1, x2, x3, x4, x5}
    let subsumed_idx = solver.add_clause_db(&[x0, x1, x2, x3, x4, x5], false);
    let subsumed_ref = ClauseRef(subsumed_idx as u32);
    // Learned clause that subsumes the irredundant one: {x0, x1, x2, x3, x4}
    // (subset of subsumed clause).
    let subsuming_idx = solver.add_clause_db(&[x0, x1, x2, x3, x4], true);
    let subsuming_ref = ClauseRef(subsuming_idx as u32);

    solver.initialize_watches();
    let _ = solver.process_initial_clauses();

    // Populate BVE occ lists
    solver
        .inproc
        .bve
        .rebuild_with_vals(&solver.arena, &solver.vals);
    assert!(solver.inproc.bve.is_occ_populated());

    // Verify occ list consistency before OTFS
    solver
        .inproc
        .bve
        .debug_verify_occ_against_rebuild(&solver.arena, &solver.vals);

    // Enter search: assign only x0=F, x1=F. This falsifies 2 of 5 in the
    // learned clause — no BCP unit propagation. OTFS subsume is called from
    // conflict analysis and doesn't require all-false assignment.
    solver.decide(x0.negated());
    solver.propagate();
    solver.decide(x1.negated());
    solver.propagate();

    // OTFS subsume: learned {x0..x4} subsumes irredundant {x0..x5}
    // This should:
    //   1. Remove {x0..x5} from occ lists (irredundant deleted)
    //   2. Promote {x0..x4} to irredundant and add to occ lists
    solver.otfs_subsume(subsuming_ref, subsumed_ref);
    assert_eq!(solver.otfs_clause_subsumed(), 1);

    // The subsuming clause should now be irredundant (promoted)
    assert!(
        !solver.arena.is_learned(subsuming_idx),
        "subsuming clause must be promoted to irredundant"
    );

    // After OTFS subsume, occ lists must reflect the deletion + promotion.
    // Pass empty vals (no satisfied-clause filtering) since we are mid-search.
    // See comment in test_otfs_strengthen_notifies_bve_occ_lists for rationale.
    solver
        .inproc
        .bve
        .debug_verify_occ_against_rebuild(&solver.arena, &[]);
}
