// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use super::*;
use crate::clause::compute_clause_signature;

#[path = "compact_tests/state_mapping.rs"]
mod state_mapping;

#[test]
fn remap_var_vec_handles_empty_source_vector() {
    let map = VariableMap {
        old_to_new: vec![0, 1, 2],
        new_num_vars: 3,
    };
    let mut vec: Vec<u32> = Vec::new();

    map.remap_var_vec(&mut vec);

    assert_eq!(vec, vec![0, 0, 0]);
}

#[test]
fn remap_lit_vec_handles_empty_source_vector() {
    let map = VariableMap {
        old_to_new: vec![0, 1],
        new_num_vars: 2,
    };
    let mut vec: Vec<u32> = Vec::new();

    map.remap_lit_vec(&mut vec);

    assert_eq!(vec, vec![0, 0, 0, 0]);
}

#[test]
fn remap_lit_vec_preserves_mapping_semantics() {
    let map = VariableMap {
        old_to_new: vec![UNMAPPED, 0, 1],
        new_num_vars: 2,
    };
    let mut vec = vec![10, 11, 20, 21, 30, 31];

    map.remap_lit_vec(&mut vec);

    assert_eq!(vec, vec![20, 21, 30, 31]);
}

#[test]
fn compact_resets_subsume_dirty_for_remapped_variables() {
    let mut solver: Solver = Solver::new(4);

    // Force non-trivial remap: keep vars 0 and 2, remove 1 and 3.
    solver.var_lifecycle.mark_eliminated(1);
    solver.var_lifecycle.mark_substituted(3);

    // Simulate a stale dirty-bit state from prior rounds.
    solver.subsume_dirty = vec![false; 4];

    solver.compact();

    assert_eq!(solver.num_vars, 2, "compaction should remove inactive vars");
    assert_eq!(
        solver.subsume_dirty,
        vec![true; 2],
        "all mapped vars must be dirty after compaction"
    );
}

/// Verify that `compact_watches` Phase A skips binary watchers whose
/// blocker references an eliminated variable, and keeps+remaps binary
/// watchers with active blockers.
///
/// Long-clause watches are handled by Phase B (arena-based rebuild),
/// tested separately in `compact_watches_long_from_arena`.
#[test]
fn compact_watches_binary_vs_long_unmapped_blocker() {
    use crate::literal::{Literal, Variable};
    use crate::watched::{ClauseRef, WatchedLists, Watcher};

    // 4 vars: 0 active, 1 eliminated, 2 active, 3 active.
    let map = VariableMap {
        old_to_new: vec![0, UNMAPPED, 1, 2],
        new_num_vars: 3,
    };
    let l = |v: u32| Literal::positive(Variable(v));
    let mut solver: Solver = Solver::new(4);

    // Arena-backed binary clauses: Phase A now checks clause liveness in the
    // arena (husk adjudication / #8497 family), so entries must reference
    // real clauses.
    let stale_idx = solver.arena.add(&[l(0), l(1)], false); // eliminated blocker
    let live_idx = solver.arena.add(&[l(0), l(2)], false); // keep + remap
    let husk_idx = solver.arena.add(&[l(0), l(2)], false); // garbage-kept husk
    solver.arena.mark_garbage_keep_data(husk_idx);

    let mut watches = WatchedLists::new(4);
    // Binary with eliminated blocker → SKIP (stale clause)
    watches.add_watch(l(0), Watcher::binary(ClauseRef(stale_idx as u32), l(1)));
    // Binary with active blocker → KEEP + remap
    watches.add_watch(l(0), Watcher::binary(ClauseRef(live_idx as u32), l(2)));
    // Binary referencing a garbage-kept husk → SKIP (logically deleted;
    // copying it would let BCP propagate through a dead clause).
    watches.add_watch(l(0), Watcher::binary(ClauseRef(husk_idx as u32), l(2)));
    // Long watchers are present but Phase A ignores them; Phase B
    // rebuilds from arena (no len>=3 arena clauses here, so 0 long entries).
    watches.add_watch(l(0), Watcher::new(ClauseRef(20), l(1)));
    watches.add_watch(l(0), Watcher::new(ClauseRef(21), l(3)));

    solver.watches = watches;
    solver.compact_watches(&map);

    let new_l0 = l(0); // old 0 → new 0
    let new_l2 = l(1); // old 2 → new 1
    let wl = solver.watches.get_watches(new_l0);

    // Phase A: 1 binary skipped (eliminated blocker) + 1 binary skipped
    // (husk) + 1 binary kept = 1 entry.
    // Phase B: no len>=3 arena clauses → 0 long entries.
    assert_eq!(
        wl.len(),
        1,
        "only the live active-blocker binary should survive"
    );

    // Entry 0: binary, blocker remapped from old var 2 → new var 1
    assert!(wl.is_binary(0));
    assert_eq!(wl.blocker(0), new_l2);
    assert_eq!(wl.clause_ref(0), ClauseRef(live_idx as u32));
}

/// Verify Phase 0 cleanup: compact() deletes active clauses that reference
/// eliminated variables before remapping (#8464).
///
/// This reproduces the bug where BVE marks a variable as eliminated but a
/// clause referencing it remains in the arena (e.g., due to inter-technique
/// mutations between BVE's post-elimination GC and compaction). Without
/// Phase 0, compact would panic at the "active clause contains
/// eliminated-variable literal" assertion.
#[test]
fn compact_phase0_deletes_stale_clauses_with_eliminated_vars() {
    use crate::literal::{Literal, Variable};

    let mut solver: Solver = Solver::new(4);

    // Add a clause referencing vars 0, 1, 2 to the arena.
    let lits = [
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
    ];
    solver.arena.add(&lits, false);

    // Add a second clause that is clean (no eliminated vars).
    let clean_lits = [
        Literal::positive(Variable(0)),
        Literal::negative(Variable(2)),
        Literal::positive(Variable(3)),
    ];
    solver.arena.add(&clean_lits, false);

    // Eliminate variable 1 -- simulates BVE marking the variable but the
    // first clause not being deleted (the root cause of #8464).
    solver.var_lifecycle.mark_eliminated(1);

    // compact() should NOT panic. Phase 0 should delete the stale clause
    // (containing eliminated var 1) before the remapping phase.
    solver.compact();

    // After compaction: vars 0, 2, 3 mapped to 0, 1, 2.
    assert_eq!(solver.num_vars, 3);

    // The stale clause should have been deleted; only the clean clause
    // should survive, with remapped literals.
    let surviving_count = solver.arena.active_indices().count();
    assert_eq!(
        surviving_count, 1,
        "only the clean clause should survive Phase 0 cleanup"
    );
}

/// Verify Phase 0+1 cleanup deletes multiple stale clauses (both learned
/// and irredundant) and correctly remaps surviving clauses (#8464).
///
/// Regression: BVE marks variable as eliminated but inter-technique mutations
/// can leave both learned AND irredundant clauses referencing the eliminated
/// variable. Both must be cleaned up before literal remapping.
#[test]
fn compact_cleanup_handles_mixed_learned_and_irredundant_stale_clauses() {
    use crate::literal::{Literal, Variable};

    let mut solver: Solver = Solver::new(5);

    // Irredundant clause with eliminated var 2
    let stale_irred = [
        Literal::positive(Variable(0)),
        Literal::negative(Variable(2)),
        Literal::positive(Variable(3)),
    ];
    solver.arena.add(&stale_irred, false);

    // Learned clause with eliminated var 2
    let stale_learned = [
        Literal::negative(Variable(1)),
        Literal::positive(Variable(2)),
        Literal::negative(Variable(4)),
    ];
    solver.arena.add(&stale_learned, true);

    // Clean irredundant clause (no eliminated vars)
    let clean = [
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
        Literal::positive(Variable(3)),
    ];
    solver.arena.add(&clean, false);

    // Eliminate variable 2
    solver.var_lifecycle.mark_eliminated(2);

    // compact() should not panic; Phase 0 deletes both stale clauses
    solver.compact();

    // After compaction: vars 0,1,3,4 mapped to 0,1,2,3
    assert_eq!(solver.num_vars, 4);

    // Only the clean clause should survive
    let surviving = solver.arena.active_indices().count();
    assert_eq!(
        surviving, 1,
        "only the clean clause should survive compaction"
    );

    // Verify remapped literals: old var 0→new 0, old var 1→new 1, old var 3→new 2
    let surviving_idx = solver.arena.active_indices().next().unwrap();
    let lits = solver.arena.literals(surviving_idx);
    assert_eq!(lits.len(), 3);
    assert_eq!(lits[0], Literal::positive(Variable(0))); // 0→0
    assert_eq!(lits[1], Literal::negative(Variable(1))); // 1→1
    assert_eq!(lits[2], Literal::positive(Variable(2))); // 3→2
}

/// Verify Phase 2 safety net: compact() gracefully handles the case where
/// multiple clauses reference eliminated variables, including scenarios where
/// the eliminated variable appears in different positions within each clause.
/// This exercises all three cleanup phases (#8464).
#[test]
fn compact_phase2_safety_net_multiple_stale_clause_positions() {
    use crate::literal::{Literal, Variable};

    let mut solver: Solver = Solver::new(6);

    // Clause 1: eliminated var at position 0
    let stale1 = [
        Literal::positive(Variable(2)), // will be eliminated
        Literal::negative(Variable(0)),
        Literal::positive(Variable(3)),
    ];
    solver.arena.add(&stale1, false);

    // Clause 2: eliminated var at position 1
    let stale2 = [
        Literal::negative(Variable(1)),
        Literal::negative(Variable(2)), // will be eliminated
        Literal::positive(Variable(4)),
    ];
    solver.arena.add(&stale2, true); // learned clause

    // Clause 3: eliminated var at position 2 (last)
    let stale3 = [
        Literal::positive(Variable(0)),
        Literal::negative(Variable(5)),
        Literal::positive(Variable(2)), // will be eliminated
    ];
    solver.arena.add(&stale3, false);

    // Clean clause (no eliminated vars)
    let clean = [
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)),
        Literal::positive(Variable(3)),
    ];
    solver.arena.add(&clean, false);

    // Eliminate variable 2
    solver.var_lifecycle.mark_eliminated(2);

    // compact() should NOT panic — all three stale clauses are deleted
    solver.compact();

    // After compaction: vars 0,1,3,4,5 mapped to 0,1,2,3,4
    assert_eq!(solver.num_vars, 5);

    // Only the clean clause should survive
    let surviving = solver.arena.active_indices().count();
    assert_eq!(
        surviving, 1,
        "only the clean clause should survive compaction"
    );

    // Verify remapped literals in the surviving clause
    let surviving_idx = solver.arena.active_indices().next().unwrap();
    let lits = solver.arena.literals(surviving_idx);
    assert_eq!(lits.len(), 3);
    // old var 0 -> new 0, old var 1 -> new 1, old var 3 -> new 2
    assert_eq!(lits[0], Literal::positive(Variable(0)));
    assert_eq!(lits[1], Literal::negative(Variable(1)));
    assert_eq!(lits[2], Literal::positive(Variable(2)));
}

/// Verify compact() handles the case where multiple variables are eliminated
/// and stale clauses reference different eliminated variables.
#[test]
fn compact_multiple_eliminated_vars_stale_clauses() {
    use crate::literal::{Literal, Variable};

    let mut solver: Solver = Solver::new(6);

    // Clause referencing eliminated var 1
    let stale1 = [
        Literal::positive(Variable(0)),
        Literal::negative(Variable(1)), // eliminated
        Literal::positive(Variable(4)),
    ];
    solver.arena.add(&stale1, false);

    // Clause referencing eliminated var 3
    let stale2 = [
        Literal::negative(Variable(2)),
        Literal::positive(Variable(3)), // eliminated
        Literal::negative(Variable(5)),
    ];
    solver.arena.add(&stale2, false);

    // Clause referencing BOTH eliminated vars 1 and 3
    let stale3 = [
        Literal::positive(Variable(1)), // eliminated
        Literal::negative(Variable(3)), // eliminated
        Literal::positive(Variable(4)),
    ];
    solver.arena.add(&stale3, true);

    // Clean clause
    let clean = [
        Literal::positive(Variable(0)),
        Literal::negative(Variable(2)),
        Literal::positive(Variable(4)),
    ];
    solver.arena.add(&clean, false);

    // Eliminate variables 1 and 3
    solver.var_lifecycle.mark_eliminated(1);
    solver.var_lifecycle.mark_eliminated(3);

    solver.compact();

    // After compaction: vars 0,2,4,5 mapped to 0,1,2,3
    assert_eq!(solver.num_vars, 4);

    let surviving = solver.arena.active_indices().count();
    assert_eq!(surviving, 1, "only the clean clause should survive");

    let surviving_idx = solver.arena.active_indices().next().unwrap();
    let lits = solver.arena.literals(surviving_idx);
    assert_eq!(lits.len(), 3);
    // old var 0 -> new 0, old var 2 -> new 1, old var 4 -> new 2
    assert_eq!(lits[0], Literal::positive(Variable(0)));
    assert_eq!(lits[1], Literal::negative(Variable(1)));
    assert_eq!(lits[2], Literal::positive(Variable(2)));
    assert_eq!(
        solver.arena.signature(surviving_idx),
        compute_clause_signature(lits),
        "compaction must refresh signatures after in-place literal remapping"
    );
}
