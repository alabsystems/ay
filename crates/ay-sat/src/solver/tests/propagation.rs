// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::assert_watch_invariant_for_all_active_clauses;
use super::*;
use crate::solver::propagation::bcp_mode;
use crate::solver::solver_stats::BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS;

#[test]
fn test_bcp_deferred_watch_path_has_no_mem_swap_source_pattern() {
    let source = include_str!("../propagation_bcp.rs");
    let std_swap = concat!("std::", "mem::", "swap");
    let mem_swap_call = concat!("mem::", "swap(");
    let old_to_deferred = concat!("swap", "_to_deferred");
    let old_from_deferred = concat!("swap", "_from_deferred");
    assert!(
        !source.contains(std_swap) && !source.contains(mem_swap_call),
        "BCP deferred watch path must not reintroduce the standard swap helper"
    );
    assert!(
        !source.contains(old_to_deferred) && !source.contains(old_from_deferred),
        "BCP should use the explicit deferred copy/restore API, not swap-shaped helpers"
    );
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "active_domain")]
fn test_standard_search_route_rejects_active_domain_in_debug() {
    let mut solver = Solver::new(2);
    let x = Variable(0);
    let y = Variable(1);

    solver.add_clause(vec![Literal::positive(x), Literal::positive(y)]);
    solver.initialize_watches();
    solver.set_domain(&[x]);

    let _ = solver.search_propagate_standard();
}

#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "bucket_queue_active")]
fn test_standard_decision_route_rejects_bucket_queue_in_debug() {
    let mut solver = Solver::new(2);
    solver.bucket_queue_active = true;

    let _ = solver.pick_next_decision_variable();
}

#[test]
fn test_rebuild_watches_rewinds_qhead_and_exposes_level0_conflict() {
    let mut solver: Solver = Solver::new(3);
    let x = Variable(0);
    let y = Variable(1);
    let z = Variable(2);

    // Level-0 assignment: x=false, y=false, z=true.
    solver.add_clause(vec![Literal::negative(x)]);
    solver.add_clause(vec![Literal::negative(y)]);
    solver.add_clause(vec![Literal::positive(z)]);
    // Initially satisfied by z=true.
    let last_clause_off = solver.arena.len();
    solver.add_clause(vec![
        Literal::positive(x),
        Literal::positive(y),
        Literal::positive(z),
    ]);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(solver.propagate().is_none());
    assert_eq!(
        solver.qhead,
        solver.trail.len(),
        "setup should finish with no pending propagation"
    );

    // Simulate an inprocessing rewrite: (x ∨ y ∨ z) -> (x ∨ y), which is now
    // conflicting under the current level-0 assignment.
    let clause_idx = last_clause_off;
    let new_lits = &[Literal::positive(x), Literal::positive(y)];
    solver.arena.replace(clause_idx, new_lits);
    solver.arena.set_saved_pos(clause_idx, 2);

    // Mark trail as affected from position 0 since clause content changed (#8095).
    solver.mark_trail_affected(0);
    solver.rebuild_watches();
    assert_eq!(
        solver.qhead, 0,
        "rebuild_watches must rewind qhead so existing assignments are rechecked"
    );
    assert!(
        solver.propagate().is_some(),
        "rebuilt watches should expose the latent level-0 conflict"
    );
}

/// Verify that `rebuild_watches` with `earliest_affected_trail_pos = None`
/// sets qhead to trail.len() (no re-propagation needed). This is the common
/// case when rebuild_watches is called without any clause content changes.
#[test]
fn test_rebuild_watches_no_affected_pos_skips_repropagation() {
    let mut solver: Solver = Solver::new(4);
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);
    let d = Variable(3);

    // Create a formula with level-0 units and a satisfied clause.
    solver.add_clause(vec![Literal::positive(a)]);
    solver.add_clause(vec![Literal::positive(b)]);
    solver.add_clause(vec![
        Literal::positive(a),
        Literal::positive(c),
        Literal::positive(d),
    ]);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(solver.propagate().is_none());
    let trail_len = solver.trail.len();

    // Reset earliest_affected_trail_pos to None (no changes during inprocessing).
    solver.earliest_affected_trail_pos = None;
    solver.rebuild_watches();

    // qhead should be set to trail.len() since nothing was affected.
    assert_eq!(
        solver.qhead, trail_len,
        "rebuild_watches with no affected pos should set qhead to trail.len()"
    );
}

/// Verify that `rebuild_watches` with `earliest_affected_trail_pos = Some(pos)`
/// rewinds qhead to exactly that position, not to 0.
#[test]
fn test_rebuild_watches_minimal_rewind_to_affected_pos() {
    let mut solver: Solver = Solver::new(5);
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);
    let d = Variable(3);
    let e = Variable(4);

    // Create a formula with several level-0 units.
    solver.add_clause(vec![Literal::positive(a)]);
    solver.add_clause(vec![Literal::positive(b)]);
    solver.add_clause(vec![Literal::positive(c)]);
    solver.add_clause(vec![
        Literal::positive(a),
        Literal::positive(d),
        Literal::positive(e),
    ]);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(solver.propagate().is_none());
    let trail_len = solver.trail.len();
    assert!(
        trail_len >= 3,
        "expected at least 3 trail entries from units"
    );

    // Simulate: inprocessing affected position 2 (e.g., a new unit was
    // derived at trail position 2).
    solver.mark_trail_affected(2);
    solver.rebuild_watches();

    assert_eq!(
        solver.qhead, 2,
        "rebuild_watches should rewind qhead to earliest_affected_trail_pos"
    );
    // Propagation from position 2 should succeed without conflict.
    assert!(solver.propagate().is_none());
}

/// Verify that `mark_trail_affected` correctly tracks the minimum position
/// across multiple calls.
#[test]
fn test_mark_trail_affected_tracks_minimum() {
    let mut solver: Solver = Solver::new(2);

    // Start with None.
    assert_eq!(solver.earliest_affected_trail_pos, None);

    // First mark: sets to 10.
    solver.mark_trail_affected(10);
    assert_eq!(solver.earliest_affected_trail_pos, Some(10));

    // Second mark at 5: should update to 5 (lower).
    solver.mark_trail_affected(5);
    assert_eq!(solver.earliest_affected_trail_pos, Some(5));

    // Third mark at 8: should keep 5 (lower).
    solver.mark_trail_affected(8);
    assert_eq!(solver.earliest_affected_trail_pos, Some(5));

    // Fourth mark at 0: should update to 0.
    solver.mark_trail_affected(0);
    assert_eq!(solver.earliest_affected_trail_pos, Some(0));
}

/// Verify that `apply_minimal_trail_rewind` records stats correctly for
/// the three rewind categories: skipped, partial, and full (#8095).
#[test]
fn test_apply_minimal_trail_rewind_records_stats() {
    let mut solver: Solver = Solver::new(5);
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);

    // Create a formula with several level-0 units.
    solver.add_clause(vec![Literal::positive(a)]);
    solver.add_clause(vec![Literal::positive(b)]);
    solver.add_clause(vec![Literal::positive(c)]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(solver.propagate().is_none());
    let trail_len = solver.trail.len();
    assert!(
        trail_len >= 3,
        "expected at least 3 trail entries from units"
    );

    // Case 1: no affected position -> skipped rewind.
    solver.earliest_affected_trail_pos = None;
    solver.apply_minimal_trail_rewind();
    assert_eq!(solver.qhead, trail_len);
    assert_eq!(solver.stats.trail_rewind_skipped, 1);
    assert_eq!(solver.stats.trail_rewind_partial, 0);
    assert_eq!(solver.stats.trail_rewind_full, 0);

    // Case 2: affected position 2 -> partial rewind.
    solver.earliest_affected_trail_pos = Some(2);
    solver.apply_minimal_trail_rewind();
    assert_eq!(solver.qhead, 2);
    assert_eq!(solver.stats.trail_rewind_skipped, 1);
    assert_eq!(solver.stats.trail_rewind_partial, 1);
    assert_eq!(solver.stats.trail_rewind_full, 0);
    assert_eq!(solver.stats.trail_rewind_saved_entries, 2);

    // Case 3: affected position 0 -> full rewind.
    solver.earliest_affected_trail_pos = Some(0);
    solver.apply_minimal_trail_rewind();
    assert_eq!(solver.qhead, 0);
    assert_eq!(solver.stats.trail_rewind_skipped, 1);
    assert_eq!(solver.stats.trail_rewind_partial, 1);
    assert_eq!(solver.stats.trail_rewind_full, 1);
    assert_eq!(solver.stats.trail_rewind_saved_entries, 2); // unchanged
}

#[test]
fn test_add_preserved_learned_sets_watches_and_enqueues_unit() {
    let mut solver: Solver = Solver::new(2);
    let x = Variable(0);
    let y = Variable(1);

    // Force x=true at level 0 so (¬x ∨ y) is unit and should enqueue y.
    solver.add_clause(vec![Literal::positive(x)]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(solver.propagate().is_none());

    let clause_idx = solver.arena.len();
    assert!(solver.add_preserved_learned(vec![Literal::negative(x), Literal::positive(y),]));

    let clause_ref = ClauseRef(clause_idx as u32);
    assert!(
        solver.arena.is_learned(clause_idx),
        "preserved clause must be marked learned"
    );
    assert_eq!(
        solver.watches.count_watches_for_clause(clause_ref),
        2,
        "preserved learned clause must be attached to two watch lists"
    );
    // AY keeps reasons at level 0 (unlike CaDiCaL which clears them) for
    // LRAT proof materialization (#6998). The important thing is that y IS
    // assigned (propagation happened).
    assert_eq!(
        solver.lit_val(Literal::positive(y)),
        1,
        "preserved learned clause should participate in unit propagation"
    );
    assert_watch_invariant_for_all_active_clauses(&solver, "add_preserved_learned");
}

#[test]
fn test_propagate_conflict_updates_no_conflict_until_binary() {
    let mut solver: Solver = Solver::new(2);
    let x = Variable(0);
    let y = Variable(1);

    solver.add_clause(vec![Literal::negative(x), Literal::negative(y)]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    solver.decide(Literal::positive(y));
    solver.enqueue(Literal::positive(x), None);
    solver.no_conflict_until = solver.trail.len();

    assert!(solver.propagate().is_some(), "expected binary conflict");
    assert_eq!(
        solver.no_conflict_until, 0,
        "binary conflict must reset no_conflict_until to level-1 trail start"
    );
}

#[test]
fn test_propagate_conflict_updates_no_conflict_until_non_binary() {
    let mut solver: Solver = Solver::new(3);
    let x = Variable(0);
    let y = Variable(1);
    let z = Variable(2);

    solver.add_clause(vec![
        Literal::negative(x),
        Literal::negative(y),
        Literal::negative(z),
    ]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    solver.decide(Literal::positive(x));
    solver.enqueue(Literal::positive(y), None);
    solver.enqueue(Literal::positive(z), None);
    solver.no_conflict_until = solver.trail.len();

    assert!(solver.propagate().is_some(), "expected non-binary conflict");
    assert_eq!(
        solver.no_conflict_until, 0,
        "non-binary conflict must reset no_conflict_until to level-1 trail start"
    );
}

#[test]
fn test_search_propagate_direct_unit_chain() {
    let mut solver: Solver = Solver::new(3);
    let x = Variable(0);
    let y = Variable(1);
    let z = Variable(2);

    solver.add_clause(vec![Literal::positive(x)]);
    solver.add_clause(vec![Literal::negative(x), Literal::positive(y)]);
    solver.add_clause(vec![Literal::negative(y), Literal::positive(z)]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    let conflict = solver.search_propagate();
    assert!(
        conflict.is_none(),
        "search propagation should not conflict on a simple implication chain"
    );
    assert_eq!(solver.lit_val(Literal::positive(x)), 1);
    assert_eq!(solver.lit_val(Literal::positive(y)), 1);
    assert_eq!(solver.lit_val(Literal::positive(z)), 1);
    // Level-0 propagated units retain their reason clause for LRAT
    // proof chain construction (#6998). Unlike CaDiCaL which clears
    // level-0 reasons, AY uses lazy proof materialization that needs
    // the reason clause to build LRAT chains for level-0 units
    // discovered during ChrBT propagation.
    assert_eq!(
        solver.var_data[y.index()].level,
        0,
        "y should be assigned at level 0"
    );
    assert!(
        solver.var_reason(y.index()).is_some(),
        "level-0 propagated y retains reason for LRAT (#6998)"
    );
    assert_eq!(
        solver.var_data[z.index()].level,
        0,
        "z should be assigned at level 0"
    );
    assert!(
        solver.var_reason(z.index()).is_some(),
        "level-0 propagated z retains reason for LRAT (#6998)"
    );
}

#[test]
fn test_enqueue_uses_reason_max_level_under_chrono() {
    let mut solver: Solver = Solver::new(3);
    solver.chrono_enabled = true;

    let a = Variable(0);
    let b = Variable(1);

    solver.add_clause(vec![Literal::negative(a), Literal::positive(b)]);
    let reason = ClauseRef(0);

    solver.decide(Literal::positive(a));
    solver.qhead = solver.trail.len();
    solver.decision_level = 2;
    solver.trail_lim.push(1);

    solver.enqueue(Literal::positive(b), Some(reason));

    assert_eq!(
        solver.var_data[b.index()].level,
        1,
        "chrono propagate should use max reason level instead of current decision level"
    );
    assert_eq!(
        solver.var_reason(b.index()),
        Some(reason),
        "non-zero assignment level must retain the reason clause"
    );
}

#[test]
fn test_enqueue_clamps_stale_reason_levels_at_root() {
    let mut solver: Solver = Solver::new(2);
    solver.chrono_enabled = true;

    let a = Variable(0);
    let b = Variable(1);

    solver.add_clause(vec![Literal::negative(a), Literal::positive(b)]);
    let reason = ClauseRef(0);

    // Simulate chrono-BT residue: `a` is still assigned true in vals[] so
    // the reason literal ¬a is false, but the stored level is stale relative
    // to the current root decision level.
    solver.vals[Literal::positive(a).index()] = 1;
    solver.vals[Literal::negative(a).index()] = -1;
    solver.var_data[a.index()].level = 1;
    solver.decision_level = 0;

    solver.enqueue(Literal::positive(b), Some(reason));

    assert_eq!(
        solver.var_data[b.index()].level,
        0,
        "root-level enqueue must clamp stale reason levels to decision_level"
    );
}

#[test]
fn test_search_propagate_binary_delete_unlinks_watches_before_flush() {
    let mut solver: Solver = Solver::new(2);
    let x = Variable(0);
    let y = Variable(1);
    let clause_ref = ClauseRef(0);
    let has_watch = |solver: &Solver, lit: Literal| {
        let watch_list = solver.watches.get_watches(lit);
        (0..watch_list.len()).any(|wi| watch_list.clause_ref(wi) == clause_ref)
    };

    solver.add_clause(vec![Literal::negative(x), Literal::positive(y)]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert!(
        has_watch(&solver, Literal::negative(x)),
        "binary clause should watch ¬x before deletion",
    );
    assert!(
        has_watch(&solver, Literal::positive(y)),
        "binary clause should watch y before deletion",
    );

    // Delete the binary clause without flushing watches. Binary watches must
    // be unlinked eagerly (#4924), unlike long-clause watches.
    let deleted = solver.delete_clause_unchecked(0, mutate::ReasonPolicy::Skip);
    assert_eq!(deleted, mutate::DeleteResult::Deleted);
    assert!(!solver.arena.is_active(0));
    assert!(
        !has_watch(&solver, Literal::negative(x)),
        "binary delete must eagerly unlink watch on ¬x",
    );
    assert!(
        !has_watch(&solver, Literal::positive(y)),
        "binary delete must eagerly unlink watch on y",
    );

    solver.decide(Literal::positive(x));
    let conflict = solver.search_propagate();
    assert!(
        conflict.is_none(),
        "deleted binary clause should not cause conflict before flush",
    );
    assert_eq!(
        solver.lit_val(Literal::positive(y)),
        0,
        "deleted binary watcher must not propagate y before flush",
    );
    assert_eq!(
        solver.var_reason(y.index()),
        None,
        "deleted binary watcher must not become y's reason",
    );

    // Flushing should preserve the same result (already unlinked).
    solver.backtrack(0);
    solver.flush_watches();
    solver.decide(Literal::positive(x));
    let conflict_after_flush = solver.search_propagate();
    assert!(conflict_after_flush.is_none());
    assert_eq!(
        solver.lit_val(Literal::positive(y)),
        0,
        "flushing should not change already-unlinked binary propagation behavior"
    );
}

#[test]
fn test_safe_bcp_binary_prefix_conflict_preserves_unscanned_long_suffix() {
    let mut solver: Solver = Solver::new(4);
    let x = Variable(0);
    let y = Variable(1);
    let z = Variable(2);
    let w = Variable(3);
    let false_lit = Literal::negative(x);

    solver.set_bcp_telemetry_enabled(true);
    solver.add_clause(vec![Literal::negative(x), Literal::negative(y)]);
    solver.add_clause(vec![
        Literal::negative(x),
        Literal::positive(z),
        Literal::positive(w),
    ]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    let before_len = solver.watches.len_of(false_lit);
    assert_eq!(
        before_len, 2,
        "test requires one binary prefix entry and one long suffix entry"
    );
    assert!(
        solver.watches.is_binary(false_lit, 0),
        "first watches[¬x] entry should be binary"
    );
    assert!(
        !solver.watches.is_binary(false_lit, 1),
        "second watches[¬x] entry should be long"
    );
    let before_entries: Vec<(u32, u64)> = (0..before_len)
        .map(|i| {
            (
                solver.watches.blocker_raw(false_lit, i),
                solver.watches.clause_raw(false_lit, i),
            )
        })
        .collect();

    solver.decide(Literal::positive(y));
    solver.qhead = solver.trail.len();
    solver.decide(Literal::positive(z));
    solver.qhead = solver.trail.len();
    solver.decide(Literal::positive(x));

    solver.deferred_watch_list.push(0xA11CE, 0xBEEF);
    let blocker_hits_before = solver.stats.bcp_blocker_fastpath_hits;
    let conflict = solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    assert!(conflict.is_some(), "binary conflict expected");
    assert_eq!(
        solver.deferred_watch_list.len(),
        1,
        "in-place binary-prefix conflict should not copy through the deferred buffer"
    );
    assert_eq!(solver.deferred_watch_list.blocker_raw(0), 0xA11CE);
    assert_eq!(solver.deferred_watch_list.clause_raw(0), 0xBEEF);
    assert_eq!(
        solver.stats.bcp_blocker_fastpath_hits, blocker_hits_before,
        "binary-prefix conflict should return before scanning the long suffix blocker"
    );
    assert_eq!(
        solver.stats.bcp_binary_path_hits, 1,
        "binary prefix should account for exactly the conflicting binary watcher"
    );
    solver.watches.debug_assert_binary_first();

    let after_len = solver.watches.len_of(false_lit);
    let after_entries: Vec<(u32, u64)> = (0..after_len)
        .map(|i| {
            (
                solver.watches.blocker_raw(false_lit, i),
                solver.watches.clause_raw(false_lit, i),
            )
        })
        .collect();
    assert_eq!(
        before_entries, after_entries,
        "binary-prefix conflict must preserve the untouched long suffix"
    );
}

#[test]
fn test_safe_bcp_inplace_binary_prefix_then_deferred_long_suffix() {
    let mut solver: Solver = Solver::new(4);
    let x = Variable(0);
    let y = Variable(1);
    let z = Variable(2);
    let w = Variable(3);
    let false_lit = Literal::negative(x);
    let replacement_lit = Literal::positive(w);

    solver.add_clause(vec![Literal::negative(x), Literal::positive(z)]);
    solver.add_clause(vec![
        Literal::negative(x),
        Literal::positive(y),
        replacement_lit,
    ]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert_eq!(
        solver.watches.len_of(false_lit),
        2,
        "test requires a binary prefix entry and one long suffix entry"
    );
    assert!(solver.watches.is_binary(false_lit, 0));
    assert!(!solver.watches.is_binary(false_lit, 1));
    let long_clause_ref = solver.watches.clause_ref(false_lit, 1);

    solver.decide(Literal::negative(y));
    solver.qhead = solver.trail.len();
    solver.decide(Literal::positive(x));

    let conflict = solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    assert!(
        conflict.is_none(),
        "binary prefix plus long suffix should not conflict"
    );
    assert_eq!(
        solver.lit_val(Literal::positive(z)),
        1,
        "in-place binary prefix should still propagate binary units"
    );
    assert_eq!(
        solver.watches.len_of(false_lit),
        1,
        "deferred long suffix should remove the replaced long watcher"
    );
    assert!(
        solver.watches.is_binary(false_lit, 0),
        "remaining false-literal watcher should be the binary prefix entry"
    );
    let replacement_has_long_watch = (0..solver.watches.len_of(replacement_lit))
        .any(|i| solver.watches.clause_ref(replacement_lit, i) == long_clause_ref);
    assert!(
        replacement_has_long_watch,
        "long suffix should still run after the in-place binary prefix and move the watch"
    );
    solver.watches.debug_assert_binary_first();
}

fn bcp_saved_pos_test_solver() -> Solver {
    let mut solver = Solver::new(6);
    let pos = |i: u32| Literal::positive(Variable(i));
    assert!(solver.add_clause(vec![pos(0), pos(1), pos(2), pos(3), pos(4), pos(5),]));
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    solver
}

fn only_active_clause_idx(solver: &Solver) -> usize {
    let mut active = solver.arena.active_indices();
    let clause_idx = active.next().expect("test clause");
    assert!(
        active.next().is_none(),
        "saved_pos tests expect exactly one active clause"
    );
    clause_idx
}

fn bcp_len_test_solver(clause_len: usize) -> (Solver, usize) {
    let mut solver = Solver::new(clause_len);
    let clause: Vec<Literal> = (0..clause_len)
        .map(|i| Literal::positive(Variable(i as u32)))
        .collect();
    assert!(solver.add_clause(clause));
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    let clause_idx = only_active_clause_idx(&solver);
    (solver, clause_idx)
}

fn bcp_long_bucket_index(labels: &[&str; 5], label: &str) -> usize {
    labels
        .iter()
        .position(|&candidate| candidate == label)
        .expect("BCP long-scan bucket label")
}

fn enable_bcp_learned_1963_blocker_cert_elision_for_test(solver: &mut Solver) {
    solver
        .stats
        .set_bcp_learned_1963_blocker_cert_elision_test_enabled(true);
}

fn enable_bcp_learned_1963_blocker_cert_shadow_for_test(solver: &mut Solver) {
    solver
        .stats
        .set_bcp_learned_1963_blocker_cert_shadow_test_enabled(true);
}

fn enable_bcp_learned_1963_blocker_cert_false_reject_demote_for_test(solver: &mut Solver) {
    solver
        .stats
        .set_bcp_learned_1963_blocker_cert_false_reject_demote_test_enabled(true);
}

fn seed_bcp_learned_1963_blocker_cert_repeats(
    solver: &mut Solver,
    clause_idx: usize,
    position: usize,
    literal_raw: u32,
    repeats: u8,
) {
    for _ in 0..repeats {
        solver.stats.record_bcp_learned_1963_blocker_cert_populate(
            clause_idx,
            position,
            literal_raw,
            true,
        );
    }
}

fn seed_bcp_learned_1963_blocker_cert(
    solver: &mut Solver,
    clause_idx: usize,
    position: usize,
    literal_raw: u32,
) {
    seed_bcp_learned_1963_blocker_cert_repeats(
        solver,
        clause_idx,
        position,
        literal_raw,
        BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS,
    );
}

fn stage_bcp_blocker_cert_false_start_wrap(
    solver: &mut Solver,
    clause_idx: usize,
    clause_len: usize,
    saved_pos: usize,
    true_slot: usize,
) {
    assert!(saved_pos > true_slot);
    assert!(true_slot >= 3);
    assert!(saved_pos < clause_len);

    solver.decide(Literal::positive(Variable(true_slot as u32)));
    solver.qhead = solver.trail.len();
    solver.decide(Literal::negative(Variable(2)));
    solver.qhead = solver.trail.len();
    for slot in saved_pos..clause_len {
        if slot != true_slot {
            solver.decide(Literal::negative(Variable(slot as u32)));
            solver.qhead = solver.trail.len();
        }
    }
    solver.arena.set_saved_pos(clause_idx, saved_pos);
}

fn run_bcp_blocker_cert_two_watch_route(
    clause_len: usize,
    learned: bool,
    gate_enabled: bool,
    seed_cert: bool,
) -> Solver {
    let saved_pos = 20.min(clause_len - 2);
    let true_slot = 3usize;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, learned);
    if gate_enabled {
        enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut solver);
    }
    stage_bcp_blocker_cert_false_start_wrap(
        &mut solver,
        clause_idx,
        clause_len,
        saved_pos,
        true_slot,
    );
    if seed_cert {
        solver.stats.record_bcp_learned_1963_blocker_cert_populate(
            clause_idx,
            true_slot,
            Literal::positive(Variable(true_slot as u32)).0,
            true,
        );
    }

    solver.decide(Literal::negative(Variable(0)));
    assert!(
        solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
        "first watched-literal scan should find the true wrapped tail"
    );
    solver.decide(Literal::negative(Variable(1)));
    assert!(
        solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
        "second watched-literal scan should stay satisfied"
    );
    solver
}

#[derive(Debug, PartialEq, Eq)]
struct BcpBlockerCertTrueReplacementObservation {
    watched_literals: (Literal, Literal),
    saved_pos: usize,
    second_watch_blocker: Literal,
}

fn bcp_blocker_cert_true_replacement_observation(
    solver: &Solver,
    clause_idx: usize,
) -> BcpBlockerCertTrueReplacementObservation {
    let watched_lit = Literal::positive(Variable(1));
    let clause_ref = ClauseRef::new(clause_idx as u32);
    let second_watch_blocker = (0..solver.watches.len_of(watched_lit))
        .find_map(|watch_idx| {
            (solver.watches.clause_ref(watched_lit, watch_idx) == clause_ref)
                .then(|| solver.watches.blocker(watched_lit, watch_idx))
        })
        .expect("second watched-literal entry for blocker-cert test clause");

    BcpBlockerCertTrueReplacementObservation {
        watched_literals: solver.arena.watched_literals(clause_idx),
        saved_pos: solver.arena.saved_pos(clause_idx),
        second_watch_blocker,
    }
}

fn bcp_blocker_cert_clause_lits(solver: &Solver, clause_idx: usize) -> Vec<Literal> {
    (0..solver.arena.len_of(clause_idx))
        .map(|idx| solver.arena.literal(clause_idx, idx))
        .collect()
}

fn run_bcp_blocker_cert_repeated_true_replacement_case(
    false_saved_pos_reset_enabled: bool,
    blocker_cert_elision_enabled: bool,
) -> (Solver, usize, usize) {
    let clause_len = 32;
    let saved_pos = 20;
    let true_slot = 3usize;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    if false_saved_pos_reset_enabled {
        solver.set_bcp_learned_1963_false_saved_pos_reset_enabled(true);
    }
    if blocker_cert_elision_enabled {
        enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut solver);
    }
    stage_bcp_blocker_cert_false_start_wrap(
        &mut solver,
        clause_idx,
        clause_len,
        saved_pos,
        true_slot,
    );
    seed_bcp_learned_1963_blocker_cert_repeats(
        &mut solver,
        clause_idx,
        true_slot,
        Literal::positive(Variable(true_slot as u32)).0,
        BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS - 1,
    );

    solver.decide(Literal::negative(Variable(0)));
    assert!(
        solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
        "first watched-literal scan should find the true wrapped tail"
    );
    solver.arena.set_saved_pos(clause_idx, saved_pos);
    solver.decide(Literal::negative(Variable(1)));
    assert!(
        solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
        "second watched-literal scan should stay satisfied"
    );

    (solver, clause_idx, true_slot)
}

fn run_bcp_blocker_cert_wrapped_prefix_non_false_case(
    blocker_cert_elision_enabled: bool,
) -> (Solver, usize, usize, usize) {
    let clause_len = 32;
    let saved_pos = 20;
    let earlier_slot = 3usize;
    let cert_slot = 4usize;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    if blocker_cert_elision_enabled {
        enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut solver);
    }

    let cert_lit = Literal::positive(Variable(cert_slot as u32));
    solver.decide(cert_lit);
    solver.qhead = solver.trail.len();
    solver.decide(Literal::negative(Variable(2)));
    solver.qhead = solver.trail.len();
    for slot in saved_pos..clause_len {
        solver.decide(Literal::negative(Variable(slot as u32)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, saved_pos);
    seed_bcp_learned_1963_blocker_cert(&mut solver, clause_idx, cert_slot, cert_lit.0);

    solver.decide(Literal::negative(Variable(0)));
    assert!(
        solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
        "fallback scan should preserve normal BCP behavior"
    );

    (solver, clause_idx, earlier_slot, cert_slot)
}

fn add_learned_1963_clause_with_blocker_cert(solver: &mut Solver) -> (usize, Literal) {
    let lits: Vec<Literal> = (0..32)
        .map(|i| Literal::positive(Variable(i as u32)))
        .collect();
    let clause_idx = solver.add_clause_db(&lits, true);
    let cert_lit = lits[3];
    solver
        .stats
        .record_bcp_learned_1963_blocker_cert_populate(clause_idx, 3, cert_lit.0, true);
    (clause_idx, cert_lit)
}

#[test]
fn test_bcp_saved_pos_advance_default_off_keeps_replacement_slot() {
    let mut solver = bcp_saved_pos_test_solver();
    let clause_idx = only_active_clause_idx(&solver);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        2,
        "default policy should keep saved_pos on the replacement slot"
    );
}

#[test]
fn test_bcp_len6_8_saved_pos_wrap_specialization_counts_steps() {
    for clause_len in 6..=8 {
        let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
        let saved_pos = clause_len - 2;

        for slot in saved_pos..clause_len {
            solver.decide(Literal::negative(Variable(slot as u32)));
            solver.qhead = solver.trail.len();
        }
        solver.arena.set_saved_pos(clause_idx, saved_pos);
        solver.set_bcp_telemetry_enabled(true);

        solver.decide(Literal::negative(Variable(0)));
        assert!(
            solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
            "len-{clause_len} wraparound replacement should not conflict"
        );

        assert_eq!(
            solver.arena.saved_pos(clause_idx),
            2,
            "len-{clause_len} replacement should wrap to slot 2"
        );
        assert_eq!(
            solver.arena.literal(clause_idx, 0),
            Literal::positive(Variable(2)),
            "len-{clause_len} replacement slot should become watched"
        );
        assert_eq!(
            solver.bcp_stats().2,
            3,
            "len-{clause_len} should scan saved slot, tail, then wrapped slot"
        );
        let long_stats = solver.bcp_long_scan_stats();
        let len6_8 = bcp_long_bucket_index(&long_stats.bucket_labels, "6-8");
        assert_eq!(long_stats.scan_steps_binary, 0);
        assert_eq!(long_stats.scan_steps_non_binary, 3);
        assert_eq!(long_stats.scan_steps_original, 3);
        assert_eq!(long_stats.scan_steps_learned, 0);
        assert_eq!(long_stats.scan_steps_by_len[len6_8], 3);
        assert_eq!(long_stats.original_scan_steps_by_len[len6_8], 3);
        assert_eq!(long_stats.learned_scan_steps_by_len[len6_8], 0);

        let saved_stats = solver.bcp_saved_pos_stats();
        assert_eq!(saved_stats.long_scans, 1);
        assert_eq!(saved_stats.long_start_false, 1);
        assert_eq!(saved_stats.long_found_unassigned, 1);
        assert_eq!(saved_stats.long_found_true, 0);
        assert_eq!(saved_stats.long_no_replacement, 0);
    }
}

#[test]
fn test_bcp_len6_8_false_saved_start_skip_counts_steps() {
    for clause_len in 6..=8 {
        let saved_pos = clause_len - 2;
        let replacement_pos = saved_pos + 1;
        let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
        solver.arena.set_learned(clause_idx, true);
        solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);

        for slot in 2..=saved_pos {
            solver.decide(Literal::negative(Variable(slot as u32)));
            solver.qhead = solver.trail.len();
        }
        solver.arena.set_saved_pos(clause_idx, saved_pos);
        solver.set_bcp_telemetry_enabled(true);

        solver.decide(Literal::negative(Variable(0)));
        assert!(
            solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
            "len-{clause_len} learned false-start skip should not conflict"
        );

        assert_eq!(
            solver.arena.literal(clause_idx, 0),
            Literal::positive(Variable(replacement_pos as u32)),
            "len-{clause_len} should skip the known-false saved start and use the next tail"
        );
        assert_eq!(
            solver.arena.saved_pos(clause_idx),
            replacement_pos,
            "len-{clause_len} should record the replacement slot"
        );
        assert_eq!(
            solver.bcp_stats().2,
            (replacement_pos - 2) as u64,
            "len-{clause_len} should not recount the known-false saved-start slot"
        );

        let long_stats = solver.bcp_long_scan_stats();
        let len6_8 = bcp_long_bucket_index(&long_stats.bucket_labels, "6-8");
        assert_eq!(
            long_stats.scan_steps_by_len[len6_8],
            (replacement_pos - 2) as u64
        );
        assert_eq!(
            long_stats.learned_scan_steps_by_len[len6_8],
            (replacement_pos - 2) as u64
        );

        let saved_stats = solver.bcp_saved_pos_stats();
        assert_eq!(saved_stats.long_scans, 1);
        assert_eq!(saved_stats.long_start_false, 1);
        assert_eq!(saved_stats.long_found_unassigned, 1);
    }
}

#[test]
fn test_bcp_long_scan_counters_len18_found_replacement_default_on() {
    let (mut solver, _) = bcp_len_test_solver(18);
    solver.set_bcp_telemetry_enabled(true);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    let stats = solver.bcp_long_scan_stats();
    let len18 = bcp_long_bucket_index(&stats.bucket_labels, "18");
    assert_eq!(stats.scans_by_len[len18], 1);
    assert_eq!(stats.found_replacement_by_len[len18], 1);
    assert_eq!(stats.found_unassigned_by_len[len18], 1);
    assert_eq!(stats.found_true_by_len[len18], 0);
    assert_eq!(stats.no_replacement_by_len[len18], 0);
    assert_eq!(stats.unit_by_len[len18], 0);
    assert_eq!(stats.conflict_by_len[len18], 0);
    assert_eq!(stats.learned_scans_by_len[len18], 0);
    assert_eq!(stats.scan_steps_binary, 0);
    assert_eq!(stats.scan_steps_non_binary, 1);
    assert_eq!(stats.scan_steps_original, 1);
    assert_eq!(stats.scan_steps_learned, 0);
    assert_eq!(stats.scan_steps_by_len[len18], 1);
    assert_eq!(stats.original_scan_steps_by_len[len18], 1);
    assert_eq!(stats.learned_scan_steps_by_len[len18], 0);
}

#[test]
fn test_bcp_len18_false_saved_pos_reset_scans_from_first_tail() {
    let (mut solver, clause_idx) = bcp_len_test_solver(18);

    solver.decide(Literal::negative(Variable(17)));
    solver.qhead = solver.trail.len();
    solver.arena.set_saved_pos(clause_idx, 17);
    solver.set_bcp_telemetry_enabled(true);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.literal(clause_idx, 0),
        Literal::positive(Variable(2)),
        "len-18 false saved-position reset should choose the first tail slot"
    );
    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        2,
        "len-18 false saved-position reset should record the replacement slot"
    );
    assert_eq!(
        solver.bcp_stats().2,
        1,
        "len-18 false saved-position reset should skip the stale saved-start slot"
    );
    let saved_stats = solver.bcp_saved_pos_stats();
    assert_eq!(saved_stats.len18_scans, 1);
    assert_eq!(saved_stats.len18_start_false, 1);
    assert_eq!(saved_stats.len18_found_unassigned, 1);
    assert_eq!(saved_stats.len18_found_true, 0);
    assert_eq!(saved_stats.len18_no_replacement, 0);
}

#[test]
fn test_bcp_len18_false_saved_pos_reset_skips_known_false_saved_start() {
    let clause_len = 18;
    let saved_pos = 8;
    let replacement_pos = saved_pos + 1;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);

    for slot in 2..=saved_pos {
        solver.decide(Literal::negative(Variable(slot as u32)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, saved_pos);
    solver.set_bcp_telemetry_enabled(true);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.literal(clause_idx, 0),
        Literal::positive(Variable(replacement_pos as u32)),
        "len-18 reset should skip the known-false saved slot and use the next non-false tail"
    );
    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        replacement_pos,
        "len-18 reset should record the actual replacement slot"
    );
    assert_eq!(
        solver.bcp_stats().2,
        (replacement_pos - 2) as u64,
        "replacement scan should not recount the known-false saved-start slot"
    );
    let saved_stats = solver.bcp_saved_pos_stats();
    assert_eq!(saved_stats.len18_scans, 1);
    assert_eq!(saved_stats.len18_start_false, 1);
    assert_eq!(saved_stats.len18_found_unassigned, 1);

    let long_stats = solver.bcp_long_scan_stats();
    let len18 = bcp_long_bucket_index(&long_stats.bucket_labels, "18");
    assert_eq!(
        long_stats.scan_steps_by_len[len18],
        (replacement_pos - 2) as u64
    );
}

#[test]
fn test_bcp_learned_1963_false_saved_pos_reset_reuses_unassigned_saved_start() {
    let clause_len = 32;
    let saved_pos = 12;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_telemetry_enabled(true);
    solver.set_bcp_learned_1963_false_saved_pos_reset_enabled(true);

    for slot in 2..saved_pos {
        solver.decide(Literal::negative(Variable(slot as u32)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, saved_pos);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.literal(clause_idx, 0),
        Literal::positive(Variable(saved_pos as u32)),
        "the sampled saved-start literal should become the replacement"
    );
    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        saved_pos,
        "saved_pos should stay on the sampled unassigned replacement"
    );
    assert_eq!(
        solver.bcp_stats().2,
        1,
        "saved-start reuse should charge exactly the sampled tail slot"
    );

    let long_stats = solver.bcp_long_scan_stats();
    let bucket = bcp_long_bucket_index(&long_stats.bucket_labels, "19-63");
    assert_eq!(long_stats.scan_steps_by_len[bucket], 1);
    assert_eq!(long_stats.learned_scan_steps_by_len[bucket], 1);

    let saved_stats = solver.bcp_saved_pos_stats();
    assert_eq!(saved_stats.long_scans, 1);
    assert_eq!(saved_stats.long_start_false, 0);
    assert_eq!(saved_stats.long_found_unassigned, 1);
    assert_eq!(saved_stats.long_found_true, 0);
    assert_eq!(saved_stats.long_no_replacement, 0);
}

#[test]
fn test_bcp_long_scan_counters_len18_learned_no_replacement_unit() {
    let (mut solver, clause_idx) = bcp_len_test_solver(18);
    solver.set_bcp_telemetry_enabled(true);
    solver.arena.set_learned(clause_idx, true);

    for var in 2..18 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    let stats = solver.bcp_long_scan_stats();
    let len18 = bcp_long_bucket_index(&stats.bucket_labels, "18");
    assert_eq!(stats.scans_by_len[len18], 1);
    assert_eq!(stats.found_replacement_by_len[len18], 0);
    assert_eq!(stats.no_replacement_by_len[len18], 1);
    assert_eq!(stats.unit_by_len[len18], 1);
    assert_eq!(stats.conflict_by_len[len18], 0);
    assert_eq!(stats.learned_scans_by_len[len18], 1);
    assert_eq!(stats.learned_no_replacement_by_len[len18], 1);
    assert_eq!(stats.learned_unit_by_len[len18], 1);
    assert_eq!(stats.learned_conflict_by_len[len18], 0);
    assert_eq!(stats.scan_steps_binary, 0);
    assert_eq!(stats.scan_steps_non_binary, 16);
    assert_eq!(stats.scan_steps_original, 0);
    assert_eq!(stats.scan_steps_learned, 16);
    assert_eq!(stats.scan_steps_by_len[len18], 16);
    assert_eq!(stats.original_scan_steps_by_len[len18], 0);
    assert_eq!(stats.learned_scan_steps_by_len[len18], 16);
}

#[test]
fn test_bcp_no_replacement_unit_refreshes_blocker_to_implied_watch() {
    let (mut solver, _) = bcp_len_test_solver(6);
    let watch_lit = Literal::positive(Variable(0));
    let implied_watch = Literal::positive(Variable(1));
    let stale_false_blocker = Literal::positive(Variable(2));

    for var in 2..6 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }

    let clause_raw = solver.watches.clause_raw(watch_lit, 0);
    solver
        .watches
        .set_entry(watch_lit, 0, stale_false_blocker.0, clause_raw);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.watches.blocker(watch_lit, 0),
        implied_watch,
        "no-replacement unit path should refresh the kept blocker to the implied watch"
    );
    assert_eq!(
        solver.lit_val(implied_watch),
        1,
        "the refreshed blocker should be the literal implied by the unit clause"
    );
}

#[test]
fn test_bcp_learned_1963_no_replacement_unit_refreshes_blocker_by_default() {
    let (mut solver, clause_idx) = bcp_len_test_solver(32);
    solver.arena.set_learned(clause_idx, true);
    let watch_lit = Literal::positive(Variable(0));
    let implied_watch = Literal::positive(Variable(1));
    let stale_false_blocker = Literal::positive(Variable(2));

    for var in 2..32 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }

    let clause_raw = solver.watches.clause_raw(watch_lit, 0);
    solver
        .watches
        .set_entry(watch_lit, 0, stale_false_blocker.0, clause_raw);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.watches.blocker(watch_lit, 0),
        implied_watch,
        "default W58 no-replacement unit path should refresh learned 19-63 blocker"
    );
    assert_eq!(solver.lit_val(implied_watch), 1);
}

#[test]
fn test_bcp_learned_1963_no_replacement_unit_refresh_disable_keeps_blocker() {
    let (mut solver, clause_idx) = bcp_len_test_solver(32);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_disable_learned_1963_no_replacement_unit_blocker_refresh_enabled(true);
    let watch_lit = Literal::positive(Variable(0));
    let implied_watch = Literal::positive(Variable(1));
    let stale_false_blocker = Literal::positive(Variable(2));

    for var in 2..32 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }

    let clause_raw = solver.watches.clause_raw(watch_lit, 0);
    solver
        .watches
        .set_entry(watch_lit, 0, stale_false_blocker.0, clause_raw);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.watches.blocker(watch_lit, 0),
        stale_false_blocker,
        "enabled experiment should keep the stale blocker for learned 19-63 unit no-replacement"
    );
    assert_eq!(
        solver.lit_val(implied_watch),
        1,
        "disabling blocker refresh must not change the implied unit"
    );
}

#[test]
fn test_bcp_long_scan_counters_len18_no_replacement_conflict() {
    let (mut solver, _) = bcp_len_test_solver(18);
    solver.set_bcp_telemetry_enabled(true);

    for var in 1..18 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_some());

    let stats = solver.bcp_long_scan_stats();
    let len18 = bcp_long_bucket_index(&stats.bucket_labels, "18");
    assert_eq!(stats.scans_by_len[len18], 1);
    assert_eq!(stats.found_replacement_by_len[len18], 0);
    assert_eq!(stats.no_replacement_by_len[len18], 1);
    assert_eq!(stats.unit_by_len[len18], 0);
    assert_eq!(stats.conflict_by_len[len18], 1);
    assert_eq!(stats.scan_steps_binary, 0);
    assert_eq!(stats.scan_steps_non_binary, 16);
    assert_eq!(stats.scan_steps_original, 16);
    assert_eq!(stats.scan_steps_learned, 0);
    assert_eq!(stats.scan_steps_by_len[len18], 16);
    assert_eq!(stats.original_scan_steps_by_len[len18], 16);
    assert_eq!(stats.learned_scan_steps_by_len[len18], 0);
}

#[test]
fn test_bcp_long_scan_counters_blocker_short_circuit_not_scanned() {
    let (mut solver, _) = bcp_len_test_solver(18);
    solver.set_bcp_telemetry_enabled(true);

    solver.decide(Literal::positive(Variable(1)));
    solver.qhead = solver.trail.len();
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    let stats = solver.bcp_long_scan_stats();
    assert_eq!(stats.long_blocker_fastpath_hits, 1);
    assert_eq!(stats.scans_by_len.iter().sum::<u64>(), 0);
    assert_eq!(stats.scan_steps_non_binary, 0);
    assert_eq!(stats.scan_steps_by_len.iter().sum::<u64>(), 0);
}

#[test]
fn test_bcp_satisfied_other_watch_blocker_miss_skips_saved_pos_scan() {
    let (mut solver, clause_idx) = bcp_len_test_solver(6);
    let watch_lit = Literal::positive(Variable(0));
    let other_watch = Literal::positive(Variable(1));
    let stale_blocker = Literal::positive(Variable(2));

    solver.decide(other_watch);
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    solver.arena.set_saved_pos(clause_idx, 4);
    let clause_raw = solver.watches.clause_raw(watch_lit, 0);
    solver
        .watches
        .set_entry(watch_lit, 0, stale_blocker.0, clause_raw);
    solver.set_bcp_telemetry_enabled(true);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.watches.blocker(watch_lit, 0),
        other_watch,
        "blocker miss with satisfied other watch should refresh blocker"
    );
    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        4,
        "satisfied other-watch path must not rewrite saved_pos"
    );
    assert_eq!(
        solver.bcp_stats(),
        (0, 0, 0),
        "satisfied other-watch path should skip replacement scanning"
    );
    assert_eq!(
        solver.bcp_saved_pos_stats().long_scans,
        0,
        "satisfied other-watch path should skip saved-position telemetry"
    );
    assert_eq!(
        solver
            .bcp_long_scan_stats()
            .scans_by_len
            .iter()
            .sum::<u64>(),
        0,
        "satisfied other-watch path should not record long-clause scan buckets"
    );
}

#[test]
fn test_bcp_len3_4_5_short_replacement_skips_saved_pos_telemetry() {
    for clause_len in 3..=5 {
        let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
        solver.set_bcp_telemetry_enabled(true);

        solver.decide(Literal::negative(Variable(0)));
        assert!(
            solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
            "len-{clause_len} short replacement should not conflict"
        );

        assert_eq!(
            solver.arena.literal(clause_idx, 0),
            Literal::positive(Variable(2)),
            "len-{clause_len} first tail literal should become watched"
        );
        assert_eq!(
            solver.bcp_stats().2,
            1,
            "len-{clause_len} should scan exactly one tail literal"
        );
        assert_eq!(
            solver.bcp_saved_pos_stats().long_scans,
            0,
            "len-{clause_len} short replacement should not use saved_pos telemetry"
        );
    }
}

#[test]
fn test_bcp_len6_saved_pos_boundary_records_telemetry() {
    let (mut solver, clause_idx) = bcp_len_test_solver(6);

    solver.decide(Literal::negative(Variable(5)));
    solver.qhead = solver.trail.len();
    solver.arena.set_saved_pos(clause_idx, 5);
    solver.set_bcp_telemetry_enabled(true);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        2,
        "len-6 saved_pos boundary should wrap to the first tail slot"
    );
    assert_eq!(
        solver.bcp_stats().2,
        2,
        "len-6 boundary should scan saved slot then wrapped slot"
    );
    let saved_stats = solver.bcp_saved_pos_stats();
    assert_eq!(saved_stats.long_scans, 1);
    assert_eq!(saved_stats.long_start_false, 1);
    assert_eq!(saved_stats.long_found_unassigned, 1);
    assert_eq!(saved_stats.long_found_true, 0);
    assert_eq!(saved_stats.long_no_replacement, 0);
}

#[test]
fn test_bcp_saved_pos_advance_unassigned_saved_pos_hit_stays_put() {
    let mut solver = bcp_saved_pos_test_solver();
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        2,
        "unassigned replacement at the current saved_pos should not advance saved_pos"
    );
}

#[test]
fn test_bcp_saved_pos_advance_unassigned_miss_advances_past_replacement() {
    let mut solver = bcp_saved_pos_test_solver();
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);

    solver.decide(Literal::negative(Variable(2)));
    solver.qhead = solver.trail.len();
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        4,
        "unassigned replacement after a saved_pos miss should advance past the replacement"
    );
}

#[test]
fn test_bcp_saved_pos_advance_ignores_original_clause() {
    let mut solver = bcp_saved_pos_test_solver();
    let clause_idx = only_active_clause_idx(&solver);
    solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);

    solver.decide(Literal::negative(Variable(2)));
    solver.qhead = solver.trail.len();
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        3,
        "default-off advance policy should not step past replacements in original clauses"
    );
}

#[test]
fn test_bcp_saved_pos_advance_guard_keeps_replacement_when_next_slot_false() {
    let mut solver = bcp_saved_pos_test_solver();
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);

    solver.decide(Literal::negative(Variable(2)));
    solver.qhead = solver.trail.len();
    solver.decide(Literal::negative(Variable(4)));
    solver.qhead = solver.trail.len();
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        3,
        "guarded advance should keep saved_pos on the replacement when the next tail slot is false"
    );
}

#[test]
fn test_bcp_saved_pos_advance_unassigned_last_tail_miss_wraps() {
    let mut solver = bcp_saved_pos_test_solver();
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);
    solver.arena.set_saved_pos(clause_idx, 4);

    solver.decide(Literal::negative(Variable(4)));
    solver.qhead = solver.trail.len();
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        2,
        "unassigned replacement at the last tail slot after a miss should wrap saved_pos to 2"
    );
}

#[test]
fn test_bcp_saved_pos_advance_leaves_satisfied_replacement_slot() {
    let mut solver = bcp_saved_pos_test_solver();
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);

    solver.decide(Literal::positive(Variable(3)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());
    solver.arena.set_saved_pos(clause_idx, 3);
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        3,
        "satisfied replacements should keep saved_pos on the replacement slot"
    );
}

#[test]
fn test_bcp_saved_pos_advance_leaves_no_replacement_unchanged() {
    let mut solver = bcp_saved_pos_test_solver();
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);

    for var in 2..6 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, 4);
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        4,
        "no-replacement unit path should not rewrite saved_pos"
    );
    assert_eq!(
        solver.lit_val(Literal::positive(Variable(1))),
        1,
        "no-replacement path should still propagate the other watched literal"
    );
}

#[test]
fn test_bcp_learned_no_replacement_saved_pos_update_default_off_keeps_saved_pos() {
    let mut solver = bcp_saved_pos_test_solver();
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);

    for var in 2..6 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, 4);
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        4,
        "default-off no-replacement gate must not rewrite saved_pos"
    );
    let long_stats = solver.bcp_long_scan_stats();
    assert!(
        !long_stats.learned_no_replacement_saved_pos_update_enabled,
        "default-off stats should report the gate disabled"
    );
    assert!(
        !long_stats.learned_no_replacement_scan_pressure_enabled,
        "scan-pressure instrumentation should also default off"
    );
    assert_eq!(
        long_stats
            .learned_no_replacement_saved_pos_eligible_by_len
            .iter()
            .sum::<u64>(),
        0,
        "default-off gate must not count eligible scans"
    );
    assert_eq!(
        long_stats
            .learned_no_replacement_scan_pressure_scans_by_len
            .iter()
            .sum::<u64>(),
        0,
        "default-off scan-pressure gate must not count learned no-replacement scans"
    );
    assert_eq!(
        long_stats.learned_1963_fsw_unit_by_lbd.iter().sum::<u64>(),
        0,
        "default-off scan-pressure gate must not count metadata buckets"
    );
    assert_eq!(
        long_stats
            .learned_1963_fsw_repeat_by_bucket
            .iter()
            .sum::<u64>(),
        0,
        "default-off scan-pressure gate must not count repeat buckets"
    );
}

#[test]
fn test_bcp_learned_no_replacement_scan_pressure_profiles_unit_scan_cost() {
    let mut solver = bcp_saved_pos_test_solver();
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_learned_no_replacement_scan_pressure_enabled(true);

    for var in 2..6 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, 4);
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        4,
        "scan-pressure profiling must not rewrite saved_pos"
    );
    assert_eq!(
        solver.lit_val(Literal::positive(Variable(1))),
        1,
        "scan-pressure profiling must preserve unit propagation"
    );

    let long_stats = solver.bcp_long_scan_stats();
    let bucket = bcp_long_bucket_index(&long_stats.bucket_labels, "6-8");
    assert!(long_stats.learned_no_replacement_scan_pressure_enabled);
    assert_eq!(
        long_stats.learned_no_replacement_scan_pressure_scans_by_len[bucket],
        1
    );
    assert_eq!(
        long_stats.learned_no_replacement_scan_pressure_steps_by_len[bucket], 4,
        "len-6 no-replacement scan should inspect all four tail literals"
    );
    assert_eq!(
        long_stats.learned_no_replacement_scan_pressure_start_false_by_len[bucket],
        1
    );
    assert_eq!(
        long_stats.learned_no_replacement_scan_pressure_wrapped_by_len[bucket],
        1
    );
    assert_eq!(
        long_stats.learned_no_replacement_scan_pressure_unit_by_len[bucket],
        1
    );
    assert_eq!(
        long_stats.learned_no_replacement_scan_pressure_conflict_by_len[bucket],
        0
    );
}

#[test]
fn test_bcp_learned_1963_false_start_wrap_pressure_metadata_buckets() {
    let mut unit_solver = bcp_len_test_solver(32).0;
    let unit_clause = only_active_clause_idx(&unit_solver);
    unit_solver.arena.set_learned(unit_clause, true);
    unit_solver.arena.set_lbd(unit_clause, 5);
    unit_solver.arena.set_used(unit_clause, 3);
    unit_solver.arena.set_saved_pos(unit_clause, 20);
    unit_solver.set_bcp_learned_no_replacement_scan_pressure_enabled(true);
    for var in 2..32 {
        unit_solver.decide(Literal::negative(Variable(var)));
        unit_solver.qhead = unit_solver.trail.len();
    }
    unit_solver.decide(Literal::negative(Variable(0)));
    assert!(unit_solver
        .propagate_bcp::<{ bcp_mode::SEARCH }>()
        .is_none());

    let unit_stats = unit_solver.bcp_long_scan_stats();
    let bucket = bcp_long_bucket_index(&unit_stats.bucket_labels, "19-63");
    assert_eq!(
        unit_stats.learned_no_replacement_scan_pressure_unit_by_len[bucket],
        1
    );
    assert_eq!(unit_stats.learned_1963_fsw_unit_by_lbd[1], 1);
    assert_eq!(unit_stats.learned_1963_fsw_unit_steps_by_lbd[1], 30);
    assert_eq!(unit_stats.learned_1963_fsw_unit_by_used[2], 1);
    assert_eq!(unit_stats.learned_1963_fsw_unit_steps_by_used[2], 30);
    assert_eq!(
        unit_stats
            .learned_1963_fsw_conflict_by_lbd
            .iter()
            .sum::<u64>(),
        0
    );
    assert_eq!(unit_stats.learned_1963_fsw_repeat_bucket_max, 1);
    assert_eq!(
        unit_stats
            .learned_1963_fsw_repeat_by_bucket
            .iter()
            .sum::<u64>(),
        1
    );

    let mut conflict_solver = bcp_len_test_solver(32).0;
    let conflict_clause = only_active_clause_idx(&conflict_solver);
    conflict_solver.arena.set_learned(conflict_clause, true);
    conflict_solver.arena.set_lbd(conflict_clause, 25);
    conflict_solver.arena.set_used(conflict_clause, 0);
    conflict_solver.arena.set_saved_pos(conflict_clause, 20);
    conflict_solver.set_bcp_learned_no_replacement_scan_pressure_enabled(true);
    for var in 1..32 {
        conflict_solver.decide(Literal::negative(Variable(var)));
        conflict_solver.qhead = conflict_solver.trail.len();
    }
    conflict_solver.decide(Literal::negative(Variable(0)));
    assert!(conflict_solver
        .propagate_bcp::<{ bcp_mode::SEARCH }>()
        .is_some());

    let conflict_stats = conflict_solver.bcp_long_scan_stats();
    assert_eq!(conflict_stats.learned_1963_fsw_conflict_by_lbd[4], 1);
    assert_eq!(conflict_stats.learned_1963_fsw_conflict_steps_by_lbd[4], 30);
    assert_eq!(conflict_stats.learned_1963_fsw_conflict_by_used[0], 1);
    assert_eq!(
        conflict_stats.learned_1963_fsw_conflict_steps_by_used[0],
        30
    );
    assert_eq!(
        conflict_stats
            .learned_1963_fsw_unit_by_lbd
            .iter()
            .sum::<u64>(),
        0
    );
}

#[test]
fn test_bcp_learned_1963_identity_profile_records_clause_row() {
    let mut solver = bcp_len_test_solver(32).0;
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.arena.set_lbd(clause_idx, 5);
    solver.arena.set_used(clause_idx, 3);
    solver.arena.set_saved_pos(clause_idx, 20);
    solver.set_bcp_learned_1963_identity_profile_enabled(true);

    for var in 2..32 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    let identity = solver.bcp_learned_1963_identity_stats(4);
    assert!(identity.enabled);
    assert_eq!(identity.exact_identity_rows, 1);
    assert_eq!(identity.total_scans, 1);
    assert_eq!(identity.total_scan_steps, 30);
    assert_eq!(identity.no_replacement_scans, 1);
    assert_eq!(identity.unit, 1);
    assert_eq!(identity.conflict, 0);
    assert_eq!(identity.fsw_scans, 1);
    assert_eq!(identity.fsw_steps, 30);
    assert_eq!(identity.fsw_repeat_steps, 0);
    assert_eq!(identity.topk_pressure_share_ppm, 1_000_000);
    assert_eq!(identity.topk_fsw_steps, 30);
    assert_eq!(identity.topk_fsw_pressure_share_ppm, 1_000_000);
    assert_eq!(identity.fsw_age_steps_by_bucket[0], 30);
    assert_eq!(identity.lbd_steps_by_bucket[1], 30);
    assert_eq!(identity.used_steps_by_bucket[2], 30);
    assert_eq!(identity.activity_steps_by_bucket[0], 30);

    assert_eq!(identity.rows.len(), 1);
    let row = &identity.rows[0];
    assert!(row.clause_id > 0);
    assert_eq!(row.clause_offset, clause_idx as u64);
    assert_eq!(row.clause_len, 32);
    assert_eq!(row.scans, 1);
    assert_eq!(row.scan_steps, 30);
    assert_eq!(row.no_replacement_scans, 1);
    assert_eq!(row.unit, 1);
    assert_eq!(row.saved_start_false, 1);
    assert_eq!(row.wrapped, 1);
    assert_eq!(row.fsw, 1);
    assert_eq!(row.fsw_steps, 30);
    assert_eq!(row.fsw_unit_steps, 30);
    assert_eq!(row.fsw_conflict_steps, 0);
    assert_eq!(row.fsw_repeat_steps, 0);
    assert_eq!(row.activity_milli, 0);
    assert_eq!(identity.fsw_rows, identity.rows);
}

#[test]
fn test_bcp_learned_1963_used5_fsw_saved_pos_reset_default_off_inert() {
    let mut solver = bcp_len_test_solver(32).0;
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.arena.set_used(clause_idx, 5);
    solver.arena.set_saved_pos(clause_idx, 20);
    solver.set_bcp_telemetry_enabled(true);

    for var in 2..32 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        20,
        "used5 FSW reset must not rewrite saved_pos unless the gate is enabled"
    );
    let long_stats = solver.bcp_long_scan_stats();
    assert!(!long_stats.learned_1963_used5_fsw_saved_pos_reset_enabled);
    assert_eq!(
        long_stats.learned_1963_used5_fsw_saved_pos_reset_eligible,
        0
    );
    assert_eq!(long_stats.learned_1963_used5_fsw_saved_pos_reset_writes, 0);
}

#[test]
fn test_bcp_learned_1963_used5_fsw_saved_pos_reset_exercises_unit_route() {
    let mut solver = bcp_len_test_solver(32).0;
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.arena.set_used(clause_idx, 5);
    solver.arena.set_saved_pos(clause_idx, 20);
    solver.set_bcp_telemetry_enabled(true);
    solver.set_bcp_learned_1963_used5_fsw_saved_pos_reset_enabled(true);

    for var in 2..32 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        2,
        "enabled used5 FSW reset should move saved_pos to the tail head"
    );
    let long_stats = solver.bcp_long_scan_stats();
    assert!(long_stats.learned_1963_used5_fsw_saved_pos_reset_enabled);
    assert_eq!(
        long_stats.learned_1963_used5_fsw_saved_pos_reset_eligible,
        1
    );
    assert_eq!(long_stats.learned_1963_used5_fsw_saved_pos_reset_writes, 1);
    assert_eq!(long_stats.learned_1963_used5_fsw_saved_pos_reset_unit, 1);
    assert_eq!(
        long_stats.learned_1963_used5_fsw_saved_pos_reset_conflict,
        0
    );
}

#[test]
fn test_bcp_learned_1963_used5_fsw_saved_pos_reset_works_with_explicit_telemetry_disabled() {
    let mut solver = bcp_len_test_solver(32).0;
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.arena.set_used(clause_idx, 5);
    solver.arena.set_saved_pos(clause_idx, 20);
    assert!(!solver.bcp_telemetry_enabled());
    solver.set_bcp_learned_1963_used5_fsw_saved_pos_reset_enabled(true);

    for var in 2..32 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        2,
        "enabled used5 FSW reset should not depend on telemetry collection"
    );
    let long_stats = solver.bcp_long_scan_stats();
    assert!(long_stats.learned_1963_used5_fsw_saved_pos_reset_enabled);
    let expected_counters = u64::from(cfg!(debug_assertions));
    assert_eq!(
        long_stats.learned_1963_used5_fsw_saved_pos_reset_eligible,
        expected_counters
    );
    assert_eq!(
        long_stats.learned_1963_used5_fsw_saved_pos_reset_writes,
        expected_counters
    );
}

#[test]
fn test_bcp_learned_1963_used5_fsw_saved_pos_reset_exercises_conflict_route() {
    let mut solver = bcp_len_test_solver(32).0;
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.arena.set_used(clause_idx, 5);
    solver.arena.set_saved_pos(clause_idx, 20);
    solver.set_bcp_telemetry_enabled(true);
    solver.set_bcp_learned_1963_used5_fsw_saved_pos_reset_enabled(true);

    for var in 1..32 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_some());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        2,
        "enabled used5 FSW reset should move conflict-route saved_pos to the tail head"
    );
    let long_stats = solver.bcp_long_scan_stats();
    assert!(long_stats.learned_1963_used5_fsw_saved_pos_reset_enabled);
    assert_eq!(
        long_stats.learned_1963_used5_fsw_saved_pos_reset_eligible,
        1
    );
    assert_eq!(long_stats.learned_1963_used5_fsw_saved_pos_reset_writes, 1);
    assert_eq!(long_stats.learned_1963_used5_fsw_saved_pos_reset_unit, 0);
    assert_eq!(
        long_stats.learned_1963_used5_fsw_saved_pos_reset_conflict,
        1
    );
}

#[test]
fn test_bcp_learned_1963_fsw_conflict_saved_pos_reset_default_off_inert() {
    let mut solver = bcp_len_test_solver(32).0;
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.arena.set_saved_pos(clause_idx, 20);
    solver.set_bcp_telemetry_enabled(true);

    for var in 1..32 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_some());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        20,
        "FSW conflict-only reset must stay inert unless the gate is enabled"
    );
    let long_stats = solver.bcp_long_scan_stats();
    assert!(!long_stats.learned_1963_fsw_conflict_saved_pos_reset_enabled);
    assert_eq!(
        long_stats.learned_1963_fsw_conflict_saved_pos_reset_eligible,
        0
    );
    assert_eq!(
        long_stats.learned_1963_fsw_conflict_saved_pos_reset_writes,
        0
    );
    assert_eq!(
        long_stats.learned_1963_fsw_conflict_saved_pos_reset_conflict,
        0
    );
}

#[test]
fn test_bcp_learned_1963_fsw_conflict_saved_pos_reset_exercises_conflict_route() {
    let mut solver = bcp_len_test_solver(32).0;
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.arena.set_saved_pos(clause_idx, 20);
    solver.set_bcp_telemetry_enabled(true);
    solver.set_bcp_learned_1963_fsw_conflict_saved_pos_reset_enabled(true);

    for var in 1..32 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_some());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        2,
        "enabled FSW conflict-only reset should move conflict-route saved_pos to the tail head"
    );
    let long_stats = solver.bcp_long_scan_stats();
    assert!(long_stats.learned_1963_fsw_conflict_saved_pos_reset_enabled);
    assert_eq!(
        long_stats.learned_1963_fsw_conflict_saved_pos_reset_eligible,
        1
    );
    assert_eq!(
        long_stats.learned_1963_fsw_conflict_saved_pos_reset_writes,
        1
    );
    assert_eq!(
        long_stats.learned_1963_fsw_conflict_saved_pos_reset_conflict,
        1
    );
}

#[test]
fn test_bcp_learned_1963_fsw_conflict_saved_pos_reset_does_not_write_unit_route() {
    let mut solver = bcp_len_test_solver(32).0;
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.arena.set_saved_pos(clause_idx, 20);
    solver.set_bcp_telemetry_enabled(true);
    solver.set_bcp_learned_1963_fsw_conflict_saved_pos_reset_enabled(true);

    for var in 2..32 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        20,
        "FSW conflict-only reset must not write saved_pos on unit outcomes"
    );
    let long_stats = solver.bcp_long_scan_stats();
    assert!(long_stats.learned_1963_fsw_conflict_saved_pos_reset_enabled);
    assert_eq!(
        long_stats.learned_1963_fsw_conflict_saved_pos_reset_eligible,
        0
    );
    assert_eq!(
        long_stats.learned_1963_fsw_conflict_saved_pos_reset_writes,
        0
    );
    assert_eq!(
        long_stats.learned_1963_fsw_conflict_saved_pos_reset_conflict,
        0
    );
}

#[test]
fn test_bcp_learned_1963_used5_fsw_saved_pos_reset_ignores_used4() {
    let mut solver = bcp_len_test_solver(32).0;
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.arena.set_used(clause_idx, 4);
    solver.arena.set_saved_pos(clause_idx, 20);
    solver.set_bcp_telemetry_enabled(true);
    solver.set_bcp_learned_1963_used5_fsw_saved_pos_reset_enabled(true);

    for var in 2..32 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(solver.arena.saved_pos(clause_idx), 20);
    let long_stats = solver.bcp_long_scan_stats();
    assert!(long_stats.learned_1963_used5_fsw_saved_pos_reset_enabled);
    assert_eq!(
        long_stats.learned_1963_used5_fsw_saved_pos_reset_eligible,
        0
    );
}

#[test]
fn test_bcp_learned_no_replacement_scan_pressure_ignores_original_clause() {
    let mut solver = bcp_saved_pos_test_solver();
    let clause_idx = only_active_clause_idx(&solver);
    solver.set_bcp_learned_no_replacement_scan_pressure_enabled(true);

    for var in 2..6 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, 4);
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    let long_stats = solver.bcp_long_scan_stats();
    assert!(long_stats.learned_no_replacement_scan_pressure_enabled);
    assert_eq!(
        long_stats
            .learned_no_replacement_scan_pressure_scans_by_len
            .iter()
            .sum::<u64>(),
        0,
        "scan-pressure profile is learned-clause only"
    );
}

#[test]
fn test_bcp_learned_no_replacement_saved_pos_update_unit_resets_to_tail_head() {
    let mut solver = bcp_saved_pos_test_solver();
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_telemetry_enabled(true);
    solver.set_bcp_learned_no_replacement_saved_pos_update_enabled(true);

    for var in 2..6 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, 4);
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        2,
        "enabled no-replacement gate should reset stale learned saved_pos to tail head"
    );
    assert_eq!(
        solver.lit_val(Literal::positive(Variable(1))),
        1,
        "no-replacement update must preserve unit propagation"
    );
    let long_stats = solver.bcp_long_scan_stats();
    let bucket = bcp_long_bucket_index(&long_stats.bucket_labels, "6-8");
    assert!(long_stats.learned_no_replacement_saved_pos_update_enabled);
    assert_eq!(
        long_stats.learned_no_replacement_saved_pos_eligible_by_len[bucket],
        1
    );
    assert_eq!(
        long_stats.learned_no_replacement_saved_pos_writes_by_len[bucket],
        1
    );
    assert_eq!(
        long_stats.learned_no_replacement_saved_pos_skipped_current_by_len[bucket],
        0
    );
    assert_eq!(
        long_stats.learned_no_replacement_saved_pos_unit_by_len[bucket],
        1
    );
    assert_eq!(
        long_stats.learned_no_replacement_saved_pos_conflict_by_len[bucket],
        0
    );
}

#[test]
fn test_bcp_learned_no_replacement_saved_pos_update_conflict_resets_to_tail_head() {
    let mut solver = bcp_saved_pos_test_solver();
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_telemetry_enabled(true);
    solver.set_bcp_learned_no_replacement_saved_pos_update_enabled(true);

    for var in 1..6 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, 4);
    solver.decide(Literal::negative(Variable(0)));
    let conflict = solver.propagate_bcp::<{ bcp_mode::SEARCH }>();

    assert!(conflict.is_some(), "all clause literals are false");
    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        2,
        "conflict no-replacement path should reset stale learned saved_pos"
    );
    let long_stats = solver.bcp_long_scan_stats();
    let bucket = bcp_long_bucket_index(&long_stats.bucket_labels, "6-8");
    assert_eq!(
        long_stats.learned_no_replacement_saved_pos_eligible_by_len[bucket],
        1
    );
    assert_eq!(
        long_stats.learned_no_replacement_saved_pos_writes_by_len[bucket],
        1
    );
    assert_eq!(
        long_stats.learned_no_replacement_saved_pos_unit_by_len[bucket],
        0
    );
    assert_eq!(
        long_stats.learned_no_replacement_saved_pos_conflict_by_len[bucket],
        1
    );
}

#[test]
fn test_bcp_learned_no_replacement_saved_pos_update_ignores_original_clause() {
    let mut solver = bcp_saved_pos_test_solver();
    let clause_idx = only_active_clause_idx(&solver);
    solver.set_bcp_telemetry_enabled(true);
    solver.set_bcp_learned_no_replacement_saved_pos_update_enabled(true);

    for var in 2..6 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, 4);
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        4,
        "original clauses are excluded from the learned no-replacement update"
    );
    let long_stats = solver.bcp_long_scan_stats();
    let bucket = bcp_long_bucket_index(&long_stats.bucket_labels, "6-8");
    assert_eq!(
        long_stats.learned_no_replacement_saved_pos_eligible_by_len[bucket],
        0
    );
}

#[test]
fn test_bcp_learned_no_replacement_saved_pos_update_counts_current_tail_head_skip() {
    let mut solver = bcp_saved_pos_test_solver();
    let clause_idx = only_active_clause_idx(&solver);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_telemetry_enabled(true);
    solver.set_bcp_learned_no_replacement_saved_pos_update_enabled(true);

    for var in 2..6 {
        solver.decide(Literal::negative(Variable(var)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, 2);
    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(solver.arena.saved_pos(clause_idx), 2);
    let long_stats = solver.bcp_long_scan_stats();
    let bucket = bcp_long_bucket_index(&long_stats.bucket_labels, "6-8");
    assert_eq!(
        long_stats.learned_no_replacement_saved_pos_eligible_by_len[bucket],
        1
    );
    assert_eq!(
        long_stats.learned_no_replacement_saved_pos_writes_by_len[bucket],
        0
    );
    assert_eq!(
        long_stats.learned_no_replacement_saved_pos_skipped_current_by_len[bucket],
        1
    );
}

#[test]
fn test_bcp_saved_pos_advance_default_off_keeps_learned_false_start_scan_order() {
    let clause_len = 12;
    let saved_pos = 8;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);

    for slot in saved_pos..clause_len {
        solver.decide(Literal::negative(Variable(slot as u32)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, saved_pos);
    solver.set_bcp_telemetry_enabled(true);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.bcp_stats().2,
        (clause_len - saved_pos + 1) as u64,
        "default-off learned false-start policy should scan saved slot, tail, then wrap"
    );
    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        2,
        "default policy still records the found replacement slot"
    );
    let long_stats = solver.bcp_long_scan_stats();
    let len9_17 = bcp_long_bucket_index(&long_stats.bucket_labels, "9-17");
    assert_eq!(long_stats.scan_steps_by_len[len9_17], 5);
    assert_eq!(long_stats.learned_scan_steps_by_len[len9_17], 5);
    let saved_stats = solver.bcp_saved_pos_stats();
    assert_eq!(saved_stats.long_scans, 1);
    assert_eq!(saved_stats.long_start_false, 1);
    assert_eq!(saved_stats.long_found_unassigned, 1);
}

#[test]
fn test_bcp_saved_pos_advance_learned_false_start_resets_bucketed() {
    for (clause_len, saved_pos, bucket_label) in [
        (9usize, 5usize, "9-17"),
        (18usize, 12usize, "18"),
        (32usize, 20usize, "19-63"),
    ] {
        let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
        solver.arena.set_learned(clause_idx, true);
        solver.set_bcp_advance_saved_pos_after_unassigned_move_enabled(true);

        for slot in saved_pos..clause_len {
            solver.decide(Literal::negative(Variable(slot as u32)));
            solver.qhead = solver.trail.len();
        }
        solver.arena.set_saved_pos(clause_idx, saved_pos);
        solver.set_bcp_telemetry_enabled(true);

        solver.decide(Literal::negative(Variable(0)));
        assert!(
            solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
            "len-{clause_len} learned false-start reset should not conflict"
        );

        assert_eq!(
            solver.bcp_stats().2,
            1,
            "len-{clause_len} learned false-start reset should check only first tail slot"
        );
        assert_eq!(
            solver.arena.saved_pos(clause_idx),
            2,
            "len-{clause_len} reset should record the first tail slot"
        );
        assert_eq!(
            solver.arena.literal(clause_idx, 0),
            Literal::positive(Variable(2)),
            "len-{clause_len} reset should move the first tail literal into the watch"
        );
        let long_stats = solver.bcp_long_scan_stats();
        let bucket = bcp_long_bucket_index(&long_stats.bucket_labels, bucket_label);
        assert_eq!(long_stats.scan_steps_by_len[bucket], 1);
        assert_eq!(long_stats.learned_scan_steps_by_len[bucket], 1);
        let saved_stats = solver.bcp_saved_pos_stats();
        assert_eq!(saved_stats.long_scans, 1);
        assert_eq!(saved_stats.long_start_false, 1);
        assert_eq!(saved_stats.long_found_unassigned, 1);
    }
}

#[test]
fn test_bcp_learned_1963_false_saved_pos_reset_default_off_keeps_scan_order() {
    let clause_len = 32;
    let saved_pos = 20;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);

    for slot in saved_pos..clause_len {
        solver.decide(Literal::negative(Variable(slot as u32)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, saved_pos);
    solver.set_bcp_telemetry_enabled(true);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    let default_steps = (clause_len - saved_pos + 1) as u64;
    assert_eq!(
        solver.bcp_stats().2,
        default_steps,
        "default-off learned 19-63 policy should scan saved slot, tail, then wrap"
    );
    let long_stats = solver.bcp_long_scan_stats();
    let bucket = bcp_long_bucket_index(&long_stats.bucket_labels, "19-63");
    assert_eq!(long_stats.scan_steps_by_len[bucket], default_steps);
    assert_eq!(long_stats.learned_scan_steps_by_len[bucket], default_steps);
}

#[test]
fn test_bcp_learned_1963_false_saved_pos_reset_skips_known_false_start() {
    let clause_len = 32;
    let saved_pos = 20;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_learned_1963_false_saved_pos_reset_enabled(true);

    for slot in saved_pos..clause_len {
        solver.decide(Literal::negative(Variable(slot as u32)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, saved_pos);
    solver.set_bcp_telemetry_enabled(true);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.bcp_stats().2,
        1,
        "learned 19-63 false-start reset should check only the first tail slot"
    );
    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        2,
        "learned 19-63 reset should record the first tail slot"
    );
    assert_eq!(
        solver.arena.literal(clause_idx, 0),
        Literal::positive(Variable(2)),
        "learned 19-63 reset should move the first tail literal into the watch"
    );
    let long_stats = solver.bcp_long_scan_stats();
    let bucket = bcp_long_bucket_index(&long_stats.bucket_labels, "19-63");
    assert_eq!(long_stats.scan_steps_by_len[bucket], 1);
    assert_eq!(long_stats.learned_scan_steps_by_len[bucket], 1);
    let saved_stats = solver.bcp_saved_pos_stats();
    assert_eq!(saved_stats.long_scans, 1);
    assert_eq!(saved_stats.long_start_false, 1);
    assert_eq!(saved_stats.long_found_unassigned, 1);
}

#[test]
fn test_bcp_learned_1963_false_saved_pos_reset_no_replacement_keeps_saved_pos() {
    let clause_len = 32;
    let saved_pos = 20;
    let expected_steps = (clause_len - 2 - 1) as u64;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_learned_1963_false_saved_pos_reset_enabled(true);

    for slot in 2..clause_len {
        solver.decide(Literal::negative(Variable(slot as u32)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, saved_pos);
    solver.set_bcp_telemetry_enabled(true);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.bcp_stats().2,
        expected_steps,
        "learned 19-63 reset should full-scan every tail slot except the known-false saved start"
    );
    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        saved_pos,
        "learned 19-63 reset must not rewrite saved_pos on no-replacement unit paths"
    );

    let long_stats = solver.bcp_long_scan_stats();
    let bucket = bcp_long_bucket_index(&long_stats.bucket_labels, "19-63");
    assert_eq!(long_stats.scans_by_len[bucket], 1);
    assert_eq!(long_stats.scan_steps_by_len[bucket], expected_steps);
    assert_eq!(long_stats.learned_scan_steps_by_len[bucket], expected_steps);
    assert_eq!(long_stats.no_replacement_by_len[bucket], 1);
    assert_eq!(long_stats.unit_by_len[bucket], 1);
    assert_eq!(long_stats.learned_no_replacement_by_len[bucket], 1);
    assert_eq!(long_stats.learned_unit_by_len[bucket], 1);

    let saved_stats = solver.bcp_saved_pos_stats();
    assert_eq!(saved_stats.long_scans, 1);
    assert_eq!(saved_stats.long_start_false, 1);
    assert_eq!(saved_stats.long_no_replacement, 1);
}

#[test]
fn test_bcp_learned_1963_fsw_gent_skip_finds_suffix_replacement() {
    let clause_len = 32;
    let saved_pos = 20;
    let replacement_pos = saved_pos + 1;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_learned_1963_fsw_gent_skip_enabled(true);
    solver.set_bcp_telemetry_enabled(true);

    solver.decide(Literal::negative(Variable(saved_pos as u32)));
    solver.qhead = solver.trail.len();
    solver.arena.set_saved_pos(clause_idx, saved_pos);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.bcp_stats().2,
        1,
        "Gent-order skip should skip only the known-false saved slot before the suffix hit"
    );
    assert_eq!(solver.arena.saved_pos(clause_idx), replacement_pos);
    assert_eq!(
        solver.arena.literal(clause_idx, 0),
        Literal::positive(Variable(replacement_pos as u32))
    );

    let long_stats = solver.bcp_long_scan_stats();
    assert!(long_stats.learned_1963_fsw_gent_skip_enabled);
    assert_eq!(long_stats.learned_1963_fsw_gent_skip_candidates, 1);
    assert_eq!(long_stats.learned_1963_fsw_gent_skip_applied, 1);
    assert_eq!(long_stats.learned_1963_fsw_gent_skip_saved_slots, 1);
    assert_eq!(
        long_stats.learned_1963_fsw_gent_skip_found_unassigned_suffix,
        1
    );
    assert_eq!(
        long_stats.learned_1963_fsw_gent_skip_found_unassigned_prefix,
        0
    );
    assert_eq!(long_stats.learned_1963_fsw_gent_skip_no_replacement_unit, 0);
}

#[cfg(not(debug_assertions))]
#[test]
fn test_bcp_learned_1963_fsw_gent_skip_runs_without_forcing_telemetry() {
    let clause_len = 32;
    let saved_pos = 20;
    let replacement_pos = saved_pos + 1;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_learned_1963_fsw_gent_skip_enabled(true);

    solver.decide(Literal::negative(Variable(saved_pos as u32)));
    solver.qhead = solver.trail.len();
    solver.arena.set_saved_pos(clause_idx, saved_pos);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        replacement_pos,
        "Gent-order skip behavior should remain active without BCP telemetry"
    );
    assert_eq!(
        solver.bcp_stats().2,
        0,
        "Gent-order skip must not force full replacement-scan telemetry"
    );
    let long_stats = solver.bcp_long_scan_stats();
    let bucket = bcp_long_bucket_index(&long_stats.bucket_labels, "19-63");
    assert_eq!(long_stats.scans_by_len[bucket], 0);
    assert_eq!(long_stats.learned_1963_fsw_gent_skip_candidates, 0);
}

#[test]
fn test_bcp_learned_1963_fsw_gent_skip_runs_with_blocker_cert_gate_without_cert() {
    let clause_len = 32;
    let saved_pos = 20;
    let replacement_pos = saved_pos + 1;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_learned_1963_fsw_gent_skip_enabled(true);
    enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut solver);
    solver.set_bcp_telemetry_enabled(true);

    solver.decide(Literal::negative(Variable(saved_pos as u32)));
    solver.qhead = solver.trail.len();
    solver.arena.set_saved_pos(clause_idx, saved_pos);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(solver.arena.saved_pos(clause_idx), replacement_pos);
    assert_eq!(
        solver.bcp_stats().2,
        1,
        "blocker-cert gate without an existing cert should not mask Gent skip"
    );
    let long_stats = solver.bcp_long_scan_stats();
    assert_eq!(long_stats.learned_1963_fsw_gent_skip_candidates, 1);
    assert_eq!(long_stats.learned_1963_fsw_gent_skip_applied, 1);
    assert_eq!(
        long_stats.learned_1963_blocker_cert_candidates, 0,
        "without a cert, blocker-cert elision should not claim the route"
    );
}

#[test]
fn test_bcp_learned_1963_fsw_gent_skip_preserves_wrap_order() {
    let clause_len = 32;
    let saved_pos = 20;
    let expected_steps = (clause_len - saved_pos - 1 + 1) as u64;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_learned_1963_fsw_gent_skip_enabled(true);
    solver.set_bcp_telemetry_enabled(true);

    for slot in saved_pos..clause_len {
        solver.decide(Literal::negative(Variable(slot as u32)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, saved_pos);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.bcp_stats().2,
        expected_steps,
        "Gent-order skip should scan suffix after saved_pos, then wrapped prefix"
    );
    assert_eq!(solver.arena.saved_pos(clause_idx), 2);
    assert_eq!(
        solver.arena.literal(clause_idx, 0),
        Literal::positive(Variable(2))
    );

    let long_stats = solver.bcp_long_scan_stats();
    assert_eq!(long_stats.learned_1963_fsw_gent_skip_candidates, 1);
    assert_eq!(long_stats.learned_1963_fsw_gent_skip_applied, 1);
    assert_eq!(
        long_stats.learned_1963_fsw_gent_skip_found_unassigned_suffix,
        0
    );
    assert_eq!(
        long_stats.learned_1963_fsw_gent_skip_found_unassigned_prefix,
        1
    );
    assert_eq!(long_stats.learned_1963_fsw_gent_skip_no_replacement_unit, 0);
}

#[test]
fn test_bcp_learned_1963_fsw_gent_skip_no_replacement_keeps_saved_pos() {
    let clause_len = 32;
    let saved_pos = 20;
    let expected_steps = (clause_len - 2 - 1) as u64;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_learned_1963_fsw_gent_skip_enabled(true);
    solver.set_bcp_telemetry_enabled(true);

    for slot in 2..clause_len {
        solver.decide(Literal::negative(Variable(slot as u32)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, saved_pos);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.bcp_stats().2,
        expected_steps,
        "Gent-order skip should full-scan every tail slot except the known-false saved start"
    );
    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        saved_pos,
        "Gent-order skip must not rewrite saved_pos on no-replacement unit paths"
    );

    let long_stats = solver.bcp_long_scan_stats();
    let bucket = bcp_long_bucket_index(&long_stats.bucket_labels, "19-63");
    assert_eq!(long_stats.scans_by_len[bucket], 1);
    assert_eq!(long_stats.scan_steps_by_len[bucket], expected_steps);
    assert_eq!(long_stats.learned_scan_steps_by_len[bucket], expected_steps);
    assert_eq!(long_stats.no_replacement_by_len[bucket], 1);
    assert_eq!(long_stats.unit_by_len[bucket], 1);
    assert_eq!(long_stats.learned_1963_fsw_gent_skip_candidates, 1);
    assert_eq!(long_stats.learned_1963_fsw_gent_skip_applied, 1);
    assert_eq!(long_stats.learned_1963_fsw_gent_skip_no_replacement_unit, 1);
    assert_eq!(
        long_stats.learned_1963_fsw_gent_skip_no_replacement_conflict,
        0
    );
}

#[test]
fn test_bcp_learned_1963_fsw_gent_skip_no_replacement_conflict_keeps_saved_pos() {
    let clause_len = 32;
    let saved_pos = 20;
    let expected_steps = (clause_len - 2 - 1) as u64;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_learned_1963_fsw_gent_skip_enabled(true);
    solver.set_bcp_telemetry_enabled(true);

    for slot in 1..clause_len {
        solver.decide(Literal::negative(Variable(slot as u32)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, saved_pos);

    solver.decide(Literal::negative(Variable(0)));
    assert!(
        solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_some(),
        "all watched and tail literals false should conflict"
    );

    assert_eq!(
        solver.bcp_stats().2,
        expected_steps,
        "Gent-order skip conflict path should skip exactly the known-false saved start"
    );
    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        saved_pos,
        "Gent-order skip must not rewrite saved_pos on no-replacement conflict paths"
    );

    let long_stats = solver.bcp_long_scan_stats();
    let bucket = bcp_long_bucket_index(&long_stats.bucket_labels, "19-63");
    assert_eq!(long_stats.scans_by_len[bucket], 1);
    assert_eq!(long_stats.scan_steps_by_len[bucket], expected_steps);
    assert_eq!(long_stats.no_replacement_by_len[bucket], 1);
    assert_eq!(long_stats.conflict_by_len[bucket], 1);
    assert_eq!(long_stats.learned_1963_fsw_gent_skip_candidates, 1);
    assert_eq!(long_stats.learned_1963_fsw_gent_skip_applied, 1);
    assert_eq!(long_stats.learned_1963_fsw_gent_skip_no_replacement_unit, 0);
    assert_eq!(
        long_stats.learned_1963_fsw_gent_skip_no_replacement_conflict,
        1
    );
}

#[test]
fn test_bcp_learned_1963_fsw_gent_skip_ignores_original_and_len64() {
    for (clause_len, learned, expected_steps, case_name) in [
        (32usize, false, 13u64, "original len32"),
        (64usize, true, 45u64, "learned len64"),
    ] {
        let saved_pos = 20;
        let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
        solver.arena.set_learned(clause_idx, learned);
        solver.set_bcp_learned_1963_fsw_gent_skip_enabled(true);
        solver.set_bcp_telemetry_enabled(true);

        for slot in saved_pos..clause_len {
            solver.decide(Literal::negative(Variable(slot as u32)));
            solver.qhead = solver.trail.len();
        }
        solver.arena.set_saved_pos(clause_idx, saved_pos);

        solver.decide(Literal::negative(Variable(0)));
        assert!(
            solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
            "{case_name} should keep normal BCP behavior"
        );

        assert_eq!(
            solver.bcp_stats().2,
            expected_steps,
            "{case_name} must keep the normal saved-position scan order"
        );
        assert_eq!(
            solver
                .bcp_long_scan_stats()
                .learned_1963_fsw_gent_skip_candidates,
            0,
            "{case_name} must not enter the learned 19-63 Gent skip route"
        );
    }
}

#[test]
fn test_bcp_learned_1963_false_saved_pos_reset_ignores_original_and_len64() {
    for (clause_len, learned, expected_steps, case_name) in [
        (32usize, false, 13u64, "original len32"),
        (64usize, true, 45u64, "learned len64"),
    ] {
        let saved_pos = 20;
        let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
        solver.arena.set_learned(clause_idx, learned);
        solver.set_bcp_learned_1963_false_saved_pos_reset_enabled(true);

        for slot in saved_pos..clause_len {
            solver.decide(Literal::negative(Variable(slot as u32)));
            solver.qhead = solver.trail.len();
        }
        solver.arena.set_saved_pos(clause_idx, saved_pos);
        solver.set_bcp_telemetry_enabled(true);

        solver.decide(Literal::negative(Variable(0)));
        assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

        assert_eq!(
            solver.bcp_stats().2,
            expected_steps,
            "{case_name} must keep the normal saved-position scan order"
        );
        assert_eq!(
            solver.arena.saved_pos(clause_idx),
            2,
            "{case_name} should record the actual wrapped replacement"
        );
        assert_eq!(
            solver.arena.literal(clause_idx, 0),
            Literal::positive(Variable(2)),
            "{case_name} should find the first wrapped tail replacement"
        );
    }
}

#[test]
fn test_bcp_learned_1963_blocker_cert_elision_default_off_inert() {
    let solver = run_bcp_blocker_cert_two_watch_route(32, true, false, false);
    let stats = solver.bcp_long_scan_stats();
    assert!(!stats.learned_1963_blocker_cert_elision_enabled);
    assert!(!stats.learned_1963_blocker_cert_shadow_enabled);
    assert!(!stats.learned_1963_blocker_cert_false_reject_demote_enabled);
    assert_eq!(stats.learned_1963_blocker_cert_candidates, 0);
    assert_eq!(stats.learned_1963_blocker_cert_populates, 0);
    assert_eq!(stats.learned_1963_blocker_cert_elisions, 0);
    assert_eq!(stats.learned_1963_blocker_cert_shadow_hits, 0);
    assert_eq!(stats.learned_1963_blocker_cert_elided_suffix_slots, 0);
}

#[test]
fn test_bcp_learned_1963_blocker_cert_elision_matches_full_scan_true_replacement_no_reset() {
    let (full_scan, full_idx, true_slot) =
        run_bcp_blocker_cert_repeated_true_replacement_case(false, false);
    let (elided, elided_idx, _) = run_bcp_blocker_cert_repeated_true_replacement_case(false, true);
    let true_lit = Literal::positive(Variable(true_slot as u32));

    assert_eq!(
        bcp_blocker_cert_true_replacement_observation(&elided, elided_idx),
        bcp_blocker_cert_true_replacement_observation(&full_scan, full_idx),
        "certified no-reset elision must keep the same true blocker and watched literals as the full scan"
    );
    assert_eq!(
        bcp_blocker_cert_clause_lits(&elided, elided_idx),
        bcp_blocker_cert_clause_lits(&full_scan, full_idx),
        "certified no-reset elision must leave the clause layout identical to the full scan"
    );
    assert_eq!(
        bcp_blocker_cert_true_replacement_observation(&elided, elided_idx).second_watch_blocker,
        true_lit,
        "the elided no-reset path must keep the same true replacement blocker"
    );

    let stats = elided.bcp_long_scan_stats();
    assert_eq!(stats.learned_1963_blocker_cert_elisions, 1);
    assert_eq!(stats.learned_1963_blocker_cert_shadow_mismatches, 0);
}

#[test]
fn test_bcp_learned_1963_blocker_cert_elision_matches_full_scan_true_replacement_reset() {
    let (full_scan, full_idx, true_slot) =
        run_bcp_blocker_cert_repeated_true_replacement_case(true, false);
    let (elided, elided_idx, _) = run_bcp_blocker_cert_repeated_true_replacement_case(true, true);
    let true_lit = Literal::positive(Variable(true_slot as u32));

    assert_eq!(
        bcp_blocker_cert_true_replacement_observation(&elided, elided_idx),
        bcp_blocker_cert_true_replacement_observation(&full_scan, full_idx),
        "certified reset-path elision must keep the same true blocker and watched literals as the full scan"
    );
    assert_eq!(
        bcp_blocker_cert_clause_lits(&elided, elided_idx),
        bcp_blocker_cert_clause_lits(&full_scan, full_idx),
        "certified reset-path elision must leave the clause layout identical to the full scan"
    );
    assert_eq!(
        bcp_blocker_cert_true_replacement_observation(&elided, elided_idx).second_watch_blocker,
        true_lit,
        "the elided reset path must keep the same true replacement blocker"
    );

    let stats = elided.bcp_long_scan_stats();
    assert_eq!(stats.learned_1963_blocker_cert_elisions, 1);
    assert_eq!(stats.learned_1963_blocker_cert_shadow_mismatches, 0);
}

#[test]
fn test_bcp_learned_1963_blocker_cert_elision_prefix_non_false_matches_full_scan_fallback() {
    let (full_scan, full_idx, earlier_slot, cert_slot) =
        run_bcp_blocker_cert_wrapped_prefix_non_false_case(false);
    let (fallback, fallback_idx, _, _) = run_bcp_blocker_cert_wrapped_prefix_non_false_case(true);
    let earlier_lit = Literal::positive(Variable(earlier_slot as u32));
    let cert_lit = Literal::positive(Variable(cert_slot as u32));

    assert_eq!(
        bcp_blocker_cert_clause_lits(&fallback, fallback_idx),
        bcp_blocker_cert_clause_lits(&full_scan, full_idx),
        "non-false wrapped prefix must reject the cert and preserve full-scan replacement behavior"
    );
    assert_eq!(
        fallback.arena.saved_pos(fallback_idx),
        full_scan.arena.saved_pos(full_idx),
        "non-false wrapped prefix fallback must preserve full-scan saved-position evolution"
    );
    assert_eq!(
        fallback.arena.literal(fallback_idx, 0),
        earlier_lit,
        "fallback must choose the earlier non-false prefix literal"
    );
    assert_ne!(
        fallback.arena.literal(fallback_idx, 0),
        cert_lit,
        "fallback must not use the later certified literal when the prefix is non-false"
    );

    let stats = fallback.bcp_long_scan_stats();
    assert_eq!(stats.learned_1963_blocker_cert_candidates, 1);
    assert_eq!(stats.learned_1963_blocker_cert_elisions, 0);
    assert_eq!(stats.learned_1963_blocker_cert_shadow_mismatches, 1);
}

#[test]
fn test_bcp_learned_1963_blocker_cert_elides_second_watch_scan() {
    let clause_len = 32;
    let saved_pos = 20;
    let true_slot = 3usize;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.set_bcp_telemetry_enabled(true);
    solver.arena.set_learned(clause_idx, true);
    enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut solver);
    stage_bcp_blocker_cert_false_start_wrap(
        &mut solver,
        clause_idx,
        clause_len,
        saved_pos,
        true_slot,
    );
    seed_bcp_learned_1963_blocker_cert_repeats(
        &mut solver,
        clause_idx,
        true_slot,
        Literal::positive(Variable(true_slot as u32)).0,
        BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS - 1,
    );

    solver.decide(Literal::negative(Variable(0)));
    assert!(
        solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
        "first watched-literal scan should find the true wrapped tail"
    );
    solver.arena.set_saved_pos(clause_idx, saved_pos);
    solver.decide(Literal::negative(Variable(1)));
    assert!(
        solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
        "second watched-literal scan should use the repeated false-start-wrap cert"
    );

    let stats = solver.bcp_long_scan_stats();
    assert!(stats.learned_1963_blocker_cert_elision_enabled);
    assert_eq!(
        stats.learned_1963_blocker_cert_populates,
        u64::from(BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS)
    );
    assert_eq!(stats.learned_1963_blocker_cert_candidates, 2);
    assert_eq!(stats.learned_1963_blocker_cert_elisions, 1);
    assert_eq!(stats.learned_1963_blocker_cert_shadow_hits, 0);
    assert_eq!(stats.learned_1963_blocker_cert_stale_rejects, 0);
    assert_eq!(stats.learned_1963_blocker_cert_false_rejects, 0);
    assert_eq!(
        stats.learned_1963_blocker_cert_repeat_rejects, 1,
        "under-certified repeats must scan normally before certification can elide"
    );
    assert_eq!(
        stats.learned_1963_blocker_cert_elided_suffix_slots, 16,
        "len-32 prefix-validated elision should account for the skipped wrapped suffix"
    );
    assert_eq!(stats.learned_1963_blocker_cert_affected_fsw_rows, 1);
    let bucket = bcp_long_bucket_index(&stats.bucket_labels, "19-63");
    assert_eq!(
        stats.learned_scan_steps_by_len[bucket], 28,
        "the second watch scan should validate the normal prefix before eliding the suffix"
    );
    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        true_slot,
        "certified elision should not pin the old false saved position"
    );
}

#[test]
fn test_bcp_learned_1963_blocker_cert_elides_with_false_saved_pos_reset_enabled() {
    let clause_len = 32;
    let saved_pos = 20;
    let true_slot = 3usize;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.set_bcp_telemetry_enabled(true);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_learned_1963_false_saved_pos_reset_enabled(true);
    enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut solver);
    stage_bcp_blocker_cert_false_start_wrap(
        &mut solver,
        clause_idx,
        clause_len,
        saved_pos,
        true_slot,
    );
    seed_bcp_learned_1963_blocker_cert_repeats(
        &mut solver,
        clause_idx,
        true_slot,
        Literal::positive(Variable(true_slot as u32)).0,
        BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS - 1,
    );

    solver.decide(Literal::negative(Variable(0)));
    assert!(
        solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
        "first watched-literal scan should find the true wrapped tail"
    );
    solver.arena.set_saved_pos(clause_idx, saved_pos);
    solver.decide(Literal::negative(Variable(1)));
    assert!(
        solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
        "second watched-literal scan should use the repeated false-start-wrap cert"
    );

    let stats = solver.bcp_long_scan_stats();
    assert!(stats.learned_1963_blocker_cert_elision_enabled);
    assert_eq!(
        stats.learned_1963_blocker_cert_populates,
        u64::from(BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS)
    );
    assert_eq!(stats.learned_1963_blocker_cert_candidates, 2);
    assert_eq!(stats.learned_1963_blocker_cert_repeat_rejects, 1);
    assert_eq!(stats.learned_1963_blocker_cert_elisions, 1);
    assert_eq!(stats.learned_1963_blocker_cert_shadow_hits, 0);
    assert_eq!(stats.learned_1963_blocker_cert_shadow_mismatches, 0);
    assert_eq!(stats.learned_1963_blocker_cert_stale_rejects, 0);
    assert_eq!(stats.learned_1963_blocker_cert_false_rejects, 0);
    assert_eq!(stats.learned_1963_blocker_cert_elided_suffix_slots, 27);
    assert_eq!(stats.learned_1963_blocker_cert_affected_fsw_rows, 1);
    let bucket = bcp_long_bucket_index(&stats.bucket_labels, "19-63");
    assert_eq!(
        stats.learned_scan_steps_by_len[bucket], 4,
        "reset path should validate only the wrapped prefix before eliding"
    );
    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        true_slot,
        "certified elision should not pin the old false saved position"
    );
}

#[test]
fn test_bcp_learned_1963_blocker_cert_elision_falls_back_on_wrapped_prefix_non_false() {
    let clause_len = 32;
    let saved_pos = 20;
    let earlier_slot = 3usize;
    let cert_slot = 4usize;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut solver);

    let cert_lit = Literal::positive(Variable(cert_slot as u32));
    solver.decide(cert_lit);
    solver.qhead = solver.trail.len();
    solver.decide(Literal::negative(Variable(2)));
    solver.qhead = solver.trail.len();
    for slot in saved_pos..clause_len {
        solver.decide(Literal::negative(Variable(slot as u32)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, saved_pos);
    seed_bcp_learned_1963_blocker_cert(&mut solver, clause_idx, cert_slot, cert_lit.0);

    solver.decide(Literal::negative(Variable(0)));
    assert!(
        solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
        "fallback scan should preserve normal BCP behavior"
    );

    let earlier_lit = Literal::positive(Variable(earlier_slot as u32));
    assert_eq!(
        solver.arena.literal(clause_idx, 0),
        earlier_lit,
        "normal BCP must choose the earlier unassigned replacement"
    );
    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        earlier_slot,
        "fallback must preserve normal saved-position evolution"
    );

    let stats = solver.bcp_long_scan_stats();
    assert!(stats.learned_1963_blocker_cert_elision_enabled);
    assert_eq!(stats.learned_1963_blocker_cert_candidates, 1);
    assert_eq!(stats.learned_1963_blocker_cert_elisions, 0);
    assert_eq!(stats.learned_1963_blocker_cert_shadow_mismatches, 1);
    assert_eq!(
        stats.learned_1963_blocker_cert_elided_suffix_slots, 0,
        "mismatched certificates must not claim elided scan work"
    );
}

#[test]
fn test_bcp_learned_1963_blocker_cert_elision_falls_back_on_saved_suffix_non_false() {
    let clause_len = 32;
    let saved_pos = 20;
    let earlier_slot = 21usize;
    let cert_slot = 3usize;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut solver);

    let cert_lit = Literal::positive(Variable(cert_slot as u32));
    solver.decide(cert_lit);
    solver.qhead = solver.trail.len();
    solver.decide(Literal::negative(Variable(saved_pos as u32)));
    solver.qhead = solver.trail.len();
    for slot in (saved_pos + 2)..clause_len {
        solver.decide(Literal::negative(Variable(slot as u32)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, saved_pos);
    seed_bcp_learned_1963_blocker_cert(&mut solver, clause_idx, cert_slot, cert_lit.0);

    solver.decide(Literal::negative(Variable(0)));
    assert!(
        solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
        "fallback scan should preserve normal saved-suffix BCP behavior"
    );

    let earlier_lit = Literal::positive(Variable(earlier_slot as u32));
    assert_eq!(
        solver.arena.literal(clause_idx, 0),
        earlier_lit,
        "normal BCP must choose the unassigned suffix replacement"
    );
    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        earlier_slot,
        "fallback must preserve normal saved-position evolution"
    );

    let stats = solver.bcp_long_scan_stats();
    assert!(stats.learned_1963_blocker_cert_elision_enabled);
    assert_eq!(stats.learned_1963_blocker_cert_candidates, 1);
    assert_eq!(
        stats.learned_1963_blocker_cert_populates,
        u64::from(BCP_LEARNED_1963_BLOCKER_CERT_MIN_REPEATS)
    );
    assert_eq!(stats.learned_1963_blocker_cert_elisions, 0);
    assert_eq!(stats.learned_1963_blocker_cert_shadow_mismatches, 1);
    assert_eq!(stats.learned_1963_blocker_cert_stale_rejects, 0);
    assert_eq!(stats.learned_1963_blocker_cert_false_rejects, 0);
    assert_eq!(stats.learned_1963_blocker_cert_repeat_rejects, 0);
    assert_eq!(stats.learned_1963_blocker_cert_elided_suffix_slots, 0);
    assert_eq!(stats.learned_1963_blocker_cert_affected_fsw_rows, 0);
}

#[test]
fn test_bcp_learned_1963_blocker_cert_shadow_keeps_normal_saved_pos() {
    let clause_len = 32;
    let saved_pos = 20;
    let true_slot = 3usize;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.set_bcp_telemetry_enabled(true);
    solver.arena.set_learned(clause_idx, true);
    enable_bcp_learned_1963_blocker_cert_shadow_for_test(&mut solver);
    stage_bcp_blocker_cert_false_start_wrap(
        &mut solver,
        clause_idx,
        clause_len,
        saved_pos,
        true_slot,
    );
    solver.stats.record_bcp_learned_1963_blocker_cert_populate(
        clause_idx,
        true_slot,
        Literal::positive(Variable(true_slot as u32)).0,
        true,
    );

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());
    solver.decide(Literal::negative(Variable(1)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    let stats = solver.bcp_long_scan_stats();
    assert!(!stats.learned_1963_blocker_cert_elision_enabled);
    assert!(stats.learned_1963_blocker_cert_shadow_enabled);
    assert_eq!(
        stats.learned_1963_blocker_cert_candidates, 1,
        "shadow mode should not pin saved_pos to manufacture a second FSW candidate"
    );
    assert_eq!(
        stats.learned_1963_blocker_cert_repeat_rejects, 1,
        "shadow mode should still require a repeated FSW certificate"
    );
    assert_eq!(stats.learned_1963_blocker_cert_elisions, 0);
    assert_eq!(stats.learned_1963_blocker_cert_shadow_hits, 0);
    assert_eq!(stats.learned_1963_blocker_cert_shadow_mismatches, 0);
    assert_eq!(
        stats.learned_1963_blocker_cert_shadow_elided_suffix_slots,
        0
    );
    assert_eq!(stats.learned_1963_blocker_cert_shadow_affected_fsw_rows, 0);
    assert_eq!(
        stats.learned_1963_blocker_cert_elided_suffix_slots, 0,
        "shadow mode must not account active elided suffix slots"
    );
    let bucket = bcp_long_bucket_index(&stats.bucket_labels, "19-63");
    assert_eq!(
        stats.learned_scan_steps_by_len[bucket], 15,
        "shadow mode should run the normal second scan from the true saved position"
    );
    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        true_slot,
        "shadow mode must preserve normal saved-position evolution"
    );
}

#[test]
fn test_bcp_learned_1963_blocker_cert_shadow_records_scan_mismatch() {
    let clause_len = 32;
    let saved_pos = 20;
    let earlier_true_slot = 3usize;
    let cert_slot = 4usize;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    enable_bcp_learned_1963_blocker_cert_shadow_for_test(&mut solver);

    for slot in [earlier_true_slot, cert_slot] {
        solver.decide(Literal::positive(Variable(slot as u32)));
        solver.qhead = solver.trail.len();
    }
    solver.decide(Literal::negative(Variable(2)));
    solver.qhead = solver.trail.len();
    for slot in saved_pos..clause_len {
        solver.decide(Literal::negative(Variable(slot as u32)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, saved_pos);
    let cert_lit = Literal::positive(Variable(cert_slot as u32));
    seed_bcp_learned_1963_blocker_cert(&mut solver, clause_idx, cert_slot, cert_lit.0);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    let stats = solver.bcp_long_scan_stats();
    assert_eq!(stats.learned_1963_blocker_cert_candidates, 1);
    assert_eq!(stats.learned_1963_blocker_cert_shadow_hits, 1);
    assert_eq!(
        stats.learned_1963_blocker_cert_shadow_mismatches, 1,
        "shadow should expose when elision would choose a later true blocker than the normal scan"
    );
    assert_eq!(stats.learned_1963_blocker_cert_elisions, 0);
}

#[test]
fn test_bcp_learned_1963_blocker_cert_filters_non_fsw_candidate() {
    let clause_len = 32;
    let true_slot = 3usize;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut solver);

    let true_tail = Literal::positive(Variable(true_slot as u32));
    solver.decide(true_tail);
    solver.qhead = solver.trail.len();
    solver.arena.set_saved_pos(clause_idx, true_slot);
    solver.stats.record_bcp_learned_1963_blocker_cert_populate(
        clause_idx,
        true_slot,
        true_tail.0,
        true,
    );
    solver.stats.record_bcp_learned_1963_blocker_cert_populate(
        clause_idx,
        true_slot,
        true_tail.0,
        true,
    );

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    let stats = solver.bcp_long_scan_stats();
    assert_eq!(
        stats.learned_1963_blocker_cert_candidates, 0,
        "cert lookup must require a false saved start and wrapped saved position"
    );
    assert_eq!(stats.learned_1963_blocker_cert_elisions, 0);
}

#[test]
fn test_bcp_learned_1963_blocker_cert_rejects_stale_literal() {
    let clause_len = 32;
    let saved_pos = 20;
    let true_slot = 3usize;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut solver);
    stage_bcp_blocker_cert_false_start_wrap(
        &mut solver,
        clause_idx,
        clause_len,
        saved_pos,
        true_slot,
    );
    solver.stats.record_bcp_learned_1963_blocker_cert_populate(
        clause_idx,
        true_slot,
        Literal::positive(Variable(4)).0,
        true,
    );
    solver.stats.record_bcp_learned_1963_blocker_cert_populate(
        clause_idx,
        true_slot,
        Literal::positive(Variable(4)).0,
        true,
    );

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    let stats = solver.bcp_long_scan_stats();
    assert_eq!(stats.learned_1963_blocker_cert_candidates, 1);
    assert_eq!(stats.learned_1963_blocker_cert_stale_rejects, 1);
    assert_eq!(stats.learned_1963_blocker_cert_elisions, 0);
}

#[test]
fn test_bcp_learned_1963_blocker_cert_rejects_non_true_literal() {
    let clause_len = 32;
    let saved_pos = 20;
    let true_slot = 3usize;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut solver);

    solver.decide(Literal::negative(Variable(2)));
    solver.qhead = solver.trail.len();
    for slot in saved_pos..clause_len {
        solver.decide(Literal::negative(Variable(slot as u32)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, saved_pos);
    seed_bcp_learned_1963_blocker_cert(
        &mut solver,
        clause_idx,
        true_slot,
        Literal::positive(Variable(true_slot as u32)).0,
    );

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    let stats = solver.bcp_long_scan_stats();
    assert_eq!(stats.learned_1963_blocker_cert_candidates, 1);
    assert_eq!(stats.learned_1963_blocker_cert_false_rejects, 1);
    assert_eq!(stats.learned_1963_blocker_cert_false_reject_demotions, 0);
    assert_eq!(stats.learned_1963_blocker_cert_elisions, 0);
    assert!(
        solver
            .stats
            .bcp_learned_1963_blocker_cert(clause_idx)
            .is_some(),
        "default false reject must keep the cert available for the existing behavior"
    );
}

#[test]
fn test_bcp_learned_1963_blocker_cert_false_reject_demote_clears_cert() {
    let clause_len = 32;
    let saved_pos = 20;
    let true_slot = 3usize;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    enable_bcp_learned_1963_blocker_cert_elision_for_test(&mut solver);
    enable_bcp_learned_1963_blocker_cert_false_reject_demote_for_test(&mut solver);

    solver.decide(Literal::negative(Variable(2)));
    solver.qhead = solver.trail.len();
    for slot in saved_pos..clause_len {
        solver.decide(Literal::negative(Variable(slot as u32)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, saved_pos);
    let cert_lit = Literal::positive(Variable(true_slot as u32));
    seed_bcp_learned_1963_blocker_cert(&mut solver, clause_idx, true_slot, cert_lit.0);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    let stats = solver.bcp_long_scan_stats();
    assert!(stats.learned_1963_blocker_cert_false_reject_demote_enabled);
    assert_eq!(stats.learned_1963_blocker_cert_candidates, 1);
    assert_eq!(stats.learned_1963_blocker_cert_false_rejects, 1);
    assert_eq!(stats.learned_1963_blocker_cert_false_reject_demotions, 1);
    assert_eq!(stats.learned_1963_blocker_cert_elisions, 0);
    assert!(
        solver
            .stats
            .bcp_learned_1963_blocker_cert(clause_idx)
            .is_none(),
        "demotion should fail closed by clearing the non-true cert"
    );
}

#[test]
fn test_bcp_learned_1963_blocker_cert_false_reject_demote_alone_is_inert() {
    let clause_len = 32;
    let saved_pos = 20;
    let true_slot = 3usize;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    enable_bcp_learned_1963_blocker_cert_false_reject_demote_for_test(&mut solver);

    solver.decide(Literal::negative(Variable(2)));
    solver.qhead = solver.trail.len();
    for slot in saved_pos..clause_len {
        solver.decide(Literal::negative(Variable(slot as u32)));
        solver.qhead = solver.trail.len();
    }
    solver.arena.set_saved_pos(clause_idx, saved_pos);
    let cert_lit = Literal::positive(Variable(true_slot as u32));
    solver
        .stats
        .record_bcp_learned_1963_blocker_cert_populate(clause_idx, true_slot, cert_lit.0, true);
    solver
        .stats
        .record_bcp_learned_1963_blocker_cert_populate(clause_idx, true_slot, cert_lit.0, true);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    let stats = solver.bcp_long_scan_stats();
    assert!(stats.learned_1963_blocker_cert_false_reject_demote_enabled);
    assert!(!stats.learned_1963_blocker_cert_elision_enabled);
    assert!(!stats.learned_1963_blocker_cert_shadow_enabled);
    assert_eq!(
        stats.learned_1963_blocker_cert_candidates, 0,
        "demotion alone must not activate blocker-cert lookup"
    );
    assert_eq!(stats.learned_1963_blocker_cert_false_rejects, 0);
    assert_eq!(stats.learned_1963_blocker_cert_false_reject_demotions, 0);
    assert_eq!(stats.learned_1963_blocker_cert_elisions, 0);
    assert!(
        solver
            .stats
            .bcp_learned_1963_blocker_cert(clause_idx)
            .is_some(),
        "demotion alone must not clear a cert that was never looked up"
    );
}

#[test]
fn test_bcp_learned_1963_blocker_cert_ignores_original_len18_and_len64() {
    for (clause_len, learned) in [(32usize, false), (18usize, true), (64usize, true)] {
        let solver = run_bcp_blocker_cert_two_watch_route(clause_len, learned, true, false);
        let stats = solver.bcp_long_scan_stats();
        assert!(
            stats.learned_1963_blocker_cert_elision_enabled,
            "test gate should be enabled for len-{clause_len} learned={learned}"
        );
        assert_eq!(
            stats.learned_1963_blocker_cert_candidates, 0,
            "len-{clause_len} learned={learned} should not attempt cert lookup outside learned 19-63"
        );
        assert_eq!(
            stats.learned_1963_blocker_cert_populates, 0,
            "len-{clause_len} learned={learned} should not populate certs outside learned 19-63"
        );
        assert_eq!(
            stats.learned_1963_blocker_cert_elisions, 0,
            "len-{clause_len} learned={learned} should not elide outside learned 19-63"
        );
    }
}

#[test]
fn test_bcp_learned_1963_blocker_cert_lifetime_helpers_clear_and_remap() {
    let mut solver = Solver::new(8);
    let old_offset = 2usize;
    let new_offset = 5usize;
    let cert_lit = Literal::positive(Variable(3));
    solver
        .stats
        .record_bcp_learned_1963_blocker_cert_populate(old_offset, 3, cert_lit.0, true);
    let mut remap = vec![u32::MAX; old_offset + 1];
    remap[old_offset] = new_offset as u32;

    solver.stats.remap_bcp_learned_1963_blocker_certs(&remap);

    assert!(
        solver
            .stats
            .bcp_learned_1963_blocker_cert(old_offset)
            .is_none(),
        "remap must remove the old arena-offset key"
    );
    let remapped = solver
        .stats
        .bcp_learned_1963_blocker_cert(new_offset)
        .expect("remapped cert");
    assert_eq!(remapped.clause_offset, new_offset);
    assert_eq!(remapped.position, 3);
    assert_eq!(remapped.literal_raw, cert_lit.0);

    solver.stats.clear_bcp_learned_1963_blocker_certs();
    assert!(
        solver
            .stats
            .bcp_learned_1963_blocker_cert(new_offset)
            .is_none(),
        "clear helper must invalidate every certificate"
    );
}

#[test]
fn test_bcp_learned_1963_blocker_cert_arena_compaction_remaps_table() {
    let mut solver = Solver::new(40);
    let dead_prefix = solver.add_clause_db(
        &[
            Literal::positive(Variable(35)),
            Literal::positive(Variable(36)),
            Literal::positive(Variable(37)),
        ],
        false,
    );
    let (old_offset, cert_lit) = add_learned_1963_clause_with_blocker_cert(&mut solver);
    assert!(
        old_offset > dead_prefix,
        "test setup expects the certified clause to move during compaction"
    );
    solver.arena.delete(dead_prefix);

    solver.compact_arena_locality();

    assert!(
        solver
            .stats
            .bcp_learned_1963_blocker_cert(old_offset)
            .is_none(),
        "compaction must remove the stale pre-compaction offset key"
    );
    let new_offset = solver
        .arena
        .active_indices()
        .find(|&idx| solver.arena.is_learned(idx) && solver.arena.len_of(idx) == 32)
        .expect("compacted learned 19-63 clause");
    assert_ne!(
        new_offset, old_offset,
        "test setup should force a non-identity remap"
    );
    let cert = solver
        .stats
        .bcp_learned_1963_blocker_cert(new_offset)
        .expect("compaction should remap the blocker cert to the new arena offset");
    assert_eq!(cert.clause_offset, new_offset);
    assert_eq!(cert.position, 3);
    assert_eq!(cert.literal_raw, cert_lit.0);
}

#[test]
fn test_bcp_learned_1963_blocker_cert_clone_drops_table() {
    let mut solver = Solver::new(32);
    let (clause_idx, _) = add_learned_1963_clause_with_blocker_cert(&mut solver);

    let clone = solver.clone_for_incremental();

    assert!(
        solver
            .stats
            .bcp_learned_1963_blocker_cert(clause_idx)
            .is_some(),
        "cloning must not mutate the source solver's cert table"
    );
    assert!(
        clone
            .stats
            .bcp_learned_1963_blocker_cert(clause_idx)
            .is_none(),
        "clone must start without arena-offset blocker certs"
    );
}

#[test]
fn test_bcp_learned_1963_blocker_cert_reset_drops_table() {
    let mut solver = Solver::new(32);
    let (clause_idx, _) = add_learned_1963_clause_with_blocker_cert(&mut solver);
    assert!(solver
        .stats
        .bcp_learned_1963_blocker_cert(clause_idx)
        .is_some());

    solver.reset_search_state();

    assert!(
        solver
            .stats
            .bcp_learned_1963_blocker_cert(clause_idx)
            .is_none(),
        "reset_search_state must clear arena-offset blocker certs"
    );
}

#[test]
fn test_bcp_learned_1963_blocker_cert_rebuild_watches_drops_table() {
    let mut solver = Solver::new(32);
    let (clause_idx, _) = add_learned_1963_clause_with_blocker_cert(&mut solver);
    assert!(solver
        .stats
        .bcp_learned_1963_blocker_cert(clause_idx)
        .is_some());

    solver.rebuild_watches();

    assert!(
        solver
            .stats
            .bcp_learned_1963_blocker_cert(clause_idx)
            .is_none(),
        "full watch rebuild must clear position-sensitive blocker certs"
    );
}

#[test]
fn test_bcp_learned_1963_blocker_cert_replace_drops_clause_cert() {
    let mut solver = Solver::new(32);
    let (clause_idx, _) = add_learned_1963_clause_with_blocker_cert(&mut solver);
    assert!(solver
        .stats
        .bcp_learned_1963_blocker_cert(clause_idx)
        .is_some());

    let replacement: Vec<Literal> = (0..31)
        .map(|i| Literal::positive(Variable(i as u32)))
        .collect();
    assert_eq!(
        solver.replace_clause_checked(clause_idx, &replacement),
        mutate::ReplaceResult::Replaced
    );

    assert!(
        solver
            .stats
            .bcp_learned_1963_blocker_cert(clause_idx)
            .is_none(),
        "in-place replacement must drop the stale position-sensitive blocker cert"
    );
}

#[test]
fn test_bcp_learned_1963_blocker_cert_delete_drops_clause_cert() {
    let mut solver = Solver::new(32);
    let (clause_idx, _) = add_learned_1963_clause_with_blocker_cert(&mut solver);
    assert!(solver
        .stats
        .bcp_learned_1963_blocker_cert(clause_idx)
        .is_some());

    assert_eq!(
        solver.delete_clause_checked(clause_idx, mutate::ReasonPolicy::Skip),
        mutate::DeleteResult::Deleted
    );

    assert!(
        solver
            .stats
            .bcp_learned_1963_blocker_cert(clause_idx)
            .is_none(),
        "clause deletion must drop the stale blocker cert"
    );
}

#[test]
fn test_bcp_learned_1963_blocker_cert_pending_garbage_mark_drops_clause_cert() {
    let mut solver = Solver::new(32);
    let (clause_idx, _) = add_learned_1963_clause_with_blocker_cert(&mut solver);
    assert!(solver
        .stats
        .bcp_learned_1963_blocker_cert(clause_idx)
        .is_some());

    assert!(solver.mark_clause_garbage_lazy(clause_idx));

    assert!(
        solver
            .stats
            .bcp_learned_1963_blocker_cert(clause_idx)
            .is_none(),
        "pending-garbage marking must drop the stale blocker cert"
    );
}

#[test]
fn test_bcp_learned_1963_blocker_cert_reconnect_bve_watches_drops_table() {
    let mut solver = Solver::new(32);
    let (clause_idx, _) = add_learned_1963_clause_with_blocker_cert(&mut solver);
    assert!(solver
        .stats
        .bcp_learned_1963_blocker_cert(clause_idx)
        .is_some());

    solver.reconnect_bve_watches(solver.arena.len());

    assert!(
        solver
            .stats
            .bcp_learned_1963_blocker_cert(clause_idx)
            .is_none(),
        "incremental watch reconnect must clear position-sensitive blocker certs"
    );
}

#[test]
fn test_bcp_learned_1963_blocker_cert_promotion_drops_clause_cert() {
    let mut solver = Solver::new(32);
    let (clause_idx, _) = add_learned_1963_clause_with_blocker_cert(&mut solver);
    assert!(solver.arena.is_learned(clause_idx));
    assert!(solver
        .stats
        .bcp_learned_1963_blocker_cert(clause_idx)
        .is_some());

    solver.arena.set_learned(clause_idx, false);
    let promoted_lits = solver.arena.literals(clause_idx).to_vec();
    solver.note_clause_promoted_to_irredundant(clause_idx, &promoted_lits);

    assert!(
        solver
            .stats
            .bcp_learned_1963_blocker_cert(clause_idx)
            .is_none(),
        "learned-to-irredundant promotion must drop the learned-only blocker cert"
    );
}

#[test]
fn test_bcp_learned_1963_true_tail_relocation_default_off_keeps_blocker_only() {
    let clause_len = 32;
    let true_slot = 3;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);

    let watched_lit = Literal::positive(Variable(0));
    let true_tail = Literal::positive(Variable(true_slot as u32));
    solver.decide(true_tail);
    solver.qhead = solver.trail.len();
    solver.arena.set_saved_pos(clause_idx, true_slot);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.literal(clause_idx, 0),
        watched_lit,
        "default-off true-tail policy should keep the original watched literal"
    );
    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        true_slot,
        "default-off true-tail policy should keep saved_pos on the found true slot"
    );
    assert_eq!(
        solver.watches.len_of(watched_lit),
        1,
        "default-off true-tail policy should keep the watcher on the falsified watch list"
    );
    assert_eq!(
        solver.watches.len_of(true_tail),
        0,
        "default-off true-tail policy should not add a tail watch"
    );
    assert_eq!(
        solver.watches.blocker(watched_lit, 0),
        true_tail,
        "default-off true-tail policy should only refresh the blocker"
    );
    let long_stats = solver.bcp_long_scan_stats();
    assert!(
        !long_stats.learned_1963_true_tail_relocation_enabled,
        "default-off stats should report the relocation gate disabled"
    );
    assert_eq!(
        long_stats.learned_1963_true_tail_relocation_attempts, 0,
        "default-off relocation gate must not count attempts"
    );
    assert_eq!(
        long_stats.learned_1963_true_tail_relocation_moves, 0,
        "default-off relocation gate must not count moved watches"
    );
}

#[test]
fn test_bcp_learned_618_true_tail_relocation_default_off_keeps_blocker_only() {
    for clause_len in [6usize, 18usize] {
        let true_slot = 3;
        let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
        solver.arena.set_learned(clause_idx, true);

        let watched_lit = Literal::positive(Variable(0));
        let true_tail = Literal::positive(Variable(true_slot as u32));
        solver.decide(true_tail);
        solver.qhead = solver.trail.len();
        solver.arena.set_saved_pos(clause_idx, true_slot);

        solver.decide(Literal::negative(Variable(0)));
        assert!(
            solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
            "len-{clause_len} default-off 6-18 relocation should not conflict"
        );

        assert_eq!(
            solver.arena.literal(clause_idx, 0),
            watched_lit,
            "len-{clause_len} default-off 6-18 policy should keep the original watched literal"
        );
        assert_eq!(
            solver.arena.saved_pos(clause_idx),
            true_slot,
            "len-{clause_len} default-off 6-18 policy should keep saved_pos on the found true slot"
        );
        assert_eq!(
            solver.watches.len_of(watched_lit),
            1,
            "len-{clause_len} default-off 6-18 policy should keep the watcher on the falsified watch list"
        );
        assert_eq!(
            solver.watches.len_of(true_tail),
            0,
            "len-{clause_len} default-off 6-18 policy should not add a tail watch"
        );
        assert_eq!(
            solver.watches.blocker(watched_lit, 0),
            true_tail,
            "len-{clause_len} default-off 6-18 policy should only refresh the blocker"
        );
        let long_stats = solver.bcp_long_scan_stats();
        assert!(
            !long_stats.learned_618_true_tail_relocation_enabled,
            "default-off stats should report the 6-18 relocation gate disabled"
        );
        assert_eq!(
            long_stats.learned_618_true_tail_relocation_attempts, 0,
            "default-off 6-18 relocation gate must not count attempts"
        );
        assert_eq!(
            long_stats.learned_618_true_tail_relocation_moves, 0,
            "default-off 6-18 relocation gate must not count moved watches"
        );
    }
}

#[test]
fn test_bcp_learned_1963_true_tail_relocation_moves_watch_and_advances_saved_pos() {
    let clause_len = 32;
    let true_slot = 3;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_telemetry_enabled(true);
    solver.set_bcp_learned_1963_true_tail_relocation_enabled(true);

    let watched_lit = Literal::positive(Variable(0));
    let true_tail = Literal::positive(Variable(true_slot as u32));
    solver.decide(true_tail);
    solver.qhead = solver.trail.len();
    solver.arena.set_saved_pos(clause_idx, true_slot);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.literal(clause_idx, 0),
        true_tail,
        "enabled true-tail policy should move the true tail into the watched slot"
    );
    assert_eq!(
        solver.arena.literal(clause_idx, true_slot),
        watched_lit,
        "enabled true-tail policy should swap the falsified watch into the tail"
    );
    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        true_slot + 1,
        "saved_pos should advance past the tail slot now holding the falsified watch"
    );
    assert_eq!(
        solver.watches.len_of(watched_lit),
        0,
        "enabled true-tail policy should remove the falsified watch-list entry"
    );
    assert_eq!(
        solver.watches.len_of(true_tail),
        1,
        "enabled true-tail policy should add a watcher to the true tail"
    );
    let long_stats = solver.bcp_long_scan_stats();
    assert!(
        long_stats.learned_1963_true_tail_relocation_enabled,
        "stats should report the relocation gate enabled"
    );
    assert_eq!(
        long_stats.learned_1963_true_tail_relocation_attempts, 1,
        "enabled telemetry should count one eligible relocation candidate"
    );
    assert_eq!(
        long_stats.learned_1963_true_tail_relocation_moves, 1,
        "enabled telemetry should count the moved true-tail watch"
    );
}

#[test]
fn test_bcp_learned_618_true_tail_relocation_moves_watch_and_advances_saved_pos() {
    for clause_len in [6usize, 18usize] {
        let true_slot = 3;
        let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
        solver.arena.set_learned(clause_idx, true);
        solver.set_bcp_telemetry_enabled(true);
        solver.set_bcp_learned_618_true_tail_relocation_enabled(true);

        let watched_lit = Literal::positive(Variable(0));
        let true_tail = Literal::positive(Variable(true_slot as u32));
        solver.decide(true_tail);
        solver.qhead = solver.trail.len();
        solver.arena.set_saved_pos(clause_idx, true_slot);

        solver.decide(Literal::negative(Variable(0)));
        assert!(
            solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
            "len-{clause_len} enabled 6-18 true-tail relocation should not conflict"
        );

        assert_eq!(
            solver.arena.literal(clause_idx, 0),
            true_tail,
            "len-{clause_len} enabled 6-18 policy should move the true tail into the watched slot"
        );
        assert_eq!(
            solver.arena.literal(clause_idx, true_slot),
            watched_lit,
            "len-{clause_len} enabled 6-18 policy should swap the falsified watch into the tail"
        );
        assert_eq!(
            solver.arena.saved_pos(clause_idx),
            true_slot + 1,
            "len-{clause_len} saved_pos should advance past the tail slot now holding the falsified watch"
        );
        assert_eq!(
            solver.watches.len_of(watched_lit),
            0,
            "len-{clause_len} enabled 6-18 policy should remove the falsified watch-list entry"
        );
        assert_eq!(
            solver.watches.len_of(true_tail),
            1,
            "len-{clause_len} enabled 6-18 policy should add a watcher to the true tail"
        );
        let long_stats = solver.bcp_long_scan_stats();
        assert!(
            long_stats.learned_618_true_tail_relocation_enabled,
            "stats should report the 6-18 relocation gate enabled"
        );
        assert_eq!(
            long_stats.learned_618_true_tail_relocation_attempts, 1,
            "enabled 6-18 telemetry should count one eligible relocation candidate"
        );
        assert_eq!(
            long_stats.learned_618_true_tail_relocation_moves, 1,
            "enabled 6-18 telemetry should count the moved true-tail watch"
        );
        assert_eq!(
            long_stats.learned_1963_true_tail_relocation_attempts, 0,
            "6-18 relocation should not use the 19-63 telemetry bucket"
        );
    }
}

#[test]
fn test_bcp_learned_1963_true_tail_relocation_saved_pos_wraps() {
    let clause_len = 32;
    let true_slot = clause_len - 1;
    let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
    solver.arena.set_learned(clause_idx, true);
    solver.set_bcp_telemetry_enabled(true);
    solver.set_bcp_learned_1963_true_tail_relocation_enabled(true);

    let true_tail = Literal::positive(Variable(true_slot as u32));
    solver.decide(true_tail);
    solver.qhead = solver.trail.len();
    solver.arena.set_saved_pos(clause_idx, true_slot);

    solver.decide(Literal::negative(Variable(0)));
    assert!(solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none());

    assert_eq!(
        solver.arena.saved_pos(clause_idx),
        2,
        "saved_pos should wrap inside the tail range after relocating the last tail slot"
    );
    assert_eq!(
        solver.arena.literal(clause_idx, true_slot),
        Literal::positive(Variable(0)),
        "last tail slot should hold the just-falsified watched literal after relocation"
    );
}

#[test]
fn test_bcp_learned_1963_true_tail_relocation_ignores_original_len18_and_len64() {
    for (clause_len, learned) in [(32usize, false), (18usize, true), (64usize, true)] {
        let true_slot = 3;
        let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
        solver.arena.set_learned(clause_idx, learned);
        solver.set_bcp_learned_1963_true_tail_relocation_enabled(true);

        let watched_lit = Literal::positive(Variable(0));
        let true_tail = Literal::positive(Variable(true_slot as u32));
        solver.decide(true_tail);
        solver.qhead = solver.trail.len();
        solver.arena.set_saved_pos(clause_idx, true_slot);

        solver.decide(Literal::negative(Variable(0)));
        assert!(
            solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
            "len-{clause_len} learned={learned} true-tail guard should not conflict"
        );

        assert_eq!(
            solver.arena.literal(clause_idx, 0),
            watched_lit,
            "len-{clause_len} learned={learned} should not relocate outside the learned 19-63 gate"
        );
        assert_eq!(
            solver.watches.len_of(true_tail),
            0,
            "len-{clause_len} learned={learned} should not add a true-tail watch"
        );
    }
}

#[test]
fn test_bcp_learned_618_true_tail_relocation_ignores_original_and_len19() {
    for (clause_len, learned) in [(12usize, false), (19usize, true)] {
        let true_slot = 3;
        let (mut solver, clause_idx) = bcp_len_test_solver(clause_len);
        solver.arena.set_learned(clause_idx, learned);
        solver.set_bcp_telemetry_enabled(true);
        solver.set_bcp_learned_618_true_tail_relocation_enabled(true);

        let watched_lit = Literal::positive(Variable(0));
        let true_tail = Literal::positive(Variable(true_slot as u32));
        solver.decide(true_tail);
        solver.qhead = solver.trail.len();
        solver.arena.set_saved_pos(clause_idx, true_slot);

        solver.decide(Literal::negative(Variable(0)));
        assert!(
            solver.propagate_bcp::<{ bcp_mode::SEARCH }>().is_none(),
            "len-{clause_len} learned={learned} 6-18 guard should not conflict"
        );

        assert_eq!(
            solver.arena.literal(clause_idx, 0),
            watched_lit,
            "len-{clause_len} learned={learned} should not relocate outside the learned 6-18 gate"
        );
        assert_eq!(
            solver.watches.len_of(true_tail),
            0,
            "len-{clause_len} learned={learned} should not add a 6-18 true-tail watch"
        );
        let long_stats = solver.bcp_long_scan_stats();
        assert_eq!(
            long_stats.learned_618_true_tail_relocation_attempts, 0,
            "len-{clause_len} learned={learned} should not count 6-18 relocation attempts"
        );
    }
}

#[test]
fn test_safe_bcp_binary_prefix_continues_after_first_conflict() {
    let mut solver: Solver = Solver::new(4);
    let x = Variable(0);
    let y = Variable(1);
    let z = Variable(2);
    let w = Variable(3);

    solver.add_clause(vec![Literal::negative(x), Literal::negative(y)]);
    solver.add_clause(vec![Literal::negative(x), Literal::positive(z)]);
    solver.add_clause(vec![Literal::negative(x), Literal::negative(w)]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    for lit in [Literal::positive(y), Literal::positive(w)] {
        solver.decide(lit);
        solver.qhead = solver.trail.len();
    }
    solver.decide(Literal::positive(x));

    let conflict = solver.propagate_bcp::<{ bcp_mode::SEARCH }>();
    assert!(conflict.is_some(), "binary conflict expected");
    assert_eq!(
        solver.lit_val(Literal::positive(z)),
        1,
        "safe binary-prefix scan should keep propagating after the first binary conflict"
    );
}

#[test]
fn test_search_propagate_matches_probe_path_without_probing_mode() {
    fn next_u64(state: &mut u64) -> u64 {
        *state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        *state
    }

    fn next_literal(state: &mut u64, num_vars: usize) -> Literal {
        let var = Variable((next_u64(state) % num_vars as u64) as u32);
        if next_u64(state) & 1 == 0 {
            Literal::positive(var)
        } else {
            Literal::negative(var)
        }
    }

    const NUM_FORMULAS: usize = 64;
    const NUM_VARS: usize = 10;

    for seed in 0..NUM_FORMULAS as u64 {
        let mut state = seed ^ 0x9E37_79B9_7F4A_7C15;
        let mut formula: Vec<Vec<Literal>> = Vec::new();
        let clause_count = 6 + (next_u64(&mut state) % 10) as usize;

        for _ in 0..clause_count {
            let clause_len = 2 + (next_u64(&mut state) % 3) as usize;
            let mut clause = Vec::with_capacity(clause_len);
            while clause.len() < clause_len {
                let lit = next_literal(&mut state, NUM_VARS);
                if !clause.contains(&lit) {
                    clause.push(lit);
                }
            }
            formula.push(clause);
        }

        let mut probe_like: Solver = Solver::new(NUM_VARS);
        let mut search: Solver = Solver::new(NUM_VARS);
        for clause in &formula {
            probe_like.add_clause(clause.clone());
            search.add_clause(clause.clone());
        }

        probe_like.initialize_watches();
        search.initialize_watches();
        let probe_ok = probe_like.process_initial_clauses().is_none();
        let search_ok = search.process_initial_clauses().is_none();
        assert_eq!(
            search_ok, probe_ok,
            "initial clause processing diverged for seed {seed}",
        );
        if !probe_ok {
            continue;
        }

        let decisions = (next_u64(&mut state) % 4) as usize;
        let mut early_conflict = false;
        for _ in 0..decisions {
            let lit = next_literal(&mut state, NUM_VARS);
            let var_idx = lit.variable().index();
            if probe_like.var_is_assigned(var_idx) {
                continue;
            }
            probe_like.decide(lit);
            search.decide(lit);
            // Propagate between decisions: decide() requires qhead == trail.len()
            // (CaDiCaL propagate.cpp:188 — all propagations complete before deciding).
            let probe_c = probe_like.propagate();
            let search_c = search.search_propagate();
            if probe_c.is_some() || search_c.is_some() {
                assert_eq!(
                    search_c.is_some(),
                    probe_c.is_some(),
                    "conflict mismatch during decision for seed {seed}",
                );
                early_conflict = true;
                break;
            }
        }
        if early_conflict {
            continue;
        }

        // Final propagation (in case 0 decisions were made).
        let probe_conflict = probe_like.propagate();
        let search_conflict = search.search_propagate();
        assert_eq!(
            search_conflict.is_some(),
            probe_conflict.is_some(),
            "conflict mismatch for seed {seed}",
        );
        if let (Some(probe_cref), Some(search_cref)) = (probe_conflict, search_conflict) {
            let probe_clause = probe_like.arena.literals(probe_cref.0 as usize);
            let search_clause = search.arena.literals(search_cref.0 as usize);
            assert_eq!(
                search_clause, probe_clause,
                "conflict clause mismatch for seed {seed}",
            );
        }

        assert_eq!(
            search.trail, probe_like.trail,
            "trail mismatch for seed {seed}"
        );
        assert_eq!(
            search.vals, probe_like.vals,
            "vals mismatch for seed {seed}",
        );
        assert_eq!(
            search.var_data, probe_like.var_data,
            "var_data mismatch for seed {seed}"
        );
        assert_eq!(
            search.qhead, probe_like.qhead,
            "qhead mismatch for seed {seed}"
        );
        assert_eq!(
            search.no_conflict_until, probe_like.no_conflict_until,
            "no_conflict_until mismatch for seed {seed}",
        );
    }
}

// ========================================================================
// Watch attachment tests (extracted from tests.rs, Part of #5142)
// ========================================================================

#[test]
fn test_watch_attachment_checker_covers_all_insertion_paths() {
    let mut solver: Solver = Solver::new(6);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);
    let x3 = Variable(3);
    let x4 = Variable(4);
    let x5 = Variable(5);

    // initialize_watches path (pre-solve clause insertion via add_clause).
    solver.add_clause(vec![
        Literal::positive(x0),
        Literal::positive(x1),
        Literal::positive(x2),
    ]);
    solver.add_clause(vec![
        Literal::negative(x0),
        Literal::negative(x1),
        Literal::positive(x3),
    ]);
    solver.initialize_watches();
    assert_watch_invariant_for_all_active_clauses(&solver, "initialize_watches");

    // add_clause_watched path.
    let mut irredundant = [
        Literal::negative(x2),
        Literal::positive(x4),
        Literal::positive(x5),
    ];
    let _ = solver.add_clause_watched(&mut irredundant);
    assert_watch_invariant_for_all_active_clauses(&solver, "add_clause_watched");

    // add_theory_lemma path.
    let theory_ref = solver.add_theory_lemma(vec![
        Literal::negative(x3),
        Literal::positive(x4),
        Literal::negative(x5),
    ]);
    assert!(theory_ref.is_some(), "expected theory lemma to be inserted");
    assert_watch_invariant_for_all_active_clauses(&solver, "add_theory_lemma");

    // add_learned_clause path (learned backtrack-order policy).
    solver.var_data[x0.index()].level = 1;
    solver.var_data[x4.index()].level = 5;
    solver.var_data[x5.index()].level = 3;
    let learned_ref = solver.add_learned_clause(
        vec![
            Literal::negative(x0),
            Literal::positive(x5),
            Literal::positive(x4),
        ],
        2,
        &[],
    );
    let learned_idx = learned_ref.0 as usize;
    assert_eq!(
        solver.arena.literal(learned_idx, 1),
        Literal::positive(x4),
        "learned-clause watch policy must place max non-UIP level at index 1"
    );
    assert_watch_invariant_for_all_active_clauses(&solver, "add_learned_clause");

    // replace_clause_checked path (strengthen/rewrite attachment).
    let _ =
        solver.replace_clause_checked(learned_idx, &[Literal::negative(x0), Literal::positive(x4)]);
    assert_watch_invariant_for_all_active_clauses(&solver, "replace_clause_checked");

    // rebuild_watches path.
    let rebuild_lits = &[
        Literal::positive(x1),
        Literal::positive(x0),
        Literal::positive(x2),
    ];
    solver.arena.replace(0, rebuild_lits);
    solver.arena.set_saved_pos(0, 2);
    // Mark trail as affected since clause content changed (#8095).
    solver.mark_trail_affected(0);
    solver.rebuild_watches();
    assert_watch_invariant_for_all_active_clauses(&solver, "rebuild_watches");
}

/// Test incremental watch maintenance via `apply_decompose_mutation`.
///
/// Verifies that clause deletion and replacement through the incremental
/// path (used by decompose/sweep) produces correct watch state without
/// a full `rebuild_watches()` call (#8093).
#[test]
fn test_incremental_watch_maintenance_delete_and_replace() {
    use crate::decompose::ClauseMutation;

    let mut solver: Solver = Solver::new(6);
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);
    let d = Variable(3);
    let e = Variable(4);
    let f = Variable(5);

    // Clause 0: (a, b, c)
    solver.add_clause(vec![
        Literal::positive(a),
        Literal::positive(b),
        Literal::positive(c),
    ]);
    // Clause 1: (d, e)
    solver.add_clause(vec![Literal::positive(d), Literal::positive(e)]);
    // Clause 2: (a, d, f) -- will be replaced
    solver.add_clause(vec![
        Literal::positive(a),
        Literal::positive(d),
        Literal::positive(f),
    ]);
    // Clause 3: (b, e, f) -- will be deleted
    solver.add_clause(vec![
        Literal::positive(b),
        Literal::positive(e),
        Literal::positive(f),
    ]);

    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    assert_watch_invariant_for_all_active_clauses(&solver, "before_mutations");

    // Get clause indices from arena.
    let clause2_idx = {
        let mut found = None;
        for idx in solver.arena.active_indices() {
            let lits = solver.arena.literals(idx);
            if lits.len() == 3
                && lits.contains(&Literal::positive(a))
                && lits.contains(&Literal::positive(d))
                && lits.contains(&Literal::positive(f))
            {
                found = Some(idx);
                break;
            }
        }
        found.expect("clause 2 not found")
    };
    let clause3_idx = {
        let mut found = None;
        for idx in solver.arena.active_indices() {
            let lits = solver.arena.literals(idx);
            if lits.len() == 3
                && lits.contains(&Literal::positive(b))
                && lits.contains(&Literal::positive(e))
                && lits.contains(&Literal::positive(f))
            {
                found = Some(idx);
                break;
            }
        }
        found.expect("clause 3 not found")
    };

    // Apply incremental mutations: delete clause 3, replace clause 2.
    let delete_mutation = ClauseMutation::Deleted {
        clause_idx: clause3_idx,
        old: vec![
            Literal::positive(b),
            Literal::positive(e),
            Literal::positive(f),
        ],
    };
    let replace_mutation = ClauseMutation::Replaced {
        clause_idx: clause2_idx,
        old: vec![
            Literal::positive(a),
            Literal::positive(d),
            Literal::positive(f),
        ],
        new: vec![Literal::positive(a), Literal::positive(d)],
    };

    solver.apply_decompose_mutation(&delete_mutation);
    solver.apply_decompose_mutation(&replace_mutation);

    // Finalize incrementally (no full rebuild).
    solver.mark_trail_affected(0);
    solver.finalize_incremental_watches();

    // Verify the watch invariant: all active clauses should have valid watches.
    assert_watch_invariant_for_all_active_clauses(&solver, "after_incremental_maintenance");

    // Verify deleted clause has no watches.
    let deleted_cref = ClauseRef(clause3_idx as u32);
    for vi in 0..6 {
        for sign in [true, false] {
            let lit = if sign {
                Literal::positive(Variable(vi))
            } else {
                Literal::negative(Variable(vi))
            };
            let wl = solver.watches.get_watches(lit);
            for wi in 0..wl.len() {
                assert_ne!(
                    wl.clause_ref(wi),
                    deleted_cref,
                    "stale watch for deleted clause {clause3_idx} on lit {lit:?}"
                );
            }
        }
    }

    // Verify the replaced clause is now binary (a, d) with correct watches.
    let replaced_cref = ClauseRef(clause2_idx as u32);
    let has_watch_a = {
        let wl = solver.watches.get_watches(Literal::positive(a));
        (0..wl.len()).any(|i| wl.clause_ref(i) == replaced_cref)
    };
    let has_watch_d = {
        let wl = solver.watches.get_watches(Literal::positive(d));
        (0..wl.len()).any(|i| wl.clause_ref(i) == replaced_cref)
    };
    assert!(
        has_watch_a && has_watch_d,
        "replaced clause should have watches on a and d"
    );
}

/// Regression test for #4797: add_preserved_learned must not panic when
/// learned clauses reference variables beyond the solver's current num_vars.
///
/// In branch-and-bound, the previous solver instance may have allocated extra
/// SAT variables (e.g., from split atoms). When those learned clauses are
/// replayed into a fresh solver with fewer variables, add_preserved_learned
/// must expand num_vars to accommodate them.
#[test]
fn test_add_preserved_learned_expands_num_vars_for_out_of_range_lits() {
    // Create a solver with only 3 variables.
    let mut solver: Solver = Solver::new(3);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());

    assert_eq!(solver.num_vars, 3);

    // Add a "preserved learned" clause that references variables 4 and 5
    // (indices beyond num_vars=3). Without the #4797 fix, this panics with:
    // "BUG: literal variable out of range (num_vars=3)"
    let result = solver.add_preserved_learned(vec![
        Literal::positive(Variable(4)),
        Literal::negative(Variable(5)),
    ]);
    assert!(
        result,
        "add_preserved_learned should succeed after expanding num_vars"
    );
    assert!(
        solver.num_vars >= 6,
        "num_vars should have expanded to at least 6, got {}",
        solver.num_vars
    );
    assert_watch_invariant_for_all_active_clauses(
        &solver,
        "add_preserved_learned with out-of-range vars",
    );
}
