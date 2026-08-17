// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::solver::inprocessing::{
    BackboneSkipReason, FactorSkipReason, HtrSkipReason, SweepSkipReason, VivifySkipReason,
};

const FACTOR_TICK_THRESHOLD: u64 = 7;
const HTR_TICK_THRESHOLD: u64 = 6;
const BACKBONE_TICK_THRESHOLD: u64 = 8;
const SWEEP_TICK_THRESHOLD: u64 = 8;
const VIVIFY_TICK_THRESHOLD: u64 = 20;

#[test]
fn test_deduplicate_binary_clauses_prefers_irredundant_duplicate() {
    let mut solver: Solver = Solver::new(2);
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));

    let learned_dup = solver.add_clause_db(&[a, b], true);
    let irred_dup = solver.add_clause_db(&[a, b], false);
    solver.initialize_watches();

    assert!(
        !solver.deduplicate_binary_clauses(),
        "duplicate binary dedup should not derive UNSAT here",
    );
    assert!(
        !solver.arena.is_active(learned_dup),
        "learned duplicate should be deleted first",
    );
    assert!(
        solver.arena.is_active(irred_dup),
        "irredundant duplicate should be preserved",
    );
}

#[test]
fn test_deduplicate_binary_clauses_preserves_reason_protected_duplicate() {
    let mut solver: Solver = Solver::new(2);
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));

    let learned_dup = solver.add_clause_db(&[a, b], true);
    let irred_dup = solver.add_clause_db(&[a, b], false);
    solver.initialize_watches();

    // Protect the learned duplicate through a live reason edge. The lazy
    // reason-mark refresh in deduplicate must preserve this clause.
    solver.enqueue(a, Some(ClauseRef(learned_dup as u32)));

    assert!(
        !solver.deduplicate_binary_clauses(),
        "duplicate binary dedup should not derive UNSAT here",
    );
    assert!(
        solver.arena.is_active(learned_dup),
        "reason-protected duplicate must not be deleted",
    );
    assert!(
        !solver.arena.is_active(irred_dup),
        "non-reason duplicate should be deleted instead",
    );
}

#[test]
fn test_deduplicate_binary_clauses_derives_hyper_unary_unit() {
    let mut solver: Solver = Solver::new(2);
    let a = Variable(0);
    let b = Variable(1);
    let a_pos = Literal::positive(a);

    // (a ∨ b) and (a ∨ ¬b) imply unit a.
    solver.add_clause_db(&[a_pos, Literal::positive(b)], false);
    solver.add_clause_db(&[a_pos, Literal::negative(b)], false);
    solver.initialize_watches();

    assert!(
        !solver.deduplicate_binary_clauses(),
        "hyper-unary derivation should not directly mark UNSAT",
    );
    assert_eq!(
        solver.get_var_assignment(a.index()),
        Some(true),
        "hyper-unary pair must enqueue unit a",
    );
    assert!(
        solver.trail.contains(&a_pos),
        "derived hyper-unary unit must be on the trail",
    );
}

#[test]
fn test_deduplicate_binary_clauses_propagates_hyper_unit_chain_conflict() {
    let mut solver: Solver = Solver::new(3);
    let a = Variable(0);
    let b = Variable(1);
    let c = Variable(2);
    let a_pos = Literal::positive(a);

    // (a ∨ b) and (a ∨ ¬b) derive unit a.
    solver.add_clause_db(&[a_pos, Literal::positive(b)], false);
    solver.add_clause_db(&[a_pos, Literal::negative(b)], false);
    // (¬a ∨ c) plus level-0 assignment ¬c force ¬a, so propagating derived
    // unit a must detect a level-0 conflict.
    solver.add_clause_db(&[Literal::negative(a), Literal::positive(c)], false);
    solver.initialize_watches();
    solver.enqueue(Literal::negative(c), None);

    assert!(
        solver.deduplicate_binary_clauses(),
        "deduplicate must propagate derived hyper-unary units and detect chain conflict",
    );
}

#[test]
fn test_decompose_runs_deduplicate_when_no_substitutions_found() {
    let mut solver: Solver = Solver::new(2);
    let a = Variable(0);
    let b = Variable(1);
    let a_pos = Literal::positive(a);

    // No SCC substitutions expected, but dedup should still run from decompose
    // and derive unit a from the binary hyper-unary pair.
    solver.add_clause_db(&[a_pos, Literal::positive(b)], false);
    solver.add_clause_db(&[a_pos, Literal::negative(b)], false);
    solver.initialize_watches();

    solver.decompose();

    assert_eq!(
        solver.get_var_assignment(a.index()),
        Some(true),
        "decompose no-substitution path must still run binary dedup/hyper-unary",
    );
}

#[test]
fn test_subsume_schedule_backs_off_on_noop_round() {
    let mut solver: Solver = Solver::new(4);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(1)),
        Literal::positive(Variable(3)),
    ]);
    assert!(solver.process_initial_clauses().is_none());

    solver.inproc_ctrl.subsume.reset_interval(SUBSUME_INTERVAL);
    solver.num_conflicts = SUBSUME_INTERVAL;
    solver.subsume();

    // No clauses are deleted/strengthened, so subsume should back off harder
    // (2x) instead of the default 1.5x growth.
    assert_eq!(
        solver.inproc_ctrl.subsume.next_conflict,
        SUBSUME_INTERVAL * 3
    );
}

#[test]
fn test_subsume_schedule_uses_large_sparse_idle_cooldown_on_noop_round() {
    let mut solver: Solver = Solver::new(25_000);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(1)),
        Literal::positive(Variable(3)),
    ]);
    assert!(solver.process_initial_clauses().is_none());
    solver
        .arena
        .spoof_active_clause_count_for_test(SUBSUME_LARGE_SPARSE_MIN_ACTIVE_CLAUSES);

    solver.inproc_ctrl.subsume.reset_interval(SUBSUME_INTERVAL);
    solver.num_conflicts = SUBSUME_INTERVAL;
    solver.subsume();

    assert_eq!(
        solver.inproc_ctrl.subsume.next_conflict,
        SUBSUME_INTERVAL + SUBSUME_INTERVAL * 4,
        "large sparse no-op rounds should use the faster idle cooldown"
    );
}

#[test]
fn test_subsume_schedule_does_not_use_large_sparse_cooldown_on_dense_noop_round() {
    let mut solver: Solver = Solver::new(10_000);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(1)),
        Literal::positive(Variable(3)),
    ]);
    assert!(solver.process_initial_clauses().is_none());
    solver
        .arena
        .spoof_active_clause_count_for_test(SUBSUME_LARGE_SPARSE_MIN_ACTIVE_CLAUSES);

    solver.inproc_ctrl.subsume.reset_interval(SUBSUME_INTERVAL);
    solver.num_conflicts = SUBSUME_INTERVAL;
    solver.subsume();

    assert_eq!(
        solver.inproc_ctrl.subsume.next_conflict,
        SUBSUME_INTERVAL * 3,
        "dense no-op rounds should retain the ordinary idle cooldown"
    );
}

#[test]
fn test_subsume_schedule_large_sparse_idle_cooldown_caps() {
    let mut solver: Solver = Solver::new(25_000);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
        Literal::positive(Variable(2)),
    ]);
    solver.add_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(1)),
        Literal::positive(Variable(3)),
    ]);
    assert!(solver.process_initial_clauses().is_none());
    solver
        .arena
        .spoof_active_clause_count_for_test(SUBSUME_LARGE_SPARSE_MIN_ACTIVE_CLAUSES);

    solver.inproc_ctrl.subsume.reset_interval(SUBSUME_INTERVAL);
    solver.num_conflicts = SUBSUME_INTERVAL;
    solver.subsume();
    assert_eq!(solver.inproc_ctrl.subsume.next_conflict, 50_000);

    solver.num_conflicts = solver.inproc_ctrl.subsume.next_conflict;
    solver.subsume();
    assert_eq!(solver.inproc_ctrl.subsume.next_conflict, 210_000);

    solver.num_conflicts = solver.inproc_ctrl.subsume.next_conflict;
    solver.subsume();
    assert_eq!(
        solver.inproc_ctrl.subsume.next_conflict,
        210_000 + SUBSUME_LARGE_MAX_IDLE_INTERVAL,
        "large sparse idle cooldown should cap at the large max interval"
    );
}

#[test]
fn test_subsume_schedule_uses_default_growth_when_round_progresses() {
    let mut solver: Solver = Solver::new(3);
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));

    // Learned clause can be deleted; irredundant subsumer stays.
    solver.add_clause_db(&[a, b], false);
    let learned_off = solver.add_clause_db(&[a, b, c], true);
    solver.initialize_watches();

    solver.inproc_ctrl.subsume.reset_interval(SUBSUME_INTERVAL);
    solver.num_conflicts = SUBSUME_INTERVAL;
    solver.subsume();

    assert!(
        !solver.arena.is_active(learned_off),
        "learned clause should be deleted by subsumption"
    );
    assert_eq!(
        solver.inproc_ctrl.subsume.next_conflict,
        SUBSUME_INTERVAL + (SUBSUME_INTERVAL * 3 / 2),
        "progressing rounds should keep default 1.5x growth"
    );
}

#[test]
fn test_factor_skip_reason_delays_later_rounds_below_tick_threshold() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = FACTOR_INTERVAL;
    solver.cold.factor_rounds = 1;
    solver.cold.factor_last_completed_epoch = 0;
    solver.cold.factor_marked_epoch = 1;
    solver.cold.last_factor_ticks = 100;
    solver.search_ticks = [
        100 + FACTOR_TICK_THRESHOLD * solver.num_clauses() as u64 - 1,
        0,
    ];

    assert_eq!(
        solver.factor_skip_reason(),
        Some(FactorSkipReason::ThresholdDelay),
        "later factor rounds should defer when tick budget is below CaDiCaL's threshold",
    );
}

#[test]
fn test_factor_skip_reason_allows_first_round_without_threshold_budget() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = FACTOR_INTERVAL;
    solver.cold.factor_rounds = 0;
    solver.cold.factor_last_completed_epoch = 0;
    solver.cold.factor_marked_epoch = 1;
    solver.cold.last_factor_ticks = 100;
    solver.search_ticks = [100, 0];

    assert_eq!(
        solver.factor_skip_reason(),
        None,
        "first factor round should rely on FACTOR_INIT_TICKS instead of threshold delay",
    );
}

#[test]
fn test_htr_skip_reason_delays_later_rounds_below_tick_threshold() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = HTR_INTERVAL;
    solver.inproc.htr.set_last_search_ticks(100);
    solver.search_ticks = [
        100 + HTR_TICK_THRESHOLD * solver.num_clauses() as u64 - 1,
        0,
    ];

    assert_eq!(
        solver.htr_skip_reason(),
        Some(HtrSkipReason::ThresholdDelay),
        "later HTR rounds should defer when tick budget is below CaDiCaL's ternary threshold",
    );
}

#[test]
fn test_htr_skip_reason_allows_first_round_without_threshold_budget() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = HTR_INTERVAL;
    solver.search_ticks = [0, 0];

    assert_eq!(
        solver.htr_skip_reason(),
        None,
        "first HTR round should not be delayed before any prior HTR effort exists",
    );
}

#[test]
fn test_hbr_subsumption_reassigns_reason_and_deletes_clause() {
    let mut solver = Solver::new(4);
    let d = Variable(0);
    let a = Variable(1);
    let b = Variable(2);
    let u = Variable(3);

    // d => a, d => b
    solver.add_clause_db(&[Literal::negative(d), Literal::positive(a)], false);
    solver.add_clause_db(&[Literal::negative(d), Literal::positive(b)], false);

    // (u ∨ ¬d ∨ ¬a ∨ ¬b) becomes unit under d=true, a=true, b=true.
    let original_idx = solver.add_clause_db(
        &[
            Literal::positive(u),
            Literal::negative(d),
            Literal::negative(a),
            Literal::negative(b),
        ],
        false,
    );

    solver.initialize_watches();
    solver.probing_mode = true;

    solver.decide(Literal::positive(d));
    assert!(solver.propagate().is_none());

    // HBR reason assignment: per CaDiCaL probe.cpp:262, when HBR emits a
    // binary clause the propagated literal's reason is ALWAYS the new binary
    // clause, regardless of whether it subsumes the original (#4719/#4753).
    let u_reason = solver
        .var_reason(u.index())
        .expect("unit should have a reason");
    let u_reason_lits = solver.arena.literals(u_reason.0 as usize);
    assert_eq!(
        u_reason_lits.len(),
        2,
        "HBR reason should be a binary clause"
    );
    assert!(u_reason_lits.contains(&Literal::negative(d)));
    assert!(u_reason_lits.contains(&Literal::positive(u)));

    assert!(
        solver.arena.is_pending_garbage(original_idx),
        "subsumed long clause should be marked pending-garbage for deferred deletion",
    );
    assert_eq!(
        solver.pending_garbage_count, 1,
        "pending-garbage counter must track deferred HBR deletions",
    );

    // collect_level0_garbage is a level-0 pass, so return from the decision.
    solver.backtrack(0);
    assert_eq!(
        solver.pending_garbage_count, 1,
        "backtrack should not clear deferred pending-garbage work",
    );

    // Production path (solve/inprocessing_schedule.rs): drain_all_pending_garbage() runs
    // BEFORE collect_level0_garbage(). The drain handles deferred HBR marks;
    // collect_level0_garbage handles satisfied/falsified literals.
    solver.drain_all_pending_garbage();
    assert!(
        solver.arena.is_empty_clause(original_idx),
        "deferred garbage clause should be deleted at level 0",
    );
    assert_eq!(
        solver.pending_garbage_count, 0,
        "pending-garbage counter should drain after deletion",
    );

    // collect_level0_garbage fixpoint guard: no new level-0 assignments means
    // it returns false without iterating. This is correct because the drain
    // already handled pending-garbage marks.
    let fixed = solver.fixed_count;
    solver.cold.last_collect_fixed = fixed;
    assert!(
        !solver.collect_level0_garbage(),
        "level-0 GC should not derive UNSAT on this fixture",
    );

    assert_eq!(solver.inproc.prober.stats().hbr_subs, 1);
}

#[test]
fn test_collect_level0_garbage_repeats_after_internal_unit_creation() {
    let mut solver = Solver::new(3);
    let a = Variable(0);
    let y = Variable(1);
    let b = Variable(2);

    // Clause scanned first. It is not initially satisfied, but becomes
    // satisfied after the second clause is shrunk to the unit literal y.
    let satisfied_later_idx =
        solver.add_clause_db(&[Literal::positive(y), Literal::positive(b)], false);
    let shrinks_to_unit_idx =
        solver.add_clause_db(&[Literal::positive(y), Literal::negative(a)], false);
    solver.initialize_watches();

    // Set level-0 assignment a=true without running BCP first. During GC,
    // (y ∨ ¬a) shrinks to unit y, which then satisfies the earlier clause.
    solver.enqueue(Literal::positive(a), None);
    solver.qhead = solver.trail.len();

    // Force collect_level0_garbage to run (skip the entry fixpoint guard).
    solver.fixed_count = 1;
    solver.cold.last_collect_fixed = 0;
    // Mark variable a as dirty for occurrence-guided GC (#8097).
    solver.l0_gc_dirty[a.index()] = true;

    assert!(
        !solver.collect_level0_garbage(),
        "fixture should remain SAT after level-0 garbage collection",
    );
    assert_eq!(
        solver.get_var_assignment(y.index()),
        Some(true),
        "shrunk binary should enqueue unit y at level 0",
    );
    assert!(
        solver.arena.len_of(shrinks_to_unit_idx) == 1,
        "second clause should be shrunk to a unit",
    );
    assert!(
        solver.arena.is_empty_clause(satisfied_later_idx),
        "collect_level0_garbage must re-run until earlier clauses satisfied by new units are deleted",
    );
}

#[test]
fn test_replace_clause_checked_skips_pending_garbage_husk() {
    // Husk adjudication #3/#4 (revival sink): a pending-garbage clause is
    // logically deleted. replace_clause_* must SKIP it — the previous
    // behavior (arena.replace clearing the GARBAGE|PENDING bits and
    // re-attaching watches) revived deliberately deleted clauses. The husk
    // stays pending and is reaped by the normal collection passes.
    let mut solver = Solver::new(3);
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let clause_idx = solver.add_clause_db(&[a, b, c], true);
    solver.initialize_watches();

    solver.arena.set_pending_garbage(clause_idx, true);
    solver.pending_garbage_count = 1;

    let result = solver.replace_clause_checked(clause_idx, &[a, b]);

    assert_eq!(
        result,
        mutate::ReplaceResult::Skipped,
        "replacement of a pending-garbage husk must be skipped, not revive it",
    );
    assert_eq!(
        solver.arena.len_of(clause_idx),
        3,
        "husk literal data must be untouched by the skipped replacement",
    );
    assert!(
        solver.arena.is_pending_garbage(clause_idx),
        "husk must stay pending-garbage (reaped by normal collection, not revived)",
    );
    assert_eq!(
        solver.pending_garbage_count, 1,
        "pending-garbage counter must be unchanged by a skipped replacement",
    );
}

#[test]
fn test_rebuild_watches_skips_garbage_kept_husk() {
    // Husk adjudication follow-up: rebuild_watches deliberately does not
    // attach watches for garbage/pending-garbage husks. Its debug
    // post-conditions ("every active clause has watches" and the #8095
    // missed-unit shadow check) must therefore skip husks too, or a husk
    // present at rebuild time fires a spurious debug assert.
    let mut solver = Solver::new(4);
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));
    let live_idx = solver.add_clause_db(&[a, b], false);
    let husk_idx = solver.add_clause_db(&[c, d], false);
    solver.initialize_watches();
    solver.arena.mark_garbage_keep_data(husk_idx);

    solver.rebuild_watches();

    // Live clause is watched on both literals.
    let cref = ClauseRef(live_idx as u32);
    let has_watch = |lit: Literal| {
        let wl = solver.watches.get_watches(lit);
        (0..wl.len()).any(|i| wl.clause_ref(i) == cref)
    };
    assert!(has_watch(a) && has_watch(b), "live clause must be watched");

    // Husk got no watches anywhere (logically deleted).
    let husk_ref = ClauseRef(husk_idx as u32);
    for vi in 0..4u32 {
        for lit in [
            Literal::positive(Variable(vi)),
            Literal::negative(Variable(vi)),
        ] {
            let wl = solver.watches.get_watches(lit);
            assert!(
                (0..wl.len()).all(|i| wl.clause_ref(i) != husk_ref),
                "husk must not be watched after rebuild_watches"
            );
        }
    }
}

#[test]
fn test_replace_clause_checked_skips_garbage_kept_husk() {
    // Same sink guard for mark_garbage_keep_data husks (eager subsumption,
    // OTFS, congruence forward subsumption).
    let mut solver = Solver::new(3);
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let clause_idx = solver.add_clause_db(&[a, b, c], false);
    solver.initialize_watches();

    solver.arena.mark_garbage_keep_data(clause_idx);

    let result = solver.replace_clause_checked(clause_idx, &[a, b]);

    assert_eq!(
        result,
        mutate::ReplaceResult::Skipped,
        "replacement of a garbage-kept husk must be skipped, not revive it",
    );
    assert!(
        solver.arena.is_garbage(clause_idx),
        "husk must stay garbage after the skipped replacement",
    );
    assert_eq!(
        solver.arena.literals(clause_idx),
        &[a, b, c],
        "husk literal data must be untouched (reason-pointer contract)",
    );
}

#[test]
fn test_delete_clause_checked_drains_pending_garbage_mark() {
    let mut solver = Solver::new(2);
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let clause_idx = solver.add_clause_db(&[a, b], true);
    solver.initialize_watches();

    solver.arena.set_pending_garbage(clause_idx, true);
    solver.pending_garbage_count = 1;

    let result = solver.delete_clause_checked(clause_idx, mutate::ReasonPolicy::Skip);
    assert_eq!(result, mutate::DeleteResult::Deleted);
    assert!(
        solver.arena.is_empty_clause(clause_idx),
        "deleted clause should be inactive",
    );
    assert_eq!(
        solver.pending_garbage_count, 0,
        "deletion should drain pending-garbage counter",
    );
}

#[test]
#[allow(clippy::many_single_char_names)]
fn test_hbr_subsumption_flushes_deferred_watch_on_conflict_return() {
    let mut solver = Solver::new(5);
    let d = Variable(0);
    let a = Variable(1);
    let b = Variable(2);
    let u = Variable(3);
    let x = Variable(4);

    // d => a, d => b
    solver.add_clause_db(&[Literal::negative(d), Literal::positive(a)], false);
    solver.add_clause_db(&[Literal::negative(d), Literal::positive(b)], false);

    // (u ∨ ¬d ∨ ¬a ∨ ¬b) becomes unit under d=true, a=true, b=true.
    solver.add_clause_db(
        &[
            Literal::positive(u),
            Literal::negative(d),
            Literal::negative(a),
            Literal::negative(b),
        ],
        false,
    );

    // Conflict through propagation chain: d→a, then a⇒¬x and a⇒x conflict.
    // These are watched on ¬a (not ¬d), so the HBR long clause on ¬d is
    // always processed before the conflict, regardless of watch sort order.
    solver.add_clause_db(&[Literal::negative(a), Literal::negative(x)], false);
    solver.add_clause_db(&[Literal::negative(a), Literal::positive(x)], false);

    solver.initialize_watches();
    solver.probing_mode = true;

    let clauses_before = solver.arena.num_clauses();
    let words_before = solver.arena.len();
    solver.decide(Literal::positive(d));
    assert!(solver.propagate().is_some());

    // HBR should have added a new binary clause (¬d ∨ u). The watch on ¬d is
    // deferred while iterating `watches[¬d]` and must be flushed even on early return.
    assert_eq!(solver.arena.num_clauses(), clauses_before + 1);
    let hbr_ref = ClauseRef(words_before as u32);
    assert_eq!(solver.watches.count_watches_for_clause(hbr_ref), 2);
}

#[test]
fn test_otfs_strengthen_replaces_watches_without_leaking_stale_entries() {
    let mut solver = Solver::new(4);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let x3 = Literal::positive(Variable(3));

    // Clause: {x0, x1, x2, x3}. In OTFS during 1UIP analysis, the pivot
    // is the propagated literal (position 0 of the reason clause). After
    // removing the pivot, ALL remaining literals must be false.
    let clause_idx = solver.add_clause_db(&[x0, x1, x2, x3], false);
    let clause_ref = ClauseRef(clause_idx as u32);
    solver.watches.add_watch(x0, Watcher::new(clause_ref, x1));
    solver.watches.add_watch(x1, Watcher::new(clause_ref, x0));

    // Simulate OTFS state: x0 = propagated (true at level 1), x1/x2/x3 falsified.
    // x0 is the propagated literal at position 0, used as pivot.
    solver.decide(x0); // x0 = true at level 1
    solver.propagate();
    solver.decide(x1.negated()); // x1 = false at level 2
    solver.propagate();
    solver.decide(x2.negated()); // x2 = false at level 3
    solver.propagate();
    solver.decide(x3.negated()); // x3 = false at level 4
    solver.propagate();

    assert_eq!(solver.watches.count_watches_for_clause(clause_ref), 2);
    assert_eq!(solver.otfs_strengthened(), 0);
    assert_eq!(solver.otfs_subsumed(), 0);

    // Pivot = x0 (the propagated literal). After removal, {x1, x2, x3} are all false.
    assert!(solver.otfs_strengthen(clause_ref, x0));

    let strengthened = solver.arena.literals(clause_idx);
    assert_eq!(strengthened.len(), 3);
    assert!(
        strengthened
            .iter()
            .all(|lit| lit.variable() != x0.variable()),
        "pivot variable must be removed from strengthened clause",
    );
    // After OTFS: highest-level literal at position 0, second-highest at position 1.
    // x3 (level 4) → pos 0, x2 (level 3) → pos 1, x1 (level 2) → pos 2.
    assert_eq!(
        strengthened[0].variable(),
        x3.variable(),
        "position 0 should be highest-level literal (x3 at level 4)"
    );
    assert_eq!(
        strengthened[1].variable(),
        x2.variable(),
        "position 1 should be second-highest-level literal (x2 at level 3)"
    );
    assert_eq!(solver.otfs_strengthened(), 1);
    assert_eq!(solver.watches.count_watches_for_clause(clause_ref), 2);

    let pivot_watch_list = solver.watches.get_watches(x0);
    assert!(
        (0..pivot_watch_list.len()).all(|i| pivot_watch_list.clause_ref(i) != clause_ref),
        "pivot watch list still contains stale OTFS watcher",
    );
}

/// OTFS reason pointer preservation (#8439, supersedes #8241): after OTFS
/// strengthens a reason clause by removing the pivot literal, the pivot
/// variable's reason pointer is PRESERVED (points to the strengthened clause).
/// The strengthened clause still implies the pivot (all remaining literals
/// are false), so the reason is semantically valid. Conflict analysis handles
/// this correctly via the `if lit == p_lit { continue; }` skip being a no-op
/// when the pivot is absent. Preserving the reason prevents backbone probing
/// trail exhaustion (#8356) and keeps the clause protected from reduce_db.
#[test]
fn test_otfs_strengthen_preserves_reason_pointer() {
    let mut solver = Solver::new(8);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let x3 = Literal::positive(Variable(3));
    let x4 = Literal::positive(Variable(4));
    let _x5 = Literal::positive(Variable(5));
    let _x6 = Literal::positive(Variable(6));

    // Clause R = {x0, x1, x2, x3}. x0 will be the propagated literal.
    // Do NOT add watches for this clause — we want to enqueue x0 manually
    // without BCP triggering propagation from R first.
    let clause_idx = solver.add_clause_db(&[x0, x1, x2, x3], false);
    let clause_ref = ClauseRef(clause_idx as u32);

    // Falsify x1, x2, x3 via dummy decisions at increasing levels.
    // Use unrelated decision variables to raise the level without touching
    // x1/x2/x3 watches, then manually assign x1/x2/x3 negations at those
    // levels. Actually, deciding x1.negated() directly is safe here since
    // R has no watches attached.
    solver.decide(x4); // level 1
    solver.propagate();
    solver.decide(x1.negated()); // level 2
    solver.propagate();
    solver.decide(x2.negated()); // level 3
    solver.propagate();
    solver.decide(x3.negated()); // level 4
    solver.propagate();

    // Now x1(false@2), x2(false@3), x3(false@4) — reason clause R is unit on x0.
    // Enqueue x0 as propagated with reason clause R.
    // With chrono-BT, assignment_level = max level of falsified lits in R = 4.
    solver.enqueue(x0, Some(clause_ref));
    // Advance qhead so subsequent operations don't panic.
    solver.qhead = solver.trail.len();

    // Add watches for the strengthened clause (needed for OTFS watch maintenance).
    // The OTFS code removes the old watches and attaches new ones.
    solver.watches.add_watch(x0, Watcher::new(clause_ref, x1));
    solver.watches.add_watch(x1, Watcher::new(clause_ref, x0));

    // Verify x0 has clause_ref as its reason.
    assert_eq!(
        solver.var_data[x0.variable().index()].reason,
        clause_ref.0,
        "x0 should have clause_ref as its reason before OTFS"
    );

    // Strengthen R by removing pivot x0. After this, R = {x1, x2, x3}.
    assert!(solver.otfs_strengthen(clause_ref, x0));

    // Verify the strengthened clause no longer contains x0.
    let strengthened = solver.arena.literals(clause_idx);
    assert_eq!(strengthened.len(), 3);
    assert!(
        strengthened.iter().all(|l| l.variable() != x0.variable()),
        "pivot x0 should be removed from strengthened clause"
    );

    // Fix #8439 (supersedes #8241): x0's reason is PRESERVED after OTFS.
    // The strengthened clause still implies x0 (all remaining literals false).
    // Keeping the reason prevents backbone probing trail exhaustion (#8356)
    // and protects the clause from reduce_db deletion.
    assert_eq!(
        solver.var_data[x0.variable().index()].reason,
        clause_ref.0,
        "x0's reason should still point to the strengthened clause after OTFS"
    );
}

/// OTFS with LRAT: clause_id must be updated to the new emitted ID after
/// strengthening, not left pointing at the deleted old clause. If stale,
/// subsequent conflict analysis would reference a deleted LRAT step.
///
/// Boundary condition from Prover audit of otfs.rs clause_ids update.
#[test]
fn test_otfs_strengthen_updates_lrat_clause_id() {
    use crate::ProofOutput;

    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 4);
    let mut solver: Solver = Solver::with_proof_output(4, proof);

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let x3 = Literal::positive(Variable(3));

    // Add clause as original (non-learned), gets LRAT ID
    let clause_idx = solver.add_clause_db(&[x0, x1, x2, x3], false);
    let clause_ref = ClauseRef(clause_idx as u32);
    solver.watches.add_watch(x0, Watcher::new(clause_ref, x1));
    solver.watches.add_watch(x1, Watcher::new(clause_ref, x0));

    let old_id = solver.clause_id(clause_ref);
    assert!(old_id != 0, "original clause must have a non-zero LRAT ID");

    // Set up state: x0 = true (propagated), x1/x2/x3 = false
    solver.decide(x0);
    solver.propagate();
    solver.decide(x1.negated());
    solver.propagate();
    solver.decide(x2.negated());
    solver.propagate();
    solver.decide(x3.negated());
    solver.propagate();

    // OTFS is disabled in LRAT proof mode because OTFS emits
    // TrustedTransform which LRAT verification rejects. Verify the
    // guard rejects strengthening.
    assert!(!solver.otfs_strengthen(clause_ref, x0));

    // Since OTFS was rejected (LRAT guard), clause ID should be unchanged.
    let new_id = solver.clause_id(clause_ref);
    assert_eq!(
        new_id, old_id,
        "clause ID must be unchanged when OTFS is rejected by LRAT guard"
    );
}

#[test]
fn test_probe_failed_literal_unit_emits_lrat_hints() {
    let proof = ProofOutput::lrat_text(Vec::<u8>::new(), 4);
    let mut solver: Solver = Solver::with_proof_output(4, proof);

    let r = Variable(0);
    let a = Variable(1);
    let b = Variable(2);
    let c = Variable(3);

    // Probe setup:
    // Binary clauses containing positive r — when r=false, BCP forces a, b:
    //   {r, a}: r=false → a=true
    //   {r, b}: r=false → b=true
    // Binary clauses chaining to conflict — a=true forces c, then b=true + c=true → conflict:
    //   {!a, c}: a=true → c=true
    //   {!b, !c}: b=true, c=true → both watched literals false → CONFLICT
    solver.add_clause(vec![Literal::positive(r), Literal::positive(a)]);
    solver.add_clause(vec![Literal::positive(r), Literal::positive(b)]);
    solver.add_clause(vec![Literal::negative(a), Literal::positive(c)]);
    solver.add_clause(vec![Literal::negative(b), Literal::negative(c)]);

    assert!(
        solver.process_initial_clauses().is_none(),
        "formula should remain consistent before probing"
    );
    solver.initialize_watches();
    assert!(
        solver.propagate().is_none(),
        "level-0 unit setup should be consistent before probing"
    );
    let probe_lit = Literal::negative(r);
    solver.decide(probe_lit);
    assert!(
        solver.propagate().is_some(),
        "r=false should trigger a probing conflict in this fixture"
    );
    solver.backtrack(0);
    for var in [a, b, c] {
        solver
            .inproc
            .prober
            .mark_probed(Literal::positive(var), solver.fixed_count);
        solver
            .inproc
            .prober
            .mark_probed(Literal::negative(var), solver.fixed_count);
    }

    let failed_before = solver.inproc.prober.stats().failed;
    // probe() returns false (no UNSAT detected); failed literals are tracked
    // via prober stats, not the return value (#4841).
    assert!(
        !solver.probe(),
        "probe() must return false when no UNSAT is detected"
    );
    assert!(
        solver.inproc.prober.stats().failed > failed_before,
        "probing should detect a failed literal and derive a unit"
    );

    let writer = solver
        .take_proof_writer()
        .expect("proof writer should exist with LRAT output");
    let proof_text = String::from_utf8(writer.into_vec().expect("flush")).expect("utf8");

    let mut saw_derived_r_with_hints = false;
    for line in proof_text.lines() {
        let tokens: Vec<&str> = line.split_whitespace().collect();
        if tokens.len() < 4 {
            continue;
        }
        let Some(first_zero) = tokens.iter().position(|token| *token == "0") else {
            continue;
        };
        if first_zero != 2 || tokens[1] != "1" {
            continue;
        }
        let trailing_zero = tokens.len() - 1;
        if tokens[trailing_zero] != "0" {
            continue;
        }
        let hint_count = trailing_zero.saturating_sub(first_zero + 1);
        if hint_count > 0 {
            saw_derived_r_with_hints = true;
            break;
        }
    }

    assert!(
        saw_derived_r_with_hints,
        "expected derived unit (r) to include LRAT hints; proof:\n{proof_text}"
    );
}

/// Regression test for #4841: probe must not report false UNSAT on SAT formulas.
///
/// The formula `(x0 v x1) AND (NOT x0 v x1)` is satisfiable (x1=true).
/// Probing ¬x1 should find a failed literal (forcing x1=true as a unit),
/// but `probe()` must return false — finding a failed literal is not UNSAT.
#[test]
fn test_probe_does_not_false_unsat_on_sat_formula() {
    let mut solver: Solver = Solver::new(2);
    let x0 = Variable(0);
    let x1 = Variable(1);

    // (x0 v x1) AND (NOT x0 v x1)  =>  x1 must be true
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);
    solver.add_clause(vec![Literal::negative(x0), Literal::positive(x1)]);

    assert!(
        solver.process_initial_clauses().is_none(),
        "formula should remain consistent (no conflict)"
    );
    solver.initialize_watches();

    // Initial propagation should not conflict.
    assert!(
        solver.propagate().is_none(),
        "no level-0 conflict on SAT formula"
    );

    // probe() must return false (not UNSAT).
    let failed_before = solver.inproc.prober.stats().failed;
    assert!(
        !solver.probe(),
        "probe() must return false on a SAT formula (#4841)"
    );

    // Probing may or may not find a failed literal depending on candidate
    // ordering and whether x1 is already unit-propagated before probing runs.
    // The critical invariant is: probe() never returns true on a SAT formula.
    let _ = failed_before; // suppress unused warning if no assertion on stats

    // Full solve must return SAT.
    let result = solver.solve().into_inner();
    assert!(
        result.is_sat(),
        "formula is SAT but solver returned {result:?}"
    );
}

/// OTFS in DRAT mode: strengthened clause emitted as TrustedTransform (#4774).
///
/// Verifies that `otfs_strengthen` with a proof-enabled solver (DRAT mode)
/// passes the forward checker's trusted transform validation (non-empty,
/// non-tautological, not fully-falsified) without requiring full RUP derivability.
///
/// Before the fix, OTFS emitted `ProofAddKind::Axiom`, which bypassed all
/// forward checker validation. Now it uses `TrustedTransform` for well-formedness
/// checks without requiring the clause to be RUP-derivable.
#[test]
#[cfg(debug_assertions)]
fn test_otfs_strengthen_drat_uses_trusted_transform() {
    use crate::ProofOutput;

    let proof = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver: Solver = Solver::with_proof_output(4, proof);

    // Verify the forward checker is active in debug DRAT mode.
    assert!(
        solver.cold.forward_checker.is_some(),
        "forward checker must be active in debug DRAT mode"
    );

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));
    let x3 = Literal::positive(Variable(3));

    // Add clause {x0, x1, x2, x3} — added as original in both solver and checker.
    let clause_idx = solver.add_clause_db(&[x0, x1, x2, x3], false);
    let clause_ref = ClauseRef(clause_idx as u32);
    solver.watches.add_watch(x0, Watcher::new(clause_ref, x1));
    solver.watches.add_watch(x1, Watcher::new(clause_ref, x0));

    // Set up OTFS state: x0 = true (pivot), x1/x2/x3 = false.
    // The forward checker only sees unit propagation from its own BCP,
    // not the solver's search decisions, so these assignments don't
    // cause the checker to see the clause as fully-falsified.
    solver.decide(x0);
    solver.propagate();
    solver.decide(x1.negated());
    solver.propagate();
    solver.decide(x2.negated());
    solver.propagate();
    solver.decide(x3.negated());
    solver.propagate();

    // OTFS fires: remove pivot x0, yielding {x1, x2, x3}.
    // With the fix, this calls proof_emit_add with TrustedTransform,
    // which validates the clause through the forward checker's
    // add_trusted_transform (non-empty, non-tautological, not fully-falsified).
    // Before the fix, it used Axiom which bypassed all validation.
    assert!(solver.otfs_strengthen(clause_ref, x0));

    let strengthened = solver.arena.literals(clause_idx);
    assert_eq!(strengthened.len(), 3);
    assert!(
        strengthened.iter().all(|l| l.variable() != x0.variable()),
        "pivot must be removed"
    );
    assert_eq!(solver.otfs_strengthened(), 1);
}

/// OTFS ternary-to-binary: when a 3-literal clause is strengthened by
/// removing the pivot, the result is a 2-literal (binary) clause.
/// The binary clause must use implicit binary watch encoding, not long-clause
/// watchers.
///
/// CaDiCaL analyze.cpp:844-851: new_size==1 bails, new_size==2 allowed.
/// Commit 973d9c2ef introduced binary OTFS output.
#[test]
fn test_otfs_strengthen_ternary_to_binary_uses_binary_watch_encoding() {
    let mut solver = Solver::new(3);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));

    // Clause: {x0, x1, x2}. After removing pivot x0, the result is {x1, x2}.
    let clause_idx = solver.add_clause_db(&[x0, x1, x2], false);
    let clause_ref = ClauseRef(clause_idx as u32);
    // Install non-binary watches for the original ternary clause.
    solver.watches.add_watch(x0, Watcher::new(clause_ref, x1));
    solver.watches.add_watch(x1, Watcher::new(clause_ref, x0));

    // Simulate OTFS state: x0 = true (propagated, pivot), x1/x2 = false.
    solver.decide(x0); // x0 = true at level 1
    solver.propagate();
    solver.decide(x1.negated()); // x1 = false at level 2
    solver.propagate();
    solver.decide(x2.negated()); // x2 = false at level 3
    solver.propagate();

    assert_eq!(solver.watches.count_watches_for_clause(clause_ref), 2);
    assert_eq!(solver.otfs_strengthened(), 0);

    // Pivot = x0. After removal: {x1, x2} — a binary clause.
    assert!(solver.otfs_strengthen(clause_ref, x0));

    // Verify the arena stores exactly 2 literals.
    let strengthened = solver.arena.literals(clause_idx);
    assert_eq!(
        strengthened.len(),
        2,
        "OTFS binary result must have 2 literals"
    );
    assert!(
        strengthened.iter().all(|l| l.variable() != x0.variable()),
        "pivot variable must be removed from strengthened clause",
    );

    // Verify level-ordering: highest-level literal at position 0.
    // x2 (level 3) should be at position 0, x1 (level 2) at position 1.
    assert_eq!(
        strengthened[0].variable(),
        x2.variable(),
        "position 0 should be highest-level literal (x2 at level 3)"
    );
    assert_eq!(
        strengthened[1].variable(),
        x1.variable(),
        "position 1 should be second-highest-level literal (x1 at level 2)"
    );

    assert_eq!(solver.otfs_strengthened(), 1);
    // Two watches must remain: one for each watched literal.
    assert_eq!(solver.watches.count_watches_for_clause(clause_ref), 2);

    // Verify binary watch encoding: watchers are stored under the watched
    // literal itself. After OTFS, watched[0] = x2, watched[1] = x1.
    // watch_clause(clause_ref, x2, x1, true) adds:
    //   watches[x2] += binary(clause_ref, x1)
    //   watches[x1] += binary(clause_ref, x2)
    let x2_watches = solver.watches.get_watches(x2);
    let mut found_binary_x2 = false;
    for i in 0..x2_watches.len() {
        if x2_watches.clause_ref(i) == clause_ref {
            assert!(
                x2_watches.is_binary(i),
                "watch on x2 for OTFS binary result must use binary encoding"
            );
            found_binary_x2 = true;
        }
    }
    assert!(
        found_binary_x2,
        "must find a binary watcher on x2 for the OTFS result"
    );

    let x1_watches = solver.watches.get_watches(x1);
    let mut found_binary_x1 = false;
    for i in 0..x1_watches.len() {
        if x1_watches.clause_ref(i) == clause_ref {
            assert!(
                x1_watches.is_binary(i),
                "watch on x1 for OTFS binary result must use binary encoding"
            );
            found_binary_x1 = true;
        }
    }
    assert!(
        found_binary_x1,
        "must find a binary watcher on x1 for the OTFS result"
    );

    // x1 had a non-binary watcher from the original clause setup, which was
    // removed by OTFS. Verify exactly 1 watcher (the new binary one) remains.
    let x1_watch_count: usize = (0..x1_watches.len())
        .filter(|&i| x1_watches.clause_ref(i) == clause_ref)
        .count();
    assert_eq!(
        x1_watch_count, 1,
        "x1 should have exactly 1 (binary) watcher, old non-binary must be removed"
    );

    // Verify the old watch on x0 (pivot / old watched literal) is gone.
    let x0_watches = solver.watches.get_watches(x0);
    for i in 0..x0_watches.len() {
        assert_ne!(
            x0_watches.clause_ref(i),
            clause_ref,
            "stale watcher on x0 (old watched literal / pivot) must be removed"
        );
    }
}

/// OTFS ternary-to-binary with DRAT: the forward checker must accept
/// the TrustedTransform for a binary clause.
#[cfg(debug_assertions)]
#[test]
fn test_otfs_strengthen_ternary_to_binary_drat_accepted() {
    use crate::ProofOutput;

    let proof = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver: Solver = Solver::with_proof_output(3, proof);

    assert!(
        solver.cold.forward_checker.is_some(),
        "forward checker must be active in debug DRAT mode"
    );

    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    let x2 = Literal::positive(Variable(2));

    let clause_idx = solver.add_clause_db(&[x0, x1, x2], false);
    let clause_ref = ClauseRef(clause_idx as u32);
    solver.watches.add_watch(x0, Watcher::new(clause_ref, x1));
    solver.watches.add_watch(x1, Watcher::new(clause_ref, x0));

    solver.decide(x0);
    solver.propagate();
    solver.decide(x1.negated());
    solver.propagate();
    solver.decide(x2.negated());
    solver.propagate();

    // Must not panic: forward checker accepts the TrustedTransform
    // for a binary clause (non-empty, non-tautological, not fully-falsified
    // in the checker's independent BCP view).
    assert!(solver.otfs_strengthen(clause_ref, x0));

    let strengthened = solver.arena.literals(clause_idx);
    assert_eq!(strengthened.len(), 2);
    assert!(
        strengthened.iter().all(|l| l.variable() != x0.variable()),
        "pivot must be removed"
    );
    assert_eq!(solver.otfs_strengthened(), 1);
}

/// Backbone computation: if assuming `¬x0` always leads to conflict,
/// then `x0` is a backbone literal that should be learned as a unit.
///
/// Formula: (x0 ∨ x1) ∧ (x0 ∨ ¬x1) — resolving gives unit x0.
/// Deciding ¬x0 forces both x1 and ¬x1 via the two clauses → conflict.
#[test]
fn test_backbone_finds_forced_unit() {
    use crate::watched::Watcher;

    let mut solver = Solver::new(2);
    let x0p = Literal::positive(Variable(0));
    let x1p = Literal::positive(Variable(1));
    let x1n = Literal::negative(Variable(1));

    // (x0 ∨ x1)
    let c0 = solver.add_clause_db(&[x0p, x1p], false);
    let c0_ref = ClauseRef(c0 as u32);
    solver.watches.add_watch(x0p, Watcher::binary(c0_ref, x1p));
    solver.watches.add_watch(x1p, Watcher::binary(c0_ref, x0p));

    // (x0 ∨ ¬x1)
    let c1 = solver.add_clause_db(&[x0p, x1n], false);
    let c1_ref = ClauseRef(c1 as u32);
    solver.watches.add_watch(x0p, Watcher::binary(c1_ref, x1n));
    solver.watches.add_watch(x1n, Watcher::binary(c1_ref, x0p));

    let found = solver.backbone();

    assert!(found, "backbone should detect x0 as forced");
    assert_eq!(
        solver.get_var_assignment(0),
        Some(true),
        "x0 should be assigned true (backbone literal)"
    );
    assert_eq!(
        solver.qhead,
        solver.trail.len(),
        "backbone must leave the trail fully propagated"
    );
}

/// Backbone probing must be able to use bounded search under the assumption,
/// not just immediate BCP conflicts.
///
/// Under `x0 = true`, these four ternary clauses reduce to the unsatisfiable
/// 2-SAT core over `x1` and `x2`, so `¬x0` is a backbone literal.
#[test]
fn test_backbone_assumption_probe_uses_limited_search() {
    let mut solver = Solver::new(3);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x2 = Variable(2);

    for clause in [
        vec![
            Literal::negative(x0),
            Literal::positive(x1),
            Literal::positive(x2),
        ],
        vec![
            Literal::negative(x0),
            Literal::positive(x1),
            Literal::negative(x2),
        ],
        vec![
            Literal::negative(x0),
            Literal::negative(x1),
            Literal::positive(x2),
        ],
        vec![
            Literal::negative(x0),
            Literal::negative(x1),
            Literal::negative(x2),
        ],
    ] {
        assert!(solver.add_clause(clause));
    }
    solver.initialize_watches();

    let found = solver.backbone();

    assert!(found, "backbone should detect ¬x0 after bounded search");
    assert_eq!(solver.get_var_assignment(0), Some(false));
    assert!(
        solver
            .arena
            .active_indices()
            .any(|idx| solver.arena.len_of(idx) == 1
                && solver.arena.literal(idx, 0) == Literal::negative(x0)),
        "backbone must materialize the detected literal as an explicit unit clause"
    );
    assert_eq!(
        solver.qhead,
        solver.trail.len(),
        "backbone must leave the trail fully propagated"
    );
}

/// Backbone should return false when no forced literals exist.
///
/// Formula: (x0 ∨ x1) — both x0=T,x1=F and x0=F,x1=T are models.
#[test]
fn test_backbone_no_forced_literals() {
    use crate::watched::Watcher;

    let mut solver = Solver::new(2);
    let x0p = Literal::positive(Variable(0));
    let x1p = Literal::positive(Variable(1));

    let c0 = solver.add_clause_db(&[x0p, x1p], false);
    let c0_ref = ClauseRef(c0 as u32);
    solver.watches.add_watch(x0p, Watcher::binary(c0_ref, x1p));
    solver.watches.add_watch(x1p, Watcher::binary(c0_ref, x0p));

    let found = solver.backbone();

    assert!(!found, "no backbone literals in (x0 ∨ x1)");
}

/// Backbone model verification: solve SAT with only backbone enabled (#4943).
/// x0 is backbone (forced true by (x0|x1)&(x0|-x1)), x2-x4 are free.
#[test]
fn test_backbone_model_verification() {
    let dimacs = "p cnf 5 5\n1 2 0\n1 -2 0\n3 4 0\n-4 5 0\n3 -5 0\n";
    let formula = crate::parse_dimacs(dimacs).expect("parse");
    let original_clauses = formula.clauses.clone();
    let mut solver = Solver::new(formula.num_vars);
    solver.disable_all_inprocessing();
    solver.set_backbone_enabled(true);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }
    let result = solver.solve().into_inner();
    let SatResult::Sat(model) = result else {
        panic!("expected SAT, got {result:?}");
    };
    for (ci, clause) in original_clauses.iter().enumerate() {
        let sat = clause
            .iter()
            .any(|l| model[l.variable().index()] == l.is_positive());
        assert!(sat, "clause {ci} unsatisfied: {clause:?}, model: {model:?}");
    }
    assert!(model[0], "backbone x0 should be true");
}

#[test]
fn test_backbone_skip_reason_delays_below_tick_threshold() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = BACKBONE_INTERVAL;
    solver.cold.last_backbone_ticks = 100;
    solver.search_ticks = [
        100 + BACKBONE_TICK_THRESHOLD * solver.num_clauses() as u64 - 1,
        0,
    ];

    assert_eq!(
        solver.backbone_skip_reason(),
        Some(BackboneSkipReason::ThresholdDelay),
        "backbone should defer when tick budget is below CaDiCaL's threshold",
    );
}

#[test]
fn test_backbone_skip_reason_allows_first_call_without_threshold_budget() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = BACKBONE_INTERVAL;
    // last_backbone_ticks == 0 means first call — threshold is bypassed.
    solver.cold.last_backbone_ticks = 0;
    solver.search_ticks = [0, 0];

    assert_eq!(
        solver.backbone_skip_reason(),
        None,
        "first backbone call should not be delayed by tick threshold",
    );
}

#[test]
fn test_backbone_skip_reason_passes_above_tick_threshold() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = BACKBONE_INTERVAL;
    solver.cold.last_backbone_ticks = 100;
    solver.search_ticks = [
        100 + BACKBONE_TICK_THRESHOLD * solver.num_clauses() as u64,
        0,
    ];

    assert_eq!(
        solver.backbone_skip_reason(),
        None,
        "backbone should fire when tick budget meets CaDiCaL's threshold",
    );
}

#[test]
fn test_sweep_skip_reason_delays_below_tick_threshold() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = SWEEP_INTERVAL;
    solver.cold.last_sweep_ticks = 100;
    solver.search_ticks = [
        100 + SWEEP_TICK_THRESHOLD * solver.num_clauses() as u64 - 1,
        0,
    ];

    assert_eq!(
        solver.sweep_skip_reason(),
        Some(SweepSkipReason::ThresholdDelay),
        "sweep should defer when tick budget is below CaDiCaL's threshold",
    );
}

#[test]
fn test_sweep_skip_reason_allows_first_call_without_threshold_budget() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = SWEEP_INTERVAL;
    solver.cold.last_sweep_ticks = 0;
    solver.search_ticks = [0, 0];

    assert_eq!(
        solver.sweep_skip_reason(),
        None,
        "first sweep call should not be delayed by tick threshold",
    );
}

#[test]
fn test_sweep_skip_reason_passes_above_tick_threshold() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = SWEEP_INTERVAL;
    solver.cold.last_sweep_ticks = 100;
    solver.search_ticks = [100 + SWEEP_TICK_THRESHOLD * solver.num_clauses() as u64, 0];

    assert_eq!(
        solver.sweep_skip_reason(),
        None,
        "sweep should fire when tick budget meets CaDiCaL's threshold",
    );
}

#[test]
fn test_vivify_skip_reason_delays_below_tick_threshold() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = VIVIFY_INTERVAL;
    solver.cold.last_vivify_ticks = 100;
    solver.search_ticks = [
        100 + VIVIFY_TICK_THRESHOLD * solver.arena.active_clause_count() as u64 - 1,
        0,
    ];

    assert_eq!(
        solver.vivify_skip_reason(),
        Some(VivifySkipReason::ThresholdDelay),
        "vivify should defer when tick budget is below CaDiCaL's threshold",
    );
}

#[test]
fn test_vivify_skip_reason_allows_first_call_without_threshold_budget() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = VIVIFY_INTERVAL;
    solver.cold.last_vivify_ticks = 0;
    solver.search_ticks = [0, 0];

    assert_eq!(
        solver.vivify_skip_reason(),
        None,
        "first vivify call should not be delayed by tick threshold",
    );
}

#[test]
fn test_vivify_skip_reason_passes_above_tick_threshold() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = VIVIFY_INTERVAL;
    solver.cold.last_vivify_ticks = 100;
    solver.search_ticks = [
        100 + VIVIFY_TICK_THRESHOLD * solver.arena.active_clause_count() as u64,
        0,
    ];

    assert_eq!(
        solver.vivify_skip_reason(),
        None,
        "vivify should fire when tick budget meets CaDiCaL's threshold",
    );
}

// ── Adaptive tick-threshold scaling tests (#8099) ──

#[test]
fn test_adaptive_tick_scale_default_is_conservative() {
    let solver: Solver = Solver::new(3);
    // Default overhead is 0.0 → scale should be 1.0 (no change).
    assert!(
        (solver.adaptive_tick_scale() - 1.0).abs() < f64::EPSILON,
        "default adaptive_tick_scale should be 1.0 when no overhead measured",
    );
}

#[test]
fn test_adaptive_tick_scale_very_low_overhead() {
    let mut solver: Solver = Solver::new(3);
    // Simulate very low overhead (<1ms from incremental maintenance).
    solver.cold.last_inprocessing_overhead_ms = 0.5;
    assert!(
        (solver.adaptive_tick_scale() - 0.25).abs() < f64::EPSILON,
        "adaptive_tick_scale should be 0.25 when overhead < 1ms",
    );
}

#[test]
fn test_adaptive_tick_scale_low_overhead() {
    let mut solver: Solver = Solver::new(3);
    // Simulate low overhead (1-3ms range).
    solver.cold.last_inprocessing_overhead_ms = 1.5;
    assert!(
        (solver.adaptive_tick_scale() - 0.5).abs() < f64::EPSILON,
        "adaptive_tick_scale should be 0.5 when overhead 1-3ms",
    );
}

#[test]
fn test_adaptive_tick_scale_moderate_overhead() {
    let mut solver: Solver = Solver::new(3);
    // Simulate moderate overhead (3-8ms range).
    solver.cold.last_inprocessing_overhead_ms = 5.0;
    assert!(
        (solver.adaptive_tick_scale() - 0.75).abs() < f64::EPSILON,
        "adaptive_tick_scale should be 0.75 when overhead 3-8ms",
    );
}

#[test]
fn test_adaptive_tick_scale_high_overhead_keeps_conservative() {
    let mut solver: Solver = Solver::new(3);
    // Simulate high overhead (e.g., 15ms from full rebuild).
    solver.cold.last_inprocessing_overhead_ms = 15.0;
    assert!(
        (solver.adaptive_tick_scale() - 1.0).abs() < f64::EPSILON,
        "adaptive_tick_scale should be 1.0 when overhead >= 8ms",
    );
}

#[test]
fn test_adaptive_tick_scale_boundary_at_8ms() {
    let mut solver: Solver = Solver::new(3);
    // Exactly 8.0ms is NOT low overhead.
    solver.cold.last_inprocessing_overhead_ms = 8.0;
    assert!(
        (solver.adaptive_tick_scale() - 1.0).abs() < f64::EPSILON,
        "adaptive_tick_scale should be 1.0 at exactly 8.0ms threshold",
    );
}

#[test]
fn test_adaptive_scaling_lowers_backbone_threshold() {
    let mut solver: Solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.add_clause_db(
        &[
            Literal::negative(Variable(0)),
            Literal::positive(Variable(2)),
        ],
        false,
    );

    solver.num_conflicts = BACKBONE_INTERVAL;
    solver.cold.last_backbone_ticks = 100;

    // Set ticks to just below the full threshold but above the scaled threshold.
    // Full threshold: BACKBONE_TICK_THRESHOLD * num_clauses = 5 * 2 = 10
    // Scaled threshold (0.5x): 5
    // ticks_delta needs to be >= 5 but < 10.
    let full_threshold = BACKBONE_TICK_THRESHOLD * solver.num_clauses() as u64;
    let half_threshold = full_threshold / 2;
    solver.search_ticks = [100 + half_threshold + 1, 0];

    // With default (no overhead measured): threshold is full, so this should delay.
    assert_eq!(
        solver.backbone_skip_reason(),
        Some(BackboneSkipReason::ThresholdDelay),
        "without adaptive scaling, ticks below full threshold should delay",
    );

    // With low overhead: threshold is halved, so the same ticks should pass.
    solver.cold.last_inprocessing_overhead_ms = 1.0;
    assert_eq!(
        solver.backbone_skip_reason(),
        None,
        "with low overhead adaptive scaling, halved threshold should allow firing",
    );
}

#[test]
fn test_inprocessing_stats_initial_values() {
    let solver: Solver = Solver::new(3);
    assert_eq!(solver.stats.inprocessing_rounds, 0);
    assert_eq!(solver.stats.inprocessing_simplifications, 0);
    assert!((solver.cold.last_inprocessing_overhead_ms - 0.0).abs() < f64::EPSILON);

    let accounting = solver.inprocessing_pass_accounting();
    assert!(accounting
        .iter()
        .any(|(label, _)| *label == "inproc_subsume_ms"));
    assert!(accounting
        .iter()
        .any(|(label, _)| *label == "inproc_probe_ms"));
    assert!(accounting
        .iter()
        .all(|(_, stats)| stats.attempts == 0 && stats.runs == 0 && stats.yields == 0));
}

mod skip_reasons;
// The bounded-CDCL backbone path can still hit an empty-streak guard, but the
// cheap binary backbone path must not inherit that backoff after finding units.

#[test]
fn test_binary_backbone_productivity_resets_shared_backbone_backoff() {
    let mut solver: Solver = Solver::new(3);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x0p = Literal::positive(x0);

    // Binary backbone can derive x0, while the later bounded-CDCL backbone
    // probe has no additional units to find. The shared backbone control must
    // treat the round as productive so future binary backbone calls are not
    // delayed by bounded-CDCL emptiness.
    solver.add_clause_db(&[x0p, Literal::positive(x1)], false);
    solver.add_clause_db(&[x0p, Literal::negative(x1)], false);
    solver.initialize_watches();
    solver.disable_all_inprocessing();
    solver.set_backbone_enabled(true);
    solver.cold.next_inprobe_conflict = 0;
    solver.inproc_ctrl.backbone.next_conflict = 0;
    solver.num_conflicts = BACKBONE_INTERVAL;
    solver.cold.backbone_consecutive_empty = BACKBONE_STALL_LIMIT;

    assert!(
        !solver.run_restart_inprocessing(),
        "backbone-only inprocessing should not derive UNSAT"
    );
    assert_eq!(
        solver.get_var_assignment(x0.index()),
        Some(true),
        "binary backbone should derive x0 as a root unit"
    );
    assert_eq!(
        solver.cold.backbone_consecutive_empty, 0,
        "binary backbone productivity should reset the shared empty counter"
    );
    assert_eq!(
        solver.inproc_ctrl.backbone.next_conflict,
        solver.num_conflicts + BACKBONE_INTERVAL,
        "productive binary backbone should keep the shared control at base cadence"
    );
    let backbone_schedule = solver.backbone_schedule_stats();
    assert_eq!(
        backbone_schedule.consecutive_empty, 0,
        "exported backbone empty-streak telemetry should match the reset state"
    );
    assert_eq!(
        backbone_schedule.conflicts_until_next, BACKBONE_INTERVAL,
        "exported backbone cadence should expose the post-reset base interval"
    );
    assert_eq!(
        backbone_schedule.backoff_interval, BACKBONE_INTERVAL,
        "exported backbone backoff interval should remain at base after productivity"
    );
    assert!(
        !backbone_schedule.stalled_by_empty,
        "exported backbone stalled flag should clear after binary productivity"
    );
}

#[test]
fn test_bounded_backbone_backoff_does_not_suppress_second_binary_pass() {
    let mut solver = empty_backbone_binary_round_solver();

    assert!(
        solver.backbone_post_vivify_binary_admission_enabled(),
        "post-vivify binary admission should preserve current behavior by default"
    );
    assert!(
        !solver.run_restart_inprocessing(),
        "backbone-only inprocessing should not derive UNSAT"
    );

    let (runs, yields) = inprocessing_pass_runs_and_yields(&solver, "inproc_backbone_ms");
    assert_eq!(
        runs, 3,
        "same-round bounded backoff must not suppress the second binary backbone pass"
    );
    assert_eq!(yields, 0, "fixture should keep all backbone passes empty");
    assert!(
        solver.inproc_ctrl.backbone.next_conflict > solver.num_conflicts,
        "the empty bounded path should still apply growing backoff for future rounds"
    );
}

#[test]
fn test_zero_decompose_bounded_backbone_gate_does_not_suppress_binary_passes() {
    let mut solver = empty_backbone_binary_round_solver();
    solver.set_bounded_backbone_zero_decompose_backoff_enabled(true);
    solver.cold.next_bounded_backbone_conflict = solver.num_conflicts + BACKBONE_INTERVAL;

    assert!(
        !solver.run_restart_inprocessing(),
        "bounded-only gate should not derive UNSAT"
    );

    let (runs, _yields) = inprocessing_pass_runs_and_yields(&solver, "inproc_backbone_ms");
    assert_eq!(
        runs, 2,
        "bounded-only gate should skip bounded CDCL but keep both binary backbone passes available"
    );
    let backbone_schedule = solver.backbone_schedule_stats();
    assert!(backbone_schedule.bounded_zero_decompose_backoff_enabled);
    assert_eq!(
        backbone_schedule.bounded_runs, 0,
        "future bounded-only cooldown should skip bounded-CDCL backbone"
    );
    assert_eq!(
        backbone_schedule.bounded_binary_suppressed, 0,
        "bounded-only cooldown must not suppress binary backbone"
    );
}

fn empty_backbone_binary_round_solver() -> Solver {
    let mut solver: Solver = Solver::new(2);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));

    // No backbone literal exists, so the first binary pass and the bounded-CDCL
    // pass are both empty. The bounded path grows the shared backbone interval,
    // making the post-vivify `should_backbone` check false in the same round.
    solver.add_clause_db(&[x0, x1], false);
    solver.initialize_watches();
    solver.disable_all_inprocessing();
    solver.set_backbone_enabled(true);
    solver.cold.next_inprobe_conflict = 0;
    solver.inproc_ctrl.backbone.next_conflict = 0;
    solver.num_conflicts = BACKBONE_INTERVAL;
    solver
}

#[test]
fn test_disabled_post_vivify_binary_admission_restores_legacy_gate() {
    let mut solver = empty_backbone_binary_round_solver();
    solver.set_backbone_post_vivify_binary_admission_enabled(false);

    assert!(
        !solver.backbone_post_vivify_binary_admission_enabled(),
        "disabled knob should restore the legacy post-vivify backbone gate"
    );
    assert!(
        !solver.run_restart_inprocessing(),
        "backbone-only inprocessing should not derive UNSAT"
    );

    let (runs, yields) = inprocessing_pass_runs_and_yields(&solver, "inproc_backbone_ms");
    assert_eq!(
        runs, 2,
        "legacy gate should skip the post-vivify binary pass after bounded backoff"
    );
    assert_eq!(yields, 0, "fixture should keep all backbone passes empty");
    assert!(
        solver.inproc_ctrl.backbone.next_conflict > solver.num_conflicts,
        "the empty bounded path should still apply growing backoff for future rounds"
    );
}

#[test]
fn test_backbone_schedule_stats_expose_empty_backoff_state() {
    let mut solver: Solver = Solver::new(1);
    solver.disable_all_inprocessing();
    solver.set_backbone_enabled(true);
    solver.num_conflicts = BACKBONE_INTERVAL;
    solver.cold.backbone_phases = 7;
    solver.cold.backbone_consecutive_empty = BACKBONE_STALL_LIMIT - 1;

    let interval = solver.inproc_ctrl.backbone.reschedule_growing(
        solver.num_conflicts,
        BACKBONE_INTERVAL,
        3,
        2,
        BACKBONE_MAX_INTERVAL,
    );
    let backbone_schedule = solver.backbone_schedule_stats();

    assert!(backbone_schedule.enabled);
    assert_eq!(backbone_schedule.phases, 7);
    assert_eq!(backbone_schedule.max_rounds, BACKBONE_MAX_ROUNDS);
    assert_eq!(
        backbone_schedule.consecutive_empty,
        BACKBONE_STALL_LIMIT - 1
    );
    assert_eq!(backbone_schedule.stall_limit, BACKBONE_STALL_LIMIT);
    assert_eq!(
        backbone_schedule.next_conflict,
        solver.num_conflicts + interval
    );
    assert_eq!(backbone_schedule.conflicts_until_next, interval);
    assert_eq!(backbone_schedule.backoff_interval, interval);
    assert_eq!(backbone_schedule.base_interval, BACKBONE_INTERVAL);
    assert_eq!(backbone_schedule.max_interval, BACKBONE_MAX_INTERVAL);
    assert!(!backbone_schedule.yield_rescue_cooldown_enabled);
    assert_eq!(backbone_schedule.yield_rescue_cooldown_rounds, 0);
    assert_eq!(
        backbone_schedule.yield_rescue_cooldown_interval,
        YIELD_RESCUE_BACKBONE_COOLDOWN_INTERVAL
    );
    assert!(!backbone_schedule.bounded_zero_decompose_backoff_enabled);
    assert_eq!(backbone_schedule.bounded_backoff_triggers, 0);
    assert_eq!(backbone_schedule.bounded_runs, 0);
    assert_eq!(backbone_schedule.bounded_yields, 0);
    assert_eq!(backbone_schedule.bounded_ms, 0);
    assert_eq!(backbone_schedule.bounded_binary_suppressed, 0);
    assert!(!backbone_schedule.due);
    assert!(!backbone_schedule.stalled_by_empty);
    assert!(!backbone_schedule.rounds_exhausted);
}

fn backbone_yield_only_round_solver() -> Solver {
    let mut solver: Solver = Solver::new(2);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));

    solver.add_clause_db(&[x0, x1], false);
    solver.add_clause_db(&[x0, x1.negated()], false);
    solver.initialize_watches();
    solver.disable_all_inprocessing();
    solver.set_backbone_enabled(true);
    solver.cold.next_inprobe_conflict = 0;
    solver.inproc_ctrl.backbone.next_conflict = 0;
    solver.num_conflicts = BACKBONE_INTERVAL;
    solver
}

fn yield_rescue_backbone_cooldown_anchor_solver() -> Solver {
    let mut solver: Solver = Solver::new(900);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));

    solver.add_clause_db(&[x0, x1], false);
    solver.add_clause_db(&[x0, x1.negated()], false);
    for i in 0..400 {
        let a = Literal::positive(Variable(4 + 2 * i));
        let b = Literal::positive(Variable(5 + 2 * i));
        solver.add_clause_db(&[a, b], false);
    }
    solver.initialize_watches();
    solver.disable_all_inprocessing();
    solver.set_backbone_enabled(true);
    solver.cold.next_inprobe_conflict = 0;
    solver.inproc_ctrl.backbone.next_conflict = 0;
    solver.num_conflicts = BACKBONE_INTERVAL;
    solver
}

fn add_decompose_equivalence_after_anchor_round(solver: &mut Solver) {
    let x2 = Literal::positive(Variable(2));
    let x3 = Literal::positive(Variable(3));

    solver.add_clause_db(&[x2.negated(), x3], false);
    solver.add_clause_db(&[x3.negated(), x2], false);
    solver.rebuild_watches();
}

#[test]
fn test_inprocessing_yield_productivity_rescue_default_off_keeps_low_productivity_backoff() {
    let mut solver = backbone_yield_only_round_solver();

    assert!(
        !solver.inprocessing_yield_productivity_rescue_enabled(),
        "#9084 scheduler rescue must stay default-off"
    );
    assert!(
        !solver.inprocessing_yield_rescue_backbone_cooldown_enabled(),
        "#9084 yield-rescue backbone cooldown must stay default-off"
    );
    assert!(
        !solver.run_restart_inprocessing(),
        "backbone-yield fixture should not derive UNSAT"
    );
    assert_eq!(
        solver.get_var_assignment(Variable(0).index()),
        Some(true),
        "binary backbone should derive a root unit"
    );
    assert_eq!(
        solver.cold.last_round_simplifications, 0,
        "fixture should isolate pass yield from clause-count simplification"
    );
    assert_eq!(
        solver.cold.consecutive_low_productivity_rounds, 1,
        "default scheduling should still count the yield-only round as low productivity"
    );
    let (runs, yields) = inprocessing_pass_runs_and_yields(&solver, "inproc_backbone_ms");
    assert!(runs > 0, "backbone should run in the fixture");
    assert!(yields > 0, "backbone should record a pass-local yield");
    let generic_delta = expected_inprobe_delta_after_round(&solver, 1.0);
    assert_eq!(
        solver.cold.next_inprobe_conflict,
        solver.total_conflicts() + generic_delta,
        "default-off rescue must not alter inprobe cadence"
    );
    assert_eq!(
        solver
            .backbone_schedule_stats()
            .yield_rescue_cooldown_rounds,
        0,
        "default-off cooldown must not record clamp rounds"
    );
}

#[test]
fn test_inprocessing_yield_productivity_rescue_counts_backbone_yield_as_productive() {
    let mut default_solver = backbone_yield_only_round_solver();
    assert!(
        !default_solver.run_restart_inprocessing(),
        "default backbone-yield fixture should not derive UNSAT"
    );

    let mut solver = backbone_yield_only_round_solver();
    solver.set_inprocessing_yield_productivity_rescue_enabled(true);

    assert!(solver.inprocessing_yield_productivity_rescue_enabled());
    assert!(
        !solver.run_restart_inprocessing(),
        "rescued backbone-yield fixture should not derive UNSAT"
    );
    assert_eq!(
        solver.cold.last_round_simplifications, 0,
        "fixture should remain a zero-simplification round"
    );
    assert_eq!(
        solver.cold.consecutive_low_productivity_rounds, 0,
        "enabled rescue should treat productive backbone yield as round productivity"
    );
    let (runs, yields) = inprocessing_pass_runs_and_yields(&solver, "inproc_backbone_ms");
    assert!(runs > 0, "backbone should run in the fixture");
    assert!(
        yields > 0,
        "backbone should record the productive pass yield"
    );
    let rescued_delta = expected_inprobe_delta_after_round(&solver, 1.0);
    assert_eq!(
        solver.cold.next_inprobe_conflict,
        solver.total_conflicts() + rescued_delta,
        "enabled rescue should schedule using the non-low-productivity cadence"
    );
    assert!(
        solver.cold.next_inprobe_conflict < default_solver.cold.next_inprobe_conflict,
        "enabled rescue should reduce the next inprobe delay versus default low-productivity backoff"
    );
}

#[test]
fn test_yield_rescue_backbone_cooldown_clamps_backbone_only_cadence() {
    let mut solver = backbone_yield_only_round_solver();
    solver.set_inprocessing_yield_productivity_rescue_enabled(true);
    solver.set_inprocessing_yield_rescue_backbone_cooldown_enabled(true);

    assert!(
        !solver.run_restart_inprocessing(),
        "cooldown scheduling should not derive UNSAT by itself"
    );
    assert_eq!(
        solver.cold.consecutive_low_productivity_rounds, 0,
        "cooldown must preserve yield-rescue productivity accounting"
    );
    let rescued_delta = expected_inprobe_delta_after_round(&solver, 1.0);
    assert_eq!(
        solver.cold.next_inprobe_conflict,
        solver.total_conflicts() + rescued_delta,
        "cooldown should not widen the rescued inprobe cadence"
    );

    let backbone_schedule = solver.backbone_schedule_stats();
    assert!(backbone_schedule.yield_rescue_cooldown_enabled);
    assert_eq!(
        backbone_schedule.yield_rescue_cooldown_rounds, 1,
        "one yield-rescued low-productivity round should apply the clamp"
    );
    assert_eq!(
        backbone_schedule.conflicts_until_next, YIELD_RESCUE_BACKBONE_COOLDOWN_INTERVAL,
        "cooldown should push only the shared backbone row out"
    );
}

#[test]
fn test_yield_rescue_backbone_cooldown_does_not_slide_on_decompose_only_round() {
    let mut solver = yield_rescue_backbone_cooldown_anchor_solver();
    solver.set_inprocessing_yield_productivity_rescue_enabled(true);
    solver.set_inprocessing_yield_rescue_backbone_cooldown_enabled(true);

    assert!(
        !solver.run_restart_inprocessing(),
        "anchoring backbone round should not derive UNSAT"
    );
    let anchored_backbone_next = solver.inproc_ctrl.backbone.next_conflict;
    assert_eq!(
        anchored_backbone_next,
        solver.num_conflicts + YIELD_RESCUE_BACKBONE_COOLDOWN_INTERVAL,
        "first cooldown should be anchored by a real backbone round"
    );
    assert_eq!(
        solver
            .backbone_schedule_stats()
            .yield_rescue_cooldown_rounds,
        1,
        "the initial backbone-yield round should apply the cooldown once"
    );

    add_decompose_equivalence_after_anchor_round(&mut solver);
    solver.set_decompose_enabled(true);
    solver.cold.next_inprobe_conflict = 0;
    solver.inproc_ctrl.decompose.next_conflict = 0;
    solver.num_conflicts = BACKBONE_INTERVAL + INPROBE_INTERVAL;
    assert!(
        solver.num_conflicts < anchored_backbone_next,
        "second round must occur while backbone is still cooling down"
    );

    let (backbone_runs_before, backbone_yields_before) =
        inprocessing_pass_runs_and_yields(&solver, "inproc_backbone_ms");
    let (decompose_runs_before, decompose_yields_before) =
        inprocessing_pass_runs_and_yields(&solver, "inproc_decompose_ms");

    assert!(
        !solver.run_restart_inprocessing(),
        "decompose-only rescue round should not derive UNSAT"
    );

    let (backbone_runs_after, backbone_yields_after) =
        inprocessing_pass_runs_and_yields(&solver, "inproc_backbone_ms");
    let (decompose_runs_after, decompose_yields_after) =
        inprocessing_pass_runs_and_yields(&solver, "inproc_decompose_ms");
    assert_eq!(
        (backbone_runs_after, backbone_yields_after),
        (backbone_runs_before, backbone_yields_before),
        "backbone must not run while its anchored cooldown is still active"
    );
    assert!(
        decompose_runs_after > decompose_runs_before,
        "fixture must run decompose in the second round"
    );
    assert!(
        decompose_yields_after > decompose_yields_before,
        "fixture must exercise a decompose-yield rescue round"
    );
    assert_eq!(
        solver.inproc_ctrl.backbone.next_conflict, anchored_backbone_next,
        "decompose-only rescue must not slide the backbone deadline forward"
    );
    assert_eq!(
        solver
            .backbone_schedule_stats()
            .yield_rescue_cooldown_rounds,
        1,
        "decompose-only rescue must not record another backbone cooldown clamp"
    );
}

fn expected_inprobe_delta_after_round(solver: &Solver, lrat_zero_yield_scale: f64) -> u64 {
    let log_factor = ((solver.cold.inprobe_phases + 9) as f64).log10();
    let base_delta = (10.0 * INPROBE_INTERVAL as f64 * log_factor) as u64;
    let active_count = solver.arena.active_clause_count();
    let clause_scale = if active_count > PREPROCESS_EXPENSIVE_MAX_CLAUSES {
        (active_count as f64 / 1_000_000.0).sqrt().max(1.0)
    } else {
        1.0
    };
    let productivity_scale = if solver.cold.consecutive_low_productivity_rounds > 0 {
        3.0_f64.powi(solver.cold.consecutive_low_productivity_rounds as i32)
    } else {
        1.0
    };
    let delta =
        (base_delta as f64 * clause_scale * productivity_scale * lrat_zero_yield_scale) as u64;
    delta.max(INPROBE_INTERVAL)
}

fn inprocessing_pass_runs_and_yields(solver: &Solver, label: &str) -> (u64, u64) {
    let (_, accounting) = solver
        .inprocessing_pass_accounting()
        .into_iter()
        .find(|(pass_label, _)| *pass_label == label)
        .expect("pass accounting label should exist");
    (accounting.runs, accounting.yields)
}

fn lrat_solver_with_due_proof_clamped_bve_factor() -> Solver {
    let proof = ProofOutput::lrat_text(Vec::new(), 1);
    let mut solver = Solver::with_proof_output(3, proof);
    solver.set_sat_comp_main_conflict_pruning(true);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.initialize_watches();
    solver.disable_all_inprocessing();
    solver.cold.next_inprobe_conflict = 0;
    solver.inproc_ctrl.bve.next_conflict = 0;
    solver.inproc_ctrl.factor.next_conflict = 0;
    solver.num_conflicts = FACTOR_INTERVAL;
    assert!(!solver.is_bve_enabled(), "LRAT BVE must stay clamped");
    assert!(!solver.is_factor_enabled(), "LRAT factor must stay clamped");
    assert!(
        solver.bve_would_be_due_if_enabled(),
        "fixture must expose shadow BVE eligibility"
    );
    assert!(
        solver.factor_would_be_due_if_enabled(),
        "fixture must expose shadow factor eligibility"
    );
    solver
}

fn lrat_solver_with_due_proof_clamped_bve_factor_and_probe_yield() -> Solver {
    let proof = ProofOutput::lrat_text(Vec::new(), 1);
    let mut solver = Solver::with_proof_output(2, proof);
    let x0 = Literal::positive(Variable(0));
    let x1 = Literal::positive(Variable(1));
    solver.add_clause_db(&[x0, x1], false);
    solver.add_clause_db(&[x0, x1.negated()], false);
    solver.initialize_watches();
    solver.disable_all_inprocessing();
    solver.set_probe_enabled(true);
    solver.cold.next_inprobe_conflict = 0;
    solver.inproc_ctrl.probe.next_conflict = 0;
    solver.inproc_ctrl.bve.next_conflict = 0;
    solver.inproc_ctrl.factor.next_conflict = 0;
    solver.num_conflicts = FACTOR_INTERVAL;
    assert!(!solver.is_bve_enabled(), "LRAT BVE must stay clamped");
    assert!(!solver.is_factor_enabled(), "LRAT factor must stay clamped");
    solver
}

#[test]
fn test_lrat_proof_clamp_probe_rescue_default_off() {
    let solver = lrat_solver_with_due_proof_clamped_bve_factor();

    assert!(
        !solver.lrat_proof_clamp_probe_rescue_enabled(),
        "probe rescue must stay default-off"
    );
}

#[test]
fn test_lrat_proof_clamped_eligibility_counters_do_not_change_default_cadence() {
    let mut solver = lrat_solver_with_due_proof_clamped_bve_factor();

    assert!(
        !solver.run_restart_inprocessing(),
        "empty LRAT shadow-eligibility round should not derive UNSAT"
    );
    assert_eq!(
        solver.inprocessing_lrat_clamp_stats(),
        (1, 1, 0),
        "shadow counters should record due proof-clamped BVE/factor without rescue"
    );
    assert_eq!(
        solver.cold.consecutive_low_productivity_rounds, 1,
        "default-off LRAT proof-clamped eligibility must still count as low productivity"
    );
    let generic_delta = expected_inprobe_delta_after_round(&solver, 1.0);
    assert_eq!(
        solver.cold.next_inprobe_conflict,
        solver.total_conflicts() + generic_delta,
        "default-off shadow counters must not alter inprobe cadence"
    );
}

#[test]
fn test_lrat_proof_clamp_probe_rescue_advances_only_probe_cadence_when_enabled() {
    let mut solver = lrat_solver_with_due_proof_clamped_bve_factor();
    solver.set_probe_enabled(true);
    solver.inproc_ctrl.probe.next_conflict = solver.num_conflicts + 10 * PROBE_INTERVAL;
    solver.set_lrat_proof_clamp_probe_rescue_enabled(true);

    assert!(
        !solver.run_restart_inprocessing(),
        "probe-rescue scheduling should not derive UNSAT by itself"
    );
    assert_eq!(
        solver.inprocessing_lrat_clamp_stats(),
        (1, 1, 1),
        "enabled rescue should be counted after zero-simplification clamped eligibility"
    );
    assert_eq!(
        solver.cold.consecutive_low_productivity_rounds, 0,
        "enabled rescue should reset the stale low-productivity backoff streak"
    );
    assert_eq!(
        solver.cold.next_inprobe_conflict,
        solver.total_conflicts() + LRAT_PROOF_CLAMP_PROBE_RESCUE_INTERVAL,
        "rescue should advance the LRAT-safe inprobe cadence"
    );
    assert_eq!(
        solver.inproc_ctrl.probe.next_conflict,
        solver.num_conflicts + LRAT_PROOF_CLAMP_PROBE_RESCUE_INTERVAL,
        "rescue should advance only the LRAT-safe probe pass cadence"
    );
    assert!(!solver.is_bve_enabled(), "rescue must not reopen BVE");
    assert!(!solver.is_factor_enabled(), "rescue must not reopen factor");
}

#[test]
fn test_lrat_proof_clamp_probe_rescue_accepts_safe_yield_only_round() {
    let mut solver = lrat_solver_with_due_proof_clamped_bve_factor_and_probe_yield();
    solver.set_lrat_proof_clamp_probe_rescue_enabled(true);

    assert!(
        !solver.run_restart_inprocessing(),
        "probe-rescue scheduling should not derive UNSAT by itself"
    );
    assert_eq!(
        solver.get_var_assignment(Variable(0).index()),
        Some(true),
        "fixture should derive a proof-safe probe unit"
    );
    assert_eq!(
        solver.cold.last_round_simplifications, 0,
        "fixture should isolate pass-local yield from clause-count simplification"
    );
    let (probe_runs, probe_yields) = inprocessing_pass_runs_and_yields(&solver, "inproc_probe_ms");
    assert!(probe_runs > 0, "probe should run in the fixture");
    assert!(
        probe_yields > 0,
        "fixture should record a safe pass-local yield"
    );
    assert_eq!(
        solver.inprocessing_lrat_clamp_stats(),
        (1, 1, 1),
        "enabled rescue should tolerate safe yield-only clamped rounds"
    );
    assert_eq!(
        solver.cold.consecutive_low_productivity_rounds, 0,
        "enabled rescue should reset the stale low-productivity backoff streak"
    );
    assert_eq!(
        solver.inproc_ctrl.probe.next_conflict,
        solver.num_conflicts + LRAT_PROOF_CLAMP_PROBE_RESCUE_INTERVAL,
        "rescue should advance only the LRAT-safe probe pass cadence"
    );
    assert!(!solver.is_bve_enabled(), "rescue must not reopen BVE");
    assert!(!solver.is_factor_enabled(), "rescue must not reopen factor");
}

#[test]
fn test_lrat_zero_yield_inprocessing_round_gets_exact_extra_cooldown() {
    let proof = ProofOutput::lrat_text(Vec::new(), 1);
    let mut solver = Solver::with_proof_output(3, proof);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
            Literal::positive(Variable(2)),
        ],
        false,
    );
    solver.initialize_watches();
    solver.disable_all_inprocessing();
    solver.set_vivify_enabled(true);
    solver.cold.next_inprobe_conflict = 0;
    solver.inproc_ctrl.vivify.next_conflict = 0;
    solver.inproc_ctrl.vivify_irred.next_conflict = 0;
    solver.num_conflicts = VIVIFY_INTERVAL;

    assert!(
        !solver.run_restart_inprocessing(),
        "zero-yield LRAT vivify-only round should not derive UNSAT"
    );
    assert_eq!(
        solver.cold.last_round_simplifications, 0,
        "fixture should exercise the zero-yield cooldown path"
    );
    assert_eq!(
        inprocessing_pass_runs_and_yields(&solver, "inproc_vivify_ms"),
        (1, 0),
        "vivify should run without producing a pass-local yield"
    );
    let generic_delta = expected_inprobe_delta_after_round(&solver, 1.0);
    let lrat_delta =
        expected_inprobe_delta_after_round(&solver, LRAT_ZERO_YIELD_INPROBE_COOLDOWN_SCALE);
    assert_ne!(
        generic_delta, lrat_delta,
        "LRAT zero-yield scale must be distinct from generic low-productivity backoff"
    );
    assert_eq!(
        solver.cold.next_inprobe_conflict,
        solver.total_conflicts() + lrat_delta,
        "zero-yield LRAT rounds should apply the LRAT multiplier exactly"
    );
}

#[test]
fn test_non_lrat_zero_yield_inprocessing_round_uses_generic_cooldown() {
    let mut solver = Solver::new(3);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
            Literal::positive(Variable(2)),
        ],
        false,
    );
    solver.initialize_watches();
    solver.disable_all_inprocessing();
    solver.set_vivify_enabled(true);
    solver.cold.next_inprobe_conflict = 0;
    solver.inproc_ctrl.vivify.next_conflict = 0;
    solver.inproc_ctrl.vivify_irred.next_conflict = 0;
    solver.num_conflicts = VIVIFY_INTERVAL;

    assert!(
        !solver.run_restart_inprocessing(),
        "zero-yield non-LRAT vivify-only round should not derive UNSAT"
    );
    assert_eq!(
        solver.cold.last_round_simplifications, 0,
        "fixture should remain a zero-simplification round"
    );
    assert_eq!(
        inprocessing_pass_runs_and_yields(&solver, "inproc_vivify_ms"),
        (1, 0),
        "vivify should run without producing a pass-local yield"
    );
    let generic_delta = expected_inprobe_delta_after_round(&solver, 1.0);
    let lrat_delta =
        expected_inprobe_delta_after_round(&solver, LRAT_ZERO_YIELD_INPROBE_COOLDOWN_SCALE);
    assert_eq!(
        solver.cold.next_inprobe_conflict,
        solver.total_conflicts() + generic_delta,
        "non-LRAT zero-yield rounds should use only generic low-productivity backoff"
    );
    assert_ne!(
        solver.cold.next_inprobe_conflict,
        solver.total_conflicts() + lrat_delta,
        "non-LRAT rounds must not inherit the LRAT zero-yield multiplier"
    );
}

#[test]
fn test_lrat_empty_inprocessing_round_uses_generic_cooldown() {
    let proof = ProofOutput::lrat_text(Vec::new(), 1);
    let mut solver = Solver::with_proof_output(1, proof);
    solver.add_clause_db(&[Literal::positive(Variable(0))], false);
    solver.initialize_watches();
    solver.disable_all_inprocessing();
    solver.cold.next_inprobe_conflict = 0;
    solver.num_conflicts = INPROBE_INTERVAL;

    assert!(
        !solver.run_restart_inprocessing(),
        "empty LRAT inprocessing round should not derive UNSAT"
    );
    assert_eq!(
        solver.cold.last_round_simplifications, 0,
        "empty round should have no simplifications"
    );
    assert!(
        solver
            .inprocessing_pass_accounting()
            .into_iter()
            .all(|(_, accounting)| accounting.runs == 0 && accounting.yields == 0),
        "empty round should not record pass runs or yields"
    );
    let generic_delta = expected_inprobe_delta_after_round(&solver, 1.0);
    let lrat_delta =
        expected_inprobe_delta_after_round(&solver, LRAT_ZERO_YIELD_INPROBE_COOLDOWN_SCALE);
    assert_eq!(
        solver.cold.next_inprobe_conflict,
        solver.total_conflicts() + generic_delta,
        "LRAT empty rounds should be guarded out of the zero-yield multiplier"
    );
    assert_ne!(
        solver.cold.next_inprobe_conflict,
        solver.total_conflicts() + lrat_delta,
        "empty LRAT rounds must not be treated as pass zero-yield"
    );
}

#[test]
fn test_lrat_pass_yield_without_clause_simplification_uses_generic_cooldown() {
    let proof = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver = Solver::with_proof_output(2, proof);
    let x0 = Variable(0);
    let x1 = Variable(1);
    let x0p = Literal::positive(x0);

    solver.add_clause_db(&[x0p, Literal::positive(x1)], false);
    solver.add_clause_db(&[x0p, Literal::negative(x1)], false);
    solver.initialize_watches();
    solver.disable_all_inprocessing();
    solver.set_backbone_enabled(true);
    solver.cold.next_inprobe_conflict = 0;
    solver.inproc_ctrl.backbone.next_conflict = 0;
    solver.num_conflicts = BACKBONE_INTERVAL;

    assert!(
        !solver.run_restart_inprocessing(),
        "LRAT backbone-yield round should not derive UNSAT"
    );
    assert_eq!(
        solver.get_var_assignment(x0.index()),
        Some(true),
        "binary backbone should derive x0 as a root unit"
    );
    assert_eq!(
        solver.cold.last_round_simplifications, 0,
        "binary backbone yield should not depend on clause-count simplification"
    );
    let (runs, yields) = inprocessing_pass_runs_and_yields(&solver, "inproc_backbone_ms");
    assert!(runs > 0, "backbone should run in the fixture");
    assert!(yields > 0, "backbone should record a pass-local yield");
    let generic_delta = expected_inprobe_delta_after_round(&solver, 1.0);
    let lrat_delta =
        expected_inprobe_delta_after_round(&solver, LRAT_ZERO_YIELD_INPROBE_COOLDOWN_SCALE);
    assert_eq!(
        solver.cold.next_inprobe_conflict,
        solver.total_conflicts() + generic_delta,
        "LRAT rounds with pass-local yield should use generic low-productivity backoff"
    );
    assert_ne!(
        solver.cold.next_inprobe_conflict,
        solver.total_conflicts() + lrat_delta,
        "LRAT pass-yield rounds must not receive the zero-yield multiplier"
    );
}

// ======== FormulaClass tests (#8150) ========

#[test]
fn test_formula_class_small() {
    let class = FormulaClass::classify(1_000, 10_000);
    assert_eq!(class, FormulaClass::Small);
}

#[test]
fn test_formula_class_medium() {
    let class = FormulaClass::classify(50_000, 500_000);
    assert_eq!(class, FormulaClass::Medium);
}

#[test]
fn test_formula_class_large_by_vars() {
    let class = FormulaClass::classify(PREPROCESS_EXPENSIVE_MAX_VARS, 100_000);
    assert_eq!(class, FormulaClass::Large);
}

#[test]
fn test_formula_class_large_by_clauses() {
    let class = FormulaClass::classify(10_000, PREPROCESS_EXPENSIVE_MAX_CLAUSES);
    assert_eq!(class, FormulaClass::Large);
}

#[test]
fn test_formula_class_boundary_small_to_medium() {
    // Just above the small threshold (10K vars).
    let class = FormulaClass::classify(10_000, 50_000);
    assert_eq!(class, FormulaClass::Medium);
}

#[test]
fn test_backbone_conflict_budget_small() {
    // Small formula with few vars: budget = min(500, 10000) = 500.
    let budget = FormulaClass::Small.backbone_conflict_budget(500);
    assert_eq!(budget, 500);
}

#[test]
fn test_backbone_conflict_budget_small_capped() {
    // Small formula with many vars: budget = min(50000, 10000) = 10000.
    let budget = FormulaClass::Small.backbone_conflict_budget(50_000);
    assert_eq!(budget, 10_000);
}

#[test]
fn test_backbone_conflict_budget_medium() {
    let budget = FormulaClass::Medium.backbone_conflict_budget(50_000);
    assert_eq!(budget, 2_000);
}

#[test]
fn test_backbone_conflict_budget_large() {
    let budget = FormulaClass::Large.backbone_conflict_budget(50_000);
    assert_eq!(budget, 1_000);
}

/// Binary-clause backbone detection: if assuming ¬x0 leads to a binary
/// conflict, backbone_binary should discover x0 as a backbone unit.
///
/// Formula: (x0 ∨ x1) ∧ (x0 ∨ ¬x1) — resolving gives unit x0.
/// Deciding ¬x0 forces x1 via first clause and ¬x1 via second → conflict.
/// 1UIP on binary implication graph yields x0 as backbone.
#[test]
fn test_backbone_binary_finds_forced_unit() {
    use crate::watched::Watcher;

    let mut solver = Solver::new(2);
    let x0p = Literal::positive(Variable(0));
    let x1p = Literal::positive(Variable(1));
    let x1n = Literal::negative(Variable(1));

    // (x0 ∨ x1)
    let c0 = solver.add_clause_db(&[x0p, x1p], false);
    let c0_ref = ClauseRef(c0 as u32);
    solver.watches.add_watch(x0p, Watcher::binary(c0_ref, x1p));
    solver.watches.add_watch(x1p, Watcher::binary(c0_ref, x0p));

    // (x0 ∨ ¬x1)
    let c1 = solver.add_clause_db(&[x0p, x1n], false);
    let c1_ref = ClauseRef(c1 as u32);
    solver.watches.add_watch(x0p, Watcher::binary(c1_ref, x1n));
    solver.watches.add_watch(x1n, Watcher::binary(c1_ref, x0p));

    let found = solver.backbone_binary();

    assert!(found, "backbone_binary should detect x0 as forced");
    assert_eq!(
        solver.get_var_assignment(0),
        Some(true),
        "x0 should be assigned true (backbone literal)"
    );
    assert_eq!(
        solver.qhead,
        solver.trail.len(),
        "backbone_binary must leave the trail fully propagated"
    );
    assert_eq!(
        solver.decision_level, 0,
        "backbone_binary must leave solver at level 0"
    );
    assert!(
        solver.stats.backbone_binary_units > 0,
        "backbone_binary_units stat should be incremented"
    );
}

/// Binary-clause backbone should return false when no backbone literals exist.
///
/// Formula: (x0 ∨ x1) — both x0=T,x1=F and x0=F,x1=T are models.
/// Neither variable is forced.
#[test]
fn test_backbone_binary_no_forced_literals() {
    use crate::watched::Watcher;

    let mut solver = Solver::new(2);
    let x0p = Literal::positive(Variable(0));
    let x1p = Literal::positive(Variable(1));

    let c0 = solver.add_clause_db(&[x0p, x1p], false);
    let c0_ref = ClauseRef(c0 as u32);
    solver.watches.add_watch(x0p, Watcher::binary(c0_ref, x1p));
    solver.watches.add_watch(x1p, Watcher::binary(c0_ref, x0p));

    let found = solver.backbone_binary();

    assert!(!found, "no backbone literals in (x0 ∨ x1)");
    assert_eq!(
        solver.decision_level, 0,
        "backbone_binary must leave solver at level 0"
    );
}

/// Binary backbone with chain: (¬x0 ∨ x1) ∧ (¬x1 ∨ x2) ∧ (¬x0 ∨ ¬x2).
///
/// Assuming x0=T propagates x1=T via first clause, x2=T via second clause,
/// then conflicts with ¬x2 in the third clause. 1UIP yields ¬x0 as backbone.
#[test]
fn test_backbone_binary_chain_propagation() {
    use crate::watched::Watcher;

    let mut solver = Solver::new(3);
    let _x0p = Literal::positive(Variable(0));
    let x0n = Literal::negative(Variable(0));
    let x1p = Literal::positive(Variable(1));
    let x1n = Literal::negative(Variable(1));
    let x2p = Literal::positive(Variable(2));
    let x2n = Literal::negative(Variable(2));

    // (¬x0 ∨ x1): x0=T → x1=T
    let c0 = solver.add_clause_db(&[x0n, x1p], false);
    let c0_ref = ClauseRef(c0 as u32);
    solver.watches.add_watch(x0n, Watcher::binary(c0_ref, x1p));
    solver.watches.add_watch(x1p, Watcher::binary(c0_ref, x0n));

    // (¬x1 ∨ x2): x1=T → x2=T
    let c1 = solver.add_clause_db(&[x1n, x2p], false);
    let c1_ref = ClauseRef(c1 as u32);
    solver.watches.add_watch(x1n, Watcher::binary(c1_ref, x2p));
    solver.watches.add_watch(x2p, Watcher::binary(c1_ref, x1n));

    // (¬x0 ∨ ¬x2): x0=T and x2=T → conflict
    let c2 = solver.add_clause_db(&[x0n, x2n], false);
    let c2_ref = ClauseRef(c2 as u32);
    solver.watches.add_watch(x0n, Watcher::binary(c2_ref, x2n));
    solver.watches.add_watch(x2n, Watcher::binary(c2_ref, x0n));

    let found = solver.backbone_binary();

    assert!(
        found,
        "backbone_binary should detect ¬x0 via chain propagation"
    );
    assert_eq!(
        solver.get_var_assignment(0),
        Some(false),
        "x0 should be assigned false (backbone literal)"
    );
    assert_eq!(
        solver.decision_level, 0,
        "backbone_binary must leave solver at level 0"
    );
}

/// OTFS is safe during backbone bounded-CDCL probing (#8439).
///
/// The original bug: OTFS strengthened a reason clause and cleared the pivot's
/// reason pointer to NO_REASON. During backbone's bounded search, subsequent
/// conflicts encountered the pivot with no reason and treated it as a decision
/// variable, corrupting the 1UIP resolution counter and causing trail exhaustion.
///
/// The fix (c06faaf76): preserve the pivot's reason pointer after OTFS
/// strengthening. The strengthened clause still implies the pivot.
///
/// This test exercises the fix by solving a formula with backbone enabled.
/// The formula structure forces backbone probing to run bounded CDCL searches
/// that produce conflicts. OTFS may trigger during these conflicts. The test
/// verifies:
/// 1. No panic from trail exhaustion (the original symptom)
/// 2. The solver reaches a correct SAT result
/// 3. The model satisfies all original clauses
#[test]
fn test_backbone_with_otfs_no_trail_exhaustion() {
    // Construct a formula where x0 is a backbone literal (forced true)
    // and conflicts during backbone probes involve multi-literal clauses
    // that are candidates for OTFS strengthening.
    //
    // x0 is backbone: (x0|x1|x2) & (x0|x1|-x2) & (x0|-x1|x2) & (x0|-x1|-x2)
    // (under -x0, the four clauses become a UNSAT 2-CNF over x1,x2)
    //
    // Additional clauses make the formula satisfiable with free variables:
    // (x3|x4) & (-x3|x5) & (x4|-x5)
    let dimacs = "\
p cnf 6 7
1 2 3 0
1 2 -3 0
1 -2 3 0
1 -2 -3 0
4 5 0
-4 6 0
5 -6 0
";
    let formula = crate::parse_dimacs(dimacs).expect("parse");
    let original_clauses = formula.clauses.clone();
    let mut solver = Solver::new(formula.num_vars);
    // Enable only backbone (disable other inprocessing that could mask the test).
    solver.disable_all_inprocessing();
    solver.set_backbone_enabled(true);
    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    let result = solver.solve().into_inner();
    let SatResult::Sat(model) = result else {
        panic!("expected SAT, got {result:?}");
    };

    // Verify all original clauses are satisfied.
    for (ci, clause) in original_clauses.iter().enumerate() {
        let sat = clause
            .iter()
            .any(|l| model[l.variable().index()] == l.is_positive());
        assert!(sat, "clause {ci} unsatisfied: {clause:?}, model: {model:?}");
    }

    // x0 is a backbone literal -- must be true in every satisfying assignment.
    assert!(model[0], "x0 should be true (backbone literal)");
}
