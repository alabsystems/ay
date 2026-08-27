// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the LBD-free two-stage clause management policy
//! (arXiv:2602.20829). See `solver/reduction_two_stage.rs`.

use super::*;
use crate::solver::reduction_two_stage::{two_stage_delete_permille, TWO_STAGE_DECAY_INTERVAL};

/// Add a learned clause of `len` literals starting at `first_var`, with a glue
/// deliberately set to the value that the OFF-arm policy would treat as
/// PERMANENTLY PROTECTED (LBD 1) unless overridden. Tests that want the arm to
/// be the only thing deciding pass `lbd`.
fn add_learned(solver: &mut Solver, first_var: usize, len: usize, lbd: u32) -> usize {
    let lits: Vec<_> = (0..len)
        .map(|offset| Literal::positive(Variable((first_var + offset) as u32)))
        .collect();
    let idx = solver.add_clause_db(&lits, true);
    solver.arena.set_lbd(idx, lbd);
    idx
}

fn armed_solver(num_vars: usize) -> Solver {
    let mut solver = Solver::new(num_vars);
    solver.set_two_stage_clause_management_enabled(true);
    solver
}

/// Survivor set, identified by CONTENT rather than by arena offset.
///
/// `reduce_db` ends in `compact_arena_locality()`, which relocates clauses as
/// soon as dead space passes 25% of the arena — exactly the regime these tests
/// create. A post-reduce `is_active(pre_reduce_offset)` therefore reads some
/// other clause's header, silently. Each fixture clause below owns a disjoint
/// variable range, so its lowest variable is a stable identity across
/// compaction.
fn surviving_learned_clauses(solver: &Solver) -> Vec<(u32, usize)> {
    let mut out: Vec<(u32, usize)> = solver
        .arena
        .indices()
        .filter(|&idx| solver.arena.is_active(idx) && solver.arena.is_learned(idx))
        .map(|idx| {
            let lits = solver.arena.literals(idx);
            let min_var = lits.iter().map(|l| l.variable().0).min().unwrap_or(0);
            (min_var, lits.len())
        })
        .collect();
    out.sort_unstable();
    out
}

#[test]
fn two_stage_is_default_off_and_the_switch_is_tri_state() {
    let solver = Solver::new(16);
    assert!(
        !solver.two_stage_clause_management_enabled(),
        "the two-stage policy must be default OFF"
    );
    let switches = ay_core::SatAbSwitches::default();
    assert_eq!(
        switches.two_stage_clause_management, None,
        "default switch must be None (= OFF), leaving room for an explicit false"
    );
}

/// `OnLearnedClause(c): score(c) <- 1` — and, critically, the conflict-analysis
/// learn site must NOT then overwrite it with MAX_USED.
#[test]
fn learned_clauses_start_at_score_one_not_max_used() {
    let mut solver = armed_solver(64);
    let idx = add_learned(&mut solver, 0, 8, 7);
    assert_eq!(
        solver.arena.two_stage_score(idx),
        1,
        "OnLearnedClause must set score 1, not the OFF arm's MAX_USED"
    );
    assert_eq!(
        solver.arena.used(idx),
        0,
        "armed, the score must live in its own field and leave `used` alone"
    );
    assert_eq!(solver.two_stage_clause_management_stats().learned_inits, 1);

    let mut off = Solver::new(64);
    let off_idx = add_learned(&mut off, 0, 8, 7);
    assert_eq!(
        (off.arena.used(off_idx), off.arena.two_stage_score(off_idx)),
        (0, 0),
        "with the arm off, clause creation must not touch either field"
    );
}

/// `OnClauseUse(c)` from BCP: a clause that forces a literal gains a point,
/// cumulatively, which is the signal AY had no counterpart for.
#[test]
fn bcp_forcing_increments_the_score_cumulatively() {
    let mut solver = armed_solver(64);
    let idx = add_learned(&mut solver, 0, 8, 7);
    assert_eq!(solver.arena.two_stage_score(idx), 1);

    for expected in 2..=5u16 {
        solver.two_stage_note_bcp_use(ClauseRef(idx as u32));
        assert_eq!(
            solver.arena.two_stage_score(idx),
            expected,
            "each BCP forcing must add exactly one point"
        );
    }
    assert_eq!(solver.two_stage_clause_management_stats().bcp_bumps, 4);

    // The counter must run PAST the old 5-bit ceiling: this is the whole
    // point of moving it out of `used`. 31 was reached above at bump 30.
    for _ in 0..64 {
        solver.two_stage_note_bcp_use(ClauseRef(idx as u32));
    }
    assert_eq!(
        solver.arena.two_stage_score(idx),
        69,
        "the score must not stall at MAX_USED any more"
    );
    assert_eq!(
        solver.two_stage_clause_management_stats().score_saturations,
        0,
        "nothing saturates 68 bumps into a 16-bit counter"
    );

    // Saturation at the real ceiling is still counted, not silent.
    solver
        .arena
        .set_two_stage_score(idx, crate::clause_arena::MAX_TWO_STAGE_SCORE);
    solver.two_stage_note_bcp_use(ClauseRef(idx as u32));
    assert_eq!(
        solver.arena.two_stage_score(idx),
        crate::clause_arena::MAX_TWO_STAGE_SCORE
    );
    assert_eq!(
        solver.two_stage_clause_management_stats().score_saturations,
        1,
        "saturation must be counted, not silent"
    );
}

/// With the arm off, the same BCP path must not write the score at all — this
/// is the inertness check for the hot-path hook.
#[test]
fn bcp_forcing_is_inert_with_the_arm_off() {
    let mut solver = Solver::new(64);
    let idx = add_learned(&mut solver, 0, 8, 7);
    solver.arena.set_used(idx, 3);
    solver.two_stage_note_bcp_use(ClauseRef(idx as u32));
    assert_eq!(solver.arena.used(idx), 3);
    assert_eq!(
        solver.arena.two_stage_score(idx),
        0,
        "the widened field must stay untouched on the OFF arm"
    );
    let stats = solver.two_stage_clause_management_stats();
    assert_eq!((stats.learned_inits, stats.bcp_bumps), (0, 0));
}

/// `OnPeriodicDecay()` runs on the CONFLICT clock (every 4096), not on the
/// reduction clock, and decrements by exactly one.
#[test]
fn periodic_decay_is_on_the_conflict_clock() {
    let mut solver = armed_solver(64);
    let idx = add_learned(&mut solver, 0, 8, 7);
    solver.arena.set_two_stage_score(idx, 3);

    // Not yet due.
    solver.num_conflicts = TWO_STAGE_DECAY_INTERVAL - 1;
    solver.two_stage_periodic_decay_if_due();
    assert_eq!(solver.arena.two_stage_score(idx), 3);
    assert_eq!(solver.two_stage_clause_management_stats().decay_rounds, 0);

    // Due.
    solver.num_conflicts = TWO_STAGE_DECAY_INTERVAL;
    solver.two_stage_periodic_decay_if_due();
    assert_eq!(
        solver.arena.two_stage_score(idx),
        2,
        "decay must subtract exactly one"
    );

    // Immediately re-running is not due again.
    solver.two_stage_periodic_decay_if_due();
    assert_eq!(solver.arena.two_stage_score(idx), 2);

    // One more period.
    solver.num_conflicts = 2 * TWO_STAGE_DECAY_INTERVAL;
    solver.two_stage_periodic_decay_if_due();
    assert_eq!(solver.arena.two_stage_score(idx), 1);

    // Floors at zero, never wraps.
    solver.num_conflicts = 3 * TWO_STAGE_DECAY_INTERVAL;
    solver.two_stage_periodic_decay_if_due();
    solver.num_conflicts = 4 * TWO_STAGE_DECAY_INTERVAL;
    solver.two_stage_periodic_decay_if_due();
    assert_eq!(solver.arena.two_stage_score(idx), 0);
}

/// Stage 1: a clause used since the last decay survives, whatever its LBD or
/// length. The control clause has the *better* LBD and the *shorter* body, so
/// only the score can explain the outcome.
#[test]
fn stage1_keeps_every_clause_used_since_the_last_decay() {
    let mut solver = armed_solver(256);
    // Long body, terrible glue, but used. Lowest variable 0.
    let used_long = add_learned(&mut solver, 0, 40, 90);
    solver.two_stage_note_bcp_use(ClauseRef(used_long as u32));
    // Short body, excellent glue, but score 0. Lowest variable 60.
    let unused_short = add_learned(&mut solver, 60, 30, 2);
    solver.arena.set_two_stage_score(unused_short, 0);
    // Enough score-0 filler that the stage-2 quota bites. Lowest variables
    // 100, 108, ... 156.
    for i in 0..8 {
        let idx = add_learned(&mut solver, 100 + i * 8, 6, 50);
        solver.arena.set_two_stage_score(idx, 0);
    }

    solver.reduce_db();

    let survivors = surviving_learned_clauses(&solver);
    assert!(
        survivors.contains(&(0, 40)),
        "stage 1 must keep a positive-score clause regardless of glue or length; \
         survivors {survivors:?}"
    );
    assert!(
        !survivors.iter().any(|&(v, _)| v == 60),
        "a score-0 clause is a stage-2 candidate however good its LBD is; \
         survivors {survivors:?}"
    );
    let stats = solver.two_stage_clause_management_stats();
    assert_eq!(stats.reduce_rounds, 1);
    assert_eq!(stats.stage1_kept, 1);
    assert_eq!(stats.stage2_candidates, 9);
    assert!(stats.stage2_deleted > 0);
    let histogram = stats.score_histogram;
    assert_eq!(histogram[0], 9, "nine score-0 candidates in the histogram");
    // `used_long` scored 1 on creation + 1 on the BCP use = 2, i.e. bucket 2-3.
    assert_eq!(histogram[2], 1, "one score-2 clause");
    assert_eq!(stats.score_total, 2);
    assert_eq!(stats.score_max, 2);
}

/// Stage 2: among score-0 clauses the ordering is LENGTH DESCENDING, so a
/// short clause outlives a long one. Both have identical glue, so LBD cannot be
/// what decided it.
#[test]
fn stage2_deletes_longest_first_among_zero_score_clauses() {
    let mut solver = armed_solver(512);
    let mut all_lens = Vec::new();
    // Ten clauses, lengths 4, 8, ... 40, all glue 50, all score 0.
    for i in 0..10usize {
        let len = 4 * (i + 1);
        let idx = add_learned(&mut solver, i * 45, len, 50);
        solver.arena.set_two_stage_score(idx, 0);
        all_lens.push(len);
    }

    solver.reduce_db();

    let mut surviving: Vec<usize> = surviving_learned_clauses(&solver)
        .into_iter()
        .map(|(_, len)| len)
        .collect();
    surviving.sort_unstable();
    let mut deleted = all_lens.clone();
    for len in &surviving {
        let pos = deleted.iter().position(|l| l == len).expect("survivor");
        deleted.remove(pos);
    }
    assert!(!deleted.is_empty(), "stage 2 must delete something");
    assert!(!surviving.is_empty(), "stage 2 must not delete everything");
    // Every deleted clause is at least as long as every survivor.
    let shortest_deleted = *deleted.iter().min().unwrap();
    let longest_survivor = *surviving.iter().max().unwrap();
    assert!(
        shortest_deleted >= longest_survivor,
        "stage 2 order is not length-descending: deleted {deleted:?}, kept {surviving:?}"
    );

    // The quota itself is the paper's percent at reduction round 1.
    let expected_deleted = (10.0 * (two_stage_delete_permille(1) as f64 / 1000.0)) as usize;
    assert_eq!(deleted.len(), expected_deleted);
}

/// The correctness-adjacent protections are unchanged by the arm: a reason
/// clause and an IC3 lemma are never deletion candidates even at score 0.
#[test]
fn two_stage_keeps_the_reason_and_ic3_protections() {
    let mut solver = armed_solver(256);
    let reason = add_learned(&mut solver, 0, 20, 50);
    solver.arena.set_two_stage_score(reason, 0);
    solver.enqueue(
        Literal::positive(Variable(21)),
        Some(ClauseRef(reason as u32)),
    );
    // `enqueue` counts as an OnClauseUse; reset so the protection, not the
    // score, is what is being tested.
    solver.arena.set_two_stage_score(reason, 0);
    let ic3 = add_learned(&mut solver, 40, 20, 50);
    solver.arena.set_ic3_lemma(ic3, true);
    solver.arena.set_two_stage_score(ic3, 0);
    for i in 0..8 {
        let idx = add_learned(&mut solver, 80 + i * 20, 20, 50);
        solver.arena.set_two_stage_score(idx, 0);
    }

    solver.reduce_db();

    let survivors = surviving_learned_clauses(&solver);
    assert!(
        survivors.contains(&(0, 20)),
        "reason protection must run before the two-stage decision; survivors {survivors:?}"
    );
    assert!(
        survivors.contains(&(40, 20)),
        "IC3 lemma protection must run before the two-stage decision; survivors {survivors:?}"
    );
}

/// The arm must not touch the reduction TRIGGER. Same starting state, same
/// conflict count: `next_reduce_db` lands on the same value either way.
#[test]
fn two_stage_leaves_the_reduction_trigger_schedule_alone() {
    let schedule = |armed: bool| -> Vec<u64> {
        let mut solver = Solver::new(256);
        solver.set_two_stage_clause_management_enabled(armed);
        for i in 0..8 {
            let idx = add_learned(&mut solver, i * 20, 20, 50);
            solver.arena.set_used(idx, 0);
            solver.arena.set_two_stage_score(idx, 0);
        }
        let mut out = Vec::new();
        for round in 0..6u64 {
            solver.num_conflicts = 10_000 * (round + 1);
            solver.reduce_db();
            out.push(solver.cold.next_reduce_db - solver.num_conflicts);
        }
        out
    };
    assert_eq!(
        schedule(true),
        schedule(false),
        "the two-stage arm must change ranking and keep/delete only, never the trigger"
    );
}

/// A due flush is absorbed into the two-stage path rather than taking the
/// aggressive tier-based flush branch — and the flush schedule still advances,
/// so `flushing()` cannot latch true forever.
///
/// NOTE the fixture has to install a FINITE flush schedule by hand. AY ships
/// `FLUSH_INIT = u64::MAX` (`solver/constants.rs`, "Disabled to match CaDiCaL's
/// default"), so on the shipped configuration the aggressive flush branch never
/// runs at all and `two_stage_flushes_absorbed` stays 0 on real instances. This
/// test covers the interaction, not a hot path.
#[test]
fn due_flush_is_absorbed_and_still_advances_its_schedule() {
    let mut solver = armed_solver(256);
    for i in 0..8 {
        let idx = add_learned(&mut solver, i * 20, 20, 50);
        solver.arena.set_two_stage_score(idx, 0);
    }
    solver.cold.flush_inc = 1_000;
    solver.cold.next_flush = 5_000;
    solver.num_conflicts = 5_000;

    solver.reduce_db();

    assert_eq!(
        solver.cold.next_flush, 8_000,
        "the flush schedule must advance (5000 + 3*1000) even when the flush path is skipped"
    );
    let stats = solver.two_stage_clause_management_stats();
    assert_eq!(stats.reduce_rounds, 1, "the two-stage path must have run");
    assert_eq!(
        stats.flushes_absorbed, 1,
        "the due flush must be attributed"
    );

    // Control: with the arm off, the same state takes the real flush branch.
    let mut off = Solver::new(256);
    for i in 0..8 {
        let idx = add_learned(&mut off, i * 20, 20, 50);
        off.arena.set_used(idx, 0);
    }
    off.cold.flush_inc = 1_000;
    off.cold.next_flush = 5_000;
    off.num_conflicts = 5_000;
    off.reduce_db();
    assert_eq!(off.cold.next_flush, 8_000);
    assert_eq!(off.two_stage_clause_management_stats().flushes_absorbed, 0);
}

/// Reachability: with the arm off, every two-stage counter is zero after a
/// reduction. A non-zero counter can only come from the new code.
#[test]
fn every_two_stage_counter_is_zero_with_the_arm_off() {
    let mut solver = Solver::new(256);
    for i in 0..12 {
        let idx = add_learned(&mut solver, i * 20, 20, 50);
        solver.arena.set_used(idx, 0);
    }
    solver.reduce_db();
    assert_eq!(
        solver.two_stage_clause_management_stats(),
        solver_stats::TwoStageClauseStats::default(),
        "the OFF arm must not be able to emit two-stage telemetry"
    );
}
