// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the ProbSAT local search walker.

use super::*;

#[test]
fn test_random() {
    let mut rng = Random::new(42);
    assert_ne!(rng.next(), rng.next());
    for _ in 0..100 {
        assert!(rng.pick(10) < 10);
    }
}

#[test]
fn test_fit_cb_value() {
    assert!((fit_cb_value(3.0) - 2.50).abs() < 0.01);
    assert!((fit_cb_value(5.0) - 3.70).abs() < 0.01);
    let cb4 = fit_cb_value(4.0);
    assert!(cb4 > 2.50 && cb4 < 3.70);
}

/// CB clamping for large clause sizes (#8360).
/// Without clamping, fit_cb_value extrapolates linearly beyond the table,
/// producing extreme CB values (e.g., CB=27 for avg_size=15.5) that make
/// ProbSAT degenerate into a greedy walk unable to escape local minima.
/// Clamped to the last table entry (7.40) for sizes >= 7.0.
#[test]
fn test_fit_cb_value_clamped_for_large_sizes() {
    // At the table boundary: exact last value
    assert!((fit_cb_value(7.0) - 7.40).abs() < 0.01);
    // Beyond the table: clamped to 7.40 (not extrapolated to 26.95)
    assert!((fit_cb_value(15.5) - 7.40).abs() < 0.01);
    assert!((fit_cb_value(100.0) - 7.40).abs() < 0.01);
    // Below the table: clamped to first value (2.0)
    assert!((fit_cb_value(0.0) - 2.00).abs() < 0.01);
    assert!((fit_cb_value(-1.0) - 2.00).abs() < 0.01);
}

#[test]
fn test_walker_score_table() {
    let mut walker = Walker::new(10, 100, 42, 1000);
    walker.populate_table(3.0, 0);
    assert!(walker.score(0) > walker.score(1));
    assert!(walker.score(1) > walker.score(2));
}

#[test]
fn test_broken_list_operations() {
    let mut walker = Walker::new(10, 100, 42, 1000);
    walker.add_broken(5);
    walker.add_broken(10);
    walker.add_broken(3);
    assert_eq!(walker.broken.len(), 3);
    assert!(walker.broken_pos[5] >= 0);
    assert!(walker.broken_pos[10] >= 0);
    walker.add_broken(5); // duplicate should not increase count
    assert_eq!(walker.broken.len(), 3);
}

fn lit(v: u32, pos: bool) -> Literal {
    if pos {
        Literal::positive(crate::literal::Variable(v))
    } else {
        Literal::negative(crate::literal::Variable(v))
    }
}

#[test]
fn test_walk_filter_irredundant_only() {
    let filter = WalkFilter::irredundant_only();
    let mut db = ClauseArena::new();
    let idx0 = db.add(&[lit(0, true), lit(1, true)], false);
    let idx1 = db.add(&[lit(2, true), lit(3, true)], true);
    db.set_lbd(idx1, 2);
    db.set_used(idx1, 1);
    assert!(filter.should_include(&db, idx0), "irredundant included");
    assert!(!filter.should_include(&db, idx1), "learned excluded");
}

#[test]
fn test_walk_filter_likely_kept() {
    let filter = WalkFilter {
        include_likely_kept: true,
        tier2_lbd: 6,
    };
    let mut db = ClauseArena::new();
    // Irredundant: always included
    let idx0 = db.add(&[lit(0, true), lit(1, true)], false);
    assert!(filter.should_include(&db, idx0));
    // Core (lbd=2 ≤ tier2=6): included
    let idx1 = db.add(&[lit(2, true), lit(3, true)], true);
    db.set_lbd(idx1, 2);
    assert!(filter.should_include(&db, idx1), "core included");
    // Tier-1 (lbd=5 ≤ tier2=6) with used>0: included
    let idx2 = db.add(&[lit(4, true), lit(5, true)], true);
    db.set_lbd(idx2, 5);
    db.set_used(idx2, 1);
    assert!(filter.should_include(&db, idx2), "tier-1 used>0 included");
    // Tier-1 (lbd=5 ≤ tier2=6) with used=0: ALSO included (CaDiCaL
    // likely_to_be_kept_clause has no `used` check, only glue <= tier2)
    let idx3 = db.add(&[lit(6, true), lit(7, true)], true);
    db.set_lbd(idx3, 5);
    db.set_used(idx3, 0);
    assert!(
        filter.should_include(&db, idx3),
        "tier-1 used=0 also included"
    );
    // Beyond tier2 (lbd=10 > tier2=6): excluded
    let idx4 = db.add(&[lit(8, true), lit(9, true)], true);
    db.set_lbd(idx4, 10);
    db.set_used(idx4, 5);
    assert!(!filter.should_include(&db, idx4), "beyond tier2 excluded");
}

#[test]
fn test_compute_walk_effort_scaling() {
    // Zero delta: returns minimum floor (WALK_MIN_EFFORT = 10_000_000).
    // Ensures rephase walks always have meaningful budget even with
    // small search tick deltas. Matches Kissat's mineffort floor concept.
    assert_eq!(compute_walk_effort(0), WALK_MIN_EFFORT);

    // Small delta: proportional < minimum, returns minimum floor
    let small_raw = 100 * WALK_EFFORT_PER_MILLE / 1000; // = 5
    assert!(small_raw < WALK_MIN_EFFORT);
    assert_eq!(compute_walk_effort(100), WALK_MIN_EFFORT);

    // Medium delta: proportional (500K) < minimum (10M), returns minimum
    let medium_effort = compute_walk_effort(10_000_000);
    assert_eq!(medium_effort, WALK_MIN_EFFORT);

    // Normal delta: proportional scaling exceeds minimum
    // 1B * 50/1000 = 50M > 10M min
    let effort = compute_walk_effort(1_000_000_000);
    assert_eq!(effort, 1_000_000_000 * WALK_EFFORT_PER_MILLE / 1000);
    assert!(effort > WALK_MIN_EFFORT);

    // Large delta: clamps to maximum
    let huge_effort = compute_walk_effort(u64::MAX / 2);
    assert!(huge_effort <= WALK_MAX_EFFORT * 1000);
}

#[test]
fn test_lazy_best_model_tracking() {
    let mut walker = Walker::new(10, 0, 42, 1000);

    // Initialize values and best_values
    for i in 0..10 {
        walker.values[i] = i % 2 == 0;
        walker.best_values[i] = walker.values[i];
    }

    // Record initial minimum
    walker.minimum = 5;
    walker.save_minimum(10);
    assert_eq!(walker.best_trail_pos, 0);

    // Simulate some flips
    walker.values[0] = !walker.values[0]; // flip var 0
    walker.push_flipped(0);
    walker.values[3] = !walker.values[3]; // flip var 3
    walker.push_flipped(3);

    // Record a new minimum
    walker.minimum = 3;
    walker.save_minimum(10);
    assert_eq!(walker.best_trail_pos, 2); // position after flips 0 and 3

    // More flips after best
    walker.values[5] = !walker.values[5];
    walker.push_flipped(5);

    // Finalize — should apply flips 0 and 3 to best_values
    walker.save_final_minimum();

    // best_values should reflect flips of vars 0 and 3 from initial
    assert!(!walker.best_values[0]); // was true (0%2==0), flipped to false
    assert!(walker.best_values[3]); // was false (3%2==1), flipped to true
    assert!(!walker.best_values[5]); // var 5 was flipped AFTER best, so unchanged
}

/// #5060 AC-4: Walk trail overflow via `push_flipped` at trail_limit.
/// When `flips_trail.len() >= trail_limit` and `best_trail_pos > 0`,
/// `push_flipped` calls `save_trail_prefix(true)` to flush the best
/// prefix into `best_values` and shift remaining flips to the front.
#[test]
fn test_walk_trail_overflow_flushes_best_prefix() {
    // Use 8 vars → trail_limit = 8/4 + 1 = 3
    let mut walker = Walker::new(8, 0, 42, 1000);

    // Initialize values and best_values
    for i in 0..8 {
        walker.values[i] = i % 2 == 0; // 0:T, 1:F, 2:T, 3:F, 4:T, 5:F, 6:T, 7:F
        walker.best_values[i] = walker.values[i];
    }

    // Record initial minimum (sets best_trail_pos = 0)
    walker.minimum = 5;
    walker.save_minimum(8);
    assert_eq!(
        walker.best_trail_pos, 0,
        "initial: best_trail_pos should be 0"
    );

    // Push 2 flips (within limit of 3)
    walker.values[0] = !walker.values[0]; // flip var 0: T→F
    walker.push_flipped(0);
    walker.values[1] = !walker.values[1]; // flip var 1: F→T
    walker.push_flipped(1);
    assert_eq!(walker.flips_trail.len(), 2);

    // Record a new minimum at position 2
    walker.minimum = 3;
    walker.save_minimum(8);
    assert_eq!(
        walker.best_trail_pos, 2,
        "best_trail_pos should be at current trail len"
    );

    // Push a 3rd flip (hits trail_limit of 3)
    walker.values[2] = !walker.values[2]; // flip var 2: T→F
    walker.push_flipped(2);
    assert_eq!(walker.flips_trail.len(), 3, "3rd push within limit");

    // Push a 4th flip — triggers overflow:
    // best_trail_pos=2 > 0, so save_trail_prefix(true) is called:
    //   - Applies flips[0..2] (var 0, var 1) to best_values
    //   - Shifts remaining [var 2] to front
    //   - Resets best_trail_pos to 0
    //   - Then pushes var 3
    walker.values[3] = !walker.values[3]; // flip var 3: F→T
    walker.push_flipped(3);

    // After overflow:
    // best_values should have flips 0 and 1 applied (from the flushed prefix)
    assert!(
        !walker.best_values[0],
        "var 0: was T, flipped → F in best_values"
    );
    assert!(
        walker.best_values[1],
        "var 1: was F, flipped → T in best_values"
    );
    // var 2 was NOT in the prefix [0..2), so best_values[2] unchanged
    assert!(
        walker.best_values[2],
        "var 2: not in flushed prefix, stays T"
    );

    // Trail should contain shifted remainder [var 2] + new [var 3]
    assert_eq!(walker.flips_trail.len(), 2, "shifted remainder + new push");
    assert_eq!(walker.flips_trail[0], 2, "shifted: var 2");
    assert_eq!(walker.flips_trail[1], 3, "new push: var 3");
    assert_eq!(
        walker.best_trail_pos, 0,
        "best_trail_pos reset to 0 after flush"
    );
}

/// #5060: Walk trail overflow with best_trail_pos==0 invalidates the trail.
/// When `flips_trail.len() >= trail_limit` and `best_trail_pos == 0`
/// (no new minimum since last flush), the trail is cleared and invalidated.
#[test]
fn test_walk_trail_overflow_invalidates_when_no_best() {
    // 8 vars → trail_limit = 3
    let mut walker = Walker::new(8, 0, 42, 1000);

    for i in 0..8 {
        walker.values[i] = i % 2 == 0;
        walker.best_values[i] = walker.values[i];
    }

    // Record initial minimum (best_trail_pos = 0)
    walker.minimum = 5;
    walker.save_minimum(8);
    assert_eq!(walker.best_trail_pos, 0);

    // Fill trail to limit without recording any new minimum
    walker.push_flipped(0);
    walker.push_flipped(1);
    walker.push_flipped(2);
    assert_eq!(walker.flips_trail.len(), 3);

    // best_trail_pos is still 0 (no save_minimum called since initial)
    assert_eq!(walker.best_trail_pos, 0);

    // Push one more — triggers overflow with best_trail_pos==0:
    // Trail is cleared and invalidated (best_trail_pos = -1)
    walker.push_flipped(3);

    assert_eq!(walker.best_trail_pos, -1, "trail should be invalidated");
    assert!(walker.flips_trail.is_empty(), "trail should be cleared");

    // Subsequent pushes are no-ops (best_trail_pos < 0 guard)
    walker.push_flipped(4);
    assert!(
        walker.flips_trail.is_empty(),
        "push after invalidation is no-op"
    );
}
