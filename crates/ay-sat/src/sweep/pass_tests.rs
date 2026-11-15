// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sweep passes under `charge_all_work`: a variable is swept once per pass
//! and a pass completes when the last candidate has been swept.

use super::*;
use crate::test_util::lit;

fn arena() -> ClauseArena {
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, true), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(2, true)], false);
    clauses.add(&[lit(2, true), lit(3, true)], false);
    clauses.add(&[lit(1, false), lit(3, false)], false);
    clauses.add(&[lit(3, true), lit(0, true), lit(2, false)], false);
    clauses
}

/// An unbounded budget sweeps every candidate and completes a pass; the next
/// sweep is a new pass and sweeps them all again.
#[test]
fn a_complete_pass_is_counted_and_the_next_sweep_starts_over() {
    let clauses = arena();
    let vals = vec![0i8; 8];
    let frozen: Vec<u32> = vec![0; 4];
    let mut sweeper = Sweeper::new(4);
    sweeper.set_charge_all_work(true);
    let _ = sweeper.sweep_with_kitten(&clauses, &vals, &frozen, u64::MAX);
    assert_eq!(sweeper.stats.completed_passes, 1);
    let swept_first = sweeper.stats.kitten_environments;
    assert!(swept_first >= 1);
    assert!(sweeper.swept_in_pass.iter().all(|&p| p == 1));
    let _ = sweeper.sweep_with_kitten(&clauses, &vals, &frozen, u64::MAX);
    assert_eq!(sweeper.stats.completed_passes, 2);
    assert_eq!(sweeper.stats.kitten_environments, 2 * swept_first);
}

/// A budget of one tick stops after the first environment; the next sweep
/// skips that variable and sweeps the next one, and no pass completes.
#[test]
fn a_cut_pass_resumes_with_the_unswept_variables() {
    let clauses = arena();
    let vals = vec![0i8; 8];
    let frozen: Vec<u32> = vec![0; 4];
    let mut sweeper = Sweeper::new(4);
    sweeper.set_charge_all_work(true);
    let _ = sweeper.sweep_with_kitten(&clauses, &vals, &frozen, 1);
    assert_eq!(sweeper.stats.completed_passes, 0);
    assert_eq!(sweeper.swept_in_pass, vec![1, 0, 0, 0]);
    let _ = sweeper.sweep_with_kitten(&clauses, &vals, &frozen, 1);
    assert_eq!(sweeper.stats.completed_passes, 0);
    assert_eq!(sweeper.swept_in_pass, vec![1, 1, 0, 0]);
}

/// Without the flag the sweep behaves as before: nothing is marked and no pass
/// is counted.
#[test]
fn without_the_flag_nothing_is_marked() {
    let clauses = arena();
    let vals = vec![0i8; 8];
    let frozen: Vec<u32> = vec![0; 4];
    let mut sweeper = Sweeper::new(4);
    let _ = sweeper.sweep_with_kitten(&clauses, &vals, &frozen, u64::MAX);
    assert_eq!(sweeper.stats.completed_passes, 0);
    assert!(sweeper.swept_in_pass.iter().all(|&p| p == 1));
}

/// The marks survive an engine re-creation (an arena compaction) through
/// `take_pass_state` / `restore_pass_state`, remapped: with variable 1 gone
/// the swept variables 0 and 2 keep their marks at their new indices, and
/// the pass number is kept.
#[test]
fn pass_marks_carry_across_a_compaction_remap() {
    let clauses = arena();
    let vals = vec![0i8; 8];
    let frozen: Vec<u32> = vec![0; 4];
    let mut sweeper = Sweeper::new(4);
    sweeper.set_charge_all_work(true);
    let _ = sweeper.sweep_with_kitten(&clauses, &vals, &frozen, 1);
    let _ = sweeper.sweep_with_kitten(&clauses, &vals, &frozen, 1);
    assert_eq!(sweeper.swept_in_pass, vec![1, 1, 0, 0]);
    sweeper.sweep_pass = 7;
    let (marks, pass) = sweeper.take_pass_state();
    assert_eq!(pass, 7);
    // Compaction drops variable 1: old 0 -> new 0, old 2 -> new 1, old 3 -> new 2.
    let remapped = vec![marks[0], marks[2], marks[3]];
    let mut fresh = Sweeper::new(3);
    fresh.restore_pass_state(remapped, pass);
    assert_eq!(fresh.swept_in_pass, vec![1, 0, 0]);
    assert_eq!(fresh.sweep_pass, 7);
    // A short vector is padded with unswept entries; pass 0 becomes 1.
    let mut padded = Sweeper::new(3);
    padded.restore_pass_state(vec![7], 0);
    assert_eq!(padded.swept_in_pass, vec![7, 0, 0]);
    assert_eq!(padded.sweep_pass, 1);
}
