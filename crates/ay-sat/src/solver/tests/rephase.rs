// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for CaDiCaL-matched rephase schedules.
//!
//! Verifies that stable and focused mode schedules match CaDiCaL's
//! `rephase.cpp` cycle orders for both walk-enabled and walk-disabled modes.
//!
//! Reference: CaDiCaL `rephase.cpp:263-367`.

use super::*;

/// Classify which rephase operation was applied by inspecting phase state.
///
/// Call this after each `apply_{stable,focused}_rephase_schedule` to identify
/// what type of rephase was performed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RephaseType {
    Original, // O: all phases = 1
    Inverted, // I: all phases = -1
    Best,     // B: phases copied from best_phase
    Random,   // #: phases are pseudo-random
    Flip,     // F: phases negated
    Walk,     // W: walk was invoked (walk_enabled must be true)
}

/// Determine the rephase type by observing the phase array after rephasing.
///
/// Uses a 4-variable solver. Before each rephase call we set known phase state,
/// then inspect the result.
fn classify_rephase_stable(solver: &mut Solver, count: u64) -> (RephaseType, bool) {
    // Disable flip search so Flip slots use simple negation (detectable by tests).
    // Flip search is tested separately in flip::tests.
    solver.cold.flip_search_enabled = false;
    // Set a known "pre" state so we can detect changes.
    // Alternate: [1, -1, 1, -1]
    solver.phase[0] = 1;
    solver.phase[1] = -1;
    solver.phase[2] = 1;
    solver.phase[3] = -1;

    // Set best_phase to a distinctive pattern: [1, 1, -1, -1]
    solver.best_phase[0] = 1;
    solver.best_phase[1] = 1;
    solver.best_phase[2] = -1;
    solver.best_phase[3] = -1;

    let is_best = solver.apply_stable_rephase_schedule(count);

    let p: Vec<i8> = solver.phase[0..4].to_vec();

    let rtype = if p == vec![1, 1, 1, 1] {
        RephaseType::Original
    } else if p == vec![-1, -1, -1, -1] {
        RephaseType::Inverted
    } else if p == vec![1, 1, -1, -1] {
        RephaseType::Best
    } else if p == vec![-1, 1, -1, 1] {
        RephaseType::Flip
    } else {
        // Walk returns early (no-op or actual walk). If walk_enabled but we get
        // the same pre-state back, it's Walk (no-op because no clauses).
        // Random produces pseudo-random values.
        if solver.phase_init.walk_enabled && p == vec![1, -1, 1, -1] {
            // Walk was called but had no effect (no clauses to walk over).
            RephaseType::Walk
        } else {
            RephaseType::Random
        }
    };

    (rtype, is_best)
}

fn classify_rephase_focused(solver: &mut Solver, count: u64) -> (RephaseType, bool) {
    // Disable flip search so Flip slots use simple negation (detectable by tests).
    solver.cold.flip_search_enabled = false;
    solver.phase[0] = 1;
    solver.phase[1] = -1;
    solver.phase[2] = 1;
    solver.phase[3] = -1;

    solver.best_phase[0] = 1;
    solver.best_phase[1] = 1;
    solver.best_phase[2] = -1;
    solver.best_phase[3] = -1;

    let is_best = solver.apply_focused_rephase_schedule(count);

    let p: Vec<i8> = solver.phase[0..4].to_vec();

    let rtype = if p == vec![1, 1, 1, 1] {
        RephaseType::Original
    } else if p == vec![-1, -1, -1, -1] {
        RephaseType::Inverted
    } else if p == vec![1, 1, -1, -1] {
        RephaseType::Best
    } else if p == vec![-1, 1, -1, 1] {
        RephaseType::Flip
    } else if solver.phase_init.walk_enabled && p == vec![1, -1, 1, -1] {
        RephaseType::Walk
    } else {
        RephaseType::Random
    };

    (rtype, is_best)
}

#[test]
fn test_rephase_attribution_records_strategy_mode_and_effects() {
    let mut solver = Solver::new(4);
    solver.set_walk_enabled(false);
    solver.stable_mode = true;
    solver.num_conflicts = 1_000;
    solver.cold.next_rephase = 1_000;
    solver.phase[0] = 1;
    solver.phase[1] = -1;
    solver.phase[2] = 0;
    solver.phase[3] = 1;

    solver.rephase();

    let stats = solver.rephase_attribution_stats();
    assert_eq!(stats.original, 1);
    assert_eq!(stats.stable_mode, 1);
    assert_eq!(stats.focused_mode, 0);
    assert_eq!(stats.direct_changed_phases, 2);
    assert_eq!(stats.target_phase_updates, 4);
    assert_eq!(stats.best_resets, 0);
}

#[test]
fn test_stable_only_rephase_gate_skips_focused_mode() {
    let mut solver = Solver::new(4);
    solver.num_conflicts = 1_000;
    solver.cold.next_rephase = 1_000;
    solver.stable_mode = false;

    assert!(
        solver.should_rephase(),
        "default rephase scheduling still fires in focused mode"
    );
    assert!(!solver.stable_only_rephase_enabled());

    solver.set_stable_only_rephase_enabled(true);
    assert!(
        !solver.should_rephase(),
        "stable-only rephase must skip focused mode"
    );

    solver.stable_mode = true;
    assert!(
        solver.should_rephase(),
        "stable-only rephase must fire after stable mode begins"
    );

    solver.cold.rephase_enabled = false;
    assert!(
        !solver.should_rephase(),
        "the stable-only gate must not override global rephase disablement"
    );
}

#[test]
fn test_rephase_attribution_records_direct_schedule_helper_calls() {
    let mut solver = Solver::new(4);
    solver.set_walk_enabled(false);
    solver.phase[0] = 1;
    solver.phase[1] = -1;
    solver.phase[2] = 1;
    solver.phase[3] = -1;
    solver.best_phase[0] = 1;
    solver.best_phase[1] = 1;
    solver.best_phase[2] = -1;
    solver.best_phase[3] = -1;

    assert!(solver.apply_stable_rephase_schedule(2));

    let stats = solver.rephase_attribution_stats();
    assert_eq!(stats.best, 1);
    assert_eq!(stats.direct_changed_phases, 2);
}

#[test]
fn test_best_rephase_uses_target_phase_for_missing_best_phase() {
    let mut solver = Solver::new(4);
    solver.set_walk_enabled(false);
    solver.phase[0] = 1;
    solver.phase[1] = 1;
    solver.phase[2] = 1;
    solver.phase[3] = 1;

    solver.best_phase[0] = -1;
    solver.best_phase[1] = 0;
    solver.best_phase[2] = 0;
    solver.best_phase[3] = 1;

    solver.target_phase[0] = 1;
    solver.target_phase[1] = -1;
    solver.target_phase[2] = -1;
    solver.target_phase[3] = -1;

    assert!(solver.apply_stable_rephase_schedule(2));

    assert_eq!(&solver.phase[0..4], &[-1, -1, -1, 1]);
    let stats = solver.rephase_attribution_stats();
    assert_eq!(stats.best, 1);
    assert_eq!(stats.direct_changed_phases, 3);
}

mod mode_schedules;
// ========================================================================
// Full Sequence Trace Tests
// ========================================================================

/// Verify the full expanded sequence for stable+walk matches CaDiCaL
/// `rephase.cpp:287-316` line by line.
///
/// CaDiCaL code (line 288-316):
///   count==0 -> rephase_original()     [line 290]
///   count==1 -> rephase_inverted()     [line 292]
///   (count-2)%6==0 -> rephase_best()   [line 296]
///   (count-2)%6==1 -> rephase_walk()   [line 299]
///   (count-2)%6==2 -> rephase_original() [line 302]
///   (count-2)%6==3 -> rephase_best()   [line 305]
///   (count-2)%6==4 -> rephase_walk()   [line 308]
///   (count-2)%6==5 -> rephase_inverted() [line 311]
#[test]
fn test_stable_walk_full_sequence_trace() {
    let mut solver = Solver::new(4);
    solver.set_walk_enabled(true);

    // Expected full sequence for counts 0..20:
    // O I B W O B W I B W O B W I B W O B W I
    let expected: Vec<RephaseType> = vec![
        RephaseType::Original, // 0
        RephaseType::Inverted, // 1
        RephaseType::Best,     // 2: (0)%6=0 -> B
        RephaseType::Walk,     // 3: (1)%6=1 -> W
        RephaseType::Original, // 4: (2)%6=2 -> O
        RephaseType::Best,     // 5: (3)%6=3 -> B
        RephaseType::Walk,     // 6: (4)%6=4 -> W
        RephaseType::Inverted, // 7: (5)%6=5 -> I
        RephaseType::Best,     // 8: (6)%6=0 -> B
        RephaseType::Walk,     // 9: (7)%6=1 -> W
        RephaseType::Original, // 10: (8)%6=2 -> O
        RephaseType::Best,     // 11: (9)%6=3 -> B
        RephaseType::Walk,     // 12: (10)%6=4 -> W
        RephaseType::Inverted, // 13: (11)%6=5 -> I
        RephaseType::Best,     // 14: (12)%6=0 -> B
        RephaseType::Walk,     // 15: (13)%6=1 -> W
        RephaseType::Original, // 16: (14)%6=2 -> O
        RephaseType::Best,     // 17: (15)%6=3 -> B
        RephaseType::Walk,     // 18: (16)%6=4 -> W
        RephaseType::Inverted, // 19: (17)%6=5 -> I
    ];

    for (count, &exp) in expected.iter().enumerate() {
        let (rtype, _) = classify_rephase_stable(&mut solver, count as u64);
        assert_eq!(
            rtype, exp,
            "stable+walk count={count}: expected {exp:?}, got {rtype:?}"
        );
    }
}

/// Verify focused+walk matches CaDiCaL `rephase.cpp:339-367`.
///
/// CaDiCaL code (line 340-367):
///   count==0 -> rephase_original()      [line 344] (NB: comment says "flipping")
///   (count-1)%6==0 -> rephase_random()  [line 346]
///   (count-1)%6==1 -> rephase_best()    [line 349]
///   (count-1)%6==2 -> rephase_walk()    [line 352]
///   (count-1)%6==3 -> rephase_flipping() [line 355]
///   (count-1)%6==4 -> rephase_best()    [line 358]
///   (count-1)%6==5 -> rephase_walk()    [line 361]
#[test]
fn test_focused_walk_full_sequence_trace() {
    let mut solver = Solver::new(4);
    solver.set_walk_enabled(true);

    // Expected full sequence for counts 0..19:
    // O # B W F B W # B W F B W # B W F B W
    let expected: Vec<RephaseType> = vec![
        RephaseType::Original, // 0
        RephaseType::Random,   // 1: (0)%6=0 -> #
        RephaseType::Best,     // 2: (1)%6=1 -> B
        RephaseType::Walk,     // 3: (2)%6=2 -> W
        RephaseType::Flip,     // 4: (3)%6=3 -> F
        RephaseType::Best,     // 5: (4)%6=4 -> B
        RephaseType::Walk,     // 6: (5)%6=5 -> W
        RephaseType::Random,   // 7: (6)%6=0 -> #
        RephaseType::Best,     // 8: (7)%6=1 -> B
        RephaseType::Walk,     // 9: (8)%6=2 -> W
        RephaseType::Flip,     // 10: (9)%6=3 -> F
        RephaseType::Best,     // 11: (10)%6=4 -> B
        RephaseType::Walk,     // 12: (11)%6=5 -> W
        RephaseType::Random,   // 13: (12)%6=0 -> #
        RephaseType::Best,     // 14: (13)%6=1 -> B
        RephaseType::Walk,     // 15: (14)%6=2 -> W
        RephaseType::Flip,     // 16: (15)%6=3 -> F
        RephaseType::Best,     // 17: (16)%6=4 -> B
        RephaseType::Walk,     // 18: (17)%6=5 -> W
    ];

    for (count, &exp) in expected.iter().enumerate() {
        let (rtype, _) = classify_rephase_focused(&mut solver, count as u64);
        assert_eq!(
            rtype, exp,
            "focused+walk count={count}: expected {exp:?}, got {rtype:?}"
        );
    }
}

/// Verify focused+nowalk matches CaDiCaL `rephase.cpp:317-338`.
///
/// CaDiCaL code (line 317-338):
///   count==0 -> rephase_flipping()      [line 320]
///   (count-1)%4==0 -> rephase_random()  [line 323]
///   (count-1)%4==1 -> rephase_best()    [line 326]
///   (count-1)%4==2 -> rephase_flipping() [line 329]
///   (count-1)%4==3 -> rephase_best()    [line 332]
#[test]
fn test_focused_nowalk_full_sequence_trace() {
    let mut solver = Solver::new(4);
    solver.set_walk_enabled(false);

    // Expected: F # B F B # B F B # B F B
    let expected: Vec<RephaseType> = vec![
        RephaseType::Flip,   // 0
        RephaseType::Random, // 1: (0)%4=0 -> #
        RephaseType::Best,   // 2: (1)%4=1 -> B
        RephaseType::Flip,   // 3: (2)%4=2 -> F
        RephaseType::Best,   // 4: (3)%4=3 -> B
        RephaseType::Random, // 5: (4)%4=0 -> #
        RephaseType::Best,   // 6: (5)%4=1 -> B
        RephaseType::Flip,   // 7: (6)%4=2 -> F
        RephaseType::Best,   // 8: (7)%4=3 -> B
        RephaseType::Random, // 9: (8)%4=0 -> #
        RephaseType::Best,   // 10: (9)%4=1 -> B
        RephaseType::Flip,   // 11: (10)%4=2 -> F
        RephaseType::Best,   // 12: (11)%4=3 -> B
    ];

    for (count, &exp) in expected.iter().enumerate() {
        let (rtype, _) = classify_rephase_focused(&mut solver, count as u64);
        assert_eq!(
            rtype, exp,
            "focused-nowalk count={count}: expected {exp:?}, got {rtype:?}"
        );
    }
}

/// Verify stable+nowalk matches CaDiCaL `rephase.cpp:263-286`.
///
/// CaDiCaL code (line 263-286):
///   count==0 -> rephase_original()      [line 266]
///   count==1 -> rephase_inverted()      [line 268]
///   (count-2)%4==0 -> rephase_best()    [line 271]
///   (count-2)%4==1 -> rephase_original() [line 274]
///   (count-2)%4==2 -> rephase_best()    [line 277]
///   (count-2)%4==3 -> rephase_inverted() [line 280]
#[test]
fn test_stable_nowalk_full_sequence_trace() {
    let mut solver = Solver::new(4);
    solver.set_walk_enabled(false);

    // Expected: O I B O B I B O B I B O B I
    let expected: Vec<RephaseType> = vec![
        RephaseType::Original, // 0
        RephaseType::Inverted, // 1
        RephaseType::Best,     // 2: (0)%4=0 -> B
        RephaseType::Original, // 3: (1)%4=1 -> O
        RephaseType::Best,     // 4: (2)%4=2 -> B
        RephaseType::Inverted, // 5: (3)%4=3 -> I
        RephaseType::Best,     // 6: (4)%4=0 -> B
        RephaseType::Original, // 7: (5)%4=1 -> O
        RephaseType::Best,     // 8: (6)%4=2 -> B
        RephaseType::Inverted, // 9: (7)%4=3 -> I
        RephaseType::Best,     // 10: (8)%4=0 -> B
        RephaseType::Original, // 11: (9)%4=1 -> O
        RephaseType::Best,     // 12: (10)%4=2 -> B
        RephaseType::Inverted, // 13: (11)%4=3 -> I
    ];

    for (count, &exp) in expected.iter().enumerate() {
        let (rtype, _) = classify_rephase_stable(&mut solver, count as u64);
        assert_eq!(
            rtype, exp,
            "stable-nowalk count={count}: expected {exp:?}, got {rtype:?}"
        );
    }
}

/// Verify that `is_best` return value is true only for Best rephases.
/// This controls `best_trail_len` reset in the caller (matching CaDiCaL
/// `backtrack.cpp:55-56` where `best_assigned = 0` only on 'B' rephase).
#[test]
fn test_is_best_return_value_correctness() {
    let mut solver = Solver::new(4);
    solver.set_walk_enabled(true);

    // Stable+walk: O I B W O B W I ...
    // is_best should be true only at positions 2, 5, 8, 11, ...
    for count in 0..20u64 {
        let (rtype, is_best) = classify_rephase_stable(&mut solver, count);
        assert_eq!(
            is_best,
            rtype == RephaseType::Best,
            "stable+walk count={count}: is_best={is_best} but rtype={rtype:?}"
        );
    }

    // Focused+walk: O # B W F B W ...
    for count in 0..20u64 {
        let (rtype, is_best) = classify_rephase_focused(&mut solver, count);
        assert_eq!(
            is_best,
            rtype == RephaseType::Best,
            "focused+walk count={count}: is_best={is_best} but rtype={rtype:?}"
        );
    }
}

// ========================================================================
// NLOG3N Scheduling Function
// ========================================================================

/// Verify the NLOG3N scaling function produces expected values.
#[test]
fn test_nlog3n_basic() {
    use super::super::rephase::nlog3n;
    // nlog3n(0) = 1 (special case)
    assert_eq!(nlog3n(0), 1);

    // nlog3n(1) = 1 * log10(10)^3 = 1 * 1^3 = 1
    assert_eq!(nlog3n(1), 1);

    // nlog3n(10) = 10 * log10(19)^3 ~= 10 * 1.279^3 ~= 10 * 2.093 ~= 20
    let v10 = nlog3n(10);
    assert!((18..=24).contains(&v10), "nlog3n(10) = {v10}, expected ~20");

    // Monotonically increasing for n > 0
    let mut prev = nlog3n(1);
    for n in 2..100u64 {
        let cur = nlog3n(n);
        assert!(
            cur >= prev,
            "nlog3n not monotonic: nlog3n({}) = {} < nlog3n({}) = {}",
            n,
            cur,
            n - 1,
            prev
        );
        prev = cur;
    }
}
