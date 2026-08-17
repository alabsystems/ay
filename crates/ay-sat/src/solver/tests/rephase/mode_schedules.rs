// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Stable and focused rephase-mode schedule regressions.

use super::*;

// ========================================================================
// Stable Mode Schedules
// ========================================================================

/// CaDiCaL `rephase.cpp:287-316`: stable mode with walk enabled.
/// Expected: O, I, (B, W, O, B, W, I)^w
#[test]
fn test_stable_rephase_schedule_walk_enabled() {
    let mut solver = Solver::new(4);
    solver.set_walk_enabled(true);

    // First two are always O, I
    let (t0, b0) = classify_rephase_stable(&mut solver, 0);
    assert_eq!(t0, RephaseType::Original);
    assert!(!b0);

    let (t1, b1) = classify_rephase_stable(&mut solver, 1);
    assert_eq!(t1, RephaseType::Inverted);
    assert!(!b1);

    // Repeating cycle: B, W, O, B, W, I
    let expected_cycle = [
        (RephaseType::Best, true),
        (RephaseType::Walk, false),
        (RephaseType::Original, false),
        (RephaseType::Best, true),
        (RephaseType::Walk, false),
        (RephaseType::Inverted, false),
    ];

    // Verify two full cycles (counts 2..14)
    for cycle in 0..2u64 {
        for (i, &(expected_type, expected_best)) in expected_cycle.iter().enumerate() {
            let count = 2 + cycle * 6 + i as u64;
            let (rtype, is_best) = classify_rephase_stable(&mut solver, count);
            assert_eq!(
                rtype, expected_type,
                "stable+walk count={count}: expected {expected_type:?}, got {rtype:?}"
            );
            assert_eq!(
                is_best, expected_best,
                "stable+walk count={count}: is_best expected {expected_best}, got {is_best}"
            );
        }
    }
}

#[test]
fn test_startup_walk_disabled_keeps_periodic_rephase_walk_schedule() {
    let mut solver = Solver::new(4);
    solver.set_startup_walk_enabled(false);

    let (stable_type, stable_best) = classify_rephase_stable(&mut solver, 3);
    assert_eq!(stable_type, RephaseType::Walk);
    assert!(!stable_best);

    let (focused_type, focused_best) = classify_rephase_focused(&mut solver, 3);
    assert_eq!(focused_type, RephaseType::Walk);
    assert!(!focused_best);
}

/// CaDiCaL `rephase.cpp:263-286`: stable mode with walk disabled.
/// Expected: O, I, (B, O, B, I)^w
#[test]
fn test_stable_rephase_schedule_walk_disabled() {
    let mut solver = Solver::new(4);
    solver.set_walk_enabled(false);

    let (t0, b0) = classify_rephase_stable(&mut solver, 0);
    assert_eq!(t0, RephaseType::Original);
    assert!(!b0);

    let (t1, b1) = classify_rephase_stable(&mut solver, 1);
    assert_eq!(t1, RephaseType::Inverted);
    assert!(!b1);

    // Repeating cycle: B, O, B, I
    let expected_cycle = [
        (RephaseType::Best, true),
        (RephaseType::Original, false),
        (RephaseType::Best, true),
        (RephaseType::Inverted, false),
    ];

    for cycle in 0..3u64 {
        for (i, &(expected_type, expected_best)) in expected_cycle.iter().enumerate() {
            let count = 2 + cycle * 4 + i as u64;
            let (rtype, is_best) = classify_rephase_stable(&mut solver, count);
            assert_eq!(
                rtype, expected_type,
                "stable-nowalk count={count}: expected {expected_type:?}, got {rtype:?}"
            );
            assert_eq!(
                is_best, expected_best,
                "stable-nowalk count={count}: is_best expected {expected_best}, got {is_best}"
            );
        }
    }
}

// ========================================================================
// Focused Mode Schedules
// ========================================================================

/// CaDiCaL `rephase.cpp:339-367`: focused mode with walk enabled.
/// Expected: O, (#, B, W, F, B, W)^w
#[test]
fn test_focused_rephase_schedule_walk_enabled() {
    let mut solver = Solver::new(4);
    solver.set_walk_enabled(true);

    let (t0, b0) = classify_rephase_focused(&mut solver, 0);
    assert_eq!(t0, RephaseType::Original);
    assert!(!b0);

    // Repeating cycle: #, B, W, F, B, W
    let expected_cycle = [
        (RephaseType::Random, false),
        (RephaseType::Best, true),
        (RephaseType::Walk, false),
        (RephaseType::Flip, false),
        (RephaseType::Best, true),
        (RephaseType::Walk, false),
    ];

    for cycle in 0..2u64 {
        for (i, &(expected_type, expected_best)) in expected_cycle.iter().enumerate() {
            let count = 1 + cycle * 6 + i as u64;
            let (rtype, is_best) = classify_rephase_focused(&mut solver, count);
            assert_eq!(
                rtype, expected_type,
                "focused+walk count={count}: expected {expected_type:?}, got {rtype:?}"
            );
            assert_eq!(
                is_best, expected_best,
                "focused+walk count={count}: is_best expected {expected_best}, got {is_best}"
            );
        }
    }
}

/// CaDiCaL `rephase.cpp:317-338`: focused mode with walk disabled.
/// Expected: F, (#, B, F, B)^w
#[test]
fn test_focused_rephase_schedule_walk_disabled() {
    let mut solver = Solver::new(4);
    solver.set_walk_enabled(false);

    let (t0, b0) = classify_rephase_focused(&mut solver, 0);
    assert_eq!(t0, RephaseType::Flip);
    assert!(!b0);

    // Repeating cycle: #, B, F, B
    let expected_cycle = [
        (RephaseType::Random, false),
        (RephaseType::Best, true),
        (RephaseType::Flip, false),
        (RephaseType::Best, true),
    ];

    for cycle in 0..3u64 {
        for (i, &(expected_type, expected_best)) in expected_cycle.iter().enumerate() {
            let count = 1 + cycle * 4 + i as u64;
            let (rtype, is_best) = classify_rephase_focused(&mut solver, count);
            assert_eq!(
                rtype, expected_type,
                "focused-nowalk count={count}: expected {expected_type:?}, got {rtype:?}"
            );
            assert_eq!(
                is_best, expected_best,
                "focused-nowalk count={count}: is_best expected {expected_best}, got {is_best}"
            );
        }
    }
}
