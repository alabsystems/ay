// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #3097: Test coverage for PDR solve() internal helpers.
//!
//! Covers: `bump_spurious_cex_weakness`, Luby restart thresholds.

use super::PdrSolver;
use crate::pdr::config::PdrConfig;
use crate::PredicateId;

fn test_linear_problem() -> crate::ChcProblem {
    crate::ChcParser::parse(
        r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (inv x) (= x2 (+ x 1))) (inv x2))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"#,
    )
    .expect("valid smtlib model")
}

fn test_config() -> PdrConfig {
    PdrConfig::default()
}

// =========================================================================
// Tests for bump_spurious_cex_weakness (#3097)
// =========================================================================

#[test]
fn bump_spurious_cex_weakness_increments_monotonically() {
    let mut solver = PdrSolver::new(test_linear_problem(), test_config());
    let key = (PredicateId(0), 12345u64);
    assert_eq!(solver.bump_spurious_cex_weakness(key), 1);
    assert_eq!(solver.bump_spurious_cex_weakness(key), 2);
    assert_eq!(solver.bump_spurious_cex_weakness(key), 3);
}

#[test]
fn bump_spurious_cex_weakness_tracks_distinct_keys() {
    let mut solver = PdrSolver::new(test_linear_problem(), test_config());
    let key_a = (PredicateId(0), 100u64);
    let key_b = (PredicateId(0), 200u64);
    let key_c = (PredicateId(1), 100u64);
    assert_eq!(solver.bump_spurious_cex_weakness(key_a), 1);
    assert_eq!(solver.bump_spurious_cex_weakness(key_b), 1);
    assert_eq!(solver.bump_spurious_cex_weakness(key_c), 1);
    assert_eq!(solver.bump_spurious_cex_weakness(key_a), 2);
    assert_eq!(solver.bump_spurious_cex_weakness(key_b), 2);
}

#[test]
fn bump_spurious_cex_weakness_saturates_at_u8_max() {
    let mut solver = PdrSolver::new(test_linear_problem(), test_config());
    let key = (PredicateId(0), 42u64);
    for _ in 0..255 {
        solver.bump_spurious_cex_weakness(key);
    }
    assert_eq!(
        solver.bump_spurious_cex_weakness(key),
        255,
        "should saturate at u8::MAX"
    );
    assert_eq!(
        solver.bump_spurious_cex_weakness(key),
        255,
        "should stay at u8::MAX"
    );
}

#[test]
fn bump_spurious_cex_weakness_cleared_on_restart() {
    let mut solver = PdrSolver::new(test_linear_problem(), test_config());
    let key = (PredicateId(0), 99u64);
    solver.bump_spurious_cex_weakness(key);
    solver.bump_spurious_cex_weakness(key);
    assert_eq!(solver.bump_spurious_cex_weakness(key), 3);
    solver.clear_restart_caches();
    assert_eq!(
        solver.bump_spurious_cex_weakness(key),
        1,
        "weakness should reset after restart"
    );
}

// =========================================================================
// Tests for Luby restart sequence (#3097)
// =========================================================================

#[test]
fn luby_sequence_first_16_values() {
    use crate::pdr::config::luby;
    let expected = [1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, 1];
    for (i, &exp) in expected.iter().enumerate() {
        assert_eq!(luby(i as u32), exp, "luby({i}) should be {exp}");
    }
}

#[test]
fn luby_restart_threshold_progression() {
    use crate::pdr::config::luby;
    let initial_threshold = 10usize;
    let expected_thresholds = [10, 10, 20, 10, 10, 20, 40, 10];
    for (i, &exp) in expected_thresholds.iter().enumerate() {
        let threshold = (luby(i as u32) as usize) * initial_threshold;
        assert_eq!(
            threshold, exp,
            "restart threshold at luby_index={i} should be {exp}"
        );
    }
}
