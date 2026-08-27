// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Default-off arms scoped to the very-large formula band
//! (`--sat-large-rephase-walk`, `--sat-mode-equiticks-large`).
//!
//! Both are resolved once at solve entry and must be inert everywhere else.

use super::*;

/// `--sat-large-rephase-walk` is default OFF and must stay a pure widening of
/// the rephase-walk clause ceiling when it is on.
///
/// The witness that motivated the arm (cabp-V-nos6.mtx.rnd-k275, 1,529,550
/// vars / 8,599,702 clauses) sits between the two caps: blocked by default,
/// admitted by the arm. kissat's own bound is `MAX_WALK_REF` = 2^31-1
/// (`walk.c:19-20`), which the arm mirrors.
#[test]
fn test_large_rephase_walk_widens_the_clause_cap_only_when_armed() {
    use crate::solver::rephase::rephase_walk_clause_cap;

    assert!(
        ay_core::sat_ab_switches().large_rephase_walk.is_none(),
        "the arm must ship default-off (None resolves to OFF)"
    );

    let default_cap = rephase_walk_clause_cap(false);
    let armed_cap = rephase_walk_clause_cap(true);
    assert_eq!(default_cap, 2_000_000);
    assert_eq!(armed_cap, (1usize << 31) - 1);
    assert!(armed_cap > default_cap, "the arm must only widen the gate");

    const WITNESS_CLAUSES: usize = 8_599_702;
    assert!(WITNESS_CLAUSES > default_cap, "witness blocked by default");
    assert!(WITNESS_CLAUSES <= armed_cap, "witness admitted when armed");
}

/// A fresh solver must resolve both large-band arms to OFF, so `rephase_walk`
/// keeps the shipped 2M ceiling and the stable budget keeps the shipped
/// nlogpow4 schedule until the CLI installs a switch on a large formula.
#[test]
fn test_large_band_arms_default_off_on_a_fresh_solver() {
    let solver = Solver::new(4);
    assert!(!solver.cold.large_rephase_walk);
    assert!(!solver.cold.mode_equiticks_large_band);
    assert_eq!(
        crate::solver::rephase::rephase_walk_clause_cap(solver.cold.large_rephase_walk),
        2_000_000
    );
    assert!(ay_core::sat_ab_switches().mode_equiticks_large.is_none());
}

/// `--sat-mode-equiticks-large` only fills in the `None` case of the global
/// `--sat-mode-equiticks` resolution: an explicit global value must still win
/// in BOTH directions, so the existing kill-switch semantics are preserved,
/// and the band flag must never arm outside the very-large band.
#[test]
fn test_mode_equiticks_large_only_fills_the_unset_global() {
    // Global unset + band armed -> the resolution falls through to the band.
    let guard = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        mode_equiticks_large: Some(true),
        ..ay_core::SatAbSwitches::default()
    });
    assert!(ay_core::sat_ab_switches().mode_equiticks.is_none());
    assert_eq!(
        ay_core::sat_ab_switches().mode_equiticks_large,
        Some(true),
        "the band switch must reach the engine"
    );
    // Small formula: the band never arms, so the resolution stays OFF.
    let solver = Solver::new(4);
    assert!(!solver.cold.mode_equiticks_large_band);
    drop(guard);

    // Global forced OFF must stay a kill-switch even with the band armed:
    // `unwrap_or(band)` never consults the band when the global is `Some`.
    let guard = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        mode_equiticks: Some(false),
        mode_equiticks_large: Some(true),
        ..ay_core::SatAbSwitches::default()
    });
    assert_eq!(ay_core::sat_ab_switches().mode_equiticks, Some(false));
    assert!(
        !ay_core::sat_ab_switches().mode_equiticks.unwrap_or(true),
        "an explicit global false must win over an armed band"
    );
    drop(guard);
}
