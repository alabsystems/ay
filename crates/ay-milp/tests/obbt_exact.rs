// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! OBBT soundness on the PURE EXACT RIM (P3 twin of `tests/obbt.rs`).
//!
//! `AY_MILP_NO_FLOAT` forces every solve off the float advice lane and down
//! the exact rim; `float_lane_enabled()` reads it once into a process-global
//! `OnceLock`, so this switch cannot be toggled per-test. Hence a dedicated
//! test binary that sets it before any solve runs. The twin's claim: OBBT
//! reaches the same sound box with no float lane at all.

use ay_milp::{LpSession, Model, ObbtOpts, Outcome, Sense, SolveOpts};
use num_traits::ToPrimitive;

#[test]
fn obbt_kill_switch_still_tightens_soundly() {
    // Must run before the first solve so the `OnceLock` initialises to "off".
    // This binary holds only this test, so nothing else races the read.
    std::env::set_var("AY_MILP_NO_FLOAT", "1");

    // A coupled box: x = y and 1 <= y <= 3, both nominally [-10, 10].
    let mut m = Model::new();
    let x = m.add_col(-10.0, 10.0);
    let y = m.add_col(-10.0, 10.0);
    m.add_row(0.0, 0.0, &[(x, 1.0), (y, -1.0)]); // x - y = 0
    m.add_row(1.0, 3.0, &[(y, 1.0)]); // 1 <= y <= 3

    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    let report = s.obbt(&[x, y], &ObbtOpts::default()).unwrap();
    assert!(!report.infeasible);

    // x pulled in to about [1, 3] purely through the exact rim.
    let (xlb, xub) = report.bounds[0];
    assert!(
        xlb >= 1.0 - 1e-9 && xub <= 3.0 + 1e-9,
        "exact-lane x box {xlb}..{xub}"
    );

    // Soundness: the box still contains x's true feasible range. Recompute
    // the exact min/max on a fresh session (same exact rim).
    for (col, want) in [(x, (1.0, 3.0)), (y, (1.0, 3.0))] {
        let mut s2 = LpSession::new(&m, &SolveOpts::new()).unwrap();
        let mn = match s2.optimize(col, Sense::Minimize).unwrap() {
            Outcome::Optimal { value, .. } => value.to_f64().unwrap(),
            other => panic!("expected Optimal min, got {other:?}"),
        };
        let mx = match s2.optimize(col, Sense::Maximize).unwrap() {
            Outcome::Optimal { value, .. } => value.to_f64().unwrap(),
            other => panic!("expected Optimal max, got {other:?}"),
        };
        assert!(
            (mn - want.0).abs() < 1e-9 && (mx - want.1).abs() < 1e-9,
            "true range off"
        );
    }
}
