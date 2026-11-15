// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! OBBT soundness on the PURE EXACT RIM (P3 twin of `tests/obbt.rs`).
//!
//! Every session receives the typed `with_float_lane(false)` option. The
//! retired environment spelling did not configure the current solver, so a
//! passing test did not establish that it exercised the exact rim. The twin's
//! claim: OBBT reaches the same sound box with no float advice lane.

use ay_milp::{EngineEconomics, LpSession, Model, ObbtOpts, Outcome, Sense, SolveOpts};
use num_traits::ToPrimitive;

#[test]
fn obbt_kill_switch_still_tightens_soundly() {
    let opts = SolveOpts::new().with_engine(EngineEconomics::new().with_float_lane(false));
    // A coupled box: x = y and 1 <= y <= 3, both nominally [-10, 10].
    let mut m = Model::new();
    let x = m.add_col(-10.0, 10.0);
    let y = m.add_col(-10.0, 10.0);
    m.add_row(0.0, 0.0, &[(x, 1.0), (y, -1.0)]); // x - y = 0
    m.add_row(1.0, 3.0, &[(y, 1.0)]); // 1 <= y <= 3

    let mut s = LpSession::new(&m, &opts).unwrap();
    let report = s.obbt(&[x, y], &ObbtOpts::default()).unwrap();
    assert!(!report.infeasible);
    assert_eq!(
        report.bounds.len(),
        2,
        "both requested columns must be reported"
    );
    assert_eq!(report.tightened, 2, "both coupled columns must tighten");

    // x pulled in to about [1, 3] purely through the exact rim.
    let (xlb, xub) = report.bounds[0];
    assert!(
        xlb >= 1.0 - 1e-9 && xub <= 3.0 + 1e-9,
        "exact-lane x box {xlb}..{xub}"
    );

    // Soundness: the box still contains x's true feasible range. Recompute
    // the exact min/max on a fresh session (same exact rim).
    for ((col, want), &(lower, upper)) in [(x, (1.0, 3.0)), (y, (1.0, 3.0))]
        .into_iter()
        .zip(&report.bounds)
    {
        let mut s2 = LpSession::new(&m, &opts).unwrap();
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
        assert!(
            lower <= mn + 1e-9 && upper >= mx - 1e-9,
            "exact-lane box {lower}..{upper} cuts true range {mn}..{mx}"
        );
    }
}
