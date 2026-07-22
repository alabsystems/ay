// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LG0 overhead ledger: per-solve overhead on trivial fixtures must be
//! < 1 ms (the P0 subprocess lane measured ~25 ms/solve). The asserts here
//! are CI-safe multiples; the printed figures are the ledger numbers
//! (capture with `cargo test -p ay-milp --release --test overhead -- --nocapture`).

use std::time::Instant;

use ay_milp::{BabSession, LpSession, Model, Outcome, Sense, SolveOpts};

fn tiny_lp() -> Model {
    // The ny ay_backend fixture: y = 2x, x in [1/4, 1].
    let mut m = Model::new();
    let x = m.add_col(0.25, 1.0);
    let y = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
    m.add_row(0.0, 0.0, &[(x, 2.0), (y, -1.0)]);
    m
}

#[test]
fn lp_session_resolve_overhead() {
    let m = tiny_lp();
    let y = m.col_at(1).unwrap();
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    // Warm up once.
    let _ = s.tighten_col_bounds(y).unwrap();
    let n = 200u32;
    let start = Instant::now();
    for _ in 0..n {
        let (lo, hi) = s.tighten_col_bounds(y).unwrap();
        assert!(matches!(lo, Outcome::Optimal { .. }));
        assert!(matches!(hi, Outcome::Optimal { .. }));
    }
    let per_solve = start.elapsed() / (2 * n);
    println!("LG0 ledger: LpSession warm re-solve = {per_solve:?} per solve");
    assert!(
        per_solve.as_millis() < 5,
        "warm LP re-solve must be far under the 25 ms subprocess baseline, got {per_solve:?}"
    );
}

#[test]
fn bab_session_build_and_check_overhead() {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_binary_col();
    m.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]);
    m.set_objective(&[(x, 1.0), (y, 2.0)], Sense::Minimize);
    let n = 20u32;
    // Warm-up.
    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    let _ = s.check().unwrap();
    let start = Instant::now();
    for _ in 0..n {
        let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
        assert!(matches!(s.check().unwrap(), Outcome::Optimal { .. }));
    }
    let per_solve = start.elapsed() / n;
    println!("LG0 ledger: BabSession cold build+optimize = {per_solve:?} per solve");
    assert!(
        per_solve.as_millis() < 25,
        "cold in-process MILP solve must beat the 25 ms subprocess baseline, got {per_solve:?}"
    );
}
