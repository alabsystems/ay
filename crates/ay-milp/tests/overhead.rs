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

/// W2-shaped ledger: a layered triangle-relaxation LP (the ny tighten-stream
/// shape) with a rigorous-bound re-solve pair per target neuron on ONE warm
/// session. This is the only test that drives `tighten_col_bounds_rigorous`
/// end to end: every emitted bound must be flagged rigorous and the pair must
/// bracket. The per-solve figure is the ledger number; it is asserted against
/// the 25 ms subprocess baseline only in release builds, where the branch
/// that first measured it (retired `milp-for-ny`, archived at tag
/// `archive/milp-for-ny`) recorded 12.7 ms/solve on a 192x240 instance.
///
/// History: when this test was first ported (2026-09-10) main's NS tier
/// declined every query on this shape — free pre-activation columns had no
/// finite corner, and 1e-17 dual noise on inactive one-sided rows killed the
/// slack terms — so each solve fell to the exact rim (26 s at this size, and
/// the 48-solve stream did not finish in six hours). The rows' implied box
/// plus the dual clamp put every solve back on the NS tier.
#[test]
fn w2_rigorous_stream_ledger() {
    // 4 layers x 24 neurons: 192 cols, 240 rows — the CI-sized W2 shape the
    // branch measured. (Edit the two constants to probe other shapes; the
    // in-module diagnostic `w2_tier_timing` prints the per-phase split.)
    let layers = 4usize;
    let width = 24usize;
    let mut m = Model::new();
    let mut prev: Vec<ay_milp::Col> = (0..width).map(|_| m.add_col(-1.0, 1.0)).collect();
    let mut rng: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next_w = || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        ((rng % 2000) as f64 - 1000.0) / 1000.0
    };
    let mut targets = Vec::new();
    for layer in 0..layers {
        let mut out = Vec::with_capacity(width);
        for _ in 0..width {
            let y = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
            let mut coeffs: Vec<(ay_milp::Col, f64)> = prev
                .iter()
                .filter_map(|&x| {
                    let w = next_w();
                    (w.abs() > 0.5).then_some((x, w))
                })
                .collect();
            coeffs.push((y, -1.0));
            m.add_row(0.0, 0.0, &coeffs);
            out.push(y);
        }
        if layer == layers - 1 {
            targets = out.clone();
        } else {
            // Triangle relaxation with a symmetric preactivation box.
            let mut post = Vec::with_capacity(width);
            for &x in &out {
                let z = m.add_col(0.0, 4.0);
                m.add_row(0.0, f64::INFINITY, &[(z, 1.0), (x, -1.0)]);
                m.add_row(f64::NEG_INFINITY, 2.0, &[(z, 1.0), (x, -0.5)]);
                post.push(z);
            }
            prev = post;
        }
    }

    // A per-solve limit: should the NS tier ever decline on this shape again, the
    // exact-rim fallback fails closed (`Unknown`, which the match below rejects)
    // instead of pinning CI for hours.
    let opts = SolveOpts::new().with_time_limit(std::time::Duration::from_secs(10));
    let mut s = LpSession::new(&m, &opts).unwrap();
    // Warm up (first factorization).
    let _ = s.tighten_col_bounds_rigorous(targets[0]).unwrap();
    let start = Instant::now();
    let mut solves = 0u32;
    let bound_of = |o: Outcome, what: &str| match o {
        Outcome::Bound {
            dual_bound,
            rigorous,
        } => {
            assert!(rigorous, "W2 {what} bound must be rigorous");
            dual_bound
        }
        Outcome::Optimal { value, .. } => value,
        other => panic!("expected Bound/Optimal {what}, got {other:?}"),
    };
    for &t in &targets {
        let (lo, hi) = s.tighten_col_bounds_rigorous(t).unwrap();
        solves += 2;
        let lo_b = bound_of(lo, "min");
        let hi_b = bound_of(hi, "max");
        assert!(lo_b <= hi_b, "rigorous bounds must bracket");
    }
    let per_solve = start.elapsed() / solves;
    println!(
        "G1 ledger: W2 rigorous stream ({} cols, {} rows, {} solves): {per_solve:?}/solve",
        m.num_cols(),
        m.num_rows(),
        solves
    );
    if cfg!(not(debug_assertions)) {
        assert!(
            per_solve.as_millis() < 25,
            "rigorous W2 re-solve must beat the 25 ms subprocess baseline, got {per_solve:?}"
        );
    }
}
