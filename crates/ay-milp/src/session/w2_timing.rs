// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-phase wall-clock instrument for the W2 ledger shape.
//!
//! A diagnostic, not a gate. It lives behind an `examples/` target rather than
//! a `#[test]`, because it asserts nothing about the numbers it reports and a
//! timing run on every `cargo test` measures nothing anybody reads.

use std::time::Instant;

use super::LpSession;
use crate::model::{Col, Model, Sense};
use crate::opts::SolveOpts;

/// The W2 ledger shape: `layers` layers of `width` columns, each column an
/// equality against a sparse weighted sum of the previous layer, with every
/// non-final layer passed through a two-row relaxed envelope.
///
/// Deterministic — the weights come from a fixed xorshift seed, so two runs
/// time the same model. Returns the model and its final-layer targets.
fn w2_ledger_shape(layers: usize, width: usize) -> (Model, Vec<Col>) {
    let mut m = Model::new();
    let mut prev: Vec<Col> = (0..width).map(|_| m.add_col(-1.0, 1.0)).collect();
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
            let mut coeffs: Vec<(Col, f64)> = prev
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
    (m, targets)
}

/// Per-phase wall clock on the W2 ledger shape (4 x 24) for the first three
/// targets — the implied-box sweep, the float solve, the NS pricing, and the
/// public rigorous query.
///
/// A diagnostic, not a gate: it asserts nothing about the numbers it reports,
/// so it is an `examples/` target rather than a `#[test]`. It was previously a
/// `#[test]` carrying `#[ignore]`, which `ay-quality-gate` forbids and which
/// meant it ran nowhere at all. The returned report is the text that test
/// printed, one phase per line.
///
/// Panics if the session or a target's float LP cannot be built, exactly as
/// the test did, so a shape that stops being solvable fails loudly instead of
/// printing a reassuring number.
///
/// Run: `cargo run --release -p ay-milp --example w2_tier_timing`
#[must_use]
pub fn diag_w2_tier_timing() -> String {
    use num_traits::ToPrimitive;

    let (layers, width) = (4usize, 24usize);
    let (m, targets) = w2_ledger_shape(layers, width);
    let mut lines = vec![format!(
        "shape {layers}x{width}: {} cols, {} rows",
        m.num_cols(),
        m.num_rows()
    )];
    let t0 = Instant::now();
    let bx = crate::presolve::implied_box_f64(&m, None);
    let open = bx.as_ref().map_or(usize::MAX, |(l, u)| {
        (0..m.num_cols())
            .filter(|&j| !l[j].is_finite() || !u[j].is_finite())
            .count()
    });
    lines.push(format!(
        "implied box: {:?} ({open} columns still open)",
        t0.elapsed()
    ));
    let mut s = LpSession::new(&m, &SolveOpts::new()).expect("session");
    for &t in targets.iter().take(3) {
        let t0 = Instant::now();
        let mut lp = s
            .float_lp(&[(t.0, 1.0)], Sense::Minimize)
            .expect("float lp");
        lp.plain_cold = true;
        let cand = lp.solve(None);
        lines.push(format!(
            "col {}: float solve {:?} status {:?}",
            t.index(),
            t0.elapsed(),
            cand.status
        ));
        let t0 = Instant::now();
        let ns = s.ns_bound(t, Sense::Minimize);
        lines.push(format!(
            "  ns_bound {:?} -> {:?}",
            t0.elapsed(),
            ns.as_ref().map(|b| b.to_f64())
        ));
        let t0 = Instant::now();
        let rb = s.rigorous_bound(t, Sense::Minimize);
        let shown: String = format!("{rb:?}").chars().take(60).collect();
        lines.push(format!("  rigorous_bound {:?} -> {shown}", t0.elapsed()));
    }
    lines.join("\n")
}
