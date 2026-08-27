// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// A `HybridView` over a history with `n` columns, weights all 1.
fn hyb_view(h: &HybridHist, rel: f64) -> HybridView<'_> {
    let (inf_avg, cut_avg) = h.avgs();
    HybridView {
        h,
        rel,
        w: 1.0,
        w_inf: 1.0,
        w_cut: 1.0,
        inf_avg,
        cut_avg,
    }
}

/// THE SHIP CONTRACT for hybrid branching: a column the search already
/// trusts must score EXACTLY what the shipped product rule scores. Not
/// "close" — bit-equal, because the tie order of `cands` is what decides the
/// branch and a 1-ulp drift on a mature column would reorder trees the
/// hybrid term was never meant to touch.
#[test]
fn hybrid_term_is_bit_identical_once_a_column_is_reliable() {
    let mut pc = PseudoCost::new(2);
    let mut h = HybridHist::new(2);
    // Column 0: fully reliable (4 records per side at rel=4) AND carrying a
    // maximal hybrid signal — every child fathomed, every cascade huge.
    for _ in 0..4 {
        pc.record(0, 0.5, false, 3.0);
        pc.record(0, 0.5, true, 7.0);
        h.visit(0, false);
        h.visit(0, true);
        h.infer(0, false, 40);
        h.infer(0, true, 40);
    }
    // Column 1: some history, so the global means are nonzero and column 0's
    // signal genuinely sits above average.
    pc.record(1, 0.5, false, 1.0);
    pc.record(1, 0.5, true, 1.0);
    h.visit(1, false);
    h.branched(1, false);
    h.infer(1, false, 1);
    let view = hyb_view(&h, 4.0);
    let avgs = pc.avgs();
    assert!(
        view.bonus(0, false) > 0.5,
        "column 0's signal is above average"
    );
    assert_eq!(
        pc.score(0, 0.5, avgs, Some(&view)).to_bits(),
        pc.score(0, 0.5, avgs, None).to_bits(),
        "a reliable column's score must be bit-identical with the hybrid term on"
    );
}

/// The regime the lever exists for: two columns the pseudocosts cannot tell
/// apart (identical `frac`, both scored off the global average) are ordered
/// by their cutoff/inference history instead of arbitrarily.
#[test]
fn hybrid_term_orders_columns_the_pseudocost_rule_ties() {
    let mut pc = PseudoCost::new(3);
    let mut h = HybridHist::new(3);
    // Column 2 alone seeds the global averages; columns 0 and 1 have no
    // pseudocost record at all, so the shipped rule scores them identically.
    pc.record(2, 0.5, false, 2.0);
    pc.record(2, 0.5, true, 2.0);
    h.visit(2, false);
    h.branched(2, false);
    h.infer(2, false, 4);
    // Column 0: every child it ever produced was fathomed. Column 1: none were.
    for _ in 0..3 {
        h.visit(0, false);
        h.visit(0, true);
        h.visit(1, false);
        h.branched(1, false);
        h.visit(1, true);
        h.branched(1, true);
    }
    let view = hyb_view(&h, 8.0);
    let avgs = pc.avgs();
    assert_eq!(
        pc.score(0, 0.5, avgs, None).to_bits(),
        pc.score(1, 0.5, avgs, None).to_bits(),
        "fixture must be a real tie under the shipped rule"
    );
    assert!(
        pc.score(0, 0.5, avgs, Some(&view)) > pc.score(1, 0.5, avgs, Some(&view)),
        "the all-fathom column must outrank the never-fathom one"
    );
}

/// The blend must stay bounded: with the default weight the hybrid term can
/// at most double one side's gain, so it cannot swamp a real pseudocost
/// difference between two columns of the same maturity.
#[test]
fn hybrid_term_is_bounded_by_its_weight() {
    let mut pc = PseudoCost::new(2);
    let mut h = HybridHist::new(2);
    pc.record(1, 0.5, false, 1.0);
    pc.record(1, 0.5, true, 1.0);
    h.visit(1, false);
    h.branched(1, false);
    // Column 0: an extreme outlier on both signals, zero pseudocost history.
    for _ in 0..50 {
        h.visit(0, false);
        h.visit(0, true);
        h.infer(0, false, 10_000);
        h.infer(0, true, 10_000);
    }
    let view = hyb_view(&h, 8.0);
    let avgs = pc.avgs();
    let plain = pc.score(0, 0.5, avgs, None);
    let hybrid = pc.score(0, 0.5, avgs, Some(&view));
    assert!(hybrid > plain, "an outlier column must be promoted at all");
    assert!(
        hybrid <= plain * 4.0 + 1e-12,
        "each side's factor is capped at 1 + w = 2, so the product is capped at 4x \
         (got {hybrid} vs {plain})"
    );
}

/// `CountDeps` must count exactly the bound changes the propagation makes,
/// and must not change what the propagation DOES: the tapped and untapped
/// runs have to leave bit-identical boxes.
#[test]
fn count_deps_counts_tightenings_without_changing_the_box() {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let y = model.add_binary_col();
    let z = model.add_binary_col();
    // x + y + z <= 1: fixing x to 1 forces y and z to 0.
    model.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0), (y, 1.0), (z, 1.0)]);
    let mut col_rows: Vec<Vec<u32>> = vec![Vec::new(); model.num_cols()];
    for r in 0..model.num_rows() {
        let (coeffs, _, _) = model.row(Row(r as u32));
        for &(c, _) in coeffs {
            col_rows[c as usize].push(r as u32);
        }
    }
    let base_lo = vec![1.0, 0.0, 0.0];
    let base_up = vec![1.0, 1.0, 1.0];
    let (mut lo_a, mut up_a) = (base_lo.clone(), base_up.clone());
    let alive_a = propagate_branch_rows(&model, &col_rows, 0, &mut lo_a, &mut up_a);
    let (mut lo_b, mut up_b) = (base_lo.clone(), base_up.clone());
    let mut tap = CountDeps { n: 0 };
    let alive_b = propagate_branch_rows_t(&model, &col_rows, 0, &mut lo_b, &mut up_b, &mut tap);
    assert_eq!(alive_a, alive_b);
    assert_eq!(
        lo_a, lo_b,
        "the tap must not change the derived lower bounds"
    );
    assert_eq!(
        up_a, up_b,
        "the tap must not change the derived upper bounds"
    );
    assert_eq!(up_b[1], 0.0);
    assert_eq!(up_b[2], 0.0);
    assert!(
        tap.n >= 2,
        "both forced zeros are domain reductions (got {})",
        tap.n
    );
}

/// A signal with no data anywhere must not silently rescale every column's
/// bonus: `bonus` normalises over the signals that HAVE data.
#[test]
fn hybrid_bonus_normalises_over_available_signals_only() {
    let mut h = HybridHist::new(2);
    // Cutoff data only — this is the shape of every model where node
    // propagation never arms.
    for _ in 0..4 {
        h.visit(0, false);
    }
    h.visit(1, false);
    h.branched(1, false);
    let view = hyb_view(&h, 8.0);
    assert_eq!(view.inf_avg, 0.0, "no cascade was ever recorded");
    // Column 0 fathoms 100% against a population mean of 4/5, so the mapped
    // term is (1.25)/(2.25) — NOT half of it.
    let expect = (1.25f64) / (1.0 + 1.25);
    assert!(
        (view.bonus(0, false) - expect).abs() < 1e-12,
        "got {} want {expect}",
        view.bonus(0, false)
    );
}

/// Unordered history cannot become branching advice. In particular, replacing
/// the explicit partial-order check with `avg <= 0.0` would let this NaN escape.
#[test]
fn hybrid_bonus_rejects_an_unordered_population_mean() {
    let mut h = HybridHist::new(1);
    h.infer(0, false, 1);
    let mut view = hyb_view(&h, 8.0);
    view.inf_avg = f64::NAN;
    view.w_cut = 0.0;

    assert_eq!(view.bonus(0, false).to_bits(), 0.0f64.to_bits());
}
