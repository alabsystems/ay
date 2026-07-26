// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DIFFERENTIAL-CORRECTNESS guard for all three basis-factorization lanes,
//! including the opt-in block-triangular-factor (BTF) lane.
//!
//! A basis is factored through `refactorize` on BOTH existing trusted lanes:
//! lane 0 = PFI slot-order (`AY_MILP_NO_BUMP_LU`'s lane) and lane 1 = Markowitz
//! bump-LU (the default lane above the bump floor). The two lanes invert the
//! SAME basis by two independent algorithms, so their FTRAN (`B⁻¹·M_j`) and
//! BTRAN (rows of `B⁻¹`) images MUST agree to floating-point noise, and they
//! must kick the same singular-dependent columns. The same fail-closed harness
//! validates the BTF lane against the monolithic bump-LU lane below.
//!
//! The lanes are forced per-solve via the inert `bump_lu_override` seam, so no
//! env toggles the lane; the env here only ACTIVATES the peel on a tiny LP
//! (`AY_MILP_TRI_CRASH`) and drops the bump floor to 1 (`AY_MILP_BUMP_LU_MIN`)
//! so lane 1 genuinely takes the bump-LU path. Env forcing is per-process and
//! serialized through the one workspace choke point; this file is its own test
//! binary, so nothing leaks into other suites.

use ay_milp::{
    bump_lu_diff_on_model, bump_lu_diff_on_model_lanes, diag_refine_probe, BumpLuDiff, Model,
};

/// Activate the peel + bump-LU on tiny LPs for the duration of `f`, serialized +
/// restored on exit through the workspace env choke point.
fn with_peel_env<T>(f: impl FnOnce() -> T) -> T {
    ay_test_support::env::with_serialized_env_vars(
        &[
            ("AY_MILP_TRI_CRASH", "1"),
            ("AY_MILP_BUMP_LU_MIN", "1"),
            ("AY_MILP_REFACTOR_EVERY", "1"),
        ],
        f,
    )
}

/// An odd cycle `x_i + x_{i+1 mod n} = 2` (n odd) has the unique solution x == 1,
/// so the optimal basis holds all n structural columns — one whole SCC with no
/// singleton front or back, i.e. an all-bump basis. This is the tightest genuine
/// non-triangular bump: the peel finds nothing to peel and hands the entire
/// basis to the bump-LU factor.
fn odd_cycle(m: &mut Model, coeff_a: f64, coeff_b: f64, rhs: f64, n: usize) -> Vec<ay_milp::Col> {
    let cols: Vec<_> = (0..n).map(|_| m.add_col(0.0, 10.0)).collect();
    for i in 0..n {
        m.add_row(
            rhs,
            rhs,
            &[(cols[i], coeff_a), (cols[(i + 1) % n], coeff_b)],
        );
    }
    cols
}

/// A deterministic diagonally-dominant sparse block (invertible by construction)
/// forced to the interior point x == 1: each equality row `a_i·x = Σ a_i` with a
/// unique solution, so all `k` columns are basic (a `k`-col bump). Unlike the odd
/// cycle its rows/columns have HETEROGENEOUS densities and magnitudes, so the
/// Markowitz min-degree pivot order (lane 1) diverges from the PFI slot-order
/// greedy pivots (lane 0) — the case that PERMUTES the basis across row slots.
fn asymmetric_block(m: &mut Model, k: usize) {
    let cols: Vec<_> = (0..k).map(|_| m.add_col(0.0, 10.0)).collect();
    // A tiny LCG for deterministic "random" off-diagonal structure.
    let mut seed: u64 = 0x9E3779B97F4A7C15;
    let mut next = || {
        seed = seed
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (seed >> 33) as usize
    };
    for i in 0..k {
        // Diagonal 10 dominates the ≤3 off-diagonal entries (each ≤3) → invertible.
        let mut coeffs: Vec<(ay_milp::Col, f64)> = vec![(cols[i], 10.0)];
        let deg = 1 + next() % 3; // 1..=3 off-diagonal entries, varying per row
        for _ in 0..deg {
            let j = next() % k;
            if j != i && !coeffs.iter().any(|&(c, _)| c == cols[j]) {
                let mag = 1.0 + (next() % 3) as f64; // 1..=3
                coeffs.push((cols[j], mag));
            }
        }
        let rhs: f64 = coeffs.iter().map(|&(_, w)| w).sum(); // a_i · 1 = Σ a_i
        m.add_row(rhs, rhs, &coeffs);
    }
}

/// Add `k` decoy bounded columns each pinned under one inequality row — a stock
/// of NONBASIC structural columns (and their slacks) so the FTRAN sample has a
/// varied batch of raw `M_j` inputs beyond the cycle's logical slacks.
fn decoy_cols(m: &mut Model, k: usize) {
    for j in 0..k {
        let c = m.add_col(0.0, 4.0);
        // A single-variable inequality: its slack is basic, c rests at a bound.
        m.add_row(
            f64::NEG_INFINITY,
            3.0 + (j % 3) as f64,
            &[(c, 1.0 + (j % 2) as f64)],
        );
    }
}

/// The two trusted lanes must invert a genuine multi-block non-triangular bump
/// IDENTICALLY: two independent odd cycles (distinct coefficients, ±1 and 2/3)
/// plus a 25-column asymmetric block whose Markowitz order diverges from PFI's,
/// decorated with 24 nonbasic decoys. The asymmetric block makes the two lanes
/// permute the basis across row slots (`perm_differs`), so this test guards the
/// column-keyed comparison that the naive row-slot comparison got wrong.
#[test]
fn two_lanes_agree_on_multiblock_bump() {
    with_peel_env(|| {
        let mut m = Model::new();
        // Cycle A: x_i + x_{i+1} = 2  → x == 1 (11 cols).
        odd_cycle(&mut m, 1.0, 1.0, 2.0, 11);
        // Cycle B: 2 y_i + 3 y_{i+1} = 5 → y == 1 (7 cols), different coefficients.
        odd_cycle(&mut m, 2.0, 3.0, 5.0, 7);
        // An asymmetric block whose Markowitz (min-degree) pivot order diverges
        // from PFI's slot-order greedy pivots — this is what makes the two lanes
        // assign columns to DIFFERENT row slots (perm_differs), exercising the
        // column-keyed comparison that the naive row-slot comparison got wrong.
        asymmetric_block(&mut m, 25);
        decoy_cols(&mut m, 24);

        let d = bump_lu_diff_on_model(&m, 30.0).expect("root LP solves + probe runs");

        // A real bump was factored (not a trivial all-logical triangular basis).
        assert!(
            d.fill[0] > 0 && d.fill[1] > 0,
            "expected a non-trivial eta file on both lanes; fill={:?}",
            d.fill
        );
        assert_eq!(
            d.bump_lu_used,
            [false, true],
            "probe must exercise PFI then bump-LU"
        );
        assert!(
            d.scale > 0.0,
            "images must be non-trivial; scale={}",
            d.scale
        );
        // The lanes MUST assign the bump to different row slots here — otherwise
        // this test would pass even with a row-slot-indexed (permutation-VARIANT)
        // comparison, and would not guard the column-keyed invariance that the
        // real full-depth instance needs. `refactorize` permutes `self.basis`, so
        // a broken/reverted harness fails exactly when this is true.
        assert!(
            d.perm_differs,
            "expected the two lanes to permute the basis differently (bump too symmetric?)"
        );
        // The harness self-validation: the two independent factorizations agree.
        assert!(
            d.agree(1e-6),
            "LANES DISAGREE (harness/lane BROKEN): ftran_diff={:.3e} btran_diff={:.3e} \
             scale={:.3e} kicked={:?} fill={:?} over {} FTRAN cols + {} BTRAN basis-cols",
            d.ftran_diff,
            d.btran_diff,
            d.scale,
            d.kicked,
            d.fill,
            d.n_ftran,
            d.n_btran
        );
        // Spell out the two components the task calls for, with an absolute floor.
        let tol = 1e-6 * d.scale.max(1.0);
        assert!(
            d.ftran_diff <= tol,
            "FTRAN diff {:.3e} > {:.3e}",
            d.ftran_diff,
            tol
        );
        assert!(
            d.btran_diff <= tol,
            "BTRAN diff {:.3e} > {:.3e}",
            d.btran_diff,
            tol
        );
        assert_eq!(d.kicked[0], d.kicked[1], "lanes kicked different counts");
        assert_eq!(
            d.kicked_columns[0], d.kicked_columns[1],
            "lanes kicked different basis columns"
        );
        assert_eq!(
            d.final_basis_columns[0], d.final_basis_columns[1],
            "lanes produced different repaired basis sets"
        );
    });
}

#[test]
fn public_probe_rejects_invalid_time_budgets_without_panicking() {
    let model = Model::new();
    for secs in [0.0, -1.0, f64::NAN, f64::INFINITY, u64::MAX as f64] {
        let error = bump_lu_diff_on_model(&model, secs)
            .err()
            .expect("invalid time budget must be rejected");
        assert!(
            error.contains("time budget"),
            "unexpected error for {secs:?}: {error}"
        );
        assert!(
            diag_refine_probe(&model, secs, 1).contains("invalid time budget"),
            "refinement diagnostic accepted invalid budget {secs:?}"
        );
    }
}

#[test]
fn agreement_rejects_bad_provenance_repairs_and_nonfinite_metrics() {
    let mut d = BumpLuDiff {
        ftran_diff: 0.0,
        btran_diff: 0.0,
        kicked: [1, 1],
        kicked_columns: [vec![3], vec![3]],
        final_basis_columns: [vec![1, 2, 4], vec![1, 2, 4]],
        bump_lu_used: [false, true],
        fill: [1, 1],
        perm_differs: true,
        secs: [0.0, 0.0],
        n_ftran: 1,
        n_btran: 1,
        scale: 1.0,
        lanes: [0, 1],
    };
    assert!(d.agree(1e-6));

    d.bump_lu_used = [false, false];
    assert!(!d.agree(1e-6), "a declined bump-LU lane must fail closed");
    d.bump_lu_used = [false, true];

    d.lanes = [1, 2];
    assert!(
        !d.agree(1e-6),
        "lane 1/2 provenance must require both bump lanes to run"
    );
    d.bump_lu_used = [true, true];
    assert!(d.agree(1e-6));
    d.lanes = [0, 1];
    d.bump_lu_used = [false, true];

    d.kicked_columns[1] = vec![4];
    assert!(
        !d.agree(1e-6),
        "equal kick counts on different columns must fail closed"
    );
    d.kicked_columns[1] = vec![3];

    d.final_basis_columns[1] = vec![1, 2, 5];
    assert!(
        !d.agree(1e-6),
        "different repaired basis sets must fail closed"
    );
    d.final_basis_columns[1] = vec![1, 2, 4];

    for invalid in [f64::NAN, f64::INFINITY, -1.0] {
        assert!(!d.agree(invalid), "invalid tolerance {invalid:?} admitted");
    }
    d.ftran_diff = f64::NAN;
    assert!(!d.agree(1e-6), "non-finite images must fail closed");
    d.ftran_diff = -1.0;
    assert!(!d.agree(1e-6), "negative differences must fail closed");
}

#[test]
fn public_probe_rejects_invalid_lane_pairs_without_panicking() {
    let model = Model::new();
    for lanes in [[0, 0], [1, 1], [2, 2], [0, 3], [4, 1]] {
        let error = bump_lu_diff_on_model_lanes(&model, 1.0, lanes)
            .err()
            .expect("invalid lane pair must be rejected");
        assert!(
            error.contains("factorization lanes"),
            "unexpected error for {lanes:?}: {error}"
        );
    }
}

/// A single larger odd cycle — a 21-column all-bump SCC — as an independent data
/// point on a differently-sized bump.
#[test]
fn two_lanes_agree_on_single_large_cycle() {
    with_peel_env(|| {
        let mut m = Model::new();
        odd_cycle(&mut m, 1.0, 1.0, 2.0, 21);
        decoy_cols(&mut m, 8);

        let d = bump_lu_diff_on_model(&m, 30.0).expect("root LP solves + probe runs");
        assert!(
            d.fill[0] > 0 && d.fill[1] > 0,
            "expected a bump; fill={:?}",
            d.fill
        );
        assert!(
            d.agree(1e-6),
            "LANES DISAGREE: ftran_diff={:.3e} btran_diff={:.3e} scale={:.3e} kicked={:?}",
            d.ftran_diff,
            d.btran_diff,
            d.scale,
            d.kicked
        );
    });
}

/// A CHAIN of `k` odd 3-cycles, each coupled one-directionally into the next:
/// cycle `i` (`i > 0`) carries the previous cycle's first variable as an extra
/// term in its opening row. Every cycle stays an odd SCC (unique solution `x ==
/// 1`), and the coupling makes cycle `i-1`'s column appear in cycle `i`'s
/// matched row — a strict dependency `block(i-1) -> block(i)`. The whole basis
/// is thus block-LOWER-triangular with `k` genuinely COUPLED diagonal blocks in
/// a forced topological order: unlike independent blocks, emitting them in the
/// WRONG order leaves a column's spill in an already-closed block's row (a
/// dangling super-diagonal L entry), so the BTF operator diverges from lane 1.
/// This is the test that pins the block-emission DIRECTION.
fn coupled_cycle_chain(m: &mut Model, k: usize) {
    let mut prev_head: Option<ay_milp::Col> = None;
    for _ in 0..k {
        let v: Vec<_> = (0..3).map(|_| m.add_col(0.0, 10.0)).collect();
        // Opening row: v0 + v1 (+ prev_head) = 2 (or 3 with the coupling).
        let mut r0: Vec<(ay_milp::Col, f64)> = vec![(v[0], 1.0), (v[1], 1.0)];
        let mut rhs0 = 2.0;
        if let Some(p) = prev_head {
            r0.push((p, 1.0));
            rhs0 += 1.0; // keeps the all-ones solution exact
        }
        m.add_row(rhs0, rhs0, &r0);
        // The rest of the 3-cycle: v1 + v2 = 2, v2 + v0 = 2.
        m.add_row(2.0, 2.0, &[(v[1], 1.0), (v[2], 1.0)]);
        m.add_row(2.0, 2.0, &[(v[2], 1.0), (v[0], 1.0)]);
        prev_head = Some(v[0]);
    }
}

/// LANE 1 vs LANE 2 on a genuinely COUPLED multi-block bump: a chain of five
/// odd 3-cycles wired `block0 -> block1 -> ... -> block4`. The two lanes invert
/// the SAME basis — lane 1 as one monolithic Markowitz core, lane 2 as the five
/// SCC blocks emitted in topological order — so their FTRAN/BTRAN images MUST
/// agree to float noise and kick identically. A reversed block-emission order
/// (or a botched open-mask / remap) would strand a coupling entry against a
/// closed pivot row and blow the diff wide open. This is the direction gate.
#[test]
fn lane1_vs_lane2_agree_on_coupled_chain() {
    with_peel_env(|| {
        let mut m = Model::new();
        coupled_cycle_chain(&mut m, 5);
        decoy_cols(&mut m, 16);

        let d = bump_lu_diff_on_model_lanes(&m, 30.0, [1, 2]).expect("root LP solves + probe runs");
        assert_eq!(d.lanes, [1, 2], "harness compared the wrong lanes");
        assert!(
            d.fill[0] > 0 && d.fill[1] > 0,
            "expected a non-trivial eta file on both lanes; fill={:?}",
            d.fill
        );
        assert!(
            d.scale > 0.0,
            "images must be non-trivial; scale={}",
            d.scale
        );
        let tol = 1e-6 * d.scale.max(1.0);
        assert!(
            d.agree(1e-6),
            "LANE 1 vs LANE 2 DISAGREE (BTF BROKEN — likely block-emission order or open-mask/remap): \
             ftran_diff={:.3e} btran_diff={:.3e} tol={:.3e} scale={:.3e} kicked={:?} fill={:?}",
            d.ftran_diff,
            d.btran_diff,
            tol,
            d.scale,
            d.kicked,
            d.fill
        );
        assert!(
            d.ftran_diff <= tol,
            "FTRAN diff {:.3e} > {:.3e}",
            d.ftran_diff,
            tol
        );
        assert!(
            d.btran_diff <= tol,
            "BTRAN diff {:.3e} > {:.3e}",
            d.btran_diff,
            tol
        );
        assert_eq!(d.kicked[0], d.kicked[1], "lanes kicked different counts");
        // The BTF lane should not fill MORE than the monolithic core on a bump
        // that is (almost) all small blocks — the whole point of the lane.
        assert!(
            d.fill[1] <= d.fill[0],
            "BTF fill {} exceeded monolithic bump-LU fill {} on a block-triangular bump",
            d.fill[1],
            d.fill[0]
        );
    });
}

/// LANE 1 vs LANE 2 on the same multi-block bump the lane-0-vs-1 test uses (two
/// independent odd cycles + a 25-col asymmetric block + decoys). Independent
/// blocks do not pin the emission direction, but this DOES exercise the
/// per-block open-mask, the block-local -> global column remap, and identical
/// kicking across a mix of SCC sizes.
#[test]
fn lane1_vs_lane2_agree_on_multiblock_bump() {
    with_peel_env(|| {
        let mut m = Model::new();
        odd_cycle(&mut m, 1.0, 1.0, 2.0, 11);
        odd_cycle(&mut m, 2.0, 3.0, 5.0, 7);
        asymmetric_block(&mut m, 25);
        decoy_cols(&mut m, 24);

        let d = bump_lu_diff_on_model_lanes(&m, 30.0, [1, 2]).expect("root LP solves + probe runs");
        assert!(
            d.fill[0] > 0 && d.fill[1] > 0,
            "expected a bump on both lanes; fill={:?}",
            d.fill
        );
        let tol = 1e-6 * d.scale.max(1.0);
        assert!(
            d.agree(1e-6),
            "LANE 1 vs LANE 2 DISAGREE: ftran_diff={:.3e} btran_diff={:.3e} tol={:.3e} kicked={:?} fill={:?}",
            d.ftran_diff,
            d.btran_diff,
            tol,
            d.kicked,
            d.fill
        );
        assert_eq!(d.kicked[0], d.kicked[1], "lanes kicked different counts");
    });
}
