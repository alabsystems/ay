// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Deep chain-aggregation fixtures and soundness regressions.

use super::*;

/// A MINIATURE FIXED-CHARGE NETWORK of the qiu shape, small enough to reason about:
/// `ARCS` arcs. Each has an upstream continuous `n_i` and TWO downstream continuous columns
/// `p_i, q_i` — the qiu proportion exactly, where `c661` carries 66 negative columns against
/// 132 positive ones and every negative column has two chain partners
/// (`x49 − x313 <= 0` and `x49 − x577 <= 0`). Each downstream column carries a variable upper
/// bound `<= U·y_i` on the arc's binary switch. The capacity row is
/// `Σ (p_i + q_i) − Σ n_i <= CAP`.
///
/// The walk must aggregate the capacity row with ONE chain row per negative column — which
/// cancels `n_i` and zeroes `p_i` in the same step — and land on the clean single-node set
/// `Σ q_i <= CAP`. That is exactly the `Σ_{66 arcs} x_j <= 48` it lands on for qiu's `c661`.
fn chain_fixture(cap: f64, u: f64) -> (Model, Vec<Col>, Vec<Col>, Vec<Col>, Vec<Col>) {
    const ARCS: usize = 10; // 30 nonzeros in the capacity row, 10 targets: both gates clear
    let mut m = Model::new();
    let (mut ps, mut qs, mut ns, mut ys) = (Vec::new(), Vec::new(), Vec::new(), Vec::new());
    for _ in 0..ARCS {
        ps.push(m.add_col(0.0, u));
        qs.push(m.add_col(0.0, u));
        ns.push(m.add_col(0.0, u));
        ys.push(m.add_int_col(0.0, 1.0));
    }
    for i in 0..ARCS {
        // chain: n_i <= p_i and n_i <= q_i
        m.add_row(f64::NEG_INFINITY, 0.0, &[(ns[i], 1.0), (ps[i], -1.0)]);
        m.add_row(f64::NEG_INFINITY, 0.0, &[(ns[i], 1.0), (qs[i], -1.0)]);
        // variable upper bounds: p_i <= U·y_i, q_i <= U·y_i
        m.add_row(f64::NEG_INFINITY, 0.0, &[(ps[i], 1.0), (ys[i], -u)]);
        m.add_row(f64::NEG_INFINITY, 0.0, &[(qs[i], 1.0), (ys[i], -u)]);
    }
    let cap_terms: Vec<(Col, f64)> = ps
        .iter()
        .chain(qs.iter())
        .map(|&c| (c, 1.0))
        .chain(ns.iter().map(|&c| (c, -1.0)))
        .collect();
    m.add_row(f64::NEG_INFINITY, cap, &cap_terms);
    m.set_objective(&[(ps[0], 1.0)], Sense::Minimize);
    (m, ps, qs, ns, ys)
}

/// The fixture's separation point: ON the capacity row's face with every chain row tight,
/// the same posture qiu's root vertex is in (`c661` activity 48 against `b = 48`).
fn chain_point(
    m: &Model,
    ps: &[Col],
    qs: &[Col],
    ns: &[Col],
    ys: &[Col],
    cap: f64,
    u: f64,
) -> Vec<f64> {
    let share = cap / ps.len() as f64;
    let mut x = vec![0.0; m.num_cols()];
    for i in 0..ps.len() {
        x[ps[i].index()] = share;
        x[qs[i].index()] = share;
        x[ns[i].index()] = share;
        x[ys[i].index()] = share / u;
    }
    x
}

/// THE WALK REACHES THE SINGLE-NODE SET, AND THE THREE-STEP FAMILY DOES NOT.
///
/// This is the whole reason the separator exists, pinned on a model small enough to check by
/// hand: `separate_mir_agg` caps at `MIR_AGG_STEPS = 3` and its base-row gate wants a
/// FRACTIONAL INTEGER column in the row — the capacity row has no integer column at all — so
/// it cannot reach the aggregate however long it is given.
///
/// The DEFAULT-OFF half is asserted first, because that is the shipped posture: the family is
/// measured net-negative on qiu and must cost the default corpus nothing.
#[test]
fn chain_agg_reaches_the_single_node_set_where_the_three_step_walk_cannot() {
    const CAP: f64 = 5.0;
    const U: f64 = 4.0;
    let (m, ps, qs, ns, ys) = chain_fixture(CAP, U);
    let x = chain_point(&m, &ps, &qs, &ns, &ys, CAP, U);
    let _env_lock = ay_test_support::env::lock_env();
    assert!(
        separate_mir_chain_agg(&m, &x, m.num_rows(), 8).is_empty(),
        "the family is opt-in and must separate nothing unless asked"
    );
    let _on = crate::tune::activate_caller(crate::tune::Profile::EMPTY.with(
        crate::tune::Knob::ChainAgg,
        crate::tune::Setting::Flag(true),
    ));
    let cuts = separate_mir_chain_agg(&m, &x, m.num_rows(), 8);
    assert!(
        !cuts.is_empty(),
        "the chain walk separated nothing on its own fixture"
    );
    // Every emitted cut is violated at `x` -- `best_over_deltas` guarantees it, and a family
    // that returned satisfied rows would be pure freight.
    for c in &cuts {
        assert!(
            violation(c, &x) > 0.0,
            "chain-aggregated cut is not violated at the separation point"
        );
    }
    // The three-step pairwise family cannot get here.
    assert!(
        separate_mir_agg(&m, &x, m.num_rows(), 8).is_empty(),
        "separate_mir_agg reached the deep aggregate: the premise of this family is wrong"
    );
}

/// VALIDITY, by construction and by sampling. The walk adds `λ · (oriented partner <= rhs)`
/// with `λ > 0` to a `<=` aggregate and hands the result to `mir_from_row`, so no cut may
/// remove a point that satisfies every row and every integrality constraint. Sampled rather
/// than exhaustive because the fixture the family needs has 10 binaries and 30 continuous
/// columns; the sampler draws switches with a quarter-open bias (so the capacity row is
/// reachable rather than always violated) and flows on an eighth grid under them.
#[test]
fn chain_aggregated_cuts_never_remove_a_feasible_point() {
    let _env_lock = ay_test_support::env::lock_env();
    let _on = crate::tune::activate_caller(crate::tune::Profile::EMPTY.with(
        crate::tune::Knob::ChainAgg,
        crate::tune::Setting::Flag(true),
    ));
    let mut seed = 0xC4A1_2026_u64;
    let mut rnd = || {
        seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        seed >> 33
    };
    let mut total_cuts = 0usize;
    let mut total_points = 0usize;
    for case in 0..40 {
        let cap = 3.0 + (rnd() % 7) as f64;
        let u = 2.0 + (rnd() % 4) as f64;
        let (m, ps, qs, ns, ys) = chain_fixture(cap, u);
        let n = m.num_cols();
        // A separation point that puts the capacity row on its face.
        let share = cap / ps.len() as f64;
        let mut x = vec![0.0; n];
        for i in 0..ps.len() {
            x[ps[i].index()] = share;
            x[qs[i].index()] = share;
            x[ns[i].index()] = share * ((rnd() % 5) as f64 / 4.0);
            x[ys[i].index()] = share / u;
        }
        let cuts = separate_mir_chain_agg(&m, &x, m.num_rows(), 8);
        total_cuts += cuts.len();
        if cuts.is_empty() {
            continue;
        }
        for _ in 0..4000 {
            let mut p = vec![0.0f64; n];
            for i in 0..ps.len() {
                let y = u64::from(rnd() % 4 == 0) as f64;
                let (pi, qi) = if y > 0.5 {
                    ((rnd() % 9) as f64 * u / 8.0, (rnd() % 9) as f64 * u / 8.0)
                } else {
                    (0.0, 0.0)
                };
                let ni = (rnd() % 9) as f64 * pi.min(qi) / 8.0;
                p[ys[i].index()] = y;
                p[ps[i].index()] = pi;
                p[qs[i].index()] = qi;
                p[ns[i].index()] = ni;
            }
            // Keep only points the MODEL accepts -- every row, in the model's own frame.
            let feasible = (0..m.num_rows()).all(|r| {
                let (coeffs, lo, hi) = m.row(Row(r as u32));
                let act: f64 = coeffs.iter().map(|&(c, a)| a * p[c as usize]).sum::<f64>();
                act >= lo - 1e-9 && act <= hi + 1e-9
            });
            if !feasible {
                continue;
            }
            total_points += 1;
            for cut in &cuts {
                let act: f64 = cut.coeffs.iter().map(|&(c, a)| a * p[c.index()]).sum();
                assert!(
                    act <= cut.ub + 1e-6 && act >= cut.lb - 1e-6,
                    "case {case}: a chain-aggregated cut deleted the feasible point {p:?} \
                     -- activity {act} outside [{}, {}]",
                    cut.lb,
                    cut.ub
                );
            }
        }
    }
    assert!(
        total_cuts > 0,
        "no chain-aggregated cut was ever separated: the guard is vacuous"
    );
    assert!(
        total_points > 1000,
        "the sampler found only {total_points} feasible points: the guard is thin"
    );
}

/// THE CHEAP GATE. A model with no wide row must not pay for the chain index, the VUB map or
/// the walk -- 16 of the 19 corpus instances are in exactly that position.
#[test]
fn chain_agg_declines_on_a_model_with_no_wide_row() {
    let _env_lock = ay_test_support::env::lock_env();
    let _on = crate::tune::activate_caller(crate::tune::Profile::EMPTY.with(
        crate::tune::Knob::ChainAgg,
        crate::tune::Setting::Flag(true),
    ));
    let mut m = Model::new();
    let a = m.add_col(0.0, 10.0);
    let b = m.add_col(0.0, 10.0);
    let y = m.add_int_col(0.0, 1.0);
    m.add_row(f64::NEG_INFINITY, 0.0, &[(a, 1.0), (b, -1.0)]);
    m.add_row(f64::NEG_INFINITY, 0.0, &[(b, 1.0), (y, -4.0)]);
    m.add_row(f64::NEG_INFINITY, 3.0, &[(a, 1.0), (b, 1.0)]);
    m.set_objective(&[(a, 1.0)], Sense::Minimize);
    let x = vec![1.5, 1.5, 0.375];
    assert!(separate_mir_chain_agg(&m, &x, m.num_rows(), 8).is_empty());
}
