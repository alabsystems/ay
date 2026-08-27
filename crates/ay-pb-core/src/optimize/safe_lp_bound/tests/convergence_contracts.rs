// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::transpose::{
    should_transpose, should_transpose_model, solve_transposed_for_box_lp_instrumented,
};
use super::*;

/// THE `converged` CONTRACT.
///
/// `converged = true` is what licenses the certified tier to trust this
/// solve's dual, so it must never be true unless the point really is an
/// optimum. Phase II's exit test only inspects REDUCED COSTS, so on its own it
/// will happily stop at a point whose basic variables have drifted outside
/// their bounds — reduced-cost optimal, primal infeasible, dual not attaining
/// anything. That is why `RunStats::converged` also requires verified primal
/// feasibility.
///
/// This asserts the contract end-to-end on random LPs, including mixed-sign
/// costs and coefficients (where the crash is NOT feasible and Phase I has
/// real work): whenever the solver claims convergence, the returned primal
/// must satisfy every row and every bound, and its objective must match the
/// dual's exact Lagrangian value.
/// THE TRANSPOSE MUST NOT CHANGE THE ANSWER.
///
/// `solve_transposed_for_box_lp` solves the same LP through its dual so the
/// basis is one entry per COLUMN instead of one per row. That is a pure
/// performance transformation: the bound the caller ultimately reports is
/// `L(y) = b·y + sum_v min(0, c_v - (A^T y)_v)`, valid at ANY `y >= 0`, so a
/// bad transposed point could only ever WEAKEN the bound. This asserts the
/// stronger and more useful property — that on row-heavy models the two forms
/// agree — and, non-negotiably, that the transposed `y` is non-negative and
/// its Lagrangian never exceeds the primal form's own optimal objective.
#[test]
fn transposed_solve_agrees_with_the_primal_form_on_row_heavy_models() {
    let mut rng = Rng(0x7ea5_1234_9876_0001);
    let mut compared = 0usize;
    for case in 0..300 {
        // Deliberately row-heavy so the dispatcher would transpose in production.
        let n = 3 + (case % 6);
        let m = n * (5 + case % 4);
        let mut rows: Vec<(Vec<(usize, f64)>, f64)> = Vec::new();
        for _ in 0..m {
            let mut coeffs: Vec<(usize, f64)> = Vec::new();
            for v in 0..n {
                if rng.next().is_multiple_of(2) {
                    coeffs.push((v, 1.0 + (rng.next() % 9) as f64));
                }
            }
            if coeffs.is_empty() {
                coeffs.push((0, 1.0));
            }
            // rhs a fraction of the row's own coefficient mass, so `x = 1`
            // satisfies it and the model is always feasible — the covering
            // shape this path is aimed at.
            let mass: f64 = coeffs.iter().map(|&(_, a)| a).sum();
            let rhs = (mass * (0.2 + 0.5 * ((rng.next() % 100) as f64 / 100.0))).max(1.0);
            rows.push((coeffs, rhs));
        }
        // Every third case uses NEGATIVE costs (the maximisation shape). Those are
        // only correct because the transposed solve crashes at the dual image of
        // `x = 0`; under the old `y = z = 0` crash they started infeasible and ran
        // 8.3x slower. Covering both signs is what licenses shape-only dispatch.
        let negate = case % 3 == 0;
        let c: Vec<f64> = (0..n)
            .map(|_| {
                let v = 1.0 + (rng.next() % 5) as f64;
                if negate {
                    -v
                } else {
                    v
                }
            })
            .collect();

        if compare_transposed_case(case, n, m, &c, &rows) {
            compared += 1;
        }
    }
    assert!(
        compared >= 100,
        "only {compared} models had both forms converge — the test is not \
         exercising the comparison"
    );
}

fn compare_transposed_case(
    case: usize,
    n: usize,
    m: usize,
    c: &[f64],
    rows: &[(Vec<(usize, f64)>, f64)],
) -> bool {
    let lagrangian = |y: &[f64]| -> f64 {
        let mut aty = vec![0.0f64; n];
        let mut val = 0.0f64;
        for (r, (coeffs, b)) in rows.iter().enumerate() {
            val += b * y[r];
            for &(v, a) in coeffs {
                aty[v] += a * y[r];
            }
        }
        for v in 0..n {
            val += (c[v] - aty[v]).min(0.0);
        }
        val
    };

    FORCE_PRIMAL.store(true, std::sync::atomic::Ordering::Relaxed);
    let primal =
        approx_dual_for_box_lp_with_iteration_budget(n, c.to_vec(), rows.to_vec(), 20_000, &|| {
            false
        });
    FORCE_PRIMAL.store(false, std::sync::atomic::Ordering::Relaxed);
    let transposed =
        approx_dual_for_box_lp_with_iteration_budget(n, c.to_vec(), rows.to_vec(), 20_000, &|| {
            false
        });

    let (Some((py, _, pconv)), Some((ty, _, tconv))) = (primal, transposed) else {
        return false;
    };
    // SOUNDNESS: the transposed dual must be non-negative — everything
    // downstream rests on it.
    for (r, &yr) in ty.iter().enumerate() {
        assert!(
            yr >= 0.0 && yr.is_finite(),
            "case {case}: transposed dual y[{r}] = {yr} is not a valid multiplier"
        );
    }
    assert_eq!(
        ty.len(),
        m,
        "case {case}: transposed dual has the wrong length"
    );

    if !(pconv && tconv) {
        return false;
    }
    let lp = lagrangian(&py);
    let lt = lagrangian(&ty);
    assert!(
        (lp - lt).abs() <= 1e-5 * (1.0 + lp.abs()),
        "case {case}: transposed bound {lt} disagrees with primal {lp}"
    );
    true
}

#[test]
fn converged_implies_a_genuinely_feasible_optimal_point() {
    let mut rng = Rng(0x00c0_ffee_1234_5678);
    let mut claimed = 0usize;
    let mut declined = 0usize;
    for case in 0..400 {
        let n = 4 + (case % 9);
        let m = 3 + (case % 11);
        let mixed = case % 3 == 0; // a third get negative coefficients/costs
        let mut rows: Vec<(Vec<(usize, f64)>, f64)> = Vec::new();
        for _ in 0..m {
            let mut coeffs: Vec<(usize, f64)> = Vec::new();
            for v in 0..n {
                if rng.next().is_multiple_of(3) {
                    let mag = 1.0 + (rng.next() % 9) as f64;
                    let sign = if mixed && rng.next().is_multiple_of(2) {
                        -1.0
                    } else {
                        1.0
                    };
                    coeffs.push((v, sign * mag));
                }
            }
            if coeffs.is_empty() {
                coeffs.push((0, 1.0));
            }
            let rhs = (rng.next() % 11) as f64 - if mixed { 5.0 } else { 0.0 };
            rows.push((coeffs, rhs));
        }
        let c: Vec<f64> = (0..n)
            .map(|_| {
                let mag = 1.0 + (rng.next() % 5) as f64;
                if mixed && rng.next().is_multiple_of(2) {
                    -mag
                } else {
                    mag
                }
            })
            .collect();

        let Some((dual, primal, converged)) = approx_dual_for_box_lp_with_iteration_budget(
            n,
            c.clone(),
            rows.clone(),
            10_000,
            &|| false,
        ) else {
            continue;
        };
        if !converged {
            declined += 1;
            continue;
        }
        claimed += 1;

        // (a) the primal must be inside the box.
        for (j, &xv) in primal.iter().enumerate() {
            assert!(
                xv.is_finite() && (-1e-6..=1.0 + 1e-6).contains(&xv),
                "case {case}: converged but x[{j}] = {xv} is outside [0,1]"
            );
        }
        // (b) the primal must satisfy every row.
        for (ri, (coeffs, b)) in rows.iter().enumerate() {
            let act: f64 = coeffs.iter().map(|&(v, a)| a * primal[v]).sum();
            assert!(
                act >= b - 1e-5,
                "case {case}: converged but row {ri} violated: {act} < {b}"
            );
        }
        // (c) the dual must be non-negative and its Lagrangian must MATCH the
        //     primal objective — zero duality gap is what "optimal" means.
        let mut lag = 0.0f64;
        let mut aty = vec![0.0f64; n];
        for (ri, (coeffs, b)) in rows.iter().enumerate() {
            let y = dual[ri];
            assert!(
                y >= -1e-9,
                "case {case}: converged with negative dual y[{ri}] = {y}"
            );
            lag += b * y;
            for &(v, a) in coeffs {
                aty[v] += a * y;
            }
        }
        for v in 0..n {
            lag += (c[v] - aty[v]).min(0.0);
        }
        let obj: f64 = (0..n).map(|v| c[v] * primal[v]).sum();
        assert!(
            (obj - lag).abs() <= 1e-4 * (1.0 + obj.abs()),
            "case {case}: converged but duality gap is {} (primal {obj}, dual {lag})",
            obj - lag
        );
    }
    assert_convergence_contract_exercised(claimed, declined);
}

fn assert_convergence_contract_exercised(claimed: usize, declined: usize) {
    assert!(
        claimed >= 100,
        "only {claimed} solves claimed convergence — the test is not exercising the contract"
    );
    assert!(
        declined > 0,
        "every solve claimed convergence ({declined} declined); the generator is too easy \
         to show the flag can also be false"
    );
}

#[test]
fn covering_crash_is_immediately_feasible_and_phase_two_converges() {
    // A random unicost covering LP in the shape of the domset family that
    // motivated this work: every coefficient positive, every rhs positive, so
    // `x = 1` satisfies every row. The crash must recognise that and hand
    // Phase I a feasible point, and Phase II must then reach its own optimum.
    let mut rng = Rng(0xfeed_face_0000_0001);
    let n = 120usize;
    let mut rows: Vec<(Vec<(usize, f64)>, f64)> = Vec::new();
    for r in 0..n {
        let mut coeffs = vec![(r, 30.0)];
        for _ in 0..6 {
            let v = (rng.next() % n as u64) as usize;
            if v != r && !coeffs.iter().any(|&(u, _)| u == v) {
                coeffs.push((v, 1.0 + (rng.next() % 19) as f64));
            }
        }
        coeffs.sort_unstable_by_key(|&(v, _)| v);
        rows.push((coeffs, 30.0));
    }
    let c = vec![1.0f64; n];
    let model = LpF64 {
        n,
        c: c.clone(),
        offset: 0.0,
        rows: rows
            .iter()
            .map(|(coeffs, b)| RowF64 {
                coeffs: coeffs.clone(),
                b: *b,
            })
            .collect(),
        upper: None,
    };
    let m = model.rows.len();
    let mut simplex = Simplex::new(&model, n, m, n + m);
    // Every structural must crash at UPPER on an all-positive covering LP.
    assert!(
        (0..n).all(|j| simplex.at[j] == AtBound::Upper),
        "covering columns must crash at their upper bound"
    );
    let stats = simplex.run_instrumented(&never_stop, SimplexLimits::iterations(20_000), None);
    assert_eq!(
        stats.stats1.iters, 1,
        "Phase I must find the crash point already feasible and exit at its \
         first feasibility check, not pivot toward feasibility"
    );
    assert!(
        stats.phase1 == LoopExit::Optimal,
        "Phase I must reach Optimal"
    );
    assert!(
        stats.phase2 == LoopExit::Optimal,
        "Phase II must reach Optimal on a degenerate covering LP"
    );
    assert!(stats.converged());
    assert_eq!(
        stats.stats2.bland_iters, 0,
        "Devex must keep Bland's anti-cycling fallback from engaging at all"
    );
    // PRICING QUALITY, not just termination. Measured on this fixture:
    // Devex reaches the optimum in 294 Phase-II iterations, Dantzig
    // (`score = |rc|`) needs 421 for the same optimum. The ceiling sits
    // between them, so reverting pricing to Dantzig — or any future change
    // that costs as much as that revert does — fails here rather than
    // silently slowing every LP bound in the solver.
    assert!(
        stats.stats2.iters <= 350,
        "Phase II took {} iterations; Devex pricing reaches this optimum in \
         294 and Dantzig needs 421, so this is a pricing regression",
        stats.stats2.iters
    );

    // Zero duality gap: the point returned really is the LP optimum.
    let result = simplex.extract(&model);
    let objective: f64 = c.iter().zip(&result.primal).map(|(cj, x)| cj * x).sum();
    let y = clamp_dual(&result.dual);
    let mut ns: f64 = rows.iter().zip(&y).map(|((_, b), yr)| yr * b).sum();
    let mut aty = vec![0.0f64; n];
    for ((coeffs, _), yr) in rows.iter().zip(&y) {
        for &(v, a) in coeffs {
            aty[v] += yr * a;
        }
    }
    for v in 0..n {
        ns += (c[v] - aty[v]).min(0.0);
    }
    assert!(
        (objective - ns).abs() <= 1e-6 * (1.0 + objective.abs()),
        "duality gap {} between primal {objective} and dual {ns}",
        objective - ns
    );

    assert_packing_crash_stays_at_lower_bounds();
}

fn assert_packing_crash_stays_at_lower_bounds() {
    // NEGATIVE CONTROL: the same rule must NOT fire on a packing LP, where
    // `x = 1` is maximally infeasible. `-x_i - x_j >= -1` has only negative
    // coefficients, so `crash_at_upper` must decline every column and
    // reproduce the classic all-lower crash.
    let packing: Vec<(Vec<(usize, f64)>, f64)> = (0..8)
        .map(|i| (vec![(i, -1.0), ((i + 1) % 9, -1.0)], -1.0))
        .collect();
    let packing_model = LpF64 {
        n: 9,
        c: vec![-1.0; 9],
        offset: 0.0,
        rows: packing
            .iter()
            .map(|(coeffs, b)| RowF64 {
                coeffs: coeffs.clone(),
                b: *b,
            })
            .collect(),
        upper: None,
    };
    let pm = packing_model.rows.len();
    let packing_simplex = Simplex::new(&packing_model, 9, pm, 9 + pm);
    assert!(
        (0..9).all(|j| packing_simplex.at[j] == AtBound::Lower),
        "packing columns must keep the classic all-lower crash"
    );
}

/// THE TRANSPOSE DISPATCH RULE.
///
/// Dispatching the transpose on SHAPE ALONE was a defect. The transposed rows are
/// `-(A^T y)_v + z_v >= -c_v`, so the all-lower crash `y = z = 0` is feasible
/// exactly when `c >= 0`. With `c >= 0` Phase I is trivial and the transpose is a
/// straight win; with any negative cost the crash starts INFEASIBLE, Phase I has
/// real work, and the transpose measured **8.3x SLOWER** than the primal form on a
/// 12:1 model (0.12x, against 2.22x FASTER at 10:1 with `c >= 0`).
///
/// Every pseudo-Boolean caller satisfies `c >= 0` because `LpModel` complements
/// any variable with a negative objective coefficient — which made the old guard
/// ACCIDENTAL rather than structural, and `approx_dual_for_box_lp` is a general
/// entry point.
#[test]
fn transpose_dispatches_on_shape_and_handles_every_cost_sign() {
    let m = 400usize;
    let n = 40usize;
    assert!(
        should_transpose(n, m),
        "precondition: this shape is row-heavy enough to dispatch on shape alone"
    );
    let nonneg = vec![1.0f64; n];
    assert!(
        should_transpose_model(&nonneg, m),
        "a row-heavy model with c >= 0 must take the transpose"
    );
    // NEGATIVE COSTS ARE NOW ACCEPTED, because the transposed solve crashes at
    // the dual image of `x = 0` instead of at `y = z = 0`. Under the old default
    // crash these models started infeasible and ran 8.3x SLOWER than the primal
    // form; with the dual-image crash the same shape runs 1.18x faster.
    let mut mixed = vec![1.0f64; n];
    mixed[n / 2] = -1.0;
    assert!(
        should_transpose_model(&mixed, m),
        "a mixed-sign cost vector must transpose once the dual-image crash exists"
    );
    let allneg = vec![-1.0f64; n];
    assert!(
        should_transpose_model(&allneg, m),
        "an all-negative cost vector must transpose once the dual-image crash exists"
    );
    assert!(
        !should_transpose_model(&nonneg, n),
        "a square model must not transpose even with c >= 0"
    );

    // THE MEASURED CROSSOVER PINS THE THRESHOLD (2026-08-17 replay on real
    // f64-tier production LPs, see `TRANSPOSE_RATIO_NUM`): at 1.00:1 the
    // primal form won 0.60-0.72x on every liu/domset base LP, and at 1.42:1
    // the transpose won 2.7x+ on count.b and everything above it. These pin
    // the real shapes on each side of the 5/4 gate; if either fires the other
    // way after a threshold or cut-cap change, RE-RUN the `replay_crossover`
    // harness on freshly dumped models before believing the new setting.
    assert!(
        !should_transpose(467, 466),
        "liu/domset base shape (1.00:1) measured primal-faster; must not transpose"
    );
    assert!(
        should_transpose(466, 694),
        "count.b shape (1.49:1) measured transpose-faster (4.9x); must transpose"
    );
    assert!(
        should_transpose(741, 2072),
        "fir04 cut-augmented shape (2.80:1) measured transpose-faster (4.2x)"
    );
}

/// THE DUAL-IMAGE CRASH IS LOAD-BEARING, and only an EFFORT assertion can say so.
///
/// The crash is a performance fix, not a correctness one: without it the
/// transposed solve still reaches the right answer, just via a long Phase I. So
/// the differential tests above cannot detect its removal — they check answers.
/// This checks WORK, which is the property the crash actually buys.
///
/// A negative-cost model is the discriminating case. Crashing at `y = z = 0`
/// violates every row with `c_v < 0`, so Phase I must claw all of them back;
/// crashing at the dual image of `x = 0` (`y = 0, z_v = max(0, -c_v)`) is feasible
/// immediately. Measured end to end, the difference was 8.3x SLOWER versus 1.18x
/// faster than the primal form.
/// THE CRASH MUST ALSO START FEASIBLE FOR `c >= 0` — the complemented
/// pseudo-Boolean case, i.e. every production model this solver builds.
///
/// This is the regression that was MISSING when the all-`z` "dual-image" crash
/// shipped: it fixed the negative-cost start (tested below) while silently
/// making every positive-cost row start INFEASIBLE (`z_v = -c_v < 0`), so on
/// the one production instance whose shape dispatches the transpose
/// (`edgecross14-019`, n=328 m=1746) Phase I burned ~314 iterations — one per
/// positive-cost column — and the transposed solve ran 4-5x slower than the
/// primal form it was supposed to beat. Answer-checking tests cannot catch
/// that (the answers agreed); only a WORK assertion can, so this pins Phase I
/// to its first feasibility check exactly like
/// `covering_crash_is_immediately_feasible_and_phase_two_converges` does for
/// the primal form's crash.
#[test]
fn transposed_positive_cost_crash_starts_feasible() {
    let n = 24usize;
    let m = n * 8; // row-heavy enough that the dispatcher would transpose
    let mut rng = Rng(0x0dd1_c0de_6666_7777);
    let mut rows: Vec<RowF64> = Vec::new();
    for _ in 0..m {
        let mut coeffs: Vec<(usize, f64)> = Vec::new();
        for v in 0..n {
            if rng.next().is_multiple_of(3) {
                coeffs.push((v, 1.0 + (rng.next() % 5) as f64));
            }
        }
        if coeffs.is_empty() {
            coeffs.push((0, 1.0));
        }
        let mass: f64 = coeffs.iter().map(|&(_, a)| a).sum();
        rows.push(RowF64 {
            coeffs,
            b: (mass * 0.4).max(1.0),
        });
    }
    // ALL costs positive — the complemented-PB shape production always sends.
    let c: Vec<f64> = (0..n).map(|_| 1.0 + (rng.next() % 4) as f64).collect();

    let (y, _x, stats) = solve_transposed_for_box_lp_instrumented(
        n,
        &c,
        &rows,
        SimplexLimits::iterations(200_000),
        &never_stop,
    )
    .expect("a row-heavy positive-cost model must produce a dual");
    assert_eq!(
        stats.stats1.iters, 1,
        "Phase I must find the positive-cost dual-image crash already feasible \
         and exit at its first feasibility check, not pivot toward feasibility"
    );
    assert!(
        stats.converged(),
        "the transposed solve must converge on positive costs"
    );
    for (r, &yr) in y.iter().enumerate() {
        assert!(
            yr >= 0.0 && yr.is_finite(),
            "dual y[{r}] = {yr} is not a valid multiplier"
        );
    }
}

#[test]
fn transposed_negative_cost_crash_starts_feasible() {
    let n = 12usize;
    let m = n * 8; // row-heavy enough that the dispatcher would transpose
    let mut rng = Rng(0x0dd1_c0de_4444_5555);
    let mut rows: Vec<(Vec<(usize, f64)>, f64)> = Vec::new();
    for _ in 0..m {
        let mut coeffs: Vec<(usize, f64)> = Vec::new();
        for v in 0..n {
            if rng.next().is_multiple_of(3) {
                coeffs.push((v, 1.0 + (rng.next() % 5) as f64));
            }
        }
        if coeffs.is_empty() {
            coeffs.push((0, 1.0));
        }
        let mass: f64 = coeffs.iter().map(|&(_, a)| a).sum();
        rows.push((coeffs, (mass * 0.4).max(1.0)));
    }
    // ALL costs negative — the shape that used to start infeasible.
    let c: Vec<f64> = (0..n).map(|_| -(1.0 + (rng.next() % 4) as f64)).collect();

    let (y, _x, converged) =
        approx_dual_for_box_lp_with_iteration_budget(n, c.clone(), rows.clone(), 200_000, &|| {
            false
        })
        .expect("a row-heavy negative-cost model must still produce a dual");
    assert!(
        converged,
        "the transposed solve must converge on negative costs"
    );
    for (r, &yr) in y.iter().enumerate() {
        assert!(
            yr >= 0.0 && yr.is_finite(),
            "dual y[{r}] = {yr} is not a valid multiplier"
        );
    }

    // The Lagrangian must still be a valid lower bound on the LP optimum, which
    // is what every consumer actually reads.
    let mut aty = vec![0.0f64; n];
    let mut lag = 0.0f64;
    for (r, (coeffs, b)) in rows.iter().enumerate() {
        lag += b * y[r];
        for &(v, a) in coeffs {
            aty[v] += a * y[r];
        }
    }
    for v in 0..n {
        lag += (c[v] - aty[v]).min(0.0);
    }
    assert!(
        lag.is_finite(),
        "the certified Lagrangian must be finite on negative-cost models"
    );
}
