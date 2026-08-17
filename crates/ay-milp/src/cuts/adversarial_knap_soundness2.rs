// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact qnet1-shaped c-MIR complementation regression.

use super::*;
use crate::model::Sense;

/// The qnet1 capacity row at its own magnitudes: `Σ w_j·y_j − 56·b − 1344·g <= 0`, `y` binary,
/// `b ∈ [0,11]`, `g ∈ [0,4]`, with a second row so the aggregation walk has a partner and a
/// continuous column so the family's self-gate opens. Every one of the 16·12·5 integer points
/// is enumerated (the continuous column is bounded and enters no row, so its endpoints suffice).
#[test]
fn adv_qnet1_capacity_shape_is_valid_under_knapsack() {
    for &(w, sep) in &[
        (
            [56.0f64, 112.0, 336.0, 1344.0],
            [0.4f64, 0.6, 0.3, 0.2, 0.7, 0.1],
        ),
        ([168.0, 224.0, 560.0, 896.0], [0.9, 0.1, 0.5, 0.5, 2.5, 0.9]),
        ([56.0, 1344.0, 1344.0, 56.0], [0.2, 0.8, 0.8, 0.2, 1.5, 0.5]),
    ] {
        let mut m = Model::new();
        let y: Vec<Col> = (0..4).map(|_| m.add_binary_col()).collect();
        let b = m.add_int_col(0.0, 11.0);
        let g = m.add_int_col(0.0, 4.0);
        let s = m.add_col(0.0, 2.0);
        let mut terms: Vec<(Col, f64)> = y.iter().zip(&w).map(|(&c, &a)| (c, a)).collect();
        terms.push((b, -56.0));
        terms.push((g, -1344.0));
        m.add_row(f64::NEG_INFINITY, 0.0, &terms);
        // A flow-conservation partner for the aggregation walk.
        m.add_row(
            1.0,
            1.0,
            &[(y[0], 1.0), (y[1], 1.0), (y[2], 1.0), (y[3], 1.0)],
        );
        m.set_objective(&[(b, 1.0), (g, 1.0)], Sense::Minimize);
        let x: Vec<f64> = vec![sep[0], sep[1], sep[2], sep[3], sep[4], sep[5], 0.5];
        let _ = s;

        let mut cuts = Vec::new();
        for knap in [false, true] {
            knap_scope(knap, || {
                cuts.extend(separate_mir(&m, &x, m.num_rows(), 16));
                cuts.extend(separate_strongcg(&m, &x, m.num_rows(), 16));
                cuts.extend(separate_mir_agg(&m, &x, m.num_rows(), 16));
            });
        }
        eprintln!("qnet1 shape w={w:?}: {} cuts", cuts.len());

        for y0 in 0..2 {
            for y1 in 0..2 {
                for y2 in 0..2 {
                    for y3 in 0..2 {
                        for bv in 0..12 {
                            for gv in 0..5 {
                                for sv in [0.0f64, 2.0] {
                                    let p = [
                                        y0 as f64, y1 as f64, y2 as f64, y3 as f64, bv as f64,
                                        gv as f64, sv,
                                    ];
                                    let cap: f64 =
                                        w.iter().zip(&p[..4]).map(|(&a, &v)| a * v).sum::<f64>()
                                            - 56.0 * p[4]
                                            - 1344.0 * p[5];
                                    if cap > 1e-9 {
                                        continue;
                                    }
                                    if (p[0] + p[1] + p[2] + p[3] - 1.0).abs() > 1e-9 {
                                        continue;
                                    }
                                    for c in &cuts {
                                        let act: f64 =
                                            c.coeffs.iter().map(|&(j, a)| a * p[j.index()]).sum();
                                        let tol = 1e-6
                                            * c.coeffs
                                                .iter()
                                                .map(|&(_, a)| a.abs())
                                                .fold(1.0, f64::max)
                                            * p.iter().map(|v| v.abs()).fold(1.0, f64::max);
                                        assert!(
                                            act <= c.ub + tol && act >= c.lb - tol,
                                            "qnet1-shape cut deleted feasible point {p:?}: \
                                             activity {act} outside [{}, {}] for {:?}",
                                            c.lb,
                                            c.ub,
                                            c.coeffs
                                        );
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
