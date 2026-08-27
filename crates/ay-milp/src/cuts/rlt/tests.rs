// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared deterministic RLT soundness fixtures.

use super::*;
use crate::model::Sense;

/// A deterministic LCG — no `rand` dependency, and the same 500 cases every run.
struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> i64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (self.0 >> 33) as i64
    }
    fn upto(&mut self, n: i64) -> i64 {
        self.next().rem_euclid(n)
    }
}

/// THE GUARD. Every RLT cut must be valid for the INTEGER HULL, so on a random model carrying
/// the structure the family keys off, enumerate every integer point of the box, keep the ones
/// the MODEL admits, and assert each emitted cut holds at all of them.
///
/// Deliberate properties, each of which is there because leaving it out makes the guard weaker
/// than the derivation it is checking:
///
/// * The generator emits VUB rows (`a·x − a·u·y ≤ 0`), packing rows (the conflict source) and
///   generic knapsack rows, so both exact substitutions and both branches actually fire.
/// * Column boxes are NON-INTEGRAL where the column is continuous (`l = 1/2`, `u = 5/2`). The
///   McCormick faces carry `l_j` and `u_j` into the coefficients, and the wrong-answer bug this
///   crate already shipped was exactly "a bound was assumed integral". A continuous column is
///   swept over its integer grid AND its half-integer grid so the enumeration is not blind to
///   the face that touches it.
/// * `x*` is random, including integral values, so face selection is exercised in every
///   configuration rather than the one the LP happens to produce.
/// * `fired > 0` — a separator that returns nothing passes any validity assertion, which is
///   the definition of not guarding.
fn random_rlt_case(
    rng: &mut Lcg,
    nbin: usize,
    ncont: usize,
) -> (Model, Vec<(Vec<f64>, f64, f64)>, Vec<f64>, Vec<Vec<f64>>) {
    let mut m = Model::new();
    let mut cols = Vec::new();
    for _ in 0..nbin {
        cols.push(m.add_binary_col());
    }
    // Continuous columns on a NON-INTEGRAL box: [1/2, 5/2].
    for _ in 0..ncont {
        cols.push(m.add_col(0.5, 2.5));
    }
    let n = nbin + ncont;
    // The value grid each column is swept over: binaries {0,1}, continuous the half-integer
    // grid of [1/2, 5/2] (its vertices and the integer points between them).
    let grids: Vec<Vec<f64>> = (0..n)
        .map(|j| {
            if j < nbin {
                vec![0.0, 1.0]
            } else {
                vec![0.5, 1.0, 1.5, 2.0, 2.5]
            }
        })
        .collect();

    let mut rows: Vec<(Vec<f64>, f64, f64)> = Vec::new();
    let push = |m: &mut Model, a: Vec<f64>, lo: f64, hi: f64, rows: &mut Vec<_>| {
        let terms: Vec<(Col, f64)> = cols
            .iter()
            .zip(&a)
            .filter(|(_, &v)| v != 0.0)
            .map(|(&c, &v)| (c, v))
            .collect();
        if terms.len() < 2 {
            return;
        }
        m.add_row(lo, hi, &terms);
        rows.push((a, lo, hi));
    };

    // 1-2 VUB rows: `a·x_j − a·u·y ≤ 0` with y binary. u is chosen so u ≥ up_j, which is what
    // makes it a genuine bound rather than an extra restriction — but the derivation does not
    // require that, so sometimes emit a TIGHTER one too.
    for _ in 0..=rng.upto(2) {
        let j = rng.upto(n as i64) as usize;
        let y = rng.upto(nbin as i64) as usize;
        if j == y {
            continue;
        }
        let a = 1.0 + rng.upto(3) as f64;
        let u = if rng.upto(2) == 0 {
            3.0
        } else {
            1.0 + rng.upto(3) as f64
        };
        let mut row = vec![0.0; n];
        row[j] = a;
        row[y] = -a * u;
        push(&mut m, row, f64::NEG_INFINITY, 0.0, &mut rows);
    }
    // 1-2 packing rows over binaries: the conflict source.
    for _ in 0..=rng.upto(2) {
        let mut row = vec![0.0; n];
        let mut k = 0;
        for j in 0..nbin {
            if rng.upto(2) == 0 {
                row[j] = 1.0;
                k += 1;
            }
        }
        if k >= 2 {
            push(&mut m, row, f64::NEG_INFINITY, 1.0, &mut rows);
        }
    }
    // 1-3 generic rows, mixed signs, both orientations and equalities.
    for _ in 0..=rng.upto(3) {
        let a: Vec<f64> = (0..n).map(|_| (rng.upto(7) - 3) as f64).collect();
        let hi = rng.upto(8) as f64;
        match rng.upto(3) {
            0 => push(&mut m, a, f64::NEG_INFINITY, hi, &mut rows),
            1 => push(&mut m, a, -hi, f64::INFINITY, &mut rows),
            _ => push(&mut m, a, hi, hi, &mut rows),
        }
    }
    m.set_objective(&[(cols[0], 1.0)], Sense::Minimize);
    let x: Vec<f64> = (0..n)
        .map(|j| {
            if j < nbin {
                rng.upto(11) as f64 / 10.0
            } else {
                0.5 + rng.upto(21) as f64 / 10.0
            }
        })
        .collect();
    (m, rows, x, grids)
}

/// Sweep every point of the grid, keep the model-feasible ones, and check every cut.
fn assert_cuts_keep_every_feasible_point(
    rows: &[(Vec<f64>, f64, f64)],
    grids: &[Vec<f64>],
    cuts: &[Cut],
    label: &str,
) {
    let n = grids.len();
    let total: usize = grids.iter().map(|g| g.len()).product();
    for code in 0..total {
        let mut p = vec![0.0f64; n];
        let mut t = code;
        for j in 0..n {
            p[j] = grids[j][t % grids[j].len()];
            t /= grids[j].len();
        }
        let feasible = rows.iter().all(|(a, lo, hi)| {
            let act: f64 = a.iter().zip(&p).map(|(&c, &v)| c * v).sum();
            act >= lo - 1e-9 && act <= hi + 1e-9
        });
        if !feasible {
            continue;
        }
        for c in cuts {
            let act: f64 = c.coeffs.iter().map(|&(col, a)| a * p[col.index()]).sum();
            assert!(
                act <= c.ub + 1e-6,
                "{label}: an RLT cut deleted the feasible integer point {p:?} \
                 (activity {act} > bound {})",
                c.ub
            );
            assert!(
                c.lb.is_infinite(),
                "{label}: emit_le_cut must produce a one-sided `≤` cut"
            );
        }
    }
}

mod soundness;
