// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Measure the W2 product — `LpSession::rigorous_bound` (the Neumaier–Shcherbina
//! fast lane) — against HiGHS on the SAME single-column bound LP, so gate G1
//! ("geomean solve time <= HiGHS on the triangle-LP stream") is checkable by
//! something that is not ay. Prints the rigorous bound alongside the time: a
//! bound that is fast because it is loose or wrong is not a bound, so
//! `W2_DUMP=<path>` emits the identical LP in CPLEX-LP form for HiGHS.
//!
//! ```text
//! W2_DUMP=/tmp/w2.lp cargo run --release -p ay-milp --example w2_speed -- 200 150 7
//! ```

use std::fmt::Write as _;
use std::time::Instant;

use ay_milp::{Col, LpSession, Model, Outcome, Row, Sense, SolveOpts};

struct Rng(u64);
impl Rng {
    fn next_u32(&mut self) -> u32 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (self.0 >> 33) as u32
    }
    fn coeff(&mut self) -> f64 {
        f64::from(self.next_u32() % 9) - 4.0
    }
}

/// A W2-shaped LP: bound an "output neuron" `x0` DEFINED by a linear
/// combination of constrained "input" columns. `x0 ∈ [−1e6, 1e6]`; inputs
/// `x1..x{n-1} ∈ [0, 10]`; each of `m` RANGE rows `a·inputs ∈ [c − r, c + r]`
/// is centred on the interior `input* = 5` (so `input* = 5` is strictly
/// feasible); and one equality `x0 = w·inputs` ties the neuron to the inputs.
/// `min x0` is then a non-trivial rational — a vertex of the input polytope,
/// with a basis-determinant denominator, which is exactly what makes the exact
/// rim slow and the NS float lane fast.
fn build(n: usize, m: usize, seed: u64) -> (Model, Vec<Col>, Vec<Row>) {
    let mut rng = Rng(seed);
    let mut model = Model::new();
    let x0 = model.add_col(-1.0e6, 1.0e6);
    let inputs: Vec<Col> = (1..n).map(|_| model.add_col(0.0, 10.0)).collect();
    let mut rows = Vec::new();
    for _ in 0..m {
        let terms: Vec<(Col, f64)> = inputs
            .iter()
            .filter_map(|&c| {
                let a = rng.coeff();
                (a != 0.0).then_some((c, a))
            })
            .collect();
        if terms.is_empty() {
            continue;
        }
        let center: f64 = terms.iter().map(|&(_, a)| a * 5.0).sum();
        let r = f64::from(rng.next_u32() % 8) + 1.0;
        rows.push(model.add_row(center - r, center + r, &terms));
    }
    // x0 − w·inputs = 0.
    let mut eq = vec![(x0, 1.0)];
    for &c in &inputs {
        let w = rng.coeff();
        if w != 0.0 {
            eq.push((c, -w));
        }
    }
    rows.push(model.add_row(0.0, 0.0, &eq));
    let mut cols = vec![x0];
    cols.extend(inputs);
    (model, cols, rows)
}

/// The identical LP as a CPLEX LP file with objective `minimize x0`.
fn to_lp_format(model: &Model, cols: &[Col], rows: &[Row]) -> String {
    let mut s = String::from("Minimize\n obj: x0\nSubject To\n");
    for (i, &r) in rows.iter().enumerate() {
        let (coeffs, lb, ub) = model.row(r);
        let mut lhs = String::new();
        for &(c, a) in coeffs {
            let _ = write!(lhs, " {a:+} x{c}");
        }
        // A range row a·x ∈ [lb, ub] as two one-sided constraints.
        let _ = writeln!(s, " c{i}lo:{lhs} >= {lb}");
        let _ = writeln!(s, " c{i}hi:{lhs} <= {ub}");
    }
    s.push_str("Bounds\n");
    for (j, &c) in cols.iter().enumerate() {
        let (lb, ub) = model.col_bounds(c);
        let _ = writeln!(s, " {lb} <= x{j} <= {ub}");
    }
    s.push_str("End\n");
    s
}

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    let n: usize = a.first().and_then(|s| s.parse().ok()).unwrap_or(200);
    let m: usize = a.get(1).and_then(|s| s.parse().ok()).unwrap_or(150);
    let seed: u64 = a.get(2).and_then(|s| s.parse().ok()).unwrap_or(12_345);

    let (model, cols, rows) = build(n, m, seed);
    if let Ok(path) = std::env::var("W2_DUMP") {
        std::fs::write(&path, to_lp_format(&model, &cols, &rows)).expect("write LP");
    }
    let mut s = LpSession::new(&model, &SolveOpts::new()).expect("continuous model");
    let t0 = Instant::now();
    let out = s.rigorous_bound(cols[0], Sense::Minimize).expect("bound");
    let dt = t0.elapsed().as_secs_f64();
    match out {
        Outcome::Bound {
            dual_bound,
            rigorous,
        } => {
            let b = dual_bound
                .numer()
                .to_string()
                .parse::<f64>()
                .unwrap_or(f64::NAN)
                / dual_bound.denom().to_string().parse::<f64>().unwrap_or(1.0);
            println!("bound = {b:.9}  rigorous = {rigorous}");
            println!("time    = {dt:.4}s");
        }
        other => {
            println!("NO BOUND: {other:?}");
            println!("time    = {dt:.4}s");
        }
    }
}
