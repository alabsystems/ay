// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Measure the native branch-and-bound on SPARSE instances — the regime the downstream optimization consumer's
//! workload lives in (thousands of columns, a handful of nonzeros per row),
//! where the basis engines genuinely differ. The dense bench family cannot
//! separate them: a 60-row dense basis fills either way.
//!
//! ```text
//! cargo run --release -p ay-milp --example milp_sparse_speed -- 2000 1500 6
//! AY_MILP_LU=1 TIME_LIMIT=30 ... -- 2000 1500 6
//! ```

use std::time::Instant;

use ay_milp::{BabSession, Model, Outcome, Sense, SolveOpts};

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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2000);
    let m: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(1500);
    let k: usize = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(6);
    let seed: u64 = args.get(4).and_then(|s| s.parse().ok()).unwrap_or(2026);

    let mut rng = Rng(seed);
    let mut model = Model::new();
    let cols: Vec<_> = (0..n).map(|_| model.add_binary_col()).collect();
    let mut nnz = 0usize;
    for _ in 0..m {
        let mut terms = Vec::with_capacity(k);
        for _ in 0..k {
            let c = cols[(rng.next_u32() as usize) % n];
            let a = rng.coeff();
            if a != 0.0 {
                terms.push((c, a));
            }
        }
        if terms.is_empty() {
            continue;
        }
        nnz += terms.len();
        let b = f64::from(rng.next_u32() % 12) + 3.0;
        model.add_row(f64::NEG_INFINITY, b, &terms);
    }
    let obj: Vec<_> = cols
        .iter()
        .map(|&c| (c, f64::from(rng.next_u32() % 10) + 1.0))
        .collect();
    model.set_objective(&obj, Sense::Maximize);
    eprintln!("sparse MILP: {n} binaries x {m} rows, ~{nnz} nnz");

    let mut opts = SolveOpts::new();
    if let Ok(secs) = std::env::var("TIME_LIMIT") {
        if let Ok(secs) = secs.parse::<f64>() {
            opts = opts.with_time_limit(std::time::Duration::from_secs_f64(secs));
        }
    }
    let mut s = BabSession::new(model, &opts).expect("model");
    let t0 = Instant::now();
    let out = s.check().expect("solve");
    let dt = t0.elapsed();
    match out {
        Outcome::Optimal { value, .. } => println!("optimum = {value} in {:.3}s", dt.as_secs_f64()),
        Outcome::Feasible { .. } => println!("incumbent (unproven) in {:.3}s", dt.as_secs_f64()),
        other => println!("no optimum: {other:?} in {:.3}s", dt.as_secs_f64()),
    }
}
