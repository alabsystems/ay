// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Measure the P1 float lane against the exact rim, and emit the same LP in
//! CPLEX-LP format so HiGHS can be asked the same question independently.
//!
//! The design doc's G1 is a *measured* claim, and this repo's standing lesson is
//! that synthetic gains do not transfer — so this prints the optimum alongside
//! every timing. A speedup that changes the answer is not a speedup, and the
//! HiGHS column is what makes that checkable by something that is not ay.
//!
//! ```text
//! cargo run --release -p ay-milp --example lp_speed -- 60 40
//! AY_MILP_NO_FLOAT=1 cargo run --release -p ay-milp --example lp_speed -- 60 40
//! ```

use std::fmt::Write as _;
use std::time::Instant;

use ay_milp::{Col, LpSession, Model, Outcome, Row, Sense, SolveOpts};

/// A deterministic LCG. Reproducibility matters more than statistical quality:
/// the same instance must be handed to every solver in the comparison.
struct Rng(u64);
impl Rng {
    fn next_u32(&mut self) -> u32 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1);
        (self.0 >> 33) as u32
    }
    /// A small integer coefficient — keeps the exact optimum human-checkable and
    /// keeps the rim's rationals from exploding for reasons unrelated to the LP.
    fn coeff(&mut self) -> f64 {
        f64::from(self.next_u32() % 9) - 4.0
    }
}

/// A random bounded LP: `n` columns in `[0, 10]`, `m` rows `a·x <= b`, all
/// coefficients small integers. Bounded and feasible by construction (`x = 0`
/// satisfies every row, since every `b >= 0`).
fn build(n: usize, m: usize, seed: u64) -> (Model, Vec<Col>, Vec<Row>) {
    let mut rng = Rng(seed);
    let mut model = Model::new();
    let cols: Vec<_> = (0..n).map(|_| model.add_col(0.0, 10.0)).collect();
    let mut rows: Vec<Row> = Vec::new();
    for _ in 0..m {
        let terms: Vec<_> = cols
            .iter()
            .filter_map(|&c| {
                let a = rng.coeff();
                (a != 0.0).then_some((c, a))
            })
            .collect();
        if terms.is_empty() {
            continue;
        }
        let b = f64::from(rng.next_u32() % 40) + 10.0;
        rows.push(model.add_row(f64::NEG_INFINITY, b, &terms));
    }
    let obj: Vec<_> = cols.iter().map(|&c| (c, rng.coeff())).collect();
    model.set_objective(&obj, Sense::Maximize);
    (model, cols, rows)
}

/// The same model as a CPLEX LP file, so HiGHS can be asked independently.
fn to_lp_format(model: &Model, cols: &[Col], rows: &[Row]) -> String {
    let mut s = String::from("Maximize\n obj:");
    for (j, &c) in cols.iter().enumerate() {
        let a = model.obj_coeff(c);
        if a != 0.0 {
            let _ = write!(s, " {a:+} x{j}");
        }
    }
    s.push_str("\nSubject To\n");
    for (i, &r) in rows.iter().enumerate() {
        let (coeffs, _, ub) = model.row(r);
        let _ = write!(s, " c{i}:");
        for &(c, a) in coeffs {
            let _ = write!(s, " {a:+} x{c}");
        }
        let _ = writeln!(s, " <= {ub}");
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
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(60);
    let m: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(40);
    let seed: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(12_345);

    let (model, cols, rows) = build(n, m, seed);
    let lane = if std::env::var_os("AY_MILP_NO_FLOAT").is_some() {
        "exact rim (float lane OFF)"
    } else {
        "float lane + exact certification"
    };
    eprintln!("LP: {n} cols x {m} rows   lane: {lane}");

    if let Ok(path) = std::env::var("LP_DUMP") {
        std::fs::write(&path, to_lp_format(&model, &cols, &rows)).expect("write LP file");
        eprintln!("wrote {path} (feed it to HiGHS for an independent optimum)");
    }

    let mut s = LpSession::new(&model, &SolveOpts::new()).expect("continuous model");
    let t0 = Instant::now();
    let out = s.optimize_model_objective().expect("solve");
    let dt = t0.elapsed();

    match out {
        Outcome::Optimal { value, cert, .. } => {
            // Print enough precision to compare against HiGHS, and the exact
            // rational so two ay lanes can be compared bit-for-bit.
            let approx = value.numer().to_string().parse::<f64>().unwrap_or(f64::NAN)
                / value.denom().to_string().parse::<f64>().unwrap_or(1.0);
            println!("optimum = {approx:.9}");
            println!("exact   = {value}");
            println!("cert    = {}", if cert.is_some() { "yes" } else { "NONE" });
            println!("time    = {:.3}s", dt.as_secs_f64());
        }
        other => {
            println!("NO OPTIMUM: {other:?}");
            println!("time    = {:.3}s", dt.as_secs_f64());
        }
    }
}
