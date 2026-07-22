// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Measure the native branch-and-bound (P2) against the ay-dpll `smt` lane it
//! replaces, and emit the same MILP for HiGHS so a third party settles the
//! answer.
//!
//! ```text
//! cargo run --release -p ay-milp --features smt --example milp_speed -- 30 20
//! AY_MILP_SMT=1 cargo run --release -p ay-milp --features smt --example milp_speed -- 30 20
//! ```

use std::fmt::Write as _;
use std::time::Instant;

use ay_milp::{BabSession, Col, Model, Outcome, Row, Sense, SolveOpts};

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

/// A 0/1 knapsack-ish MILP: `n` binary columns, `m` covering rows. Always
/// feasible (all-zero satisfies every `<=` row) and bounded (the box is `{0,1}`).
fn build(n: usize, m: usize, seed: u64) -> (Model, Vec<Col>, Vec<Row>) {
    let mut rng = Rng(seed);
    let mut model = Model::new();
    let cols: Vec<_> = (0..n).map(|_| model.add_binary_col()).collect();
    let mut rows = Vec::new();
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
        let b = f64::from(rng.next_u32() % 12) + 3.0;
        rows.push(model.add_row(f64::NEG_INFINITY, b, &terms));
    }
    let obj: Vec<_> = cols
        .iter()
        .map(|&c| (c, f64::from(rng.next_u32() % 10) + 1.0))
        .collect();
    model.set_objective(&obj, Sense::Maximize);
    (model, cols, rows)
}

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
    s.push_str("Binaries\n");
    for j in 0..cols.len() {
        let _ = write!(s, " x{j}");
    }
    s.push_str("\nEnd\n");
    s
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let n: usize = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(30);
    let m: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(20);
    let seed: u64 = args.get(3).and_then(|s| s.parse().ok()).unwrap_or(2_026);

    let (model, cols, rows) = build(n, m, seed);
    let lane = if std::env::var_os("AY_MILP_SMT").is_some() {
        "ay-dpll smt lane"
    } else {
        "native branch-and-bound"
    };
    eprintln!("MILP: {n} binaries x {m} rows   lane: {lane}");

    if let Ok(path) = std::env::var("LP_DUMP") {
        std::fs::write(&path, to_lp_format(&model, &cols, &rows)).expect("write LP");
        eprintln!("wrote {path}");
    }

    // A time limit, so an unfinished solve reports its incumbent rather than grinding on
    // — which is what makes a like-for-like comparison against another solver's
    // time-limited run possible at all.
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
        Outcome::Optimal { value, .. } => {
            println!("optimum = {value}");
            println!("time    = {:.3}s", dt.as_secs_f64());
        }
        Outcome::Feasible {
            model_values,
            dual_bound,
            ..
        } => {
            // Not proven optimal — report the incumbent's VALUE so it can be compared
            // against another solver's primal bound on the same instance.
            let mut v = num_rational::BigRational::from_integer(0.into());
            for (j, &c) in cols.iter().enumerate() {
                let a = s.model().obj_coeff(c);
                if a != 0.0 {
                    let a = num_rational::BigRational::from_float(a).unwrap();
                    v += a * &model_values[j];
                }
            }
            println!("incumbent (NOT proven optimal) = {v}");
            if let Some(db) = dual_bound {
                println!("dual bound (rigorous) = {db}");
            }
            if std::env::var_os("AY_MILP_PRINT_POINT").is_some() {
                let s: String = model_values
                    .iter()
                    .map(|v| {
                        if v.is_integer() && *v == num_rational::BigRational::from_integer(1.into())
                        {
                            '1'
                        } else {
                            '0'
                        }
                    })
                    .collect();
                println!("point   = {s}");
            }
            println!("time    = {:.3}s", dt.as_secs_f64());
        }
        other => {
            println!("NO OPTIMUM: {other:?}");
            println!("time    = {:.3}s", dt.as_secs_f64());
        }
    }
}
