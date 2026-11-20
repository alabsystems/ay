// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Time the float LP lane NY uses (`LpSession::float_dual_for_expr`, then
//! `rigorous_bound`) on the LP relaxation of one of NY's captured `.milp`
//! dumps (`crates/ny-mip/corpus/hard-six` in NY), with the per-phase
//! iteration ledger.
//!
//! ```text
//! targo --unverified run --release -p ay-milp --example ny_lp_probe -- <file.milp> [seconds] [objectives]
//! ```

use std::time::{Duration, Instant};

use ay_milp::{LpSession, Model, Outcome, Sense, SolveOpts};

fn hex(t: &str) -> f64 {
    f64::from_bits(u64::from_str_radix(t, 16).expect("hex f64"))
}

/// Parse NY's `milp v1` dump into its LP relaxation (integrality dropped).
fn relaxation(text: &str) -> (Model, usize) {
    let mut lines = text
        .lines()
        .map(|l| l.split('#').next().unwrap_or("").trim())
        .filter(|l| !l.is_empty());
    assert_eq!(lines.next(), Some("milp v1"));
    let ncols: usize = lines.next().unwrap()["cols ".len()..]
        .trim()
        .parse()
        .unwrap();
    let mut model = Model::new();
    let mut cols = Vec::with_capacity(ncols);
    let mut binaries = 0;
    for _ in 0..ncols {
        let mut f = lines.next().unwrap().split_ascii_whitespace();
        let (lb, ub) = (hex(f.next().unwrap()), hex(f.next().unwrap()));
        let _obj = hex(f.next().unwrap());
        binaries += usize::from(f.next().unwrap() == "1");
        cols.push(model.add_col(lb, ub));
    }
    let nrows: usize = lines.next().unwrap()["rows ".len()..]
        .trim()
        .parse()
        .unwrap();
    for _ in 0..nrows {
        let mut f = lines.next().unwrap().split_ascii_whitespace();
        let (lb, ub) = (hex(f.next().unwrap()), hex(f.next().unwrap()));
        let n: usize = f.next().unwrap().parse().unwrap();
        let mut coeffs = Vec::with_capacity(n);
        for _ in 0..n {
            let c: usize = f.next().unwrap().parse().unwrap();
            coeffs.push((cols[c], hex(f.next().unwrap())));
        }
        model.add_row(lb, ub, &coeffs);
    }
    (model, binaries)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let path = args
        .first()
        .expect("usage: ny_lp_probe <file.milp> [seconds] [objectives]");
    let secs: f64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(60.0);
    let objectives: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(4);
    let text = std::fs::read_to_string(path).expect("read .milp");
    let (model, binaries) = relaxation(&text);
    let nnz: usize = (0..model.num_rows())
        .map(|r| model.row(model.row_at(r).unwrap()).0.len())
        .sum();
    println!(
        "PROBE {} cols ({binaries} were binary), {} rows, {nnz} nnz",
        model.num_cols(),
        model.num_rows()
    );
    ay_milp::enable_iter_ledger();
    let opts = SolveOpts::new().with_time_limit(Duration::from_secs_f64(secs));
    let mut session = LpSession::new(&model, &opts).expect("continuous relaxation");
    // `--obbt K`: one OBBT round (NY's `ny-mip/src/tighten.rs` workload) over
    // the K finite columns with the widest boxes.
    if let Some(k) = args
        .iter()
        .position(|a| a == "--obbt")
        .and_then(|i| args.get(i + 1))
        .and_then(|v| v.parse::<usize>().ok())
    {
        let mut widths: Vec<(f64, usize)> = (0..model.num_cols())
            .filter_map(|j| {
                let (l, u) = model.col_bounds(model.col_at(j).unwrap());
                (l.is_finite() && u.is_finite() && u > l).then_some((u - l, j))
            })
            .collect();
        widths.sort_by(|a, b| b.0.total_cmp(&a.0).then(a.1.cmp(&b.1)));
        let cols: Vec<_> = widths
            .iter()
            .take(k)
            .map(|&(_, j)| model.col_at(j).unwrap())
            .collect();
        let obbt = ay_milp::ObbtOpts {
            max_rounds: 1,
            ..ay_milp::ObbtOpts::default()
        };
        let t = Instant::now();
        let report = session.obbt(&cols, &obbt).expect("valid columns");
        let shrink: f64 = report
            .bounds
            .iter()
            .zip(&widths)
            .map(|(&(l, u), &(w, _))| 1.0 - (u - l) / w)
            .sum::<f64>()
            / report.bounds.len().max(1) as f64;
        println!(
            "PROBE obbt {} cols in {:?}: tightened {}, mean width shrink {:.1}%, infeasible {}",
            cols.len(),
            t.elapsed(),
            report.tightened,
            100.0 * shrink,
            report.infeasible
        );
        return;
    }
    // The last columns of NY's encodings are the output/margin columns.
    let n = model.num_cols();
    for k in 0..objectives {
        let col = model.col_at(n - 1 - k).unwrap();
        for sense in [Sense::Minimize, Sense::Maximize] {
            let t = Instant::now();
            let duals = session
                .float_dual_for_expr(&[(col, 1.0)], sense)
                .expect("valid");
            let float_t = t.elapsed();
            let t = Instant::now();
            let bound = session.rigorous_bound(col, sense).expect("valid");
            let bound_t = t.elapsed();
            let shown = match &bound {
                Outcome::Bound { dual_bound, .. } => {
                    format!(
                        "{:.6}",
                        num_traits::ToPrimitive::to_f64(dual_bound).unwrap_or(f64::NAN)
                    )
                }
                other => format!("{other:?}").chars().take(50).collect(),
            };
            println!(
                "PROBE col {} {sense:?}: float {float_t:?} (duals {}), rigorous {bound_t:?} -> {shown}",
                col.index(),
                duals.is_some()
            );
            println!("PROBE   {}", ay_milp::iter_ledger_line());
        }
    }
}
